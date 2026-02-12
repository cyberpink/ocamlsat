module Make(El : sig type t [@@immediate] end) = struct
  type t =
    { mutable data : El.t array;
      mutable length : int;
      dummy : El.t }

  let[@inline] length v = v.length
  let[@inline] capacity v = Array.length v.data

  (* from Stdlib.Dynarray *)
  let next_capacity n =
    let n' =
      if n <= 512 then n * 2
      else n + n / 2
    in min (max 8 n') Sys.max_array_length

  let grow v =
    let new_cap = next_capacity (capacity v) in
    let new_data = Array.make new_cap v.dummy in
    Array.blit v.data 0 new_data 0 v.length;
    v.data <- new_data

  let ensure_capacity v capacity_request =
    let data = v.data in
    let cur_capacity = Array.length data in
    if capacity_request < 0 then
      raise (Invalid_argument "Monovec.ensure_capacity: negative capacity")
    else if cur_capacity >= capacity_request then
      ()
    else begin
      if capacity_request > Sys.max_array_length then
        raise (Invalid_argument "Monovec.ensure_capacity: requested size too large");
      let new_capacity =
        max (next_capacity cur_capacity) capacity_request in
      assert (new_capacity > 0);
      let new_data = Array.make new_capacity v.dummy in
      Array.blit v.data 0 new_data 0 v.length;
      v.data <- new_data
    end

  let ensure_extra_capacity a extra_capacity_request =
    ensure_capacity a (length a + extra_capacity_request)

  let create ?(capacity = 0) dummy : t =
    { length = 0; dummy; data = Array.make capacity dummy;  }

  let is_empty v = v.length = 0
  let pop v =
    let last = v.length - 1 in
    let x = v.data.(last) in
    v.length <- last;
    x

  let[@inline] unsafe_get v i = Array.unsafe_get v.data i
  let[@inline] unsafe_set v i x = Array.unsafe_set v.data i x
  let[@inline] unsafe_swap v i1 i2 =
    let open Array in
    let tmp = unsafe_get v.data i1 in
    unsafe_set v.data i1 (unsafe_get v.data i2);
    unsafe_set v.data i2 tmp

  let[@inline] get v i =
    if i >= 0 && i < v.length
    then Array.unsafe_get v.data i
    else raise (Invalid_argument "Vec.get: index out of bounds")
  let[@inline] set v i x =
    if i >= 0 && i < v.length
    then Array.unsafe_set v.data i x
    else raise (Invalid_argument "Vec.set: index out of bounds")
  let[@inline] swap v i1 i2 =
    if i1 >= 0 && i2 >= 0 && i1 < v.length && i2 < v.length
    then
      let open Array in
      let tmp = unsafe_get v.data i1 in
      unsafe_set v.data i1 (unsafe_get v.data i2);
      unsafe_set v.data i2 tmp
    else
      raise (Invalid_argument "Vec.swap: index out of bounds")

  let[@inline] to_array v = Array.sub v.data 0 v.length

  let push v x =
    let next = v.length in
    if next = capacity v then grow v;
    Array.unsafe_set v.data next x;
    v.length <- next + 1

  let push_array v a =
    let a_len = Array.length a in
    let new_len = v.length + a_len in
    ensure_capacity v new_len;
    Array.blit a 0 v.data v.length a_len;
    v.length <- new_len

  let truncate v len =
    let len = max 0 (min v.length len) in
    (* don't need to fill for a uniform vec *)
    (* Array.fill v.data len (v.length - len) v.dummy; *)
    v.length <- len

  let[@inline] clear v = v.length <- 0

  let copy v = { v with data = Array.copy v.data; }

  let delete_swap v i =
    let data = v.data in
    let length' = v.length - 1 in
    v.length <- length';
    Array.unsafe_set v.data i (Array.unsafe_get data length')
    (* Array.unsafe_set data length' v.dummy *)

  let filter_inplace fn v =
    let data = v.data in
    let j = ref 0 in
    for i = 0 to v.length - 1 do
      let x = Array.unsafe_get data i in
      if fn x then
        (Array.unsafe_set data !j x;
         incr j)
    done;
    truncate v !j

  let map_inplace fn v =
    let data = v.data in
    for i = 0 to v.length - 1 do
      let v = Array.unsafe_get data i in
      Array.unsafe_set data i (fn v)
    done

  let filter_map_inplace fn v =
    let data = v.data in
    let j = ref 0 in
    for i = 0 to v.length - 1 do
      let x = Array.unsafe_get data i in
      match fn x with
      | None -> ()
      | Some x ->
        Array.unsafe_set data !j x;
        incr j
    done;
    truncate v !j

  let iter (fn : 'a -> unit) v =
    let data = v.data in
    for i = 0 to v.length - 1 do
      fn (Array.unsafe_get data i)
    done

  let iter_range ~start ?length (fn : 'a -> unit) v =
    let length = Option.value ~default:(v.length - start) length in
    let data = v.data in
    for i = start to (start + length) - 1 do
      fn (Array.unsafe_get data i)
    done

  (* from Stdlib.Array *)
  exception Bottom of int
  let sort cmp (v : t) =
    let a = v.data in
    let open Array in
    let maxson l i =
      let i31 = i+i+i+1 in
      let x = ref i31 in
      if i31+2 < l then begin
        if cmp (unsafe_get a i31) (unsafe_get a (i31+1)) < 0 then x := i31+1;
        if cmp (unsafe_get a !x) (unsafe_get a (i31+2)) < 0 then x := i31+2;
        !x
      end else
      if i31+1 < l && cmp (unsafe_get a i31) (unsafe_get a (i31+1)) < 0
      then i31+1
      else if i31 < l then i31 else raise (Bottom i)
    in
    let rec trickledown l i e =
      let j = maxson l i in
      if cmp (unsafe_get a j) e > 0 then begin
        unsafe_set a i (unsafe_get a j);
        trickledown l j e;
      end else begin
        unsafe_set a i e;
      end;
    in
    let trickle l i e = try trickledown l i e with Bottom i -> unsafe_set a i e in
    let rec bubbledown l i =
      let j = maxson l i in
      unsafe_set a i (unsafe_get a j);
      bubbledown l j
    in
    let bubble l i = try bubbledown l i with Bottom i -> i in
    let rec trickleup i e =
      let father = (i - 1) / 3 in
      assert (i <> father);
      if cmp (unsafe_get a father) e < 0 then begin
        unsafe_set a i (unsafe_get a father);
        if father > 0 then trickleup father e else unsafe_set a 0 e;
      end else begin
        unsafe_set a i e;
      end;
    in
    let l = v.length (* length a *) in
    for i = (l + 1) / 3 - 1 downto 0 do trickle l i (unsafe_get a i); done;
    for i = l - 1 downto 2 do
      let e = (unsafe_get a i) in
      unsafe_set a i (unsafe_get a 0);
      trickleup (bubble i 0) e;
    done;
    if l > 1 then (let e = (unsafe_get a 1) in unsafe_set a 1 (unsafe_get a 0); unsafe_set a 0 e)

end
