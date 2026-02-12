external unsafe_get_uint8 : bytes -> int -> int = "%bytes_unsafe_get"
external unsafe_set_uint8 : bytes -> int -> int -> unit = "%bytes_unsafe_set"

module Var = struct
  type t = Var of int [@@unboxed] [@@immediate]
  let[@inline] of_int i = Var i
  let[@inline] to_int (Var i) = i
end

module Lit = struct
  type t = Lit of int [@@unboxed] [@@immediate]
  let dummy = Lit 0
  let[@inline] make v p = Lit ((Var.to_int v lsl 1) lor (if p then 0 else 1))
  let[@inline] makei v p = Lit ((v lsl 1) lor p)
  let[@inline] var (Lit l) = Var.of_int (l lsr 1)
  let[@inline] phase (Lit l) = l land 1
  let[@inline] sign (Lit l) = l land 1
  let[@inline] neg (Lit l) = Lit (l lxor 1)
  let[@inline] to_int (Lit l) = l
  let[@inline] of_int l = Lit l
  let[@inline] compare (Lit a) (Lit b) = Int.compare a b
  let to_string (Lit l) = string_of_int (l lsr 1 * if l land 1 = 0 then 1 else -1)
end

module IntVec = Mono_vec.Make(Int)
module LitVec = Mono_vec.Make(Lit)
module LitSlice = Mono_slice.Make(Lit)

module ClauseArena = struct
  module Ref = struct
    type t = CRef of int [@@unboxed] [@@immediate]
    let dummy = CRef (-1)
    let[@inline] of_int i = CRef i
    let[@inline] to_int (CRef i) = i
  end

  module Header = struct
    let learned_bit = 1
    let deleted_bit = 2
    let shrunk_bit = 4
    let used_bit = 8

    let[@inline] is_learned h = h land 1 = 1
    let[@inline] is_deleted h = (h lsr 1) land 1 = 1
    let[@inline] is_shrunk h = (h lsr 2) land 1 = 1
    let[@inline] is_used h = (h lsr 3) land 1 = 1
    let[@inline] lbd h = h lsr 8

    let not_lbd_mask = (1 lsl 8) - 1
    let[@inline] set_lbd h lbd = (h land not_lbd_mask) lor (lbd lsl 8)
    let[@inline] set_learned h = h lor learned_bit
    let[@inline] set_deleted h = h lor deleted_bit
    let[@inline] set_shrunk h = h lor shrunk_bit
    let[@inline] set_used h = h lor used_bit
  end

  type arena = IntVec.t
  let create ?capacity () = IntVec.create ?capacity 0

  let[@inline] (.%()) (a : arena) r = Array.unsafe_get a.data (Ref.to_int r)
  let[@inline] (.%()<-) (a : arena) r x = Array.unsafe_set a.data (Ref.to_int r) x

  let[@inline] is_deleted a c = Header.is_deleted (a.%(c))
  let[@inline] is_used a c = Header.is_used a.%(c)
  let[@inline] is_learned a c = Header.is_learned a.%(c)

  let[@inline] set_used a c = a.%(c) <- Header.set_used a.%(c)
  let[@inline] set_deleted a c = a.%(c) <- Header.set_deleted a.%(c)
  let[@inline] clear_used a c = a.%(c) <- ((lnot Header.used_bit) land a.%(c))
  let[@inline] clear_deleted a c = a.%(c) <- ((lnot Header.deleted_bit) land (a.%(c)))

  let[@inline] header a c = a.%(c)
  let[@inline] lbd a c = Header.lbd a.%(c)
  let[@inline] searched (a : arena) (Ref.CRef c) = IntVec.unsafe_get a (c + 1)
  let[@inline] length (a : arena) (Ref.CRef c) = a.data.(c + 2)
  let lits (a : arena) clause =
    let offset = Ref.to_int clause + 3 in
    let length = a.data.(Ref.to_int clause + 2) in
    LitSlice.unsafe_make ~offset ~length (Obj.magic a.data : Lit.t array)

  let[@inline] set_lbd a c lbd = a.%(c) <- Header.set_lbd a.%(c) lbd
  let[@inline] set_searched (a : arena) (Ref.CRef c) x = IntVec.unsafe_set a (c + 1) x

  let get_lit (a : arena) clause i =
    Lit.of_int (IntVec.unsafe_get a (Ref.to_int clause + 3 + i))
  let set_lit (a : arena) clause i l =
    IntVec.unsafe_set a (Ref.to_int clause + 3 + i) (Lit.to_int l)

  let alloc (a : arena) learned lbd (lits : LitVec.t) =
    let i = IntVec.length a in
    let learned_bit = if learned then 1 else 0 in
    IntVec.push a (Header.set_lbd learned_bit lbd);
    IntVec.push a 2;
    IntVec.push a (LitVec.length lits);
    LitVec.iter (fun l -> IntVec.push a (Lit.to_int l)) lits;
    Ref.of_int i

  let compact (a : arena) =
    let old_arena = a in
    let old_len = IntVec.length old_arena in
    let new_arena = create ~capacity:(IntVec.capacity old_arena) () in
    let read_idx = ref 0 in
    while !read_idx < old_len do
      let old_idx = !read_idx in
      let old_id = Ref.of_int old_idx in
      let old_length = IntVec.get old_arena (old_idx + 2) in
      read_idx := old_idx + 3 + old_length;
      if is_deleted old_arena old_id then
        IntVec.set old_arena (old_idx + 1) (-1)
      else
        let new_id = IntVec.length new_arena in
        let old_header = IntVec.get old_arena old_idx in
        let old_searched = IntVec.get old_arena (old_idx + 1) in
        let lits_start = old_idx + 3 in
        (* TODO: handle shrunk, reset searched to 2 *)
        IntVec.push new_arena old_header;
        IntVec.push new_arena old_searched;
        IntVec.push new_arena old_length;
        for i = lits_start to lits_start + old_length - 1 do
          IntVec.push new_arena (IntVec.get old_arena i)
        done;
        (* set forwarding pointer using "searched" slot *)
        IntVec.set old_arena (old_idx + 1) new_id;
    done;
    new_arena

  let iter fn (a : arena) =
    let len = IntVec.length a in
    let i = ref 0 in
    while !i < len do
      let c_idx = !i in
      let c_length = IntVec.get a (c_idx + 2) in
      fn (Ref.of_int c_idx);
      (* TODO: handle shrunk *)
      i := c_idx + 3 + c_length
    done
end

module ClauseVec = Mono_vec.Make(ClauseArena.Ref)

module Reason = struct
  type t = Reason of int [@@unboxed]

  let root = Reason (-1)
  let decision = Reason (-2)
  let[@inline] clause c = Reason (ClauseArena.Ref.to_int c)
  let[@inline] bin l = Reason (-(Lit.to_int l + 3))

  type prj = Root | Decision | Clause of ClauseArena.Ref.t | Bin of Lit.t
  let[@inline always] prj (Reason r) = match r with
    | -1 -> Root
    | -2 -> Decision
    | x when x >= 0 -> Clause (ClauseArena.Ref.of_int x)
    | x -> Bin (Lit.of_int ((-x) - 3))
end

exception Unsat

module Watchlist = struct
  type t = IntVec.t
  let create () : t = IntVec.create ~capacity:8 0

  (*  (msb..lsb) { is_bin : 1; clause : 31; other : 31 } *)
  let bin_bit = 1 lsl 62
  let[@inline] is_bin w = w land bin_bit <> 0
  let[@inline] unpack_other w = Lit.of_int (w land 0x7FFFFFFF)
  let[@inline] unpack_clause w = ClauseArena.Ref.of_int (w lsr 31)
  let[@inline] unpack w = (unpack_clause w, unpack_other w)

  let[@inline] pack clause other =
    let other_i = Lit.to_int other in
    let clause_i = ClauseArena.Ref.to_int clause in
    (clause_i lsl 31) lor other_i

  let[@inline] push ws clause other = IntVec.push ws (pack clause other)
  let[@inline] push_bin ws other = IntVec.push ws ((Lit.to_int other) lor bin_bit)
end

let ltrue = 0
let lfalse = 1
let lundef = 2
let[@inline] (.%[]) a v : int = unsafe_get_uint8 a (Var.to_int v)
let[@inline] (.%[]<-) a v (x : int) = unsafe_set_uint8 a (Var.to_int v) x
let[@inline] get_value a l = a.%[Lit.var l] lxor (Lit.phase l)
let[@inline] set_value a l = a.%[Lit.var l] <- Lit.phase l
let[@inline] unset_value a l = a.%[Lit.var l] <- lundef

let luby i =
  let rec loop i k =
    if (k lsl 1) <= i + 1 then
      loop i (k lsl 1)
    else if k = i + 1 then
      k lsr 1
    else
      loop (i - k + 1) 1
  in
  loop i 1
