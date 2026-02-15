open Common
    
module Ref = struct
  type t = CRef of int [@@unboxed] [@@immediate]
  let dummy = CRef (-1)
  let[@inline] of_int i = CRef i
  let[@inline] to_int (CRef i) = i
end
module ClauseVec = Mono_vec.Make(Ref)

module Header = struct
  let learned_bit = 1 lsl 0
  let deleted_bit = 1 lsl 1
  let shrunk_bit = 1 lsl 2
  let used_bit = 1 lsl 3
  let not_lbd_mask = (1 lsl 8) - 1

  let[@inline] is_learned h = h land learned_bit <> 0
  let[@inline] is_deleted h = h land deleted_bit <> 0
  let[@inline] is_shrunk h = h land shrunk_bit <> 0
  let[@inline] is_used h = h land used_bit <> 0
  let[@inline] lbd h = h lsr 8

  let[@inline] set_lbd h lbd = (h land not_lbd_mask) lor (lbd lsl 8)
  let[@inline] set_learned h = h lor learned_bit
  let[@inline] set_deleted h = h lor deleted_bit
  let[@inline] set_shrunk h = h lor shrunk_bit
  let[@inline] set_used h = h lor used_bit

  let[@inline] clear_used h = h land (lnot used_bit)
  let[@inline] clear_deleted h = h land (lnot deleted_bit)
  let[@inline] clear_shrunk h = h land (lnot shrunk_bit)
end
type arena = IntVec.t
let create ?capacity () = IntVec.create ?capacity 0

let[@inline] (.%()) (a : arena) r = Array.unsafe_get a.data (Ref.to_int r)
let[@inline] (.%()<-) (a : arena) r x = Array.unsafe_set a.data (Ref.to_int r) x

let[@inline] is_deleted a c = Header.is_deleted (a.%(c))
let[@inline] is_used a c = Header.is_used a.%(c)
let[@inline] is_learned a c = Header.is_learned a.%(c)
let[@inline] is_shrunk a c = Header.is_shrunk a.%(c)

let[@inline] set_used a c = a.%(c) <- Header.set_used a.%(c)
let[@inline] set_deleted a c = a.%(c) <- Header.set_deleted a.%(c)
let[@inline] clear_used a c = a.%(c) <- Header.clear_used  a.%(c)
let[@inline] clear_deleted a c = a.%(c) <- Header.clear_deleted (a.%(c))
let[@inline] clear_shrunk a c = a.%(c) <- Header.clear_shrunk a.%(c)

let[@inline] header a c = a.%(c)
let[@inline] lbd a c = Header.lbd a.%(c)
let[@inline] searched (a : arena) c = IntVec.unsafe_get a (Ref.to_int c + 1)
let[@inline] length (a : arena) c = IntVec.unsafe_get a (Ref.to_int c + 2)
let[@inline] lits (a : arena) clause =
  let offset = Ref.to_int clause + 3 in
  let length = IntVec.unsafe_get a (Ref.to_int clause + 2) in
  LitSlice.unsafe_make ~offset ~length (Obj.magic a.data : Lit.t array)

let padding (a : arena) c =
  if is_shrunk a c
  then IntVec.unsafe_get a (Ref.to_int c + 3 + (length a c))
  else 0

let[@inline] set_lbd a c lbd = a.%(c) <- Header.set_lbd a.%(c) lbd
let[@inline] set_searched a c x = IntVec.unsafe_set a (Ref.to_int c + 1) x

let shrink a c len =
  let old_len = length a c in
  let old_pad = padding a c in
  let d = old_len - len in
  set_searched a c (Int.min (searched a c) (len - 1));
  a.%(c) <- Header.set_shrunk a.%(c);
  IntVec.unsafe_set a (Ref.to_int c + 2) len;
  IntVec.unsafe_set a (Ref.to_int c + 3 + len) (old_pad + d)

let get_lit (a : arena) clause i =
  Lit.of_int (IntVec.unsafe_get a (Ref.to_int clause + 3 + i))
let set_lit (a : arena) clause i l =
  IntVec.unsafe_set a (Ref.to_int clause + 3 + i) (Lit.to_int l)

let alloc (a : arena) learned lbd (lits : LitSlice.t) = (* (lits : LitVec.t) = *)
  assert (LitSlice.length lits > 2);
  let i = IntVec.length a in
  let learned_bit = if learned then 1 else 0 in
  IntVec.push a (Header.set_lbd learned_bit lbd);
  IntVec.push a 2;
  IntVec.push a (LitSlice.length lits);
  LitSlice.iter (fun l -> IntVec.push a (Lit.to_int l)) lits;
  Ref.of_int i

let compact (a : arena) =
  let old_arena = a in
  let old_len = IntVec.length old_arena in
  let new_arena = create ~capacity:(IntVec.capacity old_arena) () in
  let i = ref 0 in
  while !i < old_len do
    let c_idx = !i in
    let c = Ref.of_int c_idx in
    let c_header = header old_arena c in
    let c_length = length old_arena c in
    begin
      if Header.is_deleted c_header then
        set_searched old_arena c (-1)
      else
        let new_id = IntVec.length new_arena in
        let c_searched = searched old_arena c in
        IntVec.push new_arena  (Header.clear_shrunk c_header);
        IntVec.push new_arena c_searched;
        IntVec.push new_arena c_length;
        let lits_start = c_idx + 3 in
        for i = lits_start to lits_start + c_length - 1 do
          IntVec.push new_arena (IntVec.get old_arena i)
        done;
        (* set forwarding pointer using "searched" slot *)
        set_searched old_arena c new_id
    end;
    i := c_idx + 3 + c_length;
    if Header.is_shrunk c_header then
      i := !i + (IntVec.get old_arena !i)
  done;
  new_arena

let iter fn (a : arena) =
  let len = IntVec.length a in
  let i = ref 0 in
  while !i < len do
    let c_idx = !i in
    let c = Ref.of_int c_idx in
    let c_header = header a c in
    let c_length = length a c in
    i := c_idx + 3 + c_length;
    if Header.is_shrunk c_header then
      i := !i + (IntVec.get a !i);
    if not (Header.is_deleted c_header) then
      fn (Ref.of_int c_idx);
  done

let count_lits a =
  let count = ref 0 in
  iter (fun c -> count := !count + length a c) a;
  !count
