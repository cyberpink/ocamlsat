open Common

type t = IntVec.t
let create () : t = IntVec.create ~capacity:8 0

(*  (msb..lsb) { is_bin : 1; clause : 31; other : 31 } *)
let bin_bit = 1 lsl 62
let[@inline] is_bin w = w land bin_bit <> 0
let[@inline] is_long w = w land bin_bit = 0
let[@inline] unpack_other w = Lit.of_int (w land 0x7FFFFFFF)
let[@inline] unpack_clause w = Clause_arena.Ref.of_int (w lsr 31)
let[@inline] unpack w = (unpack_clause w, unpack_other w)

let[@inline] pack clause other =
  let other_i = Lit.to_int other in
  let clause_i = Clause_arena.Ref.to_int clause in
  (clause_i lsl 31) lor other_i

let[@inline] push ws clause other = IntVec.push ws (pack clause other)
let[@inline] push_bin ws other = IntVec.push ws ((Lit.to_int other) lor bin_bit)
