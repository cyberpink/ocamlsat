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
module IntSlice = Mono_slice.Make(Int)
module LitVec = Mono_vec.Make(Lit)
module LitSlice = Mono_slice.Make(Lit)

exception Unsat
let ltrue = 0
let lfalse = 1
let lundef = 2

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
