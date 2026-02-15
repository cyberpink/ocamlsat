open Common

type t = Reason of int [@@unboxed]

let root = Reason (-1)
let decision = Reason (-2)
let[@inline] clause c = Reason (Clause_arena.Ref.to_int c)
let[@inline] bin l = Reason (-(Lit.to_int l + 3))

type prj = Root | Decision | Clause of Clause_arena.Ref.t | Bin of Lit.t
let[@inline always] prj (Reason r) = match r with
  | -1 -> Root
  | -2 -> Decision
  | x when x >= 0 -> Clause (Clause_arena.Ref.of_int x)
  | x -> Bin (Lit.of_int ((-x) - 3))
