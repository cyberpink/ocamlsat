open Common
open State
module CA = Clause_arena

let compute_lbd s lits =
  let { levels_to_clear; levels_seen; levels; _} = s in
  let lbd = ref 0 in
  LitSlice.iter
    (fun lit ->
       let level = levels.%(Lit.var lit) in
       if level > 0 && unsafe_get_uint8 levels_seen level = 0 then
         (unsafe_set_uint8 levels_seen level 1;
          IntVec.push levels_to_clear level;
          incr lbd))
    lits;
  IntVec.iter (fun l -> unsafe_set_uint8 levels_seen l 0) levels_to_clear;
  IntVec.clear levels_to_clear;
  !lbd

let update_lbd s clause =
  let lits = CA.lits s.clauses clause in
  let new_lbd = compute_lbd s lits in
  if new_lbd < CA.lbd s.clauses clause
  then CA.set_lbd s.clauses clause new_lbd

let clause_is_locked s clause =
  let v = Lit.var (CA.get_lit s.clauses clause 0) in
  match Reason.prj (Array.unsafe_get s.reasons (Var.to_int v)) with
  | Clause c' -> clause = c'
  | _ -> false
