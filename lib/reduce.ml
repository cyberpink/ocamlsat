open State
module CA = Clause_arena

let reduce_db s =
  let old_limit = s.learned_limit in
  s.learned_limit <- Float.to_int (Float.of_int old_limit *. s.learned_growth);
  CA.ClauseVec.iter
    (fun c -> if CA.is_used s.clauses c then Clause.update_lbd s c)
    s.learned_clauses;
  CA.ClauseVec.sort (fun a b -> Int.compare (CA.lbd s.clauses b) (CA.lbd s.clauses a))
    s.learned_clauses;
  let to_delete = ref (old_limit / 2) in
  CA.ClauseVec.filter_inplace (fun c ->
      let used = CA.is_used s.clauses c in
      if used then CA.clear_used s.clauses c;
      if CA.lbd s.clauses c <= 2 || CA.is_deleted s.clauses c then
        false
      else if !to_delete <= 0 || used || Clause.clause_is_locked s c then
        true
      else
        (CA.set_deleted s.clauses c; decr to_delete; false))
    s.learned_clauses;
  compact_arena s
