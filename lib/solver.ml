open Common
open State
module CA = Clause_arena

exception Conflict of (Lit.t * Reason.t)

let run_watchers s neg_l (ws : Watch.t) =
  let {values; clauses; watchers; _} = s in
  let i = ref 0 in
  let j = ref 0 in
  let ws_len = IntVec.length ws in
  let ws_data = ws.data in
  let conflict c =
    for i = (!i - 1) to ws_len - 1 do
      let x = Array.unsafe_get ws_data i in
      Array.unsafe_set ws_data !j x;
      incr j
    done;
    IntVec.truncate ws !j;
    raise_notrace (Conflict c)
  in
  while !i < ws_len do
    let w = Array.unsafe_get ws_data !i in
    incr i;
    let other = Watch.unpack_other w in
    let other_v = get_value values other in
    if other_v = ltrue then
      (Array.unsafe_set ws_data !j w;
       incr j)
    else if Watch.is_bin w then
      if other_v = lfalse
      then conflict (neg_l, Reason.bin other)
      else begin
        set_true s other (Reason.bin neg_l);
        Array.unsafe_set ws_data !j w;
        incr j
      end
    else
      let clause = Watch.unpack_clause w in
      (* currently, watchers on deleted clauses are already cleaned up *)
      (* if not (CA.is_deleted s.clauses clause) then *)
      let lits = CA.lits s.clauses clause in
      s.simp_props <- s.simp_props - 1;
      if neg_l = LitSlice.unsafe_get lits 0 then
        LitSlice.unsafe_swap lits 0 1;
      let other = LitSlice.unsafe_get lits 0 in
      let other_v = get_value values other in
      if other_v = ltrue then
        (Array.unsafe_set ws_data !j (Watch.pack clause other);
         incr j)
      else
        let clause_len = LitSlice.length lits in
        let last = CA.searched clauses clause in
        let rec find i =
          if i < clause_len then
            if get_value values (LitSlice.unsafe_get lits i) = lfalse
            then find (i + 1)
            else i
          else find' 2
        and find' i =
          if i < last then
            if get_value values (LitSlice.unsafe_get lits i) = lfalse
            then find' (i + 1)
            else i
          else -1
        in
        match find last with
        | -1 when other_v = lfalse ->
          conflict (neg_l, Reason.clause clause)
        | -1 ->
          set_true s other (Reason.clause clause);
          Array.unsafe_set ws_data !j (Watch.pack clause other);
          incr j
        | swap_idx ->
          CA.set_searched clauses clause swap_idx;
          let new_l = LitSlice.unsafe_get lits swap_idx in
          LitSlice.unsafe_set lits 1 new_l;
          LitSlice.unsafe_set lits swap_idx neg_l;
          Watch.push (get_watchers watchers new_l) clause other
  done;
  IntVec.truncate ws !j

let propagate s =
  let {watchers; trail; _} = s in
  try
    while s.trail_head < s.trail_length do
      let neg_l = Lit.neg (Array.unsafe_get trail s.trail_head) in
      s.trail_head <- s.trail_head + 1;
      run_watchers s neg_l (get_watchers watchers neg_l);
    done;
    None
  with Conflict c -> Some c

let backjump s target_level =
  let {values; trail; levels; reasons; saved_phase; unassigned_vars; _} = s in
  let rec go i =
    if i < 0 then
      0
    else
      let l = Array.unsafe_get trail i in
      let v = Lit.var l in
      let vi = Var.to_int v in
      if levels.%(v) <= target_level
      then        
        i + 1
      else begin
        unset_value values l;
        saved_phase.%[v] <- Lit.phase l;
        levels.%(v) <- (-1);
        Array.unsafe_set reasons vi Reason.root;
        Decision_heap.insert unassigned_vars v;
        go (i - 1)
      end
  in
  let new_len = go (s.trail_length - 1) in
  s.trail_length <- new_len;
  s.trail_head <- new_len;
  s.current_level <- target_level


let rec pick_literal s =
  match Decision_heap.pop_max s.unassigned_vars with
  | None -> None
  | Some v ->
    let vi = Var.to_int v in
    if s.values.%[v] <> lundef
    then pick_literal s
    else Some (Lit.makei vi s.saved_phase.%[v])

let rec solve (s : state) =
  match propagate s with
  | None when s.current_level = 0
           && s.trail_length > s.simp_assigns
           && s.simp_props <= 0 ->
    let new_lit_count = Simplify.simplify s in
    s.simp_props <- new_lit_count;
    s.simp_assigns <- s.trail_length;
    solve s
  | None ->
    save_target_phases s;
    begin match pick_literal s with
      | None -> ()
      | Some l ->
        s.current_level <- s.current_level + 1;
        set_true s l Reason.decision;
        solve s
    end
  | Some (con_lit, con_clause) ->
    if s.current_level = 0 then raise_notrace Unsat;

    let (learned_lits, lbd, backjump_level) =
      Analyze.analyze_conflict s con_lit con_clause in
    Decision_heap.decay_activity s.unassigned_vars;

    if CA.ClauseVec.length s.learned_clauses >= s.learned_limit then
      Reduce.reduce_db s;

    let reason : Reason.t =
      if LitVec.length learned_lits = 1 then
        Reason.root
      else if LitVec.length learned_lits = 2 then
        let l0 = LitVec.get learned_lits 0 in
        let l1 = LitVec.get learned_lits 1 in
        Watch.push_bin (get_watchers s.watchers l0) l1;
        Watch.push_bin (get_watchers s.watchers l1) l0;
        Reason.bin l1
      else
        let lits = LitSlice.make ~offset:0 ~length:(LitVec.length learned_lits)
            learned_lits.data in
        let learned_clause = CA.alloc s.clauses true lbd lits in
        (* lbd might have changed during minimization
           so set used to keep for at least 1 round and update lbd *)
        CA.set_used s.clauses learned_clause;
        (* don't insert permanent clauses into removal candidates *)
        if lbd > 2 then
          CA.ClauseVec.push s.learned_clauses learned_clause;

        let l0 = CA.get_lit s.clauses learned_clause 0 in
        let l1 = CA.get_lit s.clauses learned_clause 1 in
        Watch.push (get_watchers s.watchers l0) learned_clause l1;
        Watch.push (get_watchers s.watchers l1) learned_clause l0;
        Reason.clause learned_clause
    in

    backjump s backjump_level;
    set_true s (LitVec.get learned_lits 0) reason;

    s.conflicts <- s.conflicts + 1;
    if s.conflicts >= s.next_restart then begin
      s.restarts <- s.restarts + 1;
      s.next_restart <- s.conflicts + (luby s.restarts * s.restart_coeff);
      backjump s 0;

      if s.conflicts >= s.rephase_limit then
        rephase_all s;
    end;
    solve s
