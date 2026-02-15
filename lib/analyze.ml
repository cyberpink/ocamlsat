open Common
open State

(** resolution with binary watchers:
    mark all literals in the clause, 
    for each literal l in clause:
     for each binary watcher w of ~l:
       if w.other is in the learned clause:
         the literal being resolved can be removed from the clause
    https://www.msoos.org/2010/08/on-the-fly-self-subsuming-resolution/
*)
let binary_resolve s learned_lits =
  let lits_seen = s.lits_seen in
  let watchers = s.watchers in
  LitVec.iter (fun l -> lits_seen.$[l] <- 1) learned_lits;
  LitVec.iter (fun l ->
      let l' = Lit.neg l in
      IntVec.iter
        (fun w ->
           if Watch.is_bin w then
             let wl = Watch.unpack_other w in
             if lits_seen.$[wl] = 1 then
               lits_seen.$[l] <- 0)
        watchers.(Lit.to_int l')
    ) learned_lits;
  LitVec.filter_inplace (fun l -> lits_seen.$[l] = 1) learned_lits;
  LitVec.iter (fun l -> lits_seen.$[l] <- 0) learned_lits

let is_redundant s v =
  let { levels; reasons; analyze_seen; redundant_cache; clauses;
        levels_seen; redundant_to_clear; _ } = s in
  let rec go v =
    let vi = Var.to_int v in
    match redundant_cache.%[v] with
    | 1 -> true
    | 2 -> false
    | _ ->
      let level = levels.(vi) in
      if level = 0 then true
      else if unsafe_get_uint8 levels_seen level = 0 then false
      else
        let res =
          match Reason.prj reasons.(vi) with
          | Root -> true
          | Decision -> false
          | Bin other ->
            let v_other = Lit.var other in
            analyze_seen.%[v_other] = 1 || go v_other
          | Clause c ->
            LitSlice.for_all
              (fun l ->
                 let vl = Lit.var l in
                 vl = v || analyze_seen.%[vl] = 1 || go vl)
              (Clause_arena.lits clauses c)
        in
        IntVec.push redundant_to_clear vi;
        redundant_cache.%[v] <- if res then 1 else 2;
        res
  in go v

let analyze_conflict s lit conflict =
  let { levels; levels_seen; levels_to_clear; analyze_seen;
        reasons; clauses; learned_lits; analyze_to_clear; _ } = s in
  LitVec.clear learned_lits;
  LitVec.push learned_lits Lit.dummy;
  let counter = ref 0 in
  let lbd = ref 0 in
  let process_lit lit =
    let v = Lit.var lit in
    let level = levels.(Var.to_int v) in 
    if level > 0 && analyze_seen.%[v] = 0 then begin
      analyze_seen.%[v] <- 1;
      IntVec.push analyze_to_clear (Var.to_int v);
      if unsafe_get_uint8 levels_seen level = 0 then begin
        unsafe_set_uint8 levels_seen level 1;
        IntVec.push levels_to_clear level;
        incr lbd
      end;
      Decision_heap.bump s.unassigned_vars v;
      if level = s.current_level
      then incr counter
      else LitVec.push learned_lits lit
    end
  in
  let process_reason : Reason.t -> unit = fun r ->
    match Reason.prj r with
    | Root -> ()
    | Decision -> failwith "decision var in conflict graph"
    | Bin other -> process_lit other
    | Clause c ->
      Clause_arena.set_used clauses c;
      LitSlice.iter process_lit (Clause_arena.lits clauses c)
  in
  process_lit lit;
  process_reason conflict;

  let trail = s.trail in
  let rec walk i =
    let l = trail.(i) in
    let v = Lit.var l in
    let vi = Var.to_int v in
    if analyze_seen.%[v] = 1 then
      if !counter = 1 then 
        l
      else begin
        decr counter;
        process_reason reasons.(vi);
        walk (i - 1)
      end
    else walk (i - 1)
  in

  let uip = walk (s.trail_length - 1) in
  let uip' = Lit.neg uip in
  LitVec.set learned_lits 0 uip';

  LitVec.filter_inplace (fun l -> l = uip' || not (is_redundant s (Lit.var l)))
    learned_lits;

  (* binary_resolve seems to be too expensive to help *)
  (* binary_resolve s learned_lits; *)

  let learned_len = LitVec.length learned_lits in  
  let bt_level =
    if learned_len = 1
    then 0
    else
      let max_lvl = ref 0 in
      let max_idx = ref 1 in
      for i = 1 to learned_len - 1 do
        let l = LitVec.get learned_lits i in
        let lvl = levels.(Var.to_int (Lit.var l)) in
        if lvl > !max_lvl then (max_lvl := lvl; max_idx := i)
      done;
      let tmp = LitVec.get learned_lits !max_idx in
      LitVec.set learned_lits !max_idx (LitVec.get learned_lits 1);
      LitVec.set learned_lits 1 tmp;
      !max_lvl
  in

  IntVec.iter (fun vi -> s.redundant_cache.%[Var.of_int vi] <- 0) s.redundant_to_clear;
  IntVec.clear s.redundant_to_clear;

  IntVec.iter (fun vi -> analyze_seen.%[Var.of_int vi] <- 0) analyze_to_clear;
  IntVec.clear analyze_to_clear;

  IntVec.iter (fun l -> unsafe_set_uint8 levels_seen l 0) levels_to_clear;
  IntVec.clear levels_to_clear;

  (learned_lits, !lbd, bt_level)
