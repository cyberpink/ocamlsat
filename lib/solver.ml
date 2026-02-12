open Common
module CA = ClauseArena

type state = {
  num_vars : int;
  num_lits : int;

  values : Bytes.t;
  mutable clauses : CA.arena;
  watchers : Watchlist.t array;
  trail : Lit.t array;
  mutable trail_length : int;
  mutable trail_head : int;

  levels : int array;
  reasons : Reason.t array;
  mutable current_level : int;

  learned_lits : LitVec.t;
  learned_clauses : ClauseVec.t;
  learned_growth : float;
  mutable learned_limit : int;

  unassigned_vars : Decision_heap.t;

  restart_coeff : int;
  mutable conflicts : int;
  mutable next_restart : int;
  mutable restarts : int;

  simp_inc : int;
  mutable units : int;
  mutable simp_next : int;

  saved_phase : Bytes.t;
  target_phase : Bytes.t;
  mutable max_trail_size : int;
  mutable rephase_limit : int;
  rephase_inc : int;

  (* memo for lbd *)
  levels_seen : Bytes.t;
  levels_to_clear : IntVec.t;

  (* memos for finding 1-UIP and clause minimization *) 
  analyze_seen : Bytes.t;
  analyze_to_clear : IntVec.t;
  redundant_cache : Bytes.t;
  redundant_to_clear : IntVec.t;
  lits_seen : Bytes.t;
}

let compute_lbd s clause =
  let { levels_to_clear; levels_seen; levels; _} = s in
  let lbd = ref 0 in
  LitSlice.iter
    (fun lit ->
       let level = levels.(Var.to_int (Lit.var lit)) in
       if level > 0 && unsafe_get_uint8 levels_seen level = 0 then
         (unsafe_set_uint8 levels_seen level 1;
          IntVec.push levels_to_clear level;
          incr lbd))
    (CA.lits s.clauses clause);
  IntVec.iter (fun l -> unsafe_set_uint8 levels_seen l 0) levels_to_clear;
  IntVec.clear levels_to_clear;
  !lbd

let update_lbd s clause =
  let new_lbd = compute_lbd s clause in
  if new_lbd < CA.lbd s.clauses clause
  then CA.set_lbd s.clauses clause new_lbd

let clause_is_locked s clause =
  let v = Lit.var (CA.get_lit s.clauses clause 0) in
  match Reason.prj s.reasons.(Var.to_int v) with
  | Clause c' -> clause = c'
  | _ -> false

(** resolution with binary watchers:
    mark all literals in the clause, 
    for each literal l in clause:
     for each binary watcher w of ~l:
       if w.other is in the learned clause:
         the literal being resolved can be removed from the clause
    https://www.msoos.org/2010/08/on-the-fly-self-subsuming-resolution/
*)
let bin_resolve s learned_lits =
  let[@inline] (.%[]) a v : int = unsafe_get_uint8 a (Lit.to_int v) in
  let[@inline] (.%[]<-) a v (x : int) = unsafe_set_uint8 a (Lit.to_int v) x in
  let lits_seen = s.lits_seen in
  let watchers = s.watchers in
  LitVec.iter (fun l -> lits_seen.%[l] <- 1) learned_lits;
  LitVec.iter (fun l ->
      let l' = Lit.neg l in
      IntVec.iter
        (fun w ->
           (* if the watcher is a subset of the clause being resolved
              modulo ~l, then remove l from the clause *)
           if Watchlist.is_bin w then
             let wl = Watchlist.unpack_other w in
             if lits_seen.%[wl] = 1 then
               lits_seen.%[l] <- 0)
        watchers.(Lit.to_int l')
    ) learned_lits;
  LitVec.filter_inplace (fun l -> lits_seen.%[l] = 1) learned_lits;
  LitVec.iter (fun l -> lits_seen.%[l] <- 0) learned_lits

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
              (CA.lits clauses c)
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
      CA.set_used clauses c;
      LitSlice.iter process_lit (CA.lits clauses c)
  in
  process_lit lit;
  process_reason conflict;

  let trail = s.trail in
  let rec walk i =
    let l = Array.unsafe_get trail i in
    let v = Lit.var l in
    let vi = Var.to_int v in
    if analyze_seen.%[v] = 1 then
      if !counter = 1 then 
        l
      else begin
        decr counter;
        process_reason (Array.unsafe_get reasons vi);
        walk (i - 1)
      end
    else walk (i - 1)
  in

  let uip = walk (s.trail_length - 1) in
  let uip' = Lit.neg uip in
  LitVec.set learned_lits 0 uip';

  LitVec.filter_inplace (fun l -> l = uip' || not (is_redundant s (Lit.var l)))
    learned_lits;
  
  (* bin_resolve s learned_lits; *)

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

let compact_arena (s : state) =
  let old_arena = s.clauses in
  s.clauses <- CA.compact old_arena;

  (* update watchlists *)
  Array.iter (fun ws ->
      IntVec.filter_map_inplace (fun w ->
          if Watchlist.is_bin w then
            let other = Watchlist.unpack_other w in
            if get_value s.values other <> ltrue
            && s.levels.(Var.to_int (Lit.var other)) = 0
            then None
            else Some w
          else
            let (clause, other) = Watchlist.unpack w in
            match CA.searched old_arena clause with
            | -1 -> None
            | new_clause ->
              Some Watchlist.(pack (CA.Ref.of_int new_clause) other))
        ws)
    s.watchers;

  (* update learned_clauses *)
  ClauseVec.filter_map_inplace (fun c ->
      match CA.searched old_arena c with
      | -1 -> None
      | c -> Some (CA.Ref.of_int c))
    s.learned_clauses;

  (* update reasons *)
  for v = 1 to s.num_vars do
    match Reason.prj s.reasons.(v) with
    | Decision | Root | Bin _ -> ()
    | Clause r ->
      match CA.searched old_arena r with
      | -1 -> s.reasons.(v) <- Reason.root
      | new_id -> s.reasons.(v) <- Reason.clause (CA.Ref.of_int new_id)

  done

let reduce_db s =
  let old_limit = s.learned_limit in
  s.learned_limit <- Float.to_int (Float.of_int old_limit *. s.learned_growth);
  ClauseVec.iter
    (fun c -> if CA.is_used s.clauses c then update_lbd s c)
    s.learned_clauses;
  ClauseVec.sort (fun a b -> Int.compare (CA.lbd s.clauses b) (CA.lbd s.clauses a))
    s.learned_clauses;
  let to_delete = ref (old_limit / 2) in
  ClauseVec.filter_inplace (fun c ->
      let used = CA.is_used s.clauses c in
      if used then CA.clear_used s.clauses c;
      if CA.lbd s.clauses c <= 2 || CA.is_deleted s.clauses c then
        false
      else if !to_delete <= 0 || used || clause_is_locked s c then
        true
      else
        (CA.set_deleted s.clauses c; decr to_delete; false))
    s.learned_clauses;
  compact_arena s

let satisfied s c =
  LitSlice.exists
    (fun lit -> get_value s.values lit = ltrue)
    (CA.lits s.clauses c)

let remove_satisfied s =
  assert (s.current_level = 0);
  CA.iter (fun c -> if satisfied s c then CA.set_deleted s.clauses c)
    s.clauses;
  Array.iter
    (IntVec.filter_inplace (fun w ->
         if Watchlist.is_bin w then
           get_value s.values (Watchlist.unpack_other w) <> ltrue
         else
           let clause = Watchlist.unpack_clause w in
           not (CA.is_deleted s.clauses clause)))
    s.watchers


let set_true s l reason =
  let v = Lit.var l in
  let level = s.current_level in
  if level = 0 then s.units <- s.units + 1;
  if s.values.%[v] = lundef then
    (set_value s.values l;
     s.levels.(Var.to_int v) <- level;
     s.reasons.(Var.to_int v) <- reason;
     s.trail.(s.trail_length) <- l;
     s.trail_length <- s.trail_length + 1)

exception Conflict of (Lit.t * Reason.t)

let run_watchers s l' (ws : Watchlist.t) =
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
    let other = Watchlist.unpack_other w in
    let other_v = get_value values other in
    if other_v = ltrue then
      (Array.unsafe_set ws_data !j w;
       incr j)
    else if Watchlist.is_bin w then
      if other_v = lfalse
      then conflict (l', Reason.bin other)
      else begin
        set_true s other (Reason.bin l');
        Array.unsafe_set ws_data !j w;
        incr j
      end
    else
      let clause = Watchlist.unpack_clause w in
      let lits = CA.lits s.clauses clause in
      if l' = LitSlice.get lits 0 then
        LitSlice.swap lits 0 1;
      let other = LitSlice.get lits 0 in
      let other_v = get_value values other in
      if other_v = ltrue then
        (Array.unsafe_set ws_data !j (Watchlist.pack clause other);
         incr j)
      else
        let clause_len = LitSlice.length lits in
        let last = CA.searched clauses clause in
        let rec find i =
          if i < clause_len then
            if get_value values (LitSlice.get lits i) = lfalse
            then find (i + 1)
            else i
          else find' 2
        and find' i =
          if i < last then
            if get_value values (LitSlice.get lits i) = lfalse
            then find' (i + 1)
            else i
          else -1
        in
        match find last with
        | -1 when other_v = lfalse ->
          conflict (l', Reason.clause clause)
        | -1 ->
          set_true s other (Reason.clause clause);
          Array.unsafe_set ws_data !j (Watchlist.pack clause other);
          incr j
        | swap_idx ->
          CA.set_searched clauses clause swap_idx;
          let new_l = LitSlice.get lits swap_idx in
          LitSlice.set lits 1 new_l;
          LitSlice.set lits swap_idx l';
          Watchlist.push watchers.(Lit.to_int new_l) clause other
  done;
  IntVec.truncate ws !j

let backjump s target_level =
  let {values; trail; levels; reasons; saved_phase; unassigned_vars; _} = s in
  let rec go i =
    if i < 0 then
      0
    else
      let l = trail.(i) in
      let v = Lit.var l in
      let vi = Var.to_int v in
      if levels.(vi) <= target_level
      then        
        i + 1
      else begin
        unset_value values l;
        saved_phase.%[v] <- Lit.phase l;
        levels.(vi) <- (-1);
        reasons.(vi) <- Reason.root;
        Decision_heap.insert unassigned_vars v;
        go (i - 1)
      end
  in
  let new_len = go (s.trail_length - 1) in
  s.trail_length <- new_len;
  s.trail_head <- new_len;
  s.current_level <- target_level

let save_target_phases s =
  let trail_length = s.trail_length in
  if trail_length > s.max_trail_size then begin
    s.max_trail_size <- trail_length;
    for i = 0 to trail_length - 1 do
      let l = s.trail.(i) in
      s.target_phase.%[Lit.var l] <- Lit.phase l
    done
  end

let register_clause s c =
  match CA.length s.clauses c with
  | 0 -> raise Unsat
  | 1 -> set_true s (CA.get_lit s.clauses c 0) Reason.root (* (Reason.clause c) *)
  | 2 ->
    let l0 = CA.get_lit s.clauses c 0 in
    let l1 = CA.get_lit s.clauses c 1 in
    let i0 = Lit.to_int l0 in
    let i1 = Lit.to_int l1 in
    Watchlist.push_bin s.watchers.(i0) l1;
    Watchlist.push_bin s.watchers.(i1) l0
  | _ ->
    let l0 = CA.get_lit s.clauses c 0 in
    let l1 = CA.get_lit s.clauses c 1 in
    Watchlist.push s.watchers.(Lit.to_int l0) c l1;
    Watchlist.push s.watchers.(Lit.to_int l1) c l0

let rephase_all s =
  for i = 0 to s.num_vars do
    let v = Var.of_int i in
    s.saved_phase.%[v] <- s.target_phase.%[v]
  done;
  s.rephase_limit <- s.rephase_limit + s.rephase_inc

let[@inline] propagate s =
  let {watchers; trail; _} = s in
  try
    while s.trail_head < s.trail_length do
      let l' = Lit.neg trail.(s.trail_head) in
      s.trail_head <- s.trail_head + 1;
      run_watchers s l' watchers.(Lit.to_int l');
    done;
    None
  with Conflict c -> Some c

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
  | None when s.current_level = 0 &&
              s.units >= s.simp_next ->
    s.simp_next <- s.units + s.simp_inc;
    remove_satisfied s;
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
    if s.current_level = 0 then raise Unsat;

    let (learned_lits, lbd, backjump_level) = analyze_conflict s con_lit con_clause in
    Decision_heap.decay_activity s.unassigned_vars;

    if ClauseVec.length s.learned_clauses >= s.learned_limit then
      reduce_db s;

    let reason : Reason.t =
      if LitVec.length learned_lits = 1 then
        Reason.root
      else if LitVec.length learned_lits = 2 then
        let l0 = LitVec.get learned_lits 0 in
        let l1 = LitVec.get learned_lits 1 in
        let i0 = Lit.to_int l0 in
        let i1 = Lit.to_int l1 in
        Watchlist.push_bin s.watchers.(i0) l1;
        Watchlist.push_bin s.watchers.(i1) l0;
        Reason.bin l1
      else
        let learned_clause = CA.alloc s.clauses true lbd learned_lits in
        (* lbd might have changed during minimization
           so set used to keep for at least 1 round and update lbd
        *)
        CA.set_used s.clauses learned_clause;
        (* don't insert permanent clauses into removal candidates *)
        if lbd > 2 then
          ClauseVec.push s.learned_clauses learned_clause;
        register_clause s learned_clause;
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
