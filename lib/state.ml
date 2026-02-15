open Common    
module CA = Clause_arena

type state = {
  num_vars : int;
  num_lits : int;

  values : Bytes.t;
  mutable clauses : CA.arena;
  watchers : Watch.t array;
  trail : Lit.t array;
  mutable trail_length : int;
  mutable trail_head : int;

  levels : int array;
  reasons : Reason.t array;
  mutable current_level : int;

  learned_lits : LitVec.t;
  learned_clauses : CA.ClauseVec.t;
  learned_growth : float;
  mutable learned_limit : int;

  unassigned_vars : Decision_heap.t;

  restart_coeff : int;
  mutable conflicts : int;
  mutable next_restart : int;
  mutable restarts : int;

  mutable simp_props : int; (** Work until next simplification *)
  mutable simp_assigns : int; (** Number of units at last simplification *)

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

external unsafe_get_uint8 : bytes -> int -> int = "%bytes_unsafe_get"
external unsafe_set_uint8 : bytes -> int -> int -> unit = "%bytes_unsafe_set"
let[@inline] (.$[]) a v : int = unsafe_get_uint8 a (Lit.to_int v)
let[@inline] (.$[]<-) a v (x : int) = unsafe_set_uint8 a (Lit.to_int v) x
let[@inline] (.%[]) a v : int = unsafe_get_uint8 a (Var.to_int v)
let[@inline] (.%[]<-) a v (x : int) = unsafe_set_uint8 a (Var.to_int v) x

let[@inline] (.$()) a v : int = Array.unsafe_get a (Lit.to_int v)
let[@inline] (.$()<-) a v (x : int) = Array.unsafe_set a (Lit.to_int v) x
let[@inline] (.%()) a v : int = Array.unsafe_get a (Var.to_int v)
let[@inline] (.%()<-) a v (x : int) = Array.unsafe_set a (Var.to_int v) x

let[@inline] get_value a l = a.%[Lit.var l] lxor (Lit.phase l)
let[@inline] set_value a l = a.%[Lit.var l] <- Lit.phase l
let[@inline] unset_value a l = a.%[Lit.var l] <- lundef

let[@inline] get_watchers ws l = Array.unsafe_get ws (Lit.to_int l)

let set_true s l reason =
  let v = Lit.var l in
  let level = s.current_level in
  if s.values.%[v] = lundef then
    (set_value s.values l;
     s.levels.(Var.to_int v) <- level;
     s.reasons.(Var.to_int v) <- reason;
     s.trail.(s.trail_length) <- l;
     s.trail_length <- s.trail_length + 1)

let save_target_phases s =
  let trail_length = s.trail_length in
  if trail_length > s.max_trail_size then begin
    s.max_trail_size <- trail_length;
    for i = 0 to trail_length - 1 do
      let l = s.trail.(i) in
      s.target_phase.%[Lit.var l] <- Lit.phase l
    done
  end

let rephase_all s =
  for i = 0 to s.num_vars do
    let v = Var.of_int i in
    s.saved_phase.%[v] <- s.target_phase.%[v]
  done;
  s.rephase_limit <- s.rephase_limit + s.rephase_inc

let compact_arena (s : state) =
  let old_arena = s.clauses in
  s.clauses <- CA.compact old_arena;

  (* update watchlists *)
  Array.iter (fun ws ->
      IntVec.filter_map_inplace (fun w ->
          if Watch.is_bin w then
            (* remove level 0 satisfied inline clauses while updating *)
            let other = Watch.unpack_other w in
            if get_value s.values other = ltrue
            && s.levels.(Var.to_int (Lit.var other)) = 0
            then None
            else Some w
          else
            let (clause, other) = Watch.unpack w in
            match CA.searched old_arena clause with
            | -1 -> None
            | new_clause ->
              Some Watch.(pack (CA.Ref.of_int new_clause) other))
        ws)
    s.watchers;

  (* update learned_clauses *)
  CA.ClauseVec.filter_map_inplace (fun c ->
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
