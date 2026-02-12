open Ocamlsat
open Common

let (num_vars, num_clauses, clauses_pre) = Dimacs.parse ()
let num_lits = (num_vars + 1) * 2
let learned_initial = max num_clauses 100

let state : Solver.state = {
  num_vars;
  num_lits;

  values = Bytes.make (num_vars + 1) (Char.chr lundef);
  clauses = ClauseArena.create ();
  watchers = Array.init num_lits (fun _ -> Watchlist.create ());
  trail = Array.make num_vars Lit.dummy;
  trail_length = 0;
  trail_head = 0;

  levels = Array.make (num_vars + 1) (-1);
  reasons = Array.make (num_vars + 1) Reason.decision;
  current_level = 0;

  learned_lits = LitVec.create Lit.dummy;
  learned_limit = learned_initial;
  learned_growth = 1.1;
  learned_clauses = ClauseVec.create ~capacity:learned_initial ClauseArena.Ref.dummy;

  unassigned_vars = Decision_heap.create (num_vars + 1);

  conflicts = 0;
  restart_coeff = 100;
  next_restart = luby 1 * 100;
  restarts = 1;

  units = 0;
  simp_next = 100;
  simp_inc = 100;

  saved_phase = Bytes.make (num_vars + 1) '\x01';
  target_phase = Bytes.make (num_vars + 1) '\x00';
  max_trail_size = 0;
  rephase_limit = 1000;
  rephase_inc = 2000;

  levels_to_clear = IntVec.create 0;
  levels_seen = Bytes.make (num_vars + 1) '\x00';

  analyze_to_clear = IntVec.create 0;
  analyze_seen = Bytes.make (num_vars + 1) '\x00';
  redundant_cache = Bytes.make (num_vars + 1) '\x00';
  redundant_to_clear = IntVec.create 0;
  lits_seen = Bytes.make num_lits '\x00';  
}

module LitSet = Set.Make(Lit)
let process_lits lits =
  let lits_out = LitVec.create Lit.dummy in
  (LitSet.iter (fun l -> LitVec.push lits_out l) @@
   let exception Skip in
   try
     List.fold_left
       (fun clause (v, p) ->
          let l = Lit.make (Var v) p in
          if LitSet.mem (Lit.neg l) clause
          then raise_notrace Skip
          else LitSet.add l clause)
       LitSet.empty lits
   with Skip -> LitSet.empty);
  lits_out


let () =
  let s = state in
  try
    for id = 0 to num_clauses - 1 do
      Solver.register_clause s @@
      ClauseArena.alloc s.clauses  false 0 (process_lits clauses_pre.(id))
    done;

    for v = 1 to num_vars do
      Decision_heap.insert s.unassigned_vars (Var.of_int v)
    done;

    Solver.solve s;

    print_endline "s SATISFIABLE";
    exit 10
  with Unsat ->
    print_endline "s UNSATISFIABLE";
    exit 20
