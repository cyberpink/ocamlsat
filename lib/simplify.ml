open Common
open State
module CA = Clause_arena

(** Remove satisfied clauses and false literals at level 0 *)
let simplify s =
  assert (s.current_level = 0);
  let lit_count = ref 0 in
  CA.iter (fun c ->
      let lits = CA.lits s.clauses c in
      let len = LitSlice.length lits in
      lit_count := !lit_count + len;
        try
          let i = ref 2 in
          let j = ref 2 in
          (* first pass leaves 0 and 1 alone for 2WL *)
          (* if any true literal is found short circuit and mark as satisfied *)
          while !i < len do
            let l = LitSlice.get lits !i in
            let v = get_value s.values l in
            if v = ltrue then (* satisfied *)
              raise_notrace Exit;
            if v <> lfalse then
              (LitSlice.set lits !j l; incr j);
            incr i
          done;
          match !j with
          | 2 ->
            lit_count := !lit_count - len;
            CA.set_deleted s.clauses c;
            (* attempt to reduce it further once we don't care about first 2 slots *)
            let l0 = LitSlice.get lits 0 in
            let l1 = LitSlice.get lits 1 in
            (match (get_value s.values l0, get_value s.values l1) with
             | 0, _ | _, 0 -> ()
             | 1, 1 -> raise Unsat
             | 1, _ -> set_true s l1 Reason.root
             | _, 1 -> set_true s l0 Reason.root
             | _, _ ->
               Watch.push_bin s.watchers.(Lit.to_int l0) l1;
               Watch.push_bin s.watchers.(Lit.to_int l1) l0)
          | len' when len' < len ->
            lit_count := !lit_count - (len - len');
            CA.shrink s.clauses c len';
            CA.set_used s.clauses c
          | _ -> ()
        with Exit ->
          lit_count := !lit_count - len;
          CA.set_deleted s.clauses c)
    s.clauses;
  (* rebuild watchlists *)
  Array.iter
    (IntVec.filter_inplace (fun w ->
         if Watch.is_bin w then
           get_value s.values (Watch.unpack_other w) <> ltrue
         else
           let clause = Watch.unpack_clause w in
           not (CA.is_deleted s.clauses clause)
       ))
    s.watchers;
  !lit_count
