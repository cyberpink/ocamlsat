let parse () =
  let (nvars, nclauses) =
    let rec go () =
      let l = read_line () in
      if l.[0] = 'c'
      then go ()
      else Scanf.sscanf l "p cnf %d %d" (fun v c -> (v, c))
    in
    go ();
  in
  (* Printf.printf "vars: %d, clauses: %d\n" nvars nclauses; *)
  let clauses = Array.init nclauses @@ fun _ ->
    read_line () |>
    String.split_on_char ' ' |>
    List.filter_map int_of_string_opt |>
    List.filter ((<>) 0) |>
    List.map (fun sv -> (abs sv, sv > 0))
  in
  (nvars, nclauses, clauses)
