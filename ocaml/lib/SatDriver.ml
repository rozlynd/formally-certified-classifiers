open Extracted
open CNF
open Utils
open Satwrapper
open Explainers

(** clause_to_int_array : fin clause -> int literal array *)
let clause_to_int_literal_array c =
  let to_literal (n, pol) =
    match pol with
    | Coq_pos -> Po (to_nat 0 n)
    | Coq_neg -> Ne (to_nat 0 n)
  in
  Array.of_list (List.map to_literal c)

(** val sat_setup : int -> CNF.t -> solver -> unit *)
let sat_setup n f solver =
  (* add a clause [X \/ not X] for every feature [X] because idk how else to set the variable count *)
  List.iter solver#add_clause_array (List.init n (fun i -> Array.of_list [ Po i; Ne i ]));
  List.iter solver#add_clause_array (List.map clause_to_int_literal_array f)

module MakeSatSolver : Sat.SatSolver =
 struct
  type ans =
  | SAT of fin assignment
  | UNSAT

  let extract_get_variable_function solver n =
    let l = List.init n (fun i -> solver#get_variable i = 1) in
    fun i -> List.nth l (to_nat n i)
  
  let sat_result solver n =
    match solver#get_solve_result with
      | SolveSatisfiable -> SAT (extract_get_variable_function solver n)
      | SolveUnsatisfiable -> UNSAT
      | SolveFailure s -> failwith s

  (* let timetable = Timing.initial_timetable ()
  let solver = new Satwrapper.satWrapper (Satsolvers.get_default ()) (Some timetable)
  let _ = solver#solve *)

  (* solve : int -> fin cnf -> ans*)
  let solve n cnf = 
    let timetable = Timing.initial_timetable () in 
    let solver = new Satwrapper.satWrapper (Satsolvers.get_default ()) (Some timetable) in
    sat_setup n cnf solver;
    print_endline ("nb clauses : " ^ string_of_int solver#clause_count);
    print_endline ("nb vars : " ^ string_of_int solver#variable_count);
    solver#solve;
    let x = sat_result solver n in
    solver#dispose;
    x
 end

