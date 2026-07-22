open Extracted;;
open CNF;;
open Utils;;
open Satwrapper;;
open Explainers;;

(** val sat_setup : 
    solver -> CNF.t -> unit 
    Add each constraint encoded in the CNF h to the solver **)

let rec sat_setup solver l =
  (** aux converts a clause in our format to one that can be transformed into a suitable array for the solver **)
  let rec aux c = 
    match c with
    | [] -> []
    | (n, pol) :: q -> match pol with
      | Coq_pos -> (Po (to_nat 0 n))::(aux q)
      | Coq_neg -> (Ne (to_nat 0 n))::(aux q)
  in
  match l with
  | [] -> ();
  | t::q -> solver#add_clause_array (Array.of_list (aux t)); (* Each clause is added, an array corresponds to the disjunction of its elements *)
    (sat_setup solver q)
;;


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
      | SolveSatisfiable ->  SAT (extract_get_variable_function solver n)
      | SolveUnsatisfiable -> UNSAT
      | SolveFailure s -> failwith s

  (* let timetable = Timing.initial_timetable ()
  let solver = new Satwrapper.satWrapper (Satsolvers.get_default ()) (Some timetable)
  let _ = solver#solve *)

  (* solve : int -> fin cnf -> ans*)
  let solve n cnf = 
    let timetable = Timing.initial_timetable () in 
    let solver = new Satwrapper.satWrapper (Satsolvers.get_default ()) (Some timetable) in
    sat_setup solver cnf;
    print_endline ("nb clauses : " ^ string_of_int solver#clause_count);
    print_endline ("nb vars : " ^ string_of_int solver#variable_count);
    solver#solve;
    let x = sat_result solver n in
    solver#dispose;
    x
 end

let rec string_of_cnf cnf = match cnf with
  | [] -> ""
  | t::q -> (string_of_clause t) ^ "\n" ^ (string_of_cnf q)
and string_of_clause c = match c with
  | [] -> ""
  | t::q -> (string_of_literal t) ^ ";" ^ (string_of_clause q)
and string_of_literal l = match l with
  | i, Coq_pos -> "+" ^ (string_of_int (to_nat 0 i))
  | i, Coq_neg -> "-" ^ (string_of_int (to_nat 0 i))

let rec iter f get record st cpt =
  let x = get st in
  print_endline ("iter n°" ^ (string_of_int cpt));
  (* print_endline ("cnf : " ^ (string_of_cnf st)); *)
  match x with
  | None -> ()
  | Some y -> 
    begin
      f y;
      let next_st = record y st in
      if cpt > 20 then failwith "too much iterations"
      else iter f get record next_st (cpt+1)
    end



