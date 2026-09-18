open Arg

open Rfxp
open Driver_file
open Extracted
open DTXp
open Utils
open Dttxt.Parsing_utils
open Explainers
open Driver_enumerator

let as_list (type t_) (module S : FinSet with type t = t_) (e : S.t) =
  let l = S.elements e in
  List.map (fun f -> Extracted.Utils.to_nat S.n f) l

let string_of_features_with_names l parsed_features = 
  let rec aux acc l =
    match l with
    | [] -> acc ^ " ]"
    | x :: l -> aux (acc ^ ", \"" ^ get_feature_name_at_index x parsed_features ^ "\"") l
  in
  match l with
  | [] -> "[]"
  | x :: l -> aux ("[ \"" ^ get_feature_name_at_index x parsed_features ^ "\"") l

let string_of_int_list l =
  let rec aux acc l =
    match l with
    | [] -> acc ^ " ]"
    | x :: l -> aux (acc ^ ", " ^ string_of_int x) l
  in
  match l with
  | [] -> "[]"
  | x :: l -> aux ("[ " ^ string_of_int x) l

type mode = AXp | CXp | All

let usage_msg = "rfxp [-v] [-axp | -cxp | -all] FILES..."

let verbose = ref false
let mode = ref AXp
let fnames = ref []

let set_mode m = fun () -> mode := m
let add_fname = fun f -> fnames := f :: !fnames

let spec = [
  "-v",   Set verbose,          "Set verbose output";
  "-axp", Unit (set_mode AXp),  "Extract one AXp (default)";
  "-cxp", Unit (set_mode CXp),  "Extract one CXp";
  "-all", Unit (set_mode All),  "Extract all AXps and CXp"
]

let log s =
  if !verbose then print_endline s

let main_file mode fname =
  log ("info : parsing file '" ^ fname ^ "'");

  let write_stdout = print_endline in
  let report_axp s = write_stdout ("AXp: " ^ s) in
  let report_cxp s = write_stdout ("CXp: " ^ s) in
  
  let module D = Driver_file.MakeData (struct let filename = fname end) in
  let module FTD = MakeFeatureTreeData (D) in
  let module MakeI = MakeDTInputProblem (FTD) in

  let process_vector v =
    write_stdout ("Explaining input = " ^ string_of_vector v);
    let module Input = MakeI (struct let parsed_vector = v end) in
    
    begin
      match mode with
      | All ->
          begin
            let module Solver = MakeSatSolver in
            let module Iter = MakeIterator (Input.S) (Solver) in
            let module AXpFind = DtAXpFinder (Input) in
            let module CXpFind = DtCXpFinder (Input) in
            let module WCXpCheck = DtWCXpChecker (Input) in
            let module Enum = MakeEnumerator (Input) (Iter) (WCXpCheck) (CXpFind) (AXpFind) in

            let report_xp x =
              match x with
              | Enum.Xp.Coq_isAXp x -> report_axp (string_of_int_list (as_list (module Input.S) x))
              | Enum.Xp.Coq_isCXp x -> report_cxp (string_of_int_list (as_list (module Input.S) x))
            in 
            iter report_xp Enum.get Enum.record Enum.init 0
          end

      | AXp ->
          begin
            let module Find = DtAXpFinder (Input) in

            let axp = Find.findAXp Input.S.all in
            let out = string_of_features_with_names (as_list (module Input.S) axp) D.features in
            report_axp out
          end

      | CXp ->
          begin
            let module Find = DtCXpFinder (Input) in
            let module WCXpCheck = DtWCXpChecker (Input) in

            if WCXpCheck.checkWCXp Input.S.all then
              let cxp = Find.findCXp Input.S.all in
              let out = string_of_features_with_names (as_list (module Input.S) cxp) D.features in
              report_cxp out

            else
              write_stdout "No CXps! (constant model)"
          end
    end;
  in

  (* run on all vectors *)
  List.iter process_vector D.parsed_vectors;
  
  log "info : done"

let () =
  parse spec add_fname usage_msg;
  List.iter (main_file !mode) !fnames

