open Arg
open Format

open Rfxp
open Driver_file
open Extracted
open DTXp
open Utils
open Dttxt.Parsing_utils
open Explainers
open SatDriver

let as_list (type t_) (module S : FinSet with type t = t_) (e : S.t) =
  let l = S.elements e in
  List.map (fun f -> Extracted.Utils.to_nat S.n f) l

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

type log_kind = Info | Error

let kind_as_string = function
  | Info -> "INFO"
  | Error -> "ERROR"

let log k mssg =
  if !verbose then
    eprintf "[%s] %s@." (kind_as_string k) mssg

let info = log Info
let error = log Error

(* MAIN *)

let report_axp x = printf "AXp: %s@." (string_of_int_list x)
let report_cxp x = printf "CXp: %s@." (string_of_int_list x)
  
let process_input_problem mode (module Input : DTInputProblem) =
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
          | Enum.Xp.Coq_isAXp x -> report_axp (as_list (module Input.S) x)
          | Enum.Xp.Coq_isCXp x -> report_cxp (as_list (module Input.S) x)
        in

        let rec iter f get record st =
          let x = get st in
          match x with
          | None -> ()
          | Some y ->
            begin
              f y;
              let next_st = record y st in
              iter f get record next_st
            end
        in

        iter report_xp Enum.get Enum.record Enum.init
      end

  | AXp ->
      begin
        let module Find = DtAXpFinder (Input) in

        let axp = Find.findAXp Input.S.all in
        let out = as_list (module Input.S) axp in
        report_axp out
      end

  | CXp ->
      begin
        let module Find = DtCXpFinder (Input) in
        let module WCXpCheck = DtWCXpChecker (Input) in

        if WCXpCheck.checkWCXp Input.S.all then
          let cxp = Find.findCXp Input.S.all in
          let out = as_list (module Input.S) cxp in
          report_cxp out

        else
          error "No CXps! (constant model)"
      end

let main_file mode fname =
  info ("Parsing file '" ^ fname ^ "'");

  let module D = Driver_file.MakeData (struct let filename = fname end) in
  let module FTD = MakeFeatureTreeData (D) in
  let module MakeI = MakeDTInputProblem (FTD) in

  let process_vector v =
    printf "Explaining input = %s@." (string_of_vector v);
    let module Input = MakeI (struct let parsed_vector = v end) in
    process_input_problem mode (module Input)
  in

  List.iter process_vector D.parsed_vectors;
  info "Done"

let () =
  parse spec add_fname usage_msg;
  List.iter (main_file !mode) !fnames

