open Arg
open Format

open Rfxp
open Driver_file
open Extracted
open DTXp
open Explainers
open SatDriver
open Pretty

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

let process_input_problem mode (module Input : DTInputProblem with type K.t = string) =
  fprintf str_formatter "DT: %a@." (pp_print_dt pp_print_string Input.fs) Input.k;
  info (flush_str_formatter ());

  fprintf str_formatter "Vector: %a@." pp_print_feature_vec Input.v;
  info (flush_str_formatter ());

  let pp_print_xp = pp_print_finset (module Input.S) in
  let report_axp xp = printf "AXp: %a@." pp_print_xp xp in
  let report_cxp xp = printf "CXp: %a@." pp_print_xp xp in
  
  match mode with
  | All ->
      begin
        let module Solver = MakeSatSolver in
        let module Iter = MakeIterator (Input.S) (Solver) in
        let module AXpFind = DtAXpFinder (Input) in
        let module CXpFind = DtCXpFinder (Input) in
        let module WCXpCheck = DtWCXpChecker (Input) in
        let module Enum = MakeEnumerator (Input) (Iter) (WCXpCheck) (CXpFind) (AXpFind) in

        let report_xp xp =
          match xp with
          | Enum.Xp.Coq_isAXp xp -> report_axp xp
          | Enum.Xp.Coq_isCXp xp -> report_cxp xp
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
        report_axp axp
      end

  | CXp ->
      begin
        let module Find = DtCXpFinder (Input) in
        let module WCXpCheck = DtWCXpChecker (Input) in

        if WCXpCheck.checkWCXp Input.S.all then
          let cxp = Find.findCXp Input.S.all in
          report_cxp cxp

        else
          error "No CXps! (constant model)"
      end

let main_file mode fname =
  info ("Parsing file '" ^ fname ^ "'");

  let module D = Driver_file.MakeData (struct let filename = fname end) in
  let module FTD = MakeFeatureTreeData (D) in
  let module MakeI = MakeDTInputProblem (FTD) in

  let process_vector v =
    let module Input = MakeI (struct let parsed_vector = v end) in
    process_input_problem mode (module Input)
  in

  List.iter process_vector D.parsed_vectors;
  info "Done"

let () =
  parse spec add_fname usage_msg;
  List.iter (main_file !mode) !fnames

