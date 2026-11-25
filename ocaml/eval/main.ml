open Format

open Rfxp
open FileWrapper
open SatDriver
open Pretty

open Extracted
open Utils
open DTXp
open Explainers

let _ERR : string = "log"
let _OUT : string = "results.txt"
let _N_SAMPLES : int = 1000
let _SEED : int option = None (*Some 4815162342*)

type 'a report = {
  axps : ('a * float) list;
  cxps : ('a * float) list;
  t_total : float
}

let report_map f { axps; cxps; t_total } =
  { axps = List.map (fun (x, d) -> (f x, d)) axps
  ; cxps = List.map (fun (x, d) -> (f x, d)) cxps
  ; t_total }

let nb_xps (r : 'a report) : int * int =
  (List.length r.axps, List.length r.cxps)

type xp = AXp | CXp | End

(** Get the times for each successive computation. The order of elements in the
    returned list corresponds to the order in which explanations were computed,
    with the last element being the time it took to get UNSAT. *)
let get_times (r : 'a report) : (float * xp) list =
  let unordered = List.map (fun (_, x) -> (x, AXp)) r.axps @ List.map (fun (_, x) -> (x, CXp)) r.cxps in
  let ordered_reverse = List.sort (fun (x, _) (y, _) -> Stdlib.compare y x) unordered in
  let rec map_diff prev prev_t acc = function
    | [] -> (prev, prev_t) :: acc
    | (x, t) :: l -> map_diff x t ((prev -. x, prev_t) :: acc) l
  in
  map_diff r.t_total End [] ordered_reverse

(** Randomy select n elements from l.
    Returns l if n > length l *)
let sample n l =
  let shuffle l =
    let l = List.map (fun x -> x, Random.bits ()) l in
    let l = List.sort (fun (_, b1) (_, b2) -> Stdlib.compare b1 b2) l in
    List.map fst l
  in
  let rec nfirst n l acc =
    if n < 1 then
      acc
    else
      match l with
      | [] -> acc
      | x :: l -> nfirst (n - 1) l (x :: acc)
  in
  nfirst n (shuffle l) []

let print_progress ff file_name instance_num percent =
  fprintf ff "(%5.2f %%) %s: instance %d@." percent file_name instance_num

let process_input_problem (type t) i ff (module Input : DTInputProblem with type S.t = t) : t report =
  if i > 1 then pp_print_newline ff ();
  fprintf ff "Vector #%d: %a@." i pp_print_feature_vec Input.v;

  let module Solver = MakeSatSolver in
  let module Iter = MakeIterator (Input.S) (Solver) in
  let module AXpFind = DtAXpFinder (Input) in
  let module CXpFind = DtCXpFinder (Input) in
  let module WCXpCheck = DtWCXpChecker (Input) in
  let module Enum = MakeEnumerator (Input) (Iter) (WCXpCheck) (CXpFind) (AXpFind) in

  (* Actual work starts here... *)
  let d_start = Sys.time () in
  let now () = Sys.time () -. d_start in

  let rec iter get record st acc =
    let res = get st in
    match res with
    | None -> acc, now ()
    | Some xp ->
        let st' = record xp st in
        iter get record st' ((xp, now ()) :: acc)
  in

  let xps, d = iter Enum.get Enum.record Enum.init [] in
  (* ... and stops here *)

  let axps, cxps =
    List.fold_right (function
      | Enum.Xp.Coq_isAXp xp, d -> fun (axps, cxps) -> (xp, d) :: axps, cxps
      | Enum.Xp.Coq_isCXp xp, d -> fun (axps, cxps) -> axps, (xp, d) :: cxps)
    xps ([], [])
  in

  let pp_print_xp = pp_print_finset (module Input.S) in
  let pp_print_v ff (xp, d) = fprintf ff "%.5f: %a" d pp_print_xp xp in
  let pp_print_xps = pp_print_list ~pp_sep:(fun ff () -> fprintf ff ", ") pp_print_v in
  fprintf ff "AXps: %a@.CXps: %a@.Time elapsed: %.5f@." pp_print_xps axps pp_print_xps cxps d;
  
  let r = { axps; cxps; t_total = d } in
  let pp_print_xp ff = function AXp -> pp_print_string ff "AXp" | CXp -> pp_print_string ff "CXp" | End -> pp_print_string ff "End" in
  let pp_print_times = pp_print_list ~pp_sep:(fun ff () -> fprintf ff ", ") (fun ff (x, t) -> fprintf ff "%.5f %a" x pp_print_xp t) in
  fprintf ff "Times: %a@." pp_print_times (get_times r);
  r

(** Return (m, n, rs) where m is the number of features, n is the number of
    nodes in the tree, and rs is the list of reports obtained by processing
    vectors *)
let process_file i ff fname : int * int * int list report list =
  if i > 1 then pp_print_newline ff ();
  fprintf ff "File #%d: %s@." i fname;

  let module FileData = MakeData (struct let filename = fname end) in
  let module TreeData = MakeFeatureTreeData (FileData) in

  let process_vector j v : int * int list report =
    let percent = float_of_int (100 * (((i - 1) * _N_SAMPLES) + j)) /. float_of_int ((Array.length Sys.argv - 1) * _N_SAMPLES) in
    print_progress std_formatter fname j percent;
    let module Input = MakeDTInputProblem (TreeData) (struct let parsed_vector = v end) in
    let r = process_input_problem j ff (module Input) in
    let r = report_map (fun s -> List.map (to_nat 0) (Input.S.elements s)) r in
    (j + 1, r)
  in

  let bench = sample _N_SAMPLES FileData.parsed_vectors in
  let _, rs = List.fold_left_map process_vector 1 bench in
  (FileData.nb_features, List.length FileData.parsed_tree, rs)

let print_top ff () =
  fprintf ff "\\begin{tabular}{lcc%@{\\hspace{10pt}}*{8}{>{\\raggedleft\\arraybackslash}p{17pt}}*{4}{>{\\raggedleft\\arraybackslash}p{25pt}}}@\n";
  fprintf ff "    \\toprule@\n";
  fprintf ff "    & & & \\multicolumn{2}{c}{Med. Amount} & \\multicolumn{2}{c}{Max. Amount} & \\multicolumn{2}{c}{Med. Sizes} & \\multicolumn{2}{c}{Max. Sizes} & \\multicolumn{4}{c}{Med. Comput.\\ Times (ms)} \\\\@\n";
  fprintf ff "    \\cmidrule{4-15}@\n";
  fprintf ff "    Dataset & $\\card{\\F}$   & $\\card{\\mathrm{DT}}$  & AXp & CXp & AXp & CXp & AXp & CXp & AXp & CXp & AXp  & CXp  & End   & All \\\\@\n";
  fprintf ff "    \\midrule@\n"

let median_float cmp (l : float list) =
  let l = List.sort cmp l in
  let n = List.length l in
  let p = n / 2 in
  if n mod 2 = 0 then
    (List.nth l (p - 1) +. List.nth l p) /. 2.
  else
    List.nth l p

type median_int = TrueInt of int | IntAndHalf of int

let pp_print_median_int ff = function
  | TrueInt x -> pp_print_int ff x
  | IntAndHalf x -> fprintf ff "%d.5" x

let median_int cmp (l : int list) =
  let l = List.sort cmp l in
  let n = List.length l in
  let p = n / 2 in
  if n mod 2 = 0 then
    let s = List.nth l (p - 1) + List.nth l p in
    if s mod 2 = 0 then
      TrueInt (s / 2)
    else
      IntAndHalf (s / 2)
  else
    TrueInt (List.nth l p)

let print_report ff name n_features tree_size (rs : int list report list) =
  let all_total = List.map (fun r -> r.t_total) rs in
  let all_times = List.map get_times rs in
  let all_end, all_any =
    let split = function
      | x :: l -> (x, l)
      | _ -> assert false
    in
    List.map (fun l -> split (List.rev l)) all_times |> List.split
      |> fun (l, ls) -> (l, List.flatten ls)
  in

  let all_end = List.map (function (x, End) -> x | _ -> assert false) all_end in
  let all_axp = List.filter_map (function (x, AXp) -> Some x | _ -> None) all_any in
  let all_cxp = List.filter_map (function (x, CXp) -> Some x | _ -> None) all_any in

  let t_all = 1000. *. median_float Stdlib.compare all_total in
  let t_axp = 1000. *. median_float Stdlib.compare all_axp in
  let t_cxp = 1000. *. median_float Stdlib.compare all_cxp in
  let t_end = 1000. *. median_float Stdlib.compare all_end in

  let nbs_axps, nbs_cxps = List.map nb_xps rs |> List.split |>
    fun (l1, l2) -> List.sort Stdlib.compare l1, List.sort Stdlib.compare l2
  in

  let n_axp_med = median_int Stdlib.compare nbs_axps in
  let n_axp_max = List.hd (List.rev nbs_axps) in

  let n_cxp_med = median_int Stdlib.compare nbs_cxps in
  let n_cxp_max = List.hd (List.rev nbs_cxps) in

  let to_szs { axps; cxps; _ } =
    let f (x, _) = List.length x in
    (List.map f axps, List.map f cxps)
  in
  let sz_axps, sz_cxps =
    List.fold_right (fun r (acc_axp, acc_cxp) -> let x, y = to_szs r in (x @ acc_axp, y @ acc_cxp)) rs ([], []) |>
    fun (l1, l2) -> List.sort Stdlib.compare l1, List.sort Stdlib.compare l2
  in

  let sz_axp = median_int Stdlib.compare sz_axps in
  let sz_cxp = median_int Stdlib.compare sz_cxps in

  let sz_axp_max = List.hd (List.rev sz_axps) in
  let sz_cxp_max = List.hd (List.rev sz_cxps) in

  let name = String.concat "\\_" (String.split_on_char '_' name) in

  fprintf ff "    \\textsf{%s}  & %d  & %d  & %a  & %d  & %a  & %d  & %a  & %a  & %d  & %d  & %.2f  & %.2f  & %.2f  & %.2f \\\\@\n" name n_features tree_size pp_print_median_int n_axp_med n_axp_max pp_print_median_int n_cxp_med n_cxp_max pp_print_median_int sz_axp pp_print_median_int sz_cxp sz_axp_max sz_cxp_max t_axp t_cxp t_end t_all

let print_bottom ff () =
  fprintf ff "    \\bottomrule@\n";
  fprintf ff "\\end{tabular}@\n"

let print_results results ff =
  print_top ff ();
  List.iter (fun (fname, n_features, tree_size, rs) -> print_report ff fname n_features tree_size rs) results;
  print_bottom ff ()

let () =
  begin match _SEED with
  | Some s -> Random.init s
  | None -> Random.self_init ()
  end;

  let ff_out = open_out _OUT |> formatter_of_out_channel in
  let ff_err = open_out _ERR |> formatter_of_out_channel in

  let files = Array.fold_right List.cons Sys.argv [] |> List.tl in

  let it fname (i, acc) =
    let n_features, tree_size, rs = process_file i ff_err fname in
    let name = Filename.remove_extension (Filename.basename fname) in
    (i + 1, (name, n_features, tree_size, rs) :: acc)
  in
  let _, results = List.fold_right it files (1, []) in

  print_results results ff_out;

  fprintf ff_err "Results printed to %s@." _OUT

