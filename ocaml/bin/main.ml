open Rfxp
open Driver_file
open Extracted
open DTXp
open Utils



let as_list (type t_) (module S : FinSet with type t = t_) (e : S.t) =
  let l = S.elements e in
  List.map (fun f -> Extracted.Utils.to_nat S.n f + 1) l
;;




let string_of_int_list l =
  let rec aux acc l =
    match l with
    | [] -> acc ^ " ]"
    | x :: l -> aux (acc ^ ", " ^ string_of_int x) l
  in
  match l with
  | [] -> "[]"
  | x :: l -> aux ("[ " ^ string_of_int x) l
;;

let help_string = 
  "The program must be called like this :
  rfxp [-v] [ -a | -c | -ac | (-all) ] <input_file> [<output_file>]  
    -v    verbose                                                  
    -a    get one AXp                                              
    -c    get one CXp                                              
    -ac   get one AXp and one CXp                                  
    (-all  get all AXp and all CXp (caution : AXp and CXp are mixed) (not available yet))
    
    -h, -help, --help   print this help message

    <input_file>    the file containing Decision Tree informations.
    <output_file>   the file to write the results."
;;

let logger (verbose:bool) (s:string) =
  if verbose then print_string s
;;


(* enum type giving the research goal. *)
type mode = 
  | AXp
  | CXp
  | Both
  | All
;;

(* Write a string message in a file named filename. *)
let write_in_file message filename = 
  let oc = open_out_gen [Open_append; Open_creat] 0o666 filename in
  Printf.fprintf oc "%s\n" message;
  close_out oc
;;

let main_file verbose mode input_file output_file =
  let log = logger verbose in

  (* let _filename = "filename.txt" in *)
  let module D = Driver_file.MakeData (struct
    let filename = input_file
  end) in

  log "info : parsing file...";
  let module Input = MakeDTInputProblem (D) in
  log "done.\n\n";

  if mode = All then
    failwith "Error : parameter -all is not available yet.";

  if mode = AXp || mode = Both then
    begin
      let module FindA = DtAXpFinder (Input) in
      let axp = FindA.findAXp Input.S.all in
      let outA = string_of_int_list (as_list (module Input.S) axp) in
      print_endline ("AXp : " ^ outA);
      write_in_file ("AXp : " ^ outA) output_file;
    end;
    
  if mode = CXp || mode = Both then
    begin
      let module FindC = DtCXpFinder (Input) in
      let cxp = FindC.findCXp Input.S.all in
      let outC = string_of_int_list (as_list (module Input.S) cxp) in
      print_endline ("CXp : " ^ outC);
      write_in_file ("CXp : " ^ outC) output_file;
    end;

  log "info : main executed.\n";
;;

exception Break;;


let () =
  let verbose = ref false in
  let mode = ref AXp in
  let input_file = ref "" in  (* not read default value, has to be modified *)
  let input_file_given = ref false in
  let output_file = ref "dt_explanation_result.txt" in (* default value if not given *)
  let output_file_given = ref false in
  try
    for i=1 to (Array.length Sys.argv - 1) do
      let a =  Sys.argv.(i) in
      if a = "-h" || a = "-help" || a = "--help" then
        raise Break
      else if a = "-v" then
        verbose := true
      else if a = "-a" then
        mode := AXp
      else if a = "-c" then
        mode := CXp
      else if a = "-ac" then
        mode := Both
      else if a = "-all" then
        mode := All
      else if a.[0] = '-' then
        failwith ("Error : unknown parameter " ^ a)
      else if (not !input_file_given) then
        begin 
          input_file_given := true; 
          input_file := a
        end
      else if (not !output_file_given) then
        begin 
          output_file_given := true; 
          output_file := a
        end
      else 
        begin
          print_endline ("Error in command line arguments.\n" ^ help_string);
          failwith "Error in command line arguments"
        end
    done;
    if !input_file_given then 
      main_file !verbose !mode !input_file !output_file
    else failwith "no input file given"
  with Break -> print_endline help_string

