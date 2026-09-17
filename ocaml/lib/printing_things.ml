open Extracted
open DT 
open Features

let rec _featureTypeAtIndex features i cpt =
  match features with
  | Coq_featureSigNil -> failwith "Error : incompatibility between features and tree."
  | Coq_featureSigCons (_, get, q) -> 
    if i = cpt then get
    else _featureTypeAtIndex q i (cpt+1)

(* Get the featureKind at index i in the featureSig features *)
let rec featureTypeAtIndex features i = _featureTypeAtIndex features i 0

let string_of_unit a = if a = () then "()" else failwith "ERROR in string_of_unit"

let rec _string_of_tree prefix t features =
  match t with
  | Leaf a -> prefix ^ "Leaf(" ^ a ^ ")"
  | Node (a, _b, lc, rc) ->
    let int_a = Utils.to_nat 0 a in (* NB : 0 does not mean anything but it is the right type *)
    (* we need features to type correctly (Obj.magic _b) *)
    let b =
      match featureTypeAtIndex features int_a with
      | Coq_isBooleanFeature -> string_of_unit (Obj.magic _b : unit)
      | Coq_isContinuousFeature -> string_of_float (Obj.magic _b : float)
      | _ -> failwith "Error : enum features are not allowed yet."
    in prefix ^ "Node(" ^ string_of_int int_a ^ ", " ^ b ^ ")\n" ^
        _string_of_tree (prefix ^ "| ") lc features ^ "\n" ^
        _string_of_tree (prefix ^ "| ") rc features

let string_of_tree t features = _string_of_tree "" t features

let print_tree t features = print_endline (string_of_tree t features)

let string_of_feature f =
  if f == float_feature then "float_feature"
  else if f == boolean_feature then "boolean_feature"
  else "string_enum_features"

let get_string_of_get_and_index get test_index =
  match get with
  | Coq_isBooleanFeature -> "Coq_isBooleanFeature", "()"
  | Coq_isContinuousFeature -> "Coq_isContinuousFeature", string_of_float (Obj.magic test_index : float)
  | Coq_isStringEnumFeature s -> "Coq_isStringEnumFeature", " .___. "
  (* | _ -> failwith "Error in get_string_of_get_and_index : enum features are now allowed yet." *)

let rec string_of_featureSig prefix f =
  match f with
  | Coq_featureSigNil -> prefix ^ "Coq_featureSigNil"
  | Coq_featureSigCons (i, get, next_sig) ->
    let get_string, _ = get_string_of_get_and_index get (Obj.repr ()) in
    prefix ^ "Coq_featureSigCons(" ^ string_of_int i ^ ", " ^ 
    get_string ^ ",\n" ^ string_of_featureSig prefix next_sig ^ ")"

let rec _string_of_vector v = 
  (* print_endline "debug : appel à _string_of_vector"; *)
  match v with
  | Coq_featureVecNil -> "Coq_featureVecNil"
  | Coq_featureVecCons (get, test_index, i, feature_sig, q) ->
    (* print_endline "debug : f_string obtenu"; *)
    
    let get_string, test_index_string = get_string_of_get_and_index get test_index in
    (* print_endline "debug : get_string et test_index_string obtenu"; *)
    
    let feature_sig_string = string_of_featureSig "  " feature_sig in
    (* print_endline "debug : feature_sig_string obtenu"; *)
    
    let next_vec_string = _string_of_vector q in
    (* print_endline "debug : next_vec_string obtenu"; *)
    
    "Coq_featureVecCons(" ^ 
    get_string ^ ", " ^ test_index_string ^ ", "  ^ string_of_int i ^ ",\n" ^
    feature_sig_string ^ ",\n" ^ next_vec_string ^ ")"

let print_vector t = print_endline (_string_of_vector t)

