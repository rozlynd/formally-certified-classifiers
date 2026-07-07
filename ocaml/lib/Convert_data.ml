
open Dttxt.Parsing_utils
open Extracted.DT
open Extracted.Features
open Extracted.Utils


let set_of_string_list l =
  List.fold_right StringSet.add l StringSet.empty
;;

let rec _vector_and_features_from_parsing (v:parsed_vector) (fs:parsed_features) = match v, fs with
  | [], [] -> Coq_featureVecNil, 0, Coq_featureSigNil
  | [], _ -> 
    failwith "Error in vector_from_parsing (1) : the given vector does not respect features declaration"
  | _, [] -> 
    failwith "Error in vector_from_parsing (2) : the given vector does not respect features declaration"
  | vt :: vq, ft :: fq ->
    let next_feature, i, next_sig = _vector_and_features_from_parsing vq fq in
    begin
      match vt, ft with
      | ParsedBoolVectorElement(b), ParsedBoolFeature 
      | ParsedBoolVectorElement(b), ParsedNamedBoolFeature(_) ->
        (Coq_featureVecCons(Coq_isBooleanFeature, 
                            Obj.repr b, i, next_sig, next_feature), 
        (i+1),
        Coq_featureSigCons (i, Coq_isBooleanFeature, next_sig))
      
      | ParsedFloatVectorElement(f), ParsedFloatFeature 
      | ParsedFloatVectorElement(f), ParsedNamedFloatFeature(_) ->
        (Coq_featureVecCons(Coq_isContinuousFeature, 
                            Obj.repr f, i, next_sig, next_feature), 
        (i+1),
        Coq_featureSigCons (i, Coq_isContinuousFeature, next_sig))
      
      | ParsedEnumVectorElement(s), ParsedEnumFeature(_ss) 
      | ParsedEnumVectorElement(s), ParsedNamedEnumFeature(_, _ss) -> 
        let ss = set_of_string_list _ss in
        (Coq_featureVecCons(Coq_isStringEnumFeature ss, 
                            Obj.repr s, i, next_sig, next_feature), 
        (i+1),
        Coq_featureSigCons (i, Coq_isStringEnumFeature ss, next_sig))
      
      | _, _ -> 
        failwith "Error in vector_from_parsing (3) : the given vector does not respect features declaration"
    end
;;
(* create the vector and the features list from parsed_vector and parsed_features *)
(* vector_and_features_from_parsing : parsed_vector -> parsed_features -> featureVec * featureSig *)
let vector_and_features_from_parsing parsed_vector parsed_features = 
  let v,_,fs = (_vector_and_features_from_parsing parsed_vector parsed_features) in 
  v, fs
;;



let rec _tree_from_parsing to_fin t = match t with
  | [] -> failwith "ERROR : incorrect tree description."
  | t::q -> 
    begin
      match t with
      | ParsedLeaf(a) -> Leaf(string_of_int a), q (* il faut convertir int en string pour l'instant *)
      | ParsedNode(a, b) ->
        let tg, gq = _tree_from_parsing to_fin q in
        let td, dq = _tree_from_parsing to_fin gq in
        begin
          let b_ = match b with
            | ParsedNullValue -> Obj.repr ()
            | ParsedFloatValue(f) -> Obj.repr f
            | ParsedEnumValue(ss) -> Obj.repr (fun e -> List.mem e ss)
          in Node(to_fin a, b_, tg, td), dq
        end
    end
;;
(* create the tree from the parsed_tree_element list *)
(* tree_from_parsing : parsed_tree -> dt *)
let tree_from_parsing to_fin parsed_tree = 
  (* print_string "debug : begin tree_from_parsing..."; *)
  let r = fst (_tree_from_parsing to_fin parsed_tree) in
  (* print_endline "done."; *)
  r
;;




















(* let rec _features_from_parsing f = match f with
  | [] -> Coq_featureSigNil, 0
  | t::q ->
    let next_sig, i = _features_from_parsing q in
    match t with
      | ParsedBoolFeature ->
          Coq_featureSigCons (i, boolean_feature, Coq_isBooleanFeature, next_sig), (i+1)
      | ParsedFloatFeature ->
          Coq_featureSigCons (i, float_feature, Coq_isContinuousFeature, next_sig), (i+1)
      | ParsedEnumFeature(s) -> 
          Coq_featureSigCons (i, string_enum_feature (set_of_string_list s), 
                                 Coq_isStringEnumFeature (set_of_string_list s), next_sig), (i+1)
;;
let features_from_parsing f = fst (_features_from_parsing f) ;;



let rec _vector_from_parsing v = match v with
  | [] -> Coq_featureVecNil, 0, Coq_featureSigNil
  | t::q -> 
    let next_feature, i, next_sig = _vector_from_parsing q in
    begin
      match t with
      | ParsedBoolVectorElement(b) ->
        (Coq_featureVecCons(boolean_feature, Coq_isBooleanFeature, 
                            Obj.repr b, i, next_sig, next_feature), 
        (i+1),
        Coq_featureSigCons (i, boolean_feature, Coq_isBooleanFeature, next_sig))
      | ParsedFloatVectorElement(f) ->
        (Coq_featureVecCons(float_feature, Coq_isContinuousFeature, 
                            Obj.repr f, i, next_sig, next_feature), 
        (i+1),
        Coq_featureSigCons (i, float_feature, Coq_isContinuousFeature, next_sig)) (* il y avait un 0 à la place de i *)
      | ParsedEnumVectorElement(s) -> failwith "Error : enum features not implemented yet."
        (* (Coq_featureVecCons(string_enum_feature s, Coq_isStringEnumFeature s, 
                            Obj.repr s, i, next_sig, next_feature), 
        (i+1),
        Coq_featureSigCons (0, string_enum_feature s, Coq_isStringEnumFeature s, next_sig)) *)
    end
;;
let vector_from_parsing parsed_vector = 
  (* print_string "debug : begin vector_from_parsing..."; *)
  let a,_,_ = (_vector_from_parsing parsed_vector) in 
  (* print_endline "done.";  *)
  a
;; *)
