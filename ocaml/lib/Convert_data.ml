
open Dttxt.Parsing_utils
open Extracted.DT
open Extracted.Features
open Extracted.Utils

let set_of_string_list l =
  List.fold_right StringSet.add l StringSet.empty

(* Create the vector and the features list from parsed_vector and parsed_features. *)
(* vector_and_features_from_parsing : parsed_vector -> parsed_features -> featureVec * featureSig *)
let rec vector_and_features_from_parsing parsed_vector parsed_features = 
  let v,_,fs = (_vector_and_features_from_parsing parsed_vector parsed_features) in 
  v, fs

and _vector_and_features_from_parsing (v:parsed_vector) (fs:parsed_features) =
  match v, fs with
  | [], [] -> Coq_featureVecNil, 0, Coq_featureSigNil
  | [], _ -> 
    failwith "Error in vector_from_parsing (1) : the given vector does not respect features declaration"
  | _, [] -> 
    failwith "Error in vector_from_parsing (2) : the given vector does not respect features declaration"
  | vt :: vq, ft :: fq ->
    let next_feature, i, next_sig = _vector_and_features_from_parsing vq fq in
    begin
      match vt, ft with
      | ParsedBoolVectorElement b, (ParsedBoolFeature, _) ->
        (Coq_featureVecCons (Coq_isBooleanFeature,
                            Obj.repr b, i, next_sig, next_feature), 
        (i+1),
        Coq_featureSigCons (i, Coq_isBooleanFeature, next_sig))
      
      | ParsedFloatVectorElement f, (ParsedFloatFeature, _) ->
        (Coq_featureVecCons (Coq_isContinuousFeature,
                            Obj.repr f, i, next_sig, next_feature), 
        (i+1),
        Coq_featureSigCons (i, Coq_isContinuousFeature, next_sig))
      
      | ParsedEnumVectorElement s, (ParsedEnumFeature _ss, _) -> 
        let ss = set_of_string_list _ss in
        (Coq_featureVecCons (Coq_isStringEnumFeature ss,
                            Obj.repr s, i, next_sig, next_feature), 
        (i+1),
        Coq_featureSigCons (i, Coq_isStringEnumFeature ss, next_sig))
      
      | _, _ -> 
        failwith "Error in vector_from_parsing (3) : the given vector does not respect features declaration"
    end

(* Create the tree from the parsed_tree_element list. *)
(* tree_from_parsing : parsed_tree -> dt *)
let rec tree_from_parsing to_fin parsed_tree = 
  fst (_tree_from_parsing to_fin parsed_tree)

and _tree_from_parsing to_fin t =
  match t with
  | [] -> failwith "ERROR : incorrect tree description."
  | t :: q -> 
    begin
      match t with
      | ParsedLeaf a -> Leaf (string_of_int a), q (* il faut convertir int en string pour l'instant *)
      | ParsedNode (a, b) ->
        let tg, gq = _tree_from_parsing to_fin q in
        let td, dq = _tree_from_parsing to_fin gq in
        begin
          let b_ =
            match b with
            | ParsedNullValue -> Obj.repr ()
            | ParsedFloatValue f -> Obj.repr f
            | ParsedEnumValue ss -> Obj.repr (fun e -> List.mem e ss)
          in Node (to_fin a, b_, tg, td), dq
        end
    end

