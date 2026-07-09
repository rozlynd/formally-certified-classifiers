
(* --------------- TYPE DEFINITIONS --------------- *)


(* Features list type obtained after reading dttxt file. *)
(* type _parsed_features = _parsed_feature list
and _parsed_feature =
| ParsedBoolFeature
| ParsedFloatFeature
| ParsedEnumFeature of string list
| ParsedNamedBoolFeature of string
| ParsedNamedFloatFeature of string
| ParsedNamedEnumFeature of string * string list
;; *)
type parsed_features = (parsed_feature * string option) list
and parsed_feature =
| ParsedBoolFeature
| ParsedFloatFeature
| ParsedEnumFeature of string list
;;


(* Type of the value given in a node to compare to the vector value.
example : threshold for float features, () for bool features, list of enum values for enum features. *)
type parsed_value =
  | ParsedNullValue
  | ParsedFloatValue of float
  | ParsedEnumValue of string list
;;

(* Tree type obtained after reading dttxt file. 
A node can reference its feature by its string name, or by its int index. *)
type named_parsed_tree = named_parsed_tree_element list
and named_parsed_tree_element =
  | ParsedLeaf_ of int                        (* class_number *)
  | ParsedNode_ of int * parsed_value         (* indice_feature_index, threshold *)
  | NamedParsedNode_ of string * parsed_value (* feature_name, threshold *)
;;

(* Tree type obtained after reading dttxt file. 
All nodes reference its feature by its int index. *)
type parsed_tree = parsed_tree_element list
and parsed_tree_element =
  | ParsedLeaf of int (* class number *)
  | ParsedNode of int * parsed_value (* indice_feature, threshold *)
;;

(* Vector type obtained after reading dttxt file. *)
type parsed_vector = parsed_vector_element list
and parsed_vector_element =
| ParsedBoolVectorElement of bool
| ParsedFloatVectorElement of float
| ParsedEnumVectorElement of string
;;

type parsed_vectors = parsed_vector list;;

type temp_parsed_file = parsed_features * named_parsed_tree * parsed_vectors;;

type parsed_file = parsed_features * parsed_tree * parsed_vector;;


(* Get the index of a features given its name. If the name is not found, raise Failure. *)
let get_feature_index name parsed_features =
  
  let rec aux name parsed_features acc = match parsed_features with
    | [] -> failwith ("Error : found feature nammed `" ^ name ^ "` in tree but it is not defined in features declaration.")
    | (t, None) :: q -> aux name q (acc+1)
    | (t, Some s) :: q ->
        if name = s then acc
        else aux name q (acc+1)
  
  in aux name parsed_features 0
;;

(* Transform a named_parsed_tree in a parsed_tree (by finding the indices of named features). *)
let rec unname_tree dt parsed_features = match dt with
  | [] -> []
  | ParsedLeaf_(e) :: q -> ParsedLeaf(e) :: (unname_tree q parsed_features)
  | ParsedNode_(i, v) :: q -> ParsedNode(i, v) :: (unname_tree q parsed_features)
  | NamedParsedNode_(name, v) :: q -> ParsedNode(get_feature_index name parsed_features, v) :: (unname_tree q parsed_features)
;;



(* Get the feature name at a given index in parsed_features.
Return index as a string if it is not a named feature.
If index out of bounds, raise Failure. *)
let get_feature_name_at_index index parsed_features =
  
  let rec aux index parsed_features cpt = match parsed_features with
    | [] -> failwith ("Error : feature index " ^ (string_of_int index) ^ " out of bounds.")
    | (_, t) :: q -> 
      if cpt = index then 
        match t with
        | None -> string_of_int index
        | Some s -> s
      else aux index q (cpt+1)
  
  in aux index parsed_features 0
;;

(* Get the feature at a given index in parsed_features. 
If index out of bounds, raise Failure. *)
let get_feature_at_index index parsed_features =
  
  let rec aux index parsed_features cpt = match parsed_features with
    | [] -> failwith ("Error : feature index " ^ (string_of_int index) ^ " out of bounds.")
    | t :: q -> if cpt = index then t else aux index q (cpt+1)
  
  in aux index parsed_features 0
;;

(* Test if every element of l1 is in l2. *)
let is_subset l1 l2 = List.fold_right (fun t acc -> (List.mem t l2) && acc) l1 true;;

(* Check the types of dt given parsed_feaetures. Return
- None if no type error detected
- Some i with i the index of the first element of dt where error founded *)
let type_error dt parsed_features =
  let rec aux dt parsed_features cpt = match dt with
    | [] -> None
    | ParsedLeaf(e) :: q -> (aux q parsed_features (cpt+1))
    | ParsedNode(i, v) :: q -> 
        let f = (get_feature_at_index i parsed_features) in
        match f, v with
        | (ParsedBoolFeature, _), ParsedNullValue
        | (ParsedFloatFeature, _), ParsedFloatValue(_) -> aux q parsed_features (cpt+1)
        | (ParsedEnumFeature(ss1), _), ParsedEnumValue(ss2) -> 
            if not (is_subset ss2 ss1) then Some( cpt )
            else aux q parsed_features (cpt+1)
        | _ -> Some( cpt )
  in aux dt parsed_features 0
;;









































(* --------------- PRINT FUNCTIONS --------------- *)

(* for features : *)

let rec _string_of_string_list (l : string list) : string = match l with
  | [ ] -> ""
  | [t] -> "\"" ^ t ^ "\""
  | t::q -> "\"" ^ t ^ "\"" ^ ", " ^ (_string_of_string_list q)
;;
let string_of_string_list l = "[" ^ (_string_of_string_list l) ^ "]" ;;
let string_of_feature_element ve = 
  let f, name_opt = ve in
  match name_opt with
  | None -> ""
  | Some s -> "\"" ^ s ^ "\" : "
  ^ match f with
  | ParsedBoolFeature -> "bool"
  | ParsedFloatFeature -> "float"
  | ParsedEnumFeature(l) -> string_of_string_list l
;;
let rec _string_of_features v = match v with
  | [ ] -> ""
  | [t] ->   string_of_feature_element t
  | t::q -> (string_of_feature_element t) ^ ", " ^ (_string_of_features q)
;;
let string_of_features v = "F(" ^ (_string_of_features v) ^ ")" ;;

let print_features v = print_endline (string_of_features v) ;;




(* for vectors : *)

let string_of_vector_element ve = match ve with
  | ParsedBoolVectorElement(b) -> if b then "true" else "false"
  | ParsedFloatVectorElement(f) -> string_of_float f
  | ParsedEnumVectorElement(s) -> "\"" ^ s ^ "\""
;;
let rec _string_of_vector v = match v with
  | [] -> ""
  | [t] -> string_of_vector_element t
  | t::q -> (string_of_vector_element t) ^ ", " ^ (_string_of_vector q)
;;
let string_of_vector v = "V(" ^ (_string_of_vector v) ^ ")" ;;

let print_vector v = print_endline (string_of_vector v) ;;



(* for trees : *)

let _string_of_string_list l = match l with
  | [ ]  -> ""
  | [t]  -> "\"" ^ t ^ "\""
  | t::q -> "\"" ^ t ^ "\", " ^ (_string_of_string_list q)
;;
let string_of_string_list l = "[" ^ (_string_of_string_list l) ^ "]"

let string_of_value v = match v with
  | ParsedNullValue -> "()"
  | ParsedFloatValue f -> string_of_float f
  | ParsedEnumValue ss -> string_of_string_list ss
;;
let string_of_tree_element ve = match ve with
  | ParsedLeaf(c) -> "L(" ^ (string_of_int c) ^ ")"
  | ParsedNode(index_feature, value) -> 
      ( "N(" ^ (string_of_int index_feature) ^ ", " ^ (string_of_value value) ^ ")" );
;;
let rec _string_of_tree t = match t with
  | [ ]  -> ""
  | [a]  -> "  " ^ (string_of_tree_element a)
  | a::q -> "  " ^ (string_of_tree_element a) ^ ",\n" ^ (_string_of_tree q)
;;
let string_of_tree t = "T(\n" ^ _string_of_tree t ^ "\n)";;

let print_tree t = print_endline (string_of_tree t);;


(* --------------- end of print functions --------------- *)


