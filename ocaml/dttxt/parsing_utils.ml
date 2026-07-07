
(* --------------- type definitions --------------- *)


(* Type d'une liste de features parsée dans la lecture d'un fichier dttxt.*)
type parsed_features = parsed_feature list
and parsed_feature =
| ParsedBoolFeature
| ParsedFloatFeature
| ParsedEnumFeature of string list
| ParsedNamedBoolFeature of string
| ParsedNamedFloatFeature of string
| ParsedNamedEnumFeature of string * string list
;;


type parsed_value =
  | ParsedNullValue
  | ParsedFloatValue of float
  | ParsedEnumValue of string list
;;

(* Type d'un arbre parsé à la lecture d'un fichier dttxt.*)
type named_parsed_tree = named_parsed_tree_element list
and named_parsed_tree_element =
  | ParsedLeaf_ of int                        (* class_number *)
  | ParsedNode_ of int * parsed_value         (* indice_feature_index, threshold *)
  | NamedParsedNode_ of string * parsed_value (* feature_name, threshold *)
;;

(* Type d'un arbre parsé à la lecture d'un fichier dttxt.*)
type parsed_tree = parsed_tree_element list
and parsed_tree_element =
  | ParsedLeaf of int (* class number *)
  | ParsedNode of int * parsed_value (* indice_feature, threshold *)
;;

(* Type d'un vecteur parsé dans la lecture d'un fichier dttxt.*)
type parsed_vector = parsed_vector_element list
and parsed_vector_element =
| ParsedBoolVectorElement of bool
| ParsedFloatVectorElement of float
| ParsedEnumVectorElement of string
;;

type temp_parsed_file = parsed_features * named_parsed_tree * parsed_vector;;

type parsed_file = parsed_features * parsed_tree * parsed_vector;;



let get_feature_index name parsed_features =
  
  let rec aux name parsed_features cpt = match parsed_features with
    | [] -> failwith ("Error : found feature nammed `" ^ name ^ "` in tree but it is not defined in features declaration.")
    | ParsedBoolFeature :: q
    | ParsedFloatFeature :: q
    | ParsedEnumFeature(_) :: q -> aux name q (cpt+1)
    | ParsedNamedBoolFeature(s) :: q
    | ParsedNamedFloatFeature(s) :: q
    | ParsedNamedEnumFeature(s, _) :: q ->
        if name = s then cpt
        else aux name q (cpt+1)
  
  in aux name parsed_features 0
;;

let rec unname_tree dt parsed_features = match dt with
  | [] -> []
  | ParsedLeaf_(e) :: q -> ParsedLeaf(e) :: (unname_tree q parsed_features)
  | ParsedNode_(i, v) :: q -> ParsedNode(i, v) :: (unname_tree q parsed_features)
  | NamedParsedNode_(name, v) :: q -> ParsedNode(get_feature_index name parsed_features, v) :: (unname_tree q parsed_features)
;;




let get_feature_at_index index parsed_features =
  
  let rec aux index parsed_features cpt = match parsed_features with
    | [] -> failwith ("Error : feature index " ^ (string_of_int index) ^ " out of bounds.")
    | t :: q -> if cpt = index then t else aux index q (cpt+1)
  
  in aux index parsed_features 0
;;

let is_subset l1 l2 = List.fold_right (fun t acc -> (List.mem t l2) && acc) l1 true;;

let rec type_verif dt parsed_features = match dt with
  | [] -> true
  | ParsedLeaf(e) :: q -> (type_verif q parsed_features)
  | ParsedNode(i, v) :: q -> 
      match get_feature_at_index i parsed_features, v with
      | ParsedBoolFeature, ParsedNullValue
      | ParsedNamedBoolFeature(_), ParsedNullValue
      | ParsedFloatFeature, ParsedFloatValue(_)
      | ParsedNamedFloatFeature(_), ParsedFloatValue(_) -> true
      | ParsedEnumFeature(ss1), ParsedEnumValue(ss2)
      | ParsedNamedEnumFeature(_, ss1), ParsedEnumValue(ss2) -> is_subset ss2 ss1
      | _ -> false
       && (type_verif q parsed_features)
;;











































(* --------------- examples --------------- *)
(* let v1 = [ParsedBoolVectorElement(true); ParsedFloatVectorElement(0.1)];;
let t1 = [
  ParsedNode(0, ParsedNullValue, 1, 4);
  ParsedNode(1, ParsedFloatValue(0.5), 2, 3);
  ParsedLeaf(0);
  ParsedLeaf(1);
  ParsedLeaf(2)
];;
let f1 = t1, v1;; *)
(* --------------- end of examples --------------- *)




(* --------------- print functions --------------- *)

(* for features : *)

let rec _string_of_string_list (l : string list) : string = match l with
  | [ ] -> ""
  | [t] -> "\"" ^ t ^ "\""
  | t::q -> "\"" ^ t ^ "\"" ^ ", " ^ (_string_of_string_list q)
;;
let string_of_string_list l = "[" ^ (_string_of_string_list l) ^ "]" ;;
let string_of_feature_element ve = match ve with
  | ParsedBoolFeature -> "bool"
  | ParsedFloatFeature -> "float"
  | ParsedEnumFeature(l) -> string_of_string_list l
  | ParsedNamedBoolFeature(n) -> "\"" ^ n ^ "\" : bool"
  | ParsedNamedFloatFeature(n) -> "\"" ^ n ^ "\" : float"
  | ParsedNamedEnumFeature(n, l) -> "\"" ^ n ^ "\" : " ^ string_of_string_list l
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
















(* 
return 
- None if no type error detected
- Some i with i the index of the first element of dt where error founded *)
let type_error dt parsed_features =
  let rec aux dt parsed_features cpt = match dt with
    | [] -> None
    | ParsedLeaf(e) :: q -> (aux q parsed_features (cpt+1))
    | ParsedNode(i, v) :: q -> 
        let f = (get_feature_at_index i parsed_features) in
        (* print_endline ("feature index : " ^ (string_of_int i));
        print_endline ("feature : " ^ (string_of_feature_element f)); *)
        match f, v with
        | ParsedBoolFeature, ParsedNullValue
        | ParsedNamedBoolFeature(_), ParsedNullValue
        | ParsedFloatFeature, ParsedFloatValue(_)
        | ParsedNamedFloatFeature(_), ParsedFloatValue(_) -> aux q parsed_features (cpt+1)
        | ParsedEnumFeature(ss1), ParsedEnumValue(ss2)
        | ParsedNamedEnumFeature(_, ss1), ParsedEnumValue(ss2) -> 
            if not (is_subset ss2 ss1) then Some( cpt )
            else aux q parsed_features (cpt+1)
        | _ -> Some( cpt )
  in aux dt parsed_features 0
;;