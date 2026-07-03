
(* --------------- type definitions --------------- *)

type parsed_feature =
| ParsedBoolFeature
| ParsedFloatFeature
| ParsedEnumFeature of string list
;;
(* Type d'une liste de features parsée dans la lecture d'un fichier formatté.*)
type parsed_features = parsed_feature list;;

type parsed_value =
  | ParsedNullValue
  | ParsedFloatValue of float
  | ParsedEnumValue of string list
;;
type parsed_tree_element =
  | ParsedLeaf of int (* class number *)
  | ParsedNode of int * parsed_value (* indice_feature, threshold *)
;;
(* Type d'un arbre parsé à la lecture d'un fichier formatté.*)
type parsed_tree = parsed_tree_element list;;


type parsed_vector_element =
| ParsedBoolVectorElement of bool
| ParsedFloatVectorElement of float
| ParsedEnumVectorElement of string
;;
(* Type d'un vecteur parsé dans la lecture d'un fichier formatté.*)
type parsed_vector = parsed_vector_element list;;


type parsed_file = parsed_features * parsed_tree * parsed_vector;;



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




