%{
open Parsing_utils
%}


%token <int> IntToken
%token <float> FloatToken
%token <string> StringToken
%token TrueToken
%token FalseToken
// %token <string> StringToken
%token NullToken

%token TreeToken              // : "T"
%token NodeToken              // : "N"
%token LeafToken              // : "L"
%token VectorToken            // : "V"
%token FeatureListToken       // : "F"
%token BoolFeatureToken       // : "bool"
%token FloatFeatureToken      // : "float"

%token LeftParenthesisToken   // : "("
%token RightParenthesisToken  // : ")"
%token LeftBracketToken       // : "["
%token RightBracketToken      // : "]"
%token ComaToken              // : ","

%token EOF




(* Type de l'attribut synthétisé des non-terminaux *)
%type <Parsing_utils.parsed_tree> tree
%type <Parsing_utils.parsed_vector> vector

(* Type et définition de l'axiome *)
%start <Parsing_utils.parsed_file> main

%%
(*
  E -> FeatureList Tree Vector
  
  FeatureList -> F( Features )
  Features -> Feature, Features
  Features -> Feature
  FeatureList -> *vide*
  Feature -> bool
  Feature -> float
  Feature -> [ StringList ]
  StringList -> StringToken, StringList
  StringList -> StringToken
  StringList -> *vide*

  Tree -> Node, Tree
  Tree -> Node          (* pour pouvoir ne pas écrire ',' à la fin (car c'est une liste) *)
  Tree ->  *vide*
  Node -> N(int, Value, int, int)
  Node -> L(int)
  Value -> null
  Value -> float

  Vector -> V( VectorElements )
  VectorElements -> VectorElement, VectorElements
  VectorElements -> *vide*
  VectorElement -> TrueToken
  VectorElement -> FalseToken
  VectorElement -> FloatToken

*)

main: fs = featurelist t = tree v = vector EOF { fs, t, v }


featurelist: FeatureListToken LeftParenthesisToken fs = features RightParenthesisToken { fs }

features:
  | /* vide */     { [ ] }
  | f = feature    { [f] }
  | f = feature ComaToken fs = features    { f::fs }

feature:
  | BoolFeatureToken  { ParsedBoolFeature }
  | FloatFeatureToken { ParsedFloatFeature }
  | LeftBracketToken s = stringlist RightBracketToken { ParsedEnumFeature s }

stringlist:
  | /* vide */         { [ ] }
  | s = StringToken    { [s] }
  | s = StringToken ComaToken ss = stringlist    { s::ss }



tree: TreeToken LeftParenthesisToken ns = nodes RightParenthesisToken { ns }

nodes:
  | /* vide */        { [ ] }
  | n = node          { [n] }
  | n = node ComaToken ns = nodes    { n::ns }

node:
  | NodeToken LeftParenthesisToken 
      fi = IntToken ComaToken
      ti = value RightParenthesisToken                            { ParsedNode (fi, ti) }
  | LeafToken LeftParenthesisToken c = IntToken RightParenthesisToken { ParsedLeaf (c) }

value:
  | NullToken       { ParsedNullValue }
  | f = FloatToken  { ParsedFloatValue (f) }
  // | e = EnumToken    { ParsedEnumValue (e) }



vector: VectorToken LeftParenthesisToken vs = vector_elements RightParenthesisToken { vs }

vector_elements:
  | /* vide */            { [ ] }
  | ve = vector_element   { [ve] }
  | ve = vector_element ComaToken ves = vector_elements   { ve::ves }

vector_element:
  | TrueToken       { ParsedBoolVectorElement(true) }
  | FalseToken      { ParsedBoolVectorElement(false) }
  | f = FloatToken  { ParsedFloatVectorElement(f) }
  | s = StringToken { ParsedEnumVectorElement(s) }



