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
%token ColonToken             // : ":"

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
  FeatureList -> *empty*
  Feature -> bool
  Feature -> float
  Feature -> [ StringList ]
  StringList -> StringToken, StringList
  StringList -> StringToken
  StringList -> *empty*

  Tree -> Node, Tree
  Tree -> Node          (* pour pouvoir ne pas écrire ',' à la fin (car c'est une liste) *)
  Tree ->  *empty*
  Node -> N(int, Value, int, int)
  Node -> L(int)
  Value -> null
  Value -> float

  Vector -> V( VectorElements )
  VectorElements -> VectorElement, VectorElements
  VectorElements -> *empty*
  VectorElement -> TrueToken
  VectorElement -> FalseToken
  VectorElement -> FloatToken

*)

main: fs = featurelist t = tree v = vector EOF { fs, t, v }


featurelist: FeatureListToken LeftParenthesisToken fs = features RightParenthesisToken { fs }

features:
  | /* empty */    { [ ] }
  | f = feature    { [f] }
  | f = feature ComaToken fs = features    { f::fs }

feature:
  | BoolFeatureToken  { ParsedBoolFeature }
  | FloatFeatureToken { ParsedFloatFeature }
  | LeftBracketToken s = stringlist RightBracketToken { ParsedEnumFeature s }

stringlist:
  | /* empty */        { [ ] }
  | s = StringToken    { [s] }
  | s = StringToken ComaToken ss = stringlist    { s::ss }



tree: TreeToken LeftParenthesisToken ns = nodes RightParenthesisToken { ns }

nodes:
  | /* empty */       { [ ] }
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
  | LeftBracketToken s = stringlist RightBracketToken   { ParsedEnumValue (s) }



vector: VectorToken LeftParenthesisToken vs = vector_elements RightParenthesisToken { vs }

vector_elements:
  | /* empty */           { [ ] }
  | ve = vector_element   { [ve] }
  | ve = vector_element ComaToken ves = vector_elements   { ve::ves }

vector_element:
  | TrueToken       { ParsedBoolVectorElement(true) }
  | FalseToken      { ParsedBoolVectorElement(false) }
  | f = FloatToken  { ParsedFloatVectorElement(f) }
  | s = StringToken { ParsedEnumVectorElement(s) }



