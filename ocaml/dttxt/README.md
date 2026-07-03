# `dttxt`

## The folder

This folder contains the parsing of dttxt files.
The parsing returns a `parsed_file` object (type defined in `parsing_utils.ml`), that is : a `parsed_features * parsed_tree * parsed_vector` object.

This is not the type used in the explanation program. There are then translated to the right type (translation defined in `../lib/Convert_data.ml`)


## The `dttxt` format

The communication between Machine Learning libraries and OCaml extracted code is done by writing the _explanation problem_ in a file.
`dttxt` is the intermediate format created for that.

The explanation program needs 3 informations about the explanation problem :
- the features
- the decision tree
- the vector


### Grammar

```
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

Tree -> T( TreeElements )
TreeElements -> Node, TreeElements
TreeElements -> Node
TreeElements -> *empty*
Node -> N(int, Value, int, int)
Node -> L(int)
Value -> null
Value -> float

Vector -> V( VectorElements )
VectorElements -> VectorElement, VectorElements
VectorElements -> VectorElement
VectorElements -> *empty*
VectorElement -> TrueToken
VectorElement -> FalseToken
VectorElement -> FloatToken
VectorElement -> StringToken
```

You also can add comments in OCaml format in dttxt files, that is : `(* comment *)`

_**NB :** comments, tabulations, spaces and new lines are ignored._



### Example

Let's say we have a dataset representing rectangles. Each rectangle has 4 features : 
- width (float)
- height (float)
- is_filled (bool)
- color (enum ["red", "green", "blue"])

#### Features declaration
Here is the feature declaration :
```
F(float, float, bool, ["red", "blue", "green"])
```

#### Vector declaration
Let `v = [9., 1., true, "red"]` be a vector of that dataset.
Its representation in `dttxt` would be :
```
V(9., 1., true, "red")
```

#### Tree declaration
We want to classify those rectangles in 3 classes : 0, 1, 2.
Here is the decision tree :
```
T(
    N(0, 10.),
     N(1, 5.),
      L(0),
      L(1),
     N(3, ["red", "green"]),
      L(1),
      N(2, ()),
       L(2),
       L(1)
)
```
_**NB :** tabulations, spaces and new lines are ignored._

The node `N(0, 10.)` corresponds to :
```
     width < 10.0
        /    \
      no     yes
      /        \
```
The node `N(3, ["red", "green"]),` corresponds to :
```
color in ["red", "green"].
        /    \
      no     yes
      /        \
```
The node `N(2, ()),` corresponds to :
```
      is_filled
        /    \
     false   true
      /        \
```

Though, the final file would be :
```
(* a comment *)

F(float, float, bool, ["red", "blue", "green"])

T(
    N(0, 10.),
     N(1, 5.),
      L(0),
      L(1),
     N(3, ["red", "green"]),     (* an other comment *)
      L(1),
      N(2, ()),
       L(2),
       L(1)
)

V(9., 1., true, "red")
```

_**NB :** the data must follow this order : features, tree, vector._






