open Datatypes
open FloatUtils
open PrimFloat
open Specif
open Utils

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type feature =
  __ -> __ -> bool
  (* singleton inductive, whose constructor was mk_feature *)

type dom = __

type testIndex = __

(** val boolean_feature : feature **)

let boolean_feature =
  Obj.magic (fun _ b -> b)

type float_test =
  float_std
  (* singleton inductive, whose constructor was float_lt *)

(** val float_feature : feature **)

let float_feature t0 pat =
  negb (leb (Obj.magic t0) (Obj.magic pat))

type string_enum_test =
  StringSet.elt -> bool
  (* singleton inductive, whose constructor was subset_mem *)

(** val string_enum_feature : StringSet.t -> feature **)

let string_enum_feature _ t0 x =
  Obj.magic t0 x

(** val enum_feature : int -> feature **)

let enum_feature _ t0 x =
  Obj.magic t0 x

type featureKind =
| Coq_isContinuousFeature
| Coq_isBooleanFeature
| Coq_isStringEnumFeature of StringSet.t

(** val getf : featureKind -> feature **)

let getf = function
| Coq_isContinuousFeature -> float_feature
| Coq_isBooleanFeature -> boolean_feature
| Coq_isStringEnumFeature s -> string_enum_feature s

type featureSig =
| Coq_featureSigNil
| Coq_featureSigCons of int * featureKind * featureSig

type featureVec =
| Coq_featureVecNil
| Coq_featureVecCons of featureKind * dom * int * featureSig * featureVec

(** val getFeatureKind : int -> featureSig -> fin -> featureKind **)

let rec getFeatureKind _ fs i =
  match fs with
  | Coq_featureSigNil ->
    (match i with
     | F1 x -> Obj.magic __ x
     | FS (x, x0) -> Obj.magic __ x x0)
  | Coq_featureSigCons (n0, f, fs0) ->
    let x = getFeatureKind n0 fs0 in
    (match i with
     | F1 _ -> f
     | FS (_, i0) -> x i0)

(** val getFeature : int -> featureSig -> fin -> feature **)

let getFeature n fs i =
  getf (getFeatureKind n fs i)

(** val getValueS :
    int -> featureSig -> featureVec -> fin -> (feature, dom) sigT **)

let rec getValueS _ _ vs i =
  match vs with
  | Coq_featureVecNil ->
    (match i with
     | F1 x -> Obj.magic __ x
     | FS (x, x0) -> Obj.magic __ x x0)
  | Coq_featureVecCons (f, x, n0, fs0, vs0) ->
    let x0 = getValueS n0 fs0 vs0 in
    (match i with
     | F1 _ -> Coq_existT ((getf f), x)
     | FS (_, i0) -> x0 i0)

(** val getValue' : int -> featureSig -> featureVec -> fin -> dom **)

let getValue' n fs vs i =
  projT2 (getValueS n fs vs i)

(** val featureTest' :
    int -> featureSig -> featureVec -> fin -> testIndex -> bool **)

let featureTest' n fs vs i t0 =
  getFeature n fs i t0 (getValue' n fs vs i)
