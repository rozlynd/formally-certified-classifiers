open Datatypes
open FloatUtils
open PrimFloat
open Specif
open Utils

type __ = Obj.t

type feature =
  __ -> __ -> bool
  (* singleton inductive, whose constructor was mk_feature *)

type dom = __

type testIndex = __

val boolean_feature : feature

type float_test =
  float_std
  (* singleton inductive, whose constructor was float_lt *)

val float_feature : feature

type string_enum_test =
  StringSet.elt -> bool
  (* singleton inductive, whose constructor was subset_mem *)

val string_enum_feature : StringSet.t -> feature

val enum_feature : int -> feature

type featureKind =
| Coq_isContinuousFeature
| Coq_isBooleanFeature
| Coq_isStringEnumFeature of StringSet.t

val getf : featureKind -> feature

type featureSig =
| Coq_featureSigNil
| Coq_featureSigCons of int * featureKind * featureSig

type featureVec =
| Coq_featureVecNil
| Coq_featureVecCons of featureKind * dom * int * featureSig * featureVec

val getFeatureKind : int -> featureSig -> fin -> featureKind

val getFeature : int -> featureSig -> fin -> feature

val getValueS : int -> featureSig -> featureVec -> fin -> (feature, dom) sigT

val getValue' : int -> featureSig -> featureVec -> fin -> dom

val featureTest' : int -> featureSig -> featureVec -> fin -> testIndex -> bool
