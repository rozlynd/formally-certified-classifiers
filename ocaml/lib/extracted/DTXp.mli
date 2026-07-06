open Bool
open Datatypes
open Equalities
open Explainers
open Features
open FloatUtils
open Utils
open Xp

type __ = Obj.t

module type DTInputProblem =
 sig
  val n : int

  val fs : featureSig

  module K :
   UsualDecidableType

  type t = K.t DT.dt

  val eval : t -> featureVec -> K.t

  val k : t

  val v : featureVec

  module S :
   FinSet
 end

type boolConstraint =
| BEmpty
| BTrue
| BFalse
| BAny

type floatConstraint =
| FEmpty
| FSingleton of float_std
| FBounded of float_std * float_std
| FUnbounded of float_std

type senumConstraint =
  StringSet.t
  (* singleton inductive, whose constructor was SEnum *)

val boolConstraintEmpty : boolConstraint -> bool

val floatConstraintEmpty : floatConstraint -> bool

val senumConstraintEmpty : StringSet.t -> senumConstraint -> bool

val boolConstraintWitness : boolConstraint -> bool option

val floatConstraintWitness : floatConstraint -> float_std option

val senumConstraintWitness :
  StringSet.t -> senumConstraint -> string_enum option

val boolConstraintLeftSplit : boolConstraint -> boolConstraint

val boolConstraintRightSplit : boolConstraint -> boolConstraint

val float_lt_dec : float_std -> float_std -> bool

val floatConstraintLeftSplit :
  float_test -> floatConstraint -> floatConstraint

val floatConstraintRightSplit :
  float_test -> floatConstraint -> floatConstraint

val senumConstraintLeftSplit :
  StringSet.t -> string_enum_test -> senumConstraint -> senumConstraint

val senumConstraintRightSplit :
  StringSet.t -> string_enum_test -> senumConstraint -> senumConstraint

val boolConstraintInitFull : boolConstraint

val floatConstraintInitFull : floatConstraint

val senumConstraintInitFull : StringSet.t -> senumConstraint

val boolConstraintInitSingleton : bool -> boolConstraint

val floatConstraintInitSingleton : float_std -> floatConstraint

val senumConstraintInitSingleton :
  StringSet.t -> string_enum -> senumConstraint

type fConstraint =
| CBool of boolConstraint
| CFloat of floatConstraint
| CSEnum of StringSet.t * senumConstraint

val constraintEmpty : featureKind -> fConstraint -> bool

val constraintWitness : featureKind -> fConstraint -> dom option

val constraintLeftSplit :
  featureKind -> testIndex -> fConstraint -> fConstraint

val constraintRightSplit :
  featureKind -> testIndex -> fConstraint -> fConstraint

val constraintInitFull : featureKind -> fConstraint

val constraintInitSingleton : featureKind -> dom -> fConstraint

type featureSpaceConstraint =
| Coq_featureSpaceConstraintNil
| Coq_featureSpaceConstraintCons of featureKind * fConstraint * int
   * featureSig * featureSpaceConstraint

val update :
  int -> featureSig -> featureSpaceConstraint -> fin -> (fConstraint ->
  fConstraint) -> featureSpaceConstraint

val empty : int -> featureSig -> featureSpaceConstraint -> bool

val witness : int -> featureSig -> featureSpaceConstraint -> featureVec option

val splitLeft :
  int -> featureSig -> fin -> testIndex -> featureSpaceConstraint ->
  featureSpaceConstraint

val splitRight :
  int -> featureSig -> fin -> testIndex -> featureSpaceConstraint ->
  featureSpaceConstraint

val init :
  int -> (fin -> bool) -> featureSig -> featureVec -> featureSpaceConstraint

module DtWCXpCheckerImpl :
 functor (C:DT.DT) ->
 functor (S:FinSet) ->
 sig
  module FD :
   sig
   end

  val refute_aux : C.K.t -> featureSpaceConstraint -> C.t -> featureVec option

  val init : S.t -> featureVec -> featureSpaceConstraint

  val refute : C.t -> featureVec -> S.t -> featureVec option
 end

module DtWCXpChecker :
 functor (E_:DTInputProblem) ->
 WCXpChecker with module E = E_

module DtAXpFinder :
 functor (E_:DTInputProblem) ->
 AXpFinder with module E = E_

module DtCXpFinder :
 functor (E_:DTInputProblem) ->
 CXpFinder with module E = E_
