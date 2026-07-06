open Bool
open Datatypes
open Equalities
open Explainers
open Features
open FloatUtils
open Utils
open Xp

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

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

(** val boolConstraintEmpty : boolConstraint -> bool **)

let boolConstraintEmpty = function
| BEmpty -> true
| _ -> false

(** val floatConstraintEmpty : floatConstraint -> bool **)

let floatConstraintEmpty = function
| FEmpty -> true
| _ -> false

(** val senumConstraintEmpty : StringSet.t -> senumConstraint -> bool **)

let senumConstraintEmpty _ =
  StringSet.is_empty

(** val boolConstraintWitness : boolConstraint -> bool option **)

let boolConstraintWitness = function
| BEmpty -> None
| BFalse -> Some false
| _ -> Some true

(** val floatConstraintWitness : floatConstraint -> float_std option **)

let floatConstraintWitness = function
| FEmpty -> None
| FSingleton a -> Some a
| FBounded (a, _) -> Some a
| FUnbounded a -> Some a

(** val senumConstraintWitness :
    StringSet.t -> senumConstraint -> string_enum option **)

let senumConstraintWitness _ c =
  let filtered_var = StringSet.choose c in
  (match filtered_var with
   | Some x -> Some x
   | None -> None)

(** val boolConstraintLeftSplit : boolConstraint -> boolConstraint **)

let boolConstraintLeftSplit = function
| BEmpty -> BEmpty
| BFalse -> BEmpty
| _ -> BTrue

(** val boolConstraintRightSplit : boolConstraint -> boolConstraint **)

let boolConstraintRightSplit = function
| BEmpty -> BEmpty
| BTrue -> BEmpty
| _ -> BFalse

(** val float_lt_dec : float_std -> float_std -> bool **)

let float_lt_dec x y =
  let c = FloatOTF.compare x y in (match c with
                                   | Lt -> true
                                   | _ -> false)

(** val floatConstraintLeftSplit :
    float_test -> floatConstraint -> floatConstraint **)

let floatConstraintLeftSplit t0 = function
| FEmpty -> FEmpty
| FSingleton a ->
  let filtered_var = float_lt_dec a t0 in
  if filtered_var then FSingleton a else FEmpty
| FBounded (a, b) ->
  let filtered_var = float_lt_dec a t0 in
  if filtered_var
  then let filtered_var0 = float_lt_dec t0 b in
       if filtered_var0 then FBounded (a, t0) else FBounded (a, b)
  else FEmpty
| FUnbounded a ->
  let filtered_var = float_lt_dec a t0 in
  if filtered_var then FBounded (a, t0) else FEmpty

(** val floatConstraintRightSplit :
    float_test -> floatConstraint -> floatConstraint **)

let floatConstraintRightSplit t0 = function
| FEmpty -> FEmpty
| FSingleton a ->
  let filtered_var = float_lt_dec a t0 in
  if filtered_var then FEmpty else FSingleton a
| FBounded (a, b) ->
  let filtered_var = float_lt_dec a t0 in
  if filtered_var
  then let filtered_var0 = float_lt_dec t0 b in
       if filtered_var0 then FBounded (t0, b) else FEmpty
  else FBounded (a, b)
| FUnbounded a ->
  let filtered_var = float_lt_dec a t0 in
  if filtered_var then FUnbounded t0 else FUnbounded a

(** val senumConstraintLeftSplit :
    StringSet.t -> string_enum_test -> senumConstraint -> senumConstraint **)

let senumConstraintLeftSplit _ =
  StringSet.filter

(** val senumConstraintRightSplit :
    StringSet.t -> string_enum_test -> senumConstraint -> senumConstraint **)

let senumConstraintRightSplit _ t0 c =
  StringSet.filter (fun x -> negb (t0 x)) c

(** val boolConstraintInitFull : boolConstraint **)

let boolConstraintInitFull =
  BAny

(** val floatConstraintInitFull : floatConstraint **)

let floatConstraintInitFull =
  FUnbounded FloatOTF.neg_inf

(** val senumConstraintInitFull : StringSet.t -> senumConstraint **)

let senumConstraintInitFull s =
  s

(** val boolConstraintInitSingleton : bool -> boolConstraint **)

let boolConstraintInitSingleton = function
| true -> BTrue
| false -> BFalse

(** val floatConstraintInitSingleton : float_std -> floatConstraint **)

let floatConstraintInitSingleton x =
  FSingleton x

(** val senumConstraintInitSingleton :
    StringSet.t -> string_enum -> senumConstraint **)

let senumConstraintInitSingleton _ =
  StringSet.singleton

type fConstraint =
| CBool of boolConstraint
| CFloat of floatConstraint
| CSEnum of StringSet.t * senumConstraint

(** val constraintEmpty : featureKind -> fConstraint -> bool **)

let constraintEmpty _ = function
| CBool c0 -> boolConstraintEmpty c0
| CFloat c0 -> floatConstraintEmpty c0
| CSEnum (s, c0) -> senumConstraintEmpty s c0

(** val constraintWitness : featureKind -> fConstraint -> dom option **)

let constraintWitness _ = function
| CBool c0 -> Obj.magic boolConstraintWitness c0
| CFloat c0 -> Obj.magic floatConstraintWitness c0
| CSEnum (s, c0) -> Obj.magic senumConstraintWitness s c0

(** val constraintLeftSplit :
    featureKind -> testIndex -> fConstraint -> fConstraint **)

let constraintLeftSplit _ t0 = function
| CBool c0 -> Obj.magic (CBool (boolConstraintLeftSplit c0))
| CFloat c0 -> CFloat (floatConstraintLeftSplit (Obj.magic t0) c0)
| CSEnum (s, c0) -> CSEnum (s, (senumConstraintLeftSplit s (Obj.magic t0) c0))

(** val constraintRightSplit :
    featureKind -> testIndex -> fConstraint -> fConstraint **)

let constraintRightSplit _ t0 = function
| CBool c0 -> Obj.magic (CBool (boolConstraintRightSplit c0))
| CFloat c0 -> CFloat (floatConstraintRightSplit (Obj.magic t0) c0)
| CSEnum (s, c0) ->
  CSEnum (s, (senumConstraintRightSplit s (Obj.magic t0) c0))

(** val constraintInitFull : featureKind -> fConstraint **)

let constraintInitFull = function
| Coq_isContinuousFeature -> CFloat floatConstraintInitFull
| Coq_isBooleanFeature -> CBool boolConstraintInitFull
| Coq_isStringEnumFeature s -> CSEnum (s, (senumConstraintInitFull s))

(** val constraintInitSingleton : featureKind -> dom -> fConstraint **)

let constraintInitSingleton f x =
  match f with
  | Coq_isContinuousFeature ->
    CFloat (floatConstraintInitSingleton (Obj.magic x))
  | Coq_isBooleanFeature -> CBool (boolConstraintInitSingleton (Obj.magic x))
  | Coq_isStringEnumFeature s ->
    CSEnum (s, (senumConstraintInitSingleton s (Obj.magic x)))

type featureSpaceConstraint =
| Coq_featureSpaceConstraintNil
| Coq_featureSpaceConstraintCons of featureKind * fConstraint * int
   * featureSig * featureSpaceConstraint

(** val update :
    int -> featureSig -> featureSpaceConstraint -> fin -> (fConstraint ->
    fConstraint) -> featureSpaceConstraint **)

let rec update _ _ cs i =
  match cs with
  | Coq_featureSpaceConstraintNil -> (fun _ -> Coq_featureSpaceConstraintNil)
  | Coq_featureSpaceConstraintCons (f, c, n0, fs0, cs0) ->
    let x = update n0 fs0 cs0 in
    (fun ap ->
    match i with
    | F1 n1 ->
      Coq_featureSpaceConstraintCons
        ((getFeatureKind (Stdlib.Int.succ n1) (Coq_featureSigCons (n1, f,
           fs0)) (F1 n1)), (ap c), n1, fs0, cs0)
    | FS (n1, i0) -> Coq_featureSpaceConstraintCons (f, c, n1, fs0, (x i0 ap)))

(** val empty : int -> featureSig -> featureSpaceConstraint -> bool **)

let rec empty _ _ = function
| Coq_featureSpaceConstraintNil -> false
| Coq_featureSpaceConstraintCons (f, c, n0, fs0, cs0) ->
  (||) (constraintEmpty f c) (empty n0 fs0 cs0)

(** val witness :
    int -> featureSig -> featureSpaceConstraint -> featureVec option **)

let rec witness _ _ = function
| Coq_featureSpaceConstraintNil -> Some Coq_featureVecNil
| Coq_featureSpaceConstraintCons (f, c, n0, fs0, cs0) ->
  (match constraintWitness f c with
   | Some x ->
     (match witness n0 fs0 cs0 with
      | Some vs -> Some (Coq_featureVecCons (f, x, n0, fs0, vs))
      | None -> None)
   | None -> None)

(** val splitLeft :
    int -> featureSig -> fin -> testIndex -> featureSpaceConstraint ->
    featureSpaceConstraint **)

let splitLeft n0 fs0 i t0 cs =
  update n0 fs0 cs i (constraintLeftSplit (getFeatureKind n0 fs0 i) t0)

(** val splitRight :
    int -> featureSig -> fin -> testIndex -> featureSpaceConstraint ->
    featureSpaceConstraint **)

let splitRight n0 fs0 i t0 cs =
  update n0 fs0 cs i (constraintRightSplit (getFeatureKind n0 fs0 i) t0)

(** val init :
    int -> (fin -> bool) -> featureSig -> featureVec -> featureSpaceConstraint **)

let rec init _ x _ = function
| Coq_featureVecNil -> Coq_featureSpaceConstraintNil
| Coq_featureVecCons (f, x0, n0, fs0, vs0) ->
  let c =
    if x (F1 n0) then constraintInitFull f else constraintInitSingleton f x0
  in
  Coq_featureSpaceConstraintCons (f, c, n0, fs0,
  (init n0 (fun k0 -> x (FS (n0, k0))) fs0 vs0))

module DtWCXpCheckerImpl =
 functor (C:DT.DT) ->
 functor (S:FinSet) ->
 struct
  module FD = FeatureSigDefs(C)(S)

  (** val refute_aux :
      C.K.t -> featureSpaceConstraint -> C.t -> featureVec option **)

  let rec refute_aux c0 c = function
  | DT.Leaf c1 -> if C.K.eq_dec c1 c0 then None else witness C.n C.fs c
  | DT.Node (i, test, dt1, dt2) ->
    let cleft = splitLeft C.n C.fs i test c in
    let cRight = splitRight C.n C.fs i test c in
    if empty C.n C.fs cleft
    then if empty C.n C.fs cRight then None else refute_aux c0 cRight dt2
    else (match refute_aux c0 cleft dt1 with
          | Some r -> Some r
          | None ->
            if empty C.n C.fs cRight then None else refute_aux c0 cRight dt2)

  (** val init : S.t -> featureVec -> featureSpaceConstraint **)

  let init x =
    init S.n (fun i -> S.mem i x) C.fs

  (** val refute : C.t -> featureVec -> S.t -> featureVec option **)

  let refute dt0 v0 x =
    refute_aux (C.eval dt0 v0) (init x v0) dt0
 end

module DtWCXpChecker =
 functor (E_:DTInputProblem) ->
 struct
  module E = E_

  module Xp = ExplainersDefs(E)

  module Impl = DtWCXpCheckerImpl(E)(E.S)

  (** val checkWCXp : E_.S.t -> bool **)

  let checkWCXp x =
    match Impl.refute E.k E.v x with
    | Some _ -> true
    | None -> false

  (** val checkWCXpSound : E.S.t -> reflect **)

  let checkWCXpSound x =
    let o = Impl.refute E.k E.v x in
    (match o with
     | Some _ -> ReflectT
     | None -> ReflectF)
 end

module DtAXpFinder =
 functor (E_:DTInputProblem) ->
 struct
  module Chk = DtWCXpChecker(E_)

  module E = E_

  module Impl = AXpIterativeFinderOn(E_)(Chk)

  module Xp = Impl.Xp

  (** val findAXp : E_.S.t -> E_.S.t **)

  let findAXp =
    Impl.findAXp

  (** val findAXpSound : __ **)

  let findAXpSound =
    __

  (** val findAXpSane : __ **)

  let findAXpSane =
    __
 end

module DtCXpFinder =
 functor (E_:DTInputProblem) ->
 struct
  module Chk = DtWCXpChecker(E_)

  module E = E_

  module Impl = CXpIterativeFinderOn(E_)(Chk)

  module Xp = Impl.Xp

  (** val findCXp : E_.S.t -> E_.S.t **)

  let findCXp =
    Impl.findCXp

  (** val findCXpSound : __ **)

  let findCXpSound =
    __

  (** val findCXpSane : __ **)

  let findCXpSane =
    __
 end
