open Datatypes
open Equalities
open Features
open Utils

module type FeatureSig =
 sig
  val n : int

  val fs : featureSig
 end

module FeatureSigDefs :
 functor (F:FeatureSig) ->
 functor (S:sig
  module E :
   sig
    type t = fin

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> bool
   end

  type elt = E.t

  type t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> t * t

  val cardinal : t -> int

  val elements : t -> elt list

  val choose : t -> elt option

  val eq_dec : t -> t -> bool

  val compare : t -> t -> comparison

  val min_elt : t -> elt option

  val max_elt : t -> elt option

  val all : t

  val compl : t -> t

  val init : (elt -> bool) -> t

  val shrink : (t -> bool) -> t -> t
 end) ->
 sig
 end

module type Output =
 sig
  module K :
   UsualDecidableType
 end

module type InputProblem =
 sig
  val n : int

  val fs : featureSig

  module K :
   UsualDecidableType

  type t

  val eval : t -> featureVec -> K.t

  val k : t

  val v : featureVec

  module S :
   FinSet
 end
