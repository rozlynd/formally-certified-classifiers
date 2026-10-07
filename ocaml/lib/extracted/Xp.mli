open Datatypes
open Equalities
open Features
open Utils

type __ = Obj.t

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

module ExplanationsDefs :
 functor (E:InputProblem) ->
 sig
 end

module ExplanationsFacts :
 functor (E:InputProblem) ->
 sig
  module Xp :
   sig
   end

  module P :
   sig
    module P :
     sig
      module ME :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = fin

            val compare : fin -> fin -> comparison

            val eq_dec : fin -> fin -> bool
           end

          module TO :
           sig
            type t = fin

            val compare : fin -> fin -> comparison

            val eq_dec : fin -> fin -> bool
           end
         end

        val eq_dec : fin -> fin -> bool

        val lt_dec : fin -> fin -> bool

        val eqb : fin -> fin -> bool
       end

      module ML :
       sig
       end

      module P :
       sig
        module Dec :
         sig
          module F :
           sig
            val eqb : fin -> fin -> bool
           end

          module MSetLogicalFacts :
           sig
           end

          module MSetDecideAuxiliary :
           sig
           end

          module MSetDecideTestCases :
           sig
           end
         end

        module FM :
         sig
          val eqb : fin -> fin -> bool
         end

        val coq_In_dec : E.S.elt -> E.S.t -> bool

        val of_list : E.S.elt list -> E.S.t

        val to_list : E.S.t -> E.S.elt list

        val fold_rec :
          (E.S.elt -> 'a1 -> 'a1) -> 'a1 -> E.S.t -> (E.S.t -> __ -> 'a2) ->
          (E.S.elt -> 'a1 -> E.S.t -> E.S.t -> __ -> __ -> __ -> 'a2 -> 'a2)
          -> 'a2

        val fold_rec_bis :
          (E.S.elt -> 'a1 -> 'a1) -> 'a1 -> E.S.t -> (E.S.t -> E.S.t -> 'a1
          -> __ -> 'a2 -> 'a2) -> 'a2 -> (E.S.elt -> 'a1 -> E.S.t -> __ -> __
          -> 'a2 -> 'a2) -> 'a2

        val fold_rec_nodep :
          (E.S.elt -> 'a1 -> 'a1) -> 'a1 -> E.S.t -> 'a2 -> (E.S.elt -> 'a1
          -> __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_weak :
          (E.S.elt -> 'a1 -> 'a1) -> 'a1 -> (E.S.t -> E.S.t -> 'a1 -> __ ->
          'a2 -> 'a2) -> 'a2 -> (E.S.elt -> 'a1 -> E.S.t -> __ -> 'a2 -> 'a2)
          -> E.S.t -> 'a2

        val fold_rel :
          (E.S.elt -> 'a1 -> 'a1) -> (E.S.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
          E.S.t -> 'a3 -> (E.S.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val set_induction :
          (E.S.t -> __ -> 'a1) -> (E.S.t -> E.S.t -> 'a1 -> E.S.elt -> __ ->
          __ -> 'a1) -> E.S.t -> 'a1

        val set_induction_bis :
          (E.S.t -> E.S.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (E.S.elt -> E.S.t ->
          __ -> 'a1 -> 'a1) -> E.S.t -> 'a1

        val cardinal_inv_2 : E.S.t -> int -> E.S.elt

        val cardinal_inv_2b : E.S.t -> E.S.elt
       end

      val gtb : fin -> fin -> bool

      val leb : fin -> fin -> bool

      val elements_lt : fin -> E.S.t -> fin list

      val elements_ge : fin -> E.S.t -> fin list

      val set_induction_max :
        (E.S.t -> __ -> 'a1) -> (E.S.t -> E.S.t -> 'a1 -> fin -> __ -> __ ->
        'a1) -> E.S.t -> 'a1

      val set_induction_min :
        (E.S.t -> __ -> 'a1) -> (E.S.t -> E.S.t -> 'a1 -> fin -> __ -> __ ->
        'a1) -> E.S.t -> 'a1
     end
   end
 end
