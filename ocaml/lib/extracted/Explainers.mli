open Bool
open CNF
open Datatypes
open Equalities
open Features
open List0
open Sat
open Utils
open Xp

type __ = Obj.t

module ExplainersDefs :
 functor (E:InputProblem) ->
 sig
 end

module EnumeratorsDefs :
 functor (E:InputProblem) ->
 sig
  type coq_Xp =
  | Coq_isAXp of E.S.t
  | Coq_isCXp of E.S.t
 end

module type AXpFinder =
 sig
  module E :
   InputProblem

  module Xp :
   sig
   end

  val findAXp : E.S.t -> E.S.t
 end

module type CXpFinder =
 sig
  module E :
   InputProblem

  module Xp :
   sig
   end

  val findCXp : E.S.t -> E.S.t
 end

module type WCXpChecker =
 sig
  module E :
   InputProblem

  module Xp :
   sig
   end

  val checkWCXp : E.S.t -> bool

  val checkWCXpSound : E.S.t -> reflect
 end

module AXpIterativeFinderOn :
 functor (E:InputProblem) ->
 functor (Chk:WCXpChecker with module E = E) ->
 sig
  module Xp :
   sig
   end

  val checkWAXp : E.S.t -> bool

  val findAXp : E.S.t -> E.S.t

  module XpFacts :
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
            (E.S.elt -> 'a1 -> 'a1) -> 'a1 -> E.S.t -> (E.S.t -> __ -> 'a2)
            -> (E.S.elt -> 'a1 -> E.S.t -> E.S.t -> __ -> __ -> __ -> 'a2 ->
            'a2) -> 'a2

          val fold_rec_bis :
            (E.S.elt -> 'a1 -> 'a1) -> 'a1 -> E.S.t -> (E.S.t -> E.S.t -> 'a1
            -> __ -> 'a2 -> 'a2) -> 'a2 -> (E.S.elt -> 'a1 -> E.S.t -> __ ->
            __ -> 'a2 -> 'a2) -> 'a2

          val fold_rec_nodep :
            (E.S.elt -> 'a1 -> 'a1) -> 'a1 -> E.S.t -> 'a2 -> (E.S.elt -> 'a1
            -> __ -> 'a2 -> 'a2) -> 'a2

          val fold_rec_weak :
            (E.S.elt -> 'a1 -> 'a1) -> 'a1 -> (E.S.t -> E.S.t -> 'a1 -> __ ->
            'a2 -> 'a2) -> 'a2 -> (E.S.elt -> 'a1 -> E.S.t -> __ -> 'a2 ->
            'a2) -> E.S.t -> 'a2

          val fold_rel :
            (E.S.elt -> 'a1 -> 'a1) -> (E.S.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2
            -> E.S.t -> 'a3 -> (E.S.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) ->
            'a3

          val set_induction :
            (E.S.t -> __ -> 'a1) -> (E.S.t -> E.S.t -> 'a1 -> E.S.elt -> __
            -> __ -> 'a1) -> E.S.t -> 'a1

          val set_induction_bis :
            (E.S.t -> E.S.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (E.S.elt -> E.S.t
            -> __ -> 'a1 -> 'a1) -> E.S.t -> 'a1

          val cardinal_inv_2 : E.S.t -> int -> E.S.elt

          val cardinal_inv_2b : E.S.t -> E.S.elt
         end

        val gtb : fin -> fin -> bool

        val leb : fin -> fin -> bool

        val elements_lt : fin -> E.S.t -> fin list

        val elements_ge : fin -> E.S.t -> fin list

        val set_induction_max :
          (E.S.t -> __ -> 'a1) -> (E.S.t -> E.S.t -> 'a1 -> fin -> __ -> __
          -> 'a1) -> E.S.t -> 'a1

        val set_induction_min :
          (E.S.t -> __ -> 'a1) -> (E.S.t -> E.S.t -> 'a1 -> fin -> __ -> __
          -> 'a1) -> E.S.t -> 'a1
       end
     end
   end

  val checkWAXp_reflect : E.S.t -> reflect
 end

module AXpIterativeFinder :
 functor (E_:InputProblem) ->
 functor (Chk:WCXpChecker with module E = E_) ->
 AXpFinder with module E = E_

module CXpIterativeFinderOn :
 functor (E:InputProblem) ->
 functor (Chk:WCXpChecker with module E = E) ->
 sig
  module Xp :
   sig
   end

  val findCXp : E.S.t -> E.S.t

  module XpFacts :
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
            (E.S.elt -> 'a1 -> 'a1) -> 'a1 -> E.S.t -> (E.S.t -> __ -> 'a2)
            -> (E.S.elt -> 'a1 -> E.S.t -> E.S.t -> __ -> __ -> __ -> 'a2 ->
            'a2) -> 'a2

          val fold_rec_bis :
            (E.S.elt -> 'a1 -> 'a1) -> 'a1 -> E.S.t -> (E.S.t -> E.S.t -> 'a1
            -> __ -> 'a2 -> 'a2) -> 'a2 -> (E.S.elt -> 'a1 -> E.S.t -> __ ->
            __ -> 'a2 -> 'a2) -> 'a2

          val fold_rec_nodep :
            (E.S.elt -> 'a1 -> 'a1) -> 'a1 -> E.S.t -> 'a2 -> (E.S.elt -> 'a1
            -> __ -> 'a2 -> 'a2) -> 'a2

          val fold_rec_weak :
            (E.S.elt -> 'a1 -> 'a1) -> 'a1 -> (E.S.t -> E.S.t -> 'a1 -> __ ->
            'a2 -> 'a2) -> 'a2 -> (E.S.elt -> 'a1 -> E.S.t -> __ -> 'a2 ->
            'a2) -> E.S.t -> 'a2

          val fold_rel :
            (E.S.elt -> 'a1 -> 'a1) -> (E.S.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2
            -> E.S.t -> 'a3 -> (E.S.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) ->
            'a3

          val set_induction :
            (E.S.t -> __ -> 'a1) -> (E.S.t -> E.S.t -> 'a1 -> E.S.elt -> __
            -> __ -> 'a1) -> E.S.t -> 'a1

          val set_induction_bis :
            (E.S.t -> E.S.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (E.S.elt -> E.S.t
            -> __ -> 'a1 -> 'a1) -> E.S.t -> 'a1

          val cardinal_inv_2 : E.S.t -> int -> E.S.elt

          val cardinal_inv_2b : E.S.t -> E.S.elt
         end

        val gtb : fin -> fin -> bool

        val leb : fin -> fin -> bool

        val elements_lt : fin -> E.S.t -> fin list

        val elements_ge : fin -> E.S.t -> fin list

        val set_induction_max :
          (E.S.t -> __ -> 'a1) -> (E.S.t -> E.S.t -> 'a1 -> fin -> __ -> __
          -> 'a1) -> E.S.t -> 'a1

        val set_induction_min :
          (E.S.t -> __ -> 'a1) -> (E.S.t -> E.S.t -> 'a1 -> fin -> __ -> __
          -> 'a1) -> E.S.t -> 'a1
       end
     end
   end
 end

module CXpIterativeFinder :
 functor (E_:InputProblem) ->
 functor (Chk:WCXpChecker with module E = E_) ->
 CXpFinder with module E = E_

module type Enumerator =
 sig
  module E :
   InputProblem

  module Xp :
   sig
    type coq_Xp =
    | Coq_isAXp of E.S.t
    | Coq_isCXp of E.S.t
   end

  type s

  val init : s

  val record : Xp.coq_Xp -> s -> s

  val get : s -> Xp.coq_Xp option
 end

module type Iterator =
 sig
  module S :
   FinSet

  type s

  val init : s

  val pick : s -> S.t option

  val block_up : S.t -> s -> s

  val block_down : S.t -> s -> s
 end

module MakeIterator :
 functor (S_:FinSet) ->
 functor (Sat:SatSolver) ->
 Iterator with module S = S_ with type s = S_.elt cnf

module MakeEnumerator :
 functor (E_:InputProblem) ->
 functor (It:Iterator with module S = E_.S) ->
 functor (Chk:WCXpChecker with module E = E_) ->
 functor (FdCXp:CXpFinder with module E = E_) ->
 functor (FdAXp:AXpFinder with module E = E_) ->
 Enumerator with module E = E_ with type s = It.s
