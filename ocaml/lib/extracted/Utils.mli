open Basics
open Datatypes
open List0
open MSetInterface
open MSetList
open MSetProperties
open Orders
open OrdersEx
open PeanoNat

type __ = Obj.t

module StringOT :
 UsualOrderedType with type t = string

module StringSet :
 Sets with module E = StringOT

type string_enum = string

type 'a nelist =
| Coq_necons of 'a * 'a list

val nemap : ('a1 -> 'a2) -> 'a1 nelist -> 'a2 nelist

type fin =
| F1 of int
| FS of int * fin

val to_nat : int -> fin -> int

val to_fin : int -> int -> fin option

val to_fin' : int -> int -> fin

module type FinSig =
 sig
  val n : int
 end

module FinOT :
 functor (S:FinSig) ->
 UsualOrderedType with type t = fin

module type FinSet =
 sig
  val n : int

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
 end

module MakeFinSetOn :
 functor (S:FinSig) ->
 sig
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
 end

module MakeFinSet :
 functor (S:FinSig) ->
 FinSet

module FinSetProperties :
 functor (FS:FinSet) ->
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

      val coq_In_dec : FS.elt -> FS.t -> bool

      val of_list : FS.elt list -> FS.t

      val to_list : FS.t -> FS.elt list

      val fold_rec :
        (FS.elt -> 'a1 -> 'a1) -> 'a1 -> FS.t -> (FS.t -> __ -> 'a2) ->
        (FS.elt -> 'a1 -> FS.t -> FS.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

      val fold_rec_bis :
        (FS.elt -> 'a1 -> 'a1) -> 'a1 -> FS.t -> (FS.t -> FS.t -> 'a1 -> __
        -> 'a2 -> 'a2) -> 'a2 -> (FS.elt -> 'a1 -> FS.t -> __ -> __ -> 'a2 ->
        'a2) -> 'a2

      val fold_rec_nodep :
        (FS.elt -> 'a1 -> 'a1) -> 'a1 -> FS.t -> 'a2 -> (FS.elt -> 'a1 -> __
        -> 'a2 -> 'a2) -> 'a2

      val fold_rec_weak :
        (FS.elt -> 'a1 -> 'a1) -> 'a1 -> (FS.t -> FS.t -> 'a1 -> __ -> 'a2 ->
        'a2) -> 'a2 -> (FS.elt -> 'a1 -> FS.t -> __ -> 'a2 -> 'a2) -> FS.t ->
        'a2

      val fold_rel :
        (FS.elt -> 'a1 -> 'a1) -> (FS.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
        FS.t -> 'a3 -> (FS.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val set_induction :
        (FS.t -> __ -> 'a1) -> (FS.t -> FS.t -> 'a1 -> FS.elt -> __ -> __ ->
        'a1) -> FS.t -> 'a1

      val set_induction_bis :
        (FS.t -> FS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (FS.elt -> FS.t -> __ ->
        'a1 -> 'a1) -> FS.t -> 'a1

      val cardinal_inv_2 : FS.t -> int -> FS.elt

      val cardinal_inv_2b : FS.t -> FS.elt
     end

    val gtb : fin -> fin -> bool

    val leb : fin -> fin -> bool

    val elements_lt : fin -> FS.t -> fin list

    val elements_ge : fin -> FS.t -> fin list

    val set_induction_max :
      (FS.t -> __ -> 'a1) -> (FS.t -> FS.t -> 'a1 -> fin -> __ -> __ -> 'a1)
      -> FS.t -> 'a1

    val set_induction_min :
      (FS.t -> __ -> 'a1) -> (FS.t -> FS.t -> 'a1 -> fin -> __ -> __ -> 'a1)
      -> FS.t -> 'a1
   end
 end
