open Basics
open Datatypes
open List0
open MSetInterface
open MSetList
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
