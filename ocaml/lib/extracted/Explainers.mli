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

module AXpIterativeFinderBaseOn :
 functor (E:InputProblem) ->
 functor (Chk:WCXpChecker with module E = E) ->
 sig
  module Xp :
   sig
   end

  val checkWAXp : E.S.t -> bool

  val findAXp : E.S.t -> E.S.t
 end

module AXpIterativeFinderOn :
 functor (E:InputProblem) ->
 functor (Chk:WCXpChecker with module E = E) ->
 sig
  module Xp :
   sig
   end

  val findAXp : E.S.t -> E.S.t
 end

module AXpIterativeFinder :
 functor (E_:InputProblem) ->
 functor (Chk:WCXpChecker with module E = E_) ->
 AXpFinder with module E = E_

module CXpIterativeFinderBaseOn :
 functor (E:InputProblem) ->
 functor (Chk:WCXpChecker with module E = E) ->
 sig
  module Xp :
   sig
   end

  val findCXp : E.S.t -> E.S.t
 end

module CXpIterativeFinderOn :
 functor (E:InputProblem) ->
 functor (Chk:WCXpChecker with module E = E) ->
 sig
  module Xp :
   sig
   end

  val findCXp : E.S.t -> E.S.t
 end

module CXpIterativeFinder :
 functor (E_:InputProblem) ->
 functor (Chk:WCXpChecker with module E = E_) ->
 CXpFinder with module E = E_

module type EnumeratorBase =
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
 functor (Shrink:CXpFinder with module E = E_) ->
 functor (Grow:AXpFinder with module E = E_) ->
 EnumeratorBase with module E = E_
