open Bool
open Datatypes
open Equalities
open Features
open Utils
open Xp

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module ExplainersDefs =
 functor (E:InputProblem) ->
 struct
 end

module EnumeratorsDefs =
 functor (E:InputProblem) ->
 struct
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

module AXpIterativeFinderBaseOn =
 functor (E:InputProblem) ->
 functor (Chk:WCXpChecker with module E = E) ->
 struct
  module Xp = ExplainersDefs(E)

  (** val checkWAXp : E.S.t -> bool **)

  let checkWAXp x =
    negb (Chk.checkWCXp (E.S.compl x))

  (** val findAXp : E.S.t -> E.S.t **)

  let findAXp =
    E.S.shrink checkWAXp
 end

module AXpIterativeFinderOn =
 functor (E:InputProblem) ->
 functor (Chk:WCXpChecker with module E = E) ->
 struct
  module Impl = AXpIterativeFinderBaseOn(E)(Chk)

  module Xp = Impl.Xp

  (** val checkWAXp : E.S.t -> bool **)

  let checkWAXp x =
    negb (Chk.checkWCXp (E.S.compl x))

  (** val findAXp : E.S.t -> E.S.t **)

  let findAXp =
    E.S.shrink checkWAXp

  (** val findAXpSound : __ **)

  let findAXpSound =
    __

  (** val findAXpSane : __ **)

  let findAXpSane =
    __
 end

module AXpIterativeFinder =
 functor (E_:InputProblem) ->
 functor (Chk:WCXpChecker with module E = E_) ->
 struct
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

module CXpIterativeFinderBaseOn =
 functor (E:InputProblem) ->
 functor (Chk:WCXpChecker with module E = E) ->
 struct
  module Xp = ExplainersDefs(E)

  (** val findCXp : E.S.t -> E.S.t **)

  let findCXp =
    E.S.shrink Chk.checkWCXp
 end

module CXpIterativeFinderOn =
 functor (E:InputProblem) ->
 functor (Chk:WCXpChecker with module E = E) ->
 struct
  module Impl = CXpIterativeFinderBaseOn(E)(Chk)

  module Xp = Impl.Xp

  (** val findCXp : E.S.t -> E.S.t **)

  let findCXp =
    E.S.shrink Chk.checkWCXp

  (** val findCXpSound : __ **)

  let findCXpSound =
    __

  (** val findCXpSane : __ **)

  let findCXpSane =
    __
 end

module CXpIterativeFinder =
 functor (E_:InputProblem) ->
 functor (Chk:WCXpChecker with module E = E_) ->
 struct
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

module DummyExplainer =
 functor (E_:InputProblem) ->
 struct
  module Xp = EnumeratorsDefs(E_)

  module E = E_

  type s = unit

  (** val init : unit **)

  let init =
    ()

  (** val record : Xp.coq_Xp -> s -> s **)

  let record _ =
    Obj.magic id

  (** val get : s -> Xp.coq_Xp option **)

  let get _ =
    Some (Xp.Coq_isAXp E.S.all)
 end
