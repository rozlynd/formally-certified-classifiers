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

module MakeIterator =
 functor (S_:FinSet) ->
 functor (Sat:SatSolver) ->
 struct
  module S = S_

  type s = S.elt cnf

  (** val init : S.elt cnf **)

  let init =
    []

  (** val pick : S.elt cnf -> S.t option **)

  let pick c =
    match Sat.solve S.n c with
    | Sat.SAT i -> Some (S.init i)
    | Sat.UNSAT -> None

  (** val clause_block : polarity -> S.t -> S.elt clause **)

  let clause_block p x =
    map (fun x0 -> (x0, p)) (S.elements x)

  (** val block_up : S.t -> S.elt cnf -> S.elt clause list **)

  let block_up x c =
    (clause_block Coq_neg x) :: c

  (** val block_down : S.t -> S.elt cnf -> S.elt clause list **)

  let block_down x c =
    (clause_block Coq_pos (S.compl x)) :: c

  (** val pick_block_up : __ **)

  let pick_block_up =
    __

  (** val pick_block_down : __ **)

  let pick_block_down =
    __
 end

module MakeEnumerator =
 functor (E_:InputProblem) ->
 functor (It:Iterator with module S = E_.S) ->
 functor (Chk:WCXpChecker with module E = E_) ->
 functor (Shrink:CXpFinder with module E = E_) ->
 functor (Grow:AXpFinder with module E = E_) ->
 struct
  module E = E_

  module Xp = EnumeratorsDefs(E)

  type s = It.s

  (** val init : It.s **)

  let init =
    It.init

  (** val record : Xp.coq_Xp -> s -> It.s **)

  let record x st =
    match x with
    | Xp.Coq_isAXp x0 -> It.block_up x0 st
    | Xp.Coq_isCXp x0 -> It.block_down x0 st

  (** val get : s -> Xp.coq_Xp option **)

  let get st =
    match It.pick st with
    | Some x ->
      if Chk.checkWCXp x
      then Some (Xp.Coq_isCXp (Shrink.findCXp x))
      else Some (Xp.Coq_isAXp (Grow.findAXp (E_.S.compl x)))
    | None -> None
 end
