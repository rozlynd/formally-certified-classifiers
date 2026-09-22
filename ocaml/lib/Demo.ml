open Extracted

open Utils
open Features
open Xp
open Explainers
open DT
open DTXp

let set_of_string_list l =
  List.fold_right StringSet.add l StringSet.empty

let s = set_of_string_list [ "s1" ; "s2" ; "s3" ]

module F : FeatureSig = struct

  let n = 3

  let fs =
    Coq_featureSigCons (2, Coq_isBooleanFeature,
    Coq_featureSigCons (1, Coq_isContinuousFeature,
    Coq_featureSigCons (0, Coq_isStringEnumFeature s,
    Coq_featureSigNil)))

end

module O : Output
  with module K = StringOT
    = struct

  module K = StringOT

end

module Dt = MakeDT (F) (O)

module Input : DTInputProblem with type K.t = string = struct

  let n = F.n

  let fs = F.fs

  module K = O.K

  type t = Dt.t

  let eval = Dt.eval

  let to_fin = to_fin' F.n

  let k =
    Node (to_fin 1, Obj.repr 20.0,
      Node (to_fin 2, Obj.repr (fun e -> List.mem e [ "s1" ; "s2" ]),
        Node (to_fin 1, Obj.repr (-10.0),
          Leaf "1",
          Leaf "0"),
        Leaf "0"),
      Node (to_fin 0, Obj.repr (),
        Node (to_fin 2, Obj.repr (fun e -> List.mem e [ "s1" ]),
          Leaf "1",
          Leaf "0"),
        Leaf "0"))

  let v =
    Coq_featureVecCons (Coq_isBooleanFeature, Obj.repr true, 2,
      (Coq_featureSigCons (1, Coq_isContinuousFeature,
      (Coq_featureSigCons (0, Coq_isStringEnumFeature s,
      Coq_featureSigNil)))),
    Coq_featureVecCons (Coq_isContinuousFeature, Obj.repr 30.0, 1,
      (Coq_featureSigCons (0, Coq_isStringEnumFeature s,
      Coq_featureSigNil)),
    Coq_featureVecCons (Coq_isStringEnumFeature s, Obj.repr "s2", 0,
      Coq_featureSigNil,
    Coq_featureVecNil)))

  module S = MakeFinSet (struct let n = n end)

  (* EXPECTED:
    AXps : [ 2, 3 ]
    CXps : [ 2 ], [ 3 ]
  *)

end

module AXpFind = DtAXpFinder (Input)
module CXpFind = DtCXpFinder (Input)
