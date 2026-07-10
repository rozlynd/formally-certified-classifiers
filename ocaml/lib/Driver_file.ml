open Dttxt.Parse_file
open Dttxt.Parsing_utils

open Extracted.Utils
open Extracted.Features
open Extracted.Xp
open Extracted.Explainers
open Extracted.DT
open Extracted.DTXp

open Convert_data




let set_of_string_list l =
  List.fold_right StringSet.add l StringSet.empty


module type Data = sig
  val nb_features : int
  val features : parsed_features
  val parsed_tree : parsed_tree
  val parsed_vectors : parsed_vectors
end

module type FeatureTreeData = sig
  val nb_features : int
  val parsed_features : parsed_features
  val parsed_tree : parsed_tree
end

module type VectorData = sig
  val parsed_vector : parsed_vector
end

module type FileNameModule = sig
  val filename : string
end


module MakeData = functor (F:FileNameModule) -> struct
  let fs, t, vs = Dttxt.Parse_file.read_file F.filename
  let nb_features = List.length fs
  let features = fs
  let parsed_tree = t
  let parsed_vectors = vs
end

module MakeFeatureTreeData (D:Data) = struct
  let nb_features = D.nb_features
  let parsed_features = D.features
  let parsed_tree = D.parsed_tree
end



module MakeDTInputProblem (FTD:FeatureTreeData) (VD:VectorData) : DTInputProblem with module K = StringOT =
 
 struct

  let v_, fs_ = vector_and_features_from_parsing VD.parsed_vector FTD.parsed_features
  
  module F : FeatureSig = struct
    let n = FTD.nb_features
    let fs = fs_
  end

  module O : Output with module K = StringOT = struct
    module K = StringOT
  end

  module Dt = MakeDT (F) (O)
  
  let n = F.n

  let fs = F.fs

  module K = O.K

  type t = Dt.t

  let eval = Dt.eval

  let to_fin = to_fin' n

  let k = tree_from_parsing to_fin FTD.parsed_tree

  let v = v_

  module S = MakeFinSet (struct let n = n end)
end











(* 
module MakeDTInputProblem (Data:Data) : DTInputProblem with module K = StringOT =
 
 struct

  let v_, fs_ = vector_and_features_from_parsing Data.parsed_vector Data.features
  
  module F : FeatureSig = struct
    let n = Data.nb_features
    let fs = fs_
  end

  module O : Output with module K = StringOT = struct
    module K = StringOT
  end

  module Dt = MakeDT (F) (O)
  
  let n = F.n

  let fs = F.fs

  module K = O.K

  type t = Dt.t

  let eval = Dt.eval

  let to_fin = to_fin' n

  let k = tree_from_parsing to_fin Data.parsed_tree

  let v = v_

  module S = MakeFinSet (struct let n = n end)
end 
*)

