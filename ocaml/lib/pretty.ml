open Format

open Extracted
open Utils
open Features
open DT 
open CNF

(* Utils *)

let pp_print_fin n ff k =
  pp_print_int ff (to_nat n k)

let pp_print_finset (type t_) (module S : FinSet with type t = t_) ff (e : S.t) =
  let l = S.elements e in
  let pp_sep ff () = fprintf ff ",@ " in
  fprintf ff "@[{@ %a@ }@]" (pp_print_list ~pp_sep (pp_print_fin S.n)) l

(* Features *)

let pp_print_feature_kind ff = function
  | Coq_isContinuousFeature -> pp_print_string ff "@[[Kind:@ Continuous]@]"
  | Coq_isBooleanFeature -> pp_print_string ff "@[[Kind:@ Boolean]@]"
  | Coq_isStringEnumFeature s -> fprintf ff "@[[Kind:@ Enum:@ @[{%a}@]]@]" (pp_print_list ~pp_sep:(fun ff () -> fprintf ff ",@,") pp_print_string) (StringSet.elements s)

let rec pp_print_feature_sig ff fs =
  match fs with
  | Coq_featureSigNil -> fprintf ff "@[[FSig:@ ]@]"
  | Coq_featureSigCons (_, k, fs) -> fprintf ff "@[[FSig:@ %a%a]@]" pp_print_feature_kind k pp_print_feature_sig_aux fs

and pp_print_feature_sig_aux ff fs =
  match fs with
  | Coq_featureSigNil -> fprintf ff ""
  | Coq_featureSigCons (_, k, fs) -> fprintf ff ",@ %a%a" pp_print_feature_kind k pp_print_feature_sig_aux fs

let pp_print_value kind ff (v : dom) =
  match kind with
  | Coq_isContinuousFeature -> pp_print_float ff (Obj.magic v)
  | Coq_isBooleanFeature -> pp_print_bool ff (Obj.magic v)
  | Coq_isStringEnumFeature _ -> pp_print_string ff (Obj.magic v)

let rec pp_print_feature_vec ff vs =
  match vs with
  | Coq_featureVecNil -> fprintf ff "@[[FVec:@ ]@]"
  | Coq_featureVecCons (k, x, _, _, vs) -> fprintf ff "@[[FVec:@ %a%a]@]" (pp_print_value k) x pp_print_feature_vec_aux vs

and pp_print_feature_vec_aux ff vs =
  match vs with
  | Coq_featureVecNil -> fprintf ff ""
  | Coq_featureVecCons (k, x, _, _, vs) -> fprintf ff ",@ %a%a" (pp_print_value k) x pp_print_feature_vec_aux vs

(* Decision Trees *)

let pp_print_test fs ff (k, ti) =
  let f_kind = getFeatureKind 0 fs k in
  match f_kind with
  | Coq_isContinuousFeature -> fprintf ff "$%a < %a" (pp_print_fin 0) k pp_print_float (Obj.magic ti : float)
  | Coq_isBooleanFeature -> fprintf ff "$%a" (pp_print_fin 0) k
  | Coq_isStringEnumFeature _ -> fprintf ff "$%a \\in @[{@ %a@ }@]" (pp_print_fin 0) k (pp_print_list ~pp_sep:(fun ff () -> fprintf ff ",@ ") pp_print_string) (StringSet.elements (Obj.magic ti : StringSet.t))

let rec _pp_print_dt pp_print_t fs ff t =
  match t with
  | Leaf c -> fprintf ff "@[LEAF@ %a@]" pp_print_t c
  | Node (k, ti, t1, t2) -> fprintf ff "@[NODE@ (%a,@ [%a]@ [%a])@]" (pp_print_test fs) (k, ti) (_pp_print_dt pp_print_t fs) t1 (_pp_print_dt pp_print_t fs) t2

let pp_print_dt pp_print_t fs ff t =
  fprintf ff "@[[DT:@ %a]@]" (_pp_print_dt pp_print_t fs) t

(* CNF *)

let pp_print_literal pp_value ff (v, pol) =
  match pol with
  | Coq_pos -> fprintf ff "@[%a@]" pp_value v
  | Coq_neg -> fprintf ff "@[~ %a@]" pp_value v

let pp_print_clause pp_value =
  pp_print_list ~pp_sep:(fun ff () -> pp_print_string ff " \\/ ") (pp_print_literal pp_value)

let pp_cnf pp_value =
  pp_print_list ~pp_sep:(fun ff () -> pp_print_string ff " /\\ ") (fun ff c -> fprintf ff "@[(@ %a@ )@]" (pp_print_clause pp_value) c)

