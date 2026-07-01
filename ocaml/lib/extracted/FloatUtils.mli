open Datatypes
open PrimFloat

type float_std = Float64.t

module FloatOTF :
 sig
  val compare : float_std -> float_std -> comparison

  val neg_inf : float_std
 end
