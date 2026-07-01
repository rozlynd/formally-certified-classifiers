open Datatypes
open PrimFloat

type float_std = Float64.t

module FloatOTF =
 struct
  (** val compare : float_std -> float_std -> comparison **)

  let compare x y =
    if leb x y then if leb y x then Eq else Lt else Gt

  (** val neg_inf : float_std **)

  let neg_inf =
    neg_infinity
 end
