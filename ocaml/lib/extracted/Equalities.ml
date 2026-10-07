
module type DecidableType =
 sig
  type t

  val eq_dec : t -> t -> bool
 end

module type UsualDecidableType =
 sig
  type t

  val eq_dec : t -> t -> bool
 end
