open Extracted

module MakeSatSolver : Sat.SatSolver

val iter : ('a -> unit) -> ('s -> 'a option) -> ('a -> 's -> 's) -> 's -> int -> unit

