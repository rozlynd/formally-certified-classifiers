open CNF
open Utils

module type SatSolver =
 sig
  type ans =
  | SAT of fin assignment
  | UNSAT

  val solve : int -> fin cnf -> ans
 end
