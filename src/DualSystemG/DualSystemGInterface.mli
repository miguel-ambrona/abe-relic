open Algebra
module R = Relic

(* ** Dual System Groups *)

module type DualSystemGroup = sig
  val k : int
  val dual_system_pairing : G1.t -> G2.t -> R.gt
  val samp_Dk : int -> R.bn list list * R.bn list
  val sampP   : int -> (R.g1 list list * R.g1 list list list * R.g2 list list * R.g2 list list list)
                      * (R.bn list * R.bn list * R.bn list list list)
  val sampGT  : ?randomness:(R.bn list option) -> R.gt list -> R.gt
  val sampG   : ?randomness:(R.bn list option) -> G1.t list * G1.t list list * 'a * 'b -> G1.t list
  val sampH   : 'a * 'b * G2.t list * G2.t list list -> G2.t list
end
