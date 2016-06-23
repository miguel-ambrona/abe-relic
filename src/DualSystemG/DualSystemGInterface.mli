open Abbrevs
open AlgStructures

(* ** Dual System Groups *)

module type DualSystemGroup =
  functor (B : BilinearGroup) ->
    sig
      val k : int
(*      val dual_system_pairing : B.G1.t -> B.G2.t -> B.Gt.t*)
      val samp_Dk : int -> R.bn list list * R.bn list
      val sampP   : int -> (B.G1.t list * B.G1.t list list *
                            B.G2.t list * B.G2.t list list) *
                           (R.bn list * R.bn list * R.bn list list list)
      val sampGT  : ?randomness:(R.bn list option) -> B.Gt.t list -> B.Gt.t
      val sampG   : ?randomness:(R.bn list option) -> B.G1.t list * B.G1.t list list * 'a * 'b -> B.G1.t list
      val sampH   : 'a * 'b * B.G2.t list * B.G2.t list list -> B.G2.t list
    end
