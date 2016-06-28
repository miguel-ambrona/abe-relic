open Abbrevs
open AlgStructures

(* ** Dual System Groups *)

module type DualSystemGroup =
  functor (B : BilinearGroup) ->
    sig
      type pp
      type sp
      type img_mu
      val sampP   : int -> (B.G2.t -> img_mu) * (pp * sp)
      val sampGT  : ?randomness:(R.bn list option) -> img_mu -> B.Gt.t
      val sampG   : ?randomness:(R.bn list option) -> pp -> B.G1.t list
      val sampH   : ?randomness:(R.bn list option) -> pp -> B.G2.t list

      val string_of_pp     : pp -> string
      val string_of_img_mu : img_mu -> string
      val pp_of_string     : string -> pp
      val img_mu_of_string : string -> img_mu
    end
