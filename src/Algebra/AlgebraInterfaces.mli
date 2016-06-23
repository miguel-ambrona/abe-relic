open Abbrevs

(* ** Groups *)
module type Group = sig
  type atom
  val atom_gen : atom
  val atom_add : atom -> atom -> atom
  val atom_mul : atom -> R.bn -> atom

  type t
  val add  : t -> t -> t
  val neg  : t -> t
  val mul  : t -> R.bn -> t
  val one  : t
  val zero : t
  val samp : unit -> t

  val equal : t -> t -> bool

  val to_list : t -> atom list
  val from_list : atom list -> t
end

(* ** Fields *)
module type Field = sig
  type t
  val pp : F.formatter -> t -> unit
  val add : t -> t -> t
  val neg : t -> t
  val mul : t -> t -> t
  val inv : t -> t
  val ring_exp : t -> int -> t
  val one : t
  val zero : t
  val is_zero : t -> bool
  val ladd : t list -> t
  val from_int : int -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val use_parens : bool

  val samp     : unit -> t
  val read_str : string -> t
end

(* ** Bilinear Group *)
module type BilinearGroup =
  sig
    val p  : R.bn
    module G1 : Group 
    module G2 : Group
    module Gt : Group
    val e  : G1.t -> G2.t -> Gt.t
end
