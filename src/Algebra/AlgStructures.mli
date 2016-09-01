open Abbrevs

(* ** Groups *)
module type Group = sig
  type atom
  type t
  val add  : t -> t -> t
  val neg  : t -> t
  val mul  : t -> R.bn -> t
  val one  : t
  val zero : t
  val samp : unit -> t

  val equal : t -> t -> bool

  val atom_from_dlog : R.bn -> atom
  val to_list : t -> atom list
  val from_list : atom list -> t

  val to_string : t -> string
  val of_string : string -> t
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
  val one  : t
  val zero : t
  val is_zero : t -> bool
  val ladd : t list -> t
  val from_int : int -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val use_parens : bool

  val samp     : unit -> t
  val read_str : string -> t
  val write_str: t -> string
end

(* ** Bilinear Groups *)
module type BilinearGroup =
  sig
    val p  : R.bn
    module G1 : Group
    module G2 : Group
    module Gt : Group
    val e  : G1.t -> G2.t -> Gt.t
end
