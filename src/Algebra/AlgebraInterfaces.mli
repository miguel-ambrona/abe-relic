open Abbrevs

(* ** Groups *)
module type Group = sig
  type t
(*  val k : int*)
  val add  : t -> t -> t
  val neg  : t -> t
  val mul  : t -> R.bn -> t
  val one  : t
  val zero : t
  val samp : unit -> t
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
