open MakeAlgebra
open Predicates


(* ** Pair Encodings *)

module type PairEnc_Par = sig
  val par_n1 : int
  val par_n2 : int
  val par_T :  int
end

module P = Zp_Poly
                            
module type PairEnc = sig
  type x
  type y

  val monom_s  : P.monom
  val monom_alpha : P.monom
  val monom_si : P.monom list
  val monom_ri : P.monom list
  val monom_bi : P.monom list

  val param : int
  val encC : x -> P.t list * int
  val encK : y -> P.t list * int
  val pair : x -> y -> (P.Coeffs.t list list) option

  val set_x : generic_attribute -> x
  val set_y : generic_attribute -> y

  val string_of_x : x -> string
  val string_of_y : y -> string
  val x_of_string : string -> x
  val y_of_string : string -> y
end
