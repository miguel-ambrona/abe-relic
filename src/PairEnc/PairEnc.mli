(* Pair Encodings as defined in
  "A study of Pair Encodings: Predicate Encryption in Prime order Groups"
   Shashank Agrawal and Melissa Chase at TCC-2015.
 *)

open MakeAlgebra
open Predicates

module type PairEnc_Par = sig
  val par_n1 : int
  val par_n2 : int
  val par_T :  int
end

module type PairEnc = sig
  type x
  type y

  val monom_s  : Zp_Poly.monom
  val monom_alpha : Zp_Poly.monom
  val monom_si : Zp_Poly.monom list
  val monom_ri : Zp_Poly.monom list
  val monom_bi : Zp_Poly.monom list

  val param : int
  val encC : x -> Zp_Poly.t list * int
  val encK : y -> Zp_Poly.t list * int
  val pair : x -> y -> (Zp_Poly.Coeffs.t list list) option

  val set_x : generic_attribute -> x
  val set_y : generic_attribute -> y

  val string_of_x : x -> string
  val string_of_y : y -> string
  val x_of_string : string -> x
  val y_of_string : string -> y
end
