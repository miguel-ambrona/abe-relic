(* Predicate Encodings as defined in
  "Improved Dual System ABE in Prime-Order Groups via Predicate Encodings"
   Jie Chen, Romain Gay and Hoeteck Wee at IACR-EUROCRYPT-2015.
 *)

open AlgStructures
open MakeAlgebra
open Predicates
       
module type PredEnc =
  functor (B : BilinearGroup) ->
    sig
      type x
      type y
      val n : int

      val sE : x -> B.G1.t list -> B.G1.t list
      val rE : y -> B.G2.t list -> B.G2.t list
      val kE : y -> B.G2.t -> B.G2.t list
      val sD : x -> y -> B.G1.t list -> B.G1.t
      val rD : x -> y -> B.G2.t list -> B.G2.t

      val set_x : generic_attribute -> x
      val set_y : generic_attribute -> y

      val string_of_x : x -> string
      val string_of_y : y -> string
      val x_of_string : string -> x
      val y_of_string : string -> y
    end

module type PredEnc_Characterization = sig
  type x
  type y
  val predicate : x -> y -> bool
    
  val s : int
  val r : int
  val w : int

  val sE_matrix : x -> Zp.t list list
  val rE_matrix : y -> Zp.t list list
  val kE_vector : y -> Zp.t list
  val sD_vector : x -> y -> Zp.t list
  val rD_vector : x -> y -> Zp.t list

  val get_witness : x -> y -> Zp.t list
    
  val set_x : generic_attribute -> x
  val set_y : generic_attribute -> y
    
  val string_of_x : x -> string
  val string_of_y : y -> string
  val x_of_string : string -> x
  val y_of_string : string -> y
end
