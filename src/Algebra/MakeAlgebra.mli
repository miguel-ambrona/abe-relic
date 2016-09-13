open Abbrevs
open AlgStructures
open PolyInterfaces

module Zp : (Field with type t = R.bn)

val make_BilinearGroup : int -> (module BilinearGroup)

module Zp_Poly : (Poly with
                    type var = string and
                    type coeff = Zp.t
                 )
