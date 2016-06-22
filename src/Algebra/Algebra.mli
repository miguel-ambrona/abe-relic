(* ** Imports *)
open Abbrevs
open AlgebraInterfaces

module Zp : (Field with type t = R.bn)
module G1 : (Group with type t = R.g1 list)
module G2 : (Group with type t = R.g2 list)
