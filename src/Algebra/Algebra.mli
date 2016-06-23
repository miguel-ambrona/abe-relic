(* ** Imports *)
open Abbrevs
open AlgebraInterfaces

module Zp : (Field with type t = R.bn)
module G1 : (Group with type atom = R.g1 and type t = R.g1 list)
module G2 : (Group with type atom = R.g2 and type t = R.g2 list)
module Gt : (Group with type t = R.gt)
module B : BilinearGroup
