open Abbrevs
open AlgStructures

module Zp : (Field with type t = R.bn)
val make_BilinearGroup : int -> (module BilinearGroup)
