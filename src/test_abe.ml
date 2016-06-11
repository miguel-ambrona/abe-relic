open Core_kernel.Std
open Abbrevs

let main =
  if Array.length Sys.argv <> 1 then
    output_string stderr (F.sprintf "usage: %s\n" Sys.argv.(0))
  else
    ABE.test ()
