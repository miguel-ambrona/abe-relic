open Core_kernel.Std
open Abbrevs

let main =
  if Array.length Sys.argv = 1 then
    (ABE.test_predEnc (); F.print_flush ();
     ABE.test_pairEnc ();
    )
  else
    BoolFormsTest.test Sys.argv.(1)
