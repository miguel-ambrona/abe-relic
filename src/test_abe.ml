open Core_kernel.Std
open Abbrevs

let main =
  if Array.length Sys.argv = 1 then
    (Test.test_predEnc (); F.print_flush ();
     Test.test_predEnc_Disjunction (); F.print_flush ();
     Test.test_predEnc_Negation (); F.print_flush ();
     Test.test_predEnc_Conjunction (); F.print_flush ();
     Test.test_predEnc_Dual (); F.print_flush ();
     Test.test_pairEnc ();
    )
  else
    BoolFormsTest.test Sys.argv.(1)
