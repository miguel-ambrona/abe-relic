open Core_kernel.Std
open Abbrevs

let main =
  if Array.length Sys.argv = 1 then
    (
     Test.test_predEnc (); F.print_flush ();
     Test.test_Fast_BF_predEnc (); F.print_flush ();
     Test.test_ArithmeticSpanProgram (); F.print_flush ();
     Test.test_Fast_ArithmeticSpanProgram (); F.print_flush ();
     Test.test_predEnc_Broadcast (); F.print_flush ();
     Test.test_predEnc_ZIP (); F.print_flush ();
     Test.test_predEnc_shareRoot (); F.print_flush ();
     Test.test_predEnc_Disjunction (); F.print_flush ();
     Test.test_predEnc_Negation (); F.print_flush ();
     Test.test_predEnc_Revocation (); F.print_flush ();
     Test.test_predEnc_Conjunction (); F.print_flush ();
     Test.test_predEnc_Dual (); F.print_flush ();
     Test.test_pairEnc ();
    )
  else
    match Sys.argv.(1) with
    | "revocation" -> Revocation.test ()
    | "ASP" -> ArithmeticSpanP.test ()
    | _ -> BoolFormsTest.test Sys.argv.(1)

    (*for n = 10 to 10000 do
      (if n % 5 = 0 then
         BoolFormsTest.bigPredEnc_test n
       else ()
      );
    done
     *)
