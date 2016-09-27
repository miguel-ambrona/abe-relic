open Abbrevs
open Util
open DualSystemG
open MakeAlgebra
open BoolForms
open NonMonotonicBF
open Predicates
open ABE
open MakePredEnc

let round int decimals =
  let factor = 10.0**decimals in
  Pervasives.ceil ((factor *. int)) /. factor

let setup_time_slow  = ref 0.0
let enc_time_slow    = ref 0.0
let keygen_time_slow = ref 0.0
let dec_time_slow    = ref 0.0
let setup_time_fast  = ref 0.0
let enc_time_fast    = ref 0.0
let keygen_time_fast = ref 0.0
let dec_time_fast    = ref 0.0
                                         
let run_test ~n ~rep ~repetitions ~counter () =

  let module DSG = Hoeteck's_DSG in
  let module B = (val make_BilinearGroup 2) in

  let module PE = (val make_ArithmeticSpanProgram_PredEnc n rep) in
  let module ABE = PredEncABE (B) (DSG) (PE) in
  
  let attributes = L.map (list_range 1 (1+n)) ~f:(fun i -> Att(i)) in
  
  let rec valid_decryption_key_formula () =
    let key_size = 1 + Rand.int n in
    let key_attributes = random_permutation ~len:key_size attributes in
    let n_leaves = 1 + Rand.int (1+(n/3)) in
    let leaves = random_permutation ~len:n_leaves (list_range 1 (1+n)) in
    let formula = generate_nm_bool_formula leaves in
    if eval_nm_boolean_formula ~attributes:(L.map key_attributes ~f:(function | Att(i) -> i)) formula then
      try let _ = ABE.set_y (NonMonBoolForm(rep, formula)) in key_attributes, formula with
      | _ -> valid_decryption_key_formula ()
    else valid_decryption_key_formula ()
  in
  
  let key_attributes, formula = valid_decryption_key_formula () in
  
  for i = 1 to 2 do

    let module PE =
      (val (if i = 1 then make_ArithmeticSpanProgram_PredEnc n rep
            else make_Fast_ArithmeticSpanProgram_PredEnc n rep)
      )
    in
    let module ABE = PredEncABE (B) (DSG) (PE) in

    (if counter = 1 then
       ( setup_time_slow := 0.0;
         enc_time_slow   := 0.0;
         keygen_time_slow:= 0.0;
         dec_time_slow   := 0.0;
         setup_time_fast := 0.0;
         enc_time_fast   := 0.0;
         keygen_time_fast:= 0.0;
         dec_time_fast   := 0.0;
       )
     else ()
    );
      
    let time1 = Unix.gettimeofday() in
    let mpk, msk = ABE.setup () in
    
    let time2 = Unix.gettimeofday() in
    let x = ABE.set_x (BoolForm_Attrs(n, rep, key_attributes)) in
    let msg = ABE.rand_msg () in
    let ct_x = ABE.enc mpk x msg in
    
    let time3 = Unix.gettimeofday() in
    let y = ABE.set_y (NonMonBoolForm(rep, formula)) in
    let sk_y = ABE.keyGen mpk msk y in
    
    let time4 = Unix.gettimeofday() in
    let msg' = ABE.dec mpk sk_y ct_x in
    
    let time5 = Unix.gettimeofday() in
    
    assert (B.Gt.equal msg msg');

    
    if i = 1 then
      (setup_time_slow  := !setup_time_slow  +. ((time2 -. time1) /. (I.to_float repetitions));
       enc_time_slow    := !enc_time_slow    +. ((time3 -. time2) /. (I.to_float repetitions));
       keygen_time_slow := !keygen_time_slow +. ((time4 -. time3) /. (I.to_float repetitions));
       dec_time_slow    := !dec_time_slow    +. ((time5 -. time4) /. (I.to_float repetitions));
       if counter = repetitions then
         (F.printf "Slow\t%d Setup:%Fs Enc:%Fs KeyGen:%Fs Dec:%Fs\n"
                   n
                   (Pervasives.ceil ((100.0 *. !setup_time_slow )) /. 100.0)
                   (Pervasives.ceil ((100.0 *. !enc_time_slow   )) /. 100.0)
                   (Pervasives.ceil ((100.0 *. !keygen_time_slow)) /. 100.0)
                   (Pervasives.ceil ((100.0 *. !dec_time_slow   )) /. 100.0);
          F.print_flush ()
         )
      )
    else
      (setup_time_fast  := !setup_time_fast  +. ((time2 -. time1) /. (I.to_float repetitions));
       enc_time_fast    := !enc_time_fast    +. ((time3 -. time2) /. (I.to_float repetitions));
       keygen_time_fast := !keygen_time_fast +. ((time4 -. time3) /. (I.to_float repetitions));
       dec_time_fast    := !dec_time_fast    +. ((time5 -. time4) /. (I.to_float repetitions));
       if counter = repetitions then
         (F.printf "Fast\t%d Setup:%Fs Enc:%Fs KeyGen:%Fs Dec:%Fs\n"
                   n
                   (Pervasives.ceil ((100.0 *. !setup_time_fast )) /. 100.0)
                   (Pervasives.ceil ((100.0 *. !enc_time_fast   )) /. 100.0)
                   (Pervasives.ceil ((100.0 *. !keygen_time_fast)) /. 100.0)
                   (Pervasives.ceil ((100.0 *. !dec_time_fast   )) /. 100.0);
          F.print_flush ()
         )
      )
  done;
  ()

let test () =
  (for n = 1 to 100 do
     let repetitions = 20 in
     for counter = 1 to repetitions do
       run_test ~n:(2*n) ~rep:10 ~repetitions ~counter()       
     done;
   done)
