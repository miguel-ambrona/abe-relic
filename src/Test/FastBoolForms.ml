open Abbrevs
open Util
open DualSystemG
open MakeAlgebra
open BoolForms
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

let run_test ~n ~and_gates ~repetitions ~counter () =

  let module DSG = Hoeteck's_DSG in
  let module B = (val make_BilinearGroup 2) in

  let attributes = L.map (list_range 1 (1+n)) ~f:(fun i -> Att(i)) in

  let rec valid_decryption_key_formula () =
    let key_size = 1 + Rand.int n in
    let key_attributes = random_permutation ~len:key_size attributes in
    let n_leaves = 1 + Rand.int n in
    let formula = generate_bool_formula ~and_gates ~leaf_nodes:n_leaves ~rep:1 attributes in
    if eval_boolean_formula ~attributes:key_attributes formula then key_attributes, formula
    else valid_decryption_key_formula ()
  in

  let rec reverse_formula = function
    | Or (f1,f2)  -> And(reverse_formula f1, reverse_formula f2)
    | And (f1,f2) -> Or(reverse_formula f1, reverse_formula f2)
    | Leaf (a)    -> Leaf (a)
  in

  let key_attributes, formula = valid_decryption_key_formula () in

  for i = 1 to 2 do

    let module PE =
      (val (if i = 1 then make_BF_PredEnc (n+and_gates+1)
            else make_Fast_BF_PredEnc n)
      )
    in

    let key_attributes, formula =
      if i = 1 then key_attributes, formula
      else
        L.filter attributes ~f:(fun a -> not (L.mem key_attributes a)),
        reverse_formula formula
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
    let x = ABE.set_x (BoolForm_Policy(n, 1, and_gates, formula)) in
    let msg = ABE.rand_msg () in
    let ct_x = ABE.enc mpk x msg in

    let time3 = Unix.gettimeofday() in
    let y = ABE.set_y (BoolForm_Attrs(n, 1, key_attributes)) in
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
                   n !setup_time_slow !enc_time_slow !keygen_time_slow !dec_time_slow;
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
                   n !setup_time_fast !enc_time_fast !keygen_time_fast !dec_time_fast;
          F.print_flush ()
         )
      )
  done;
  ()

let test () =
  (for n = 1 to 100 do
     let repetitions = 70 in
     for counter = 1 to repetitions do
       run_test ~n:n ~and_gates:n ~repetitions ~counter()
     done;
   done)
