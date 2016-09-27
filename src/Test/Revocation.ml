open Abbrevs
open DualSystemG
open MakeAlgebra
open Predicates
open ABE
open PredEncTransformations
open MakePredEncChar

let round int decimals =
  let factor = 10.0**decimals in
  Pervasives.ceil ((factor *. int)) /. factor

let run_test ~t ~t' () =

  let module DSG = Hoeteck's_DSG in
  let module B = (val make_BilinearGroup 2) in

  let module C = (val make_BroadcastEnc_Characterization t t') in
  let module PE = PredEnc_from_Characterization (C) in
  let module ABE = PredEncABE (B) (DSG) (PE) in

  let rep = 5 in
  let setup_time  = ref 0.0 in
  let enc_time    = ref 0.0 in
  let keygen_time = ref 0.0 in
  let dec_time    = ref 0.0 in

  for _ = 1 to rep do
    let time1 = Unix.gettimeofday() in
    let mpk, msk = ABE.setup () in

    let time2 = Unix.gettimeofday() in
    let x = ABE.set_x (BroadcastEncVector(t,t', true :: (Util.mk_list false (t*t'-1)) )) in
    let msg = ABE.rand_msg () in
    let ct_x = ABE.enc mpk x msg in

    let time3 = Unix.gettimeofday() in
    let id = 0 in
    let y = ABE.set_y (BroadcastEncIndex(t,t', (id/t,id mod t))) in
    let sk_y = ABE.keyGen mpk msk y in

    let time4 = Unix.gettimeofday() in
    let msg' = ABE.dec mpk sk_y ct_x in

    let time5 = Unix.gettimeofday() in

    assert (B.Gt.equal msg msg');

    setup_time  := !setup_time  +. ((time2 -. time1) /. (I.to_float rep));
    enc_time    := !enc_time    +. ((time3 -. time2) /. (I.to_float rep));
    keygen_time := !keygen_time +. ((time4 -. time3) /. (I.to_float rep));
    dec_time    := !dec_time    +. ((time5 -. time4) /. (I.to_float rep));
    ()
  done;

  F.printf "%dx%d = %d\t Setup: %Fs\t Enc: %Fs\t KeyGen: %Fs\t Dec: %Fs\n"
           t t' (t*t')
           (Pervasives.ceil ((100.0 *. !setup_time )) /. 100.0)
           (Pervasives.ceil ((100.0 *. !enc_time   )) /. 100.0)
           (Pervasives.ceil ((100.0 *. !keygen_time)) /. 100.0)
           (Pervasives.ceil ((100.0 *. !dec_time   )) /. 100.0);
  F.print_flush ()

let test () =
  (for n = 1 to 200 do
     run_test ~t:n ~t':n ()
   done)
