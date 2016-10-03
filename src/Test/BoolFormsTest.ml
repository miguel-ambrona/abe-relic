open Abbrevs
open Util
open BoolForms
open DualSystemG
open MakeAlgebra
open ABE
open Printf
open MakePredEnc
open MakePairEnc

let round int decimals =
  let factor = 10.0**decimals in
  Pervasives.ceil ((factor *. int)) /. factor

let run_test ~n_attributes ~and_gates ~rep ~max_leaf_nodes () =

  let attributes = L.map (list_range 1 (1+n_attributes)) ~f:(fun i -> Att(i)) in

  let module DSG = Hoeteck's_DSG in
  let module B = (val make_BilinearGroup 2) in

  let module PE1 = (val make_BF_PredEnc (n_attributes * rep + and_gates + 1)) in
  let module ABE1 = PredEncABE (B) (DSG) (PE1) in

  let module PE2 = (val make_BF_PairEnc max_leaf_nodes and_gates n_attributes) in
  let module ABE2 = PairEncABE (B) (DSG) (PE2) in

  let rec _valid_decryption_key_policy () =
    let key_size = 1 + Rand.int n_attributes in
    let key_attributes = random_permutation ~len:key_size attributes in
    let leaf_nodes = 1 + (Rand.int max_leaf_nodes) in
    let policy = generate_bool_formula ~and_gates ~leaf_nodes ~rep attributes in
    if eval_boolean_formula ~attributes:key_attributes policy then key_attributes, policy
    else _valid_decryption_key_policy ()
  in

  let all_and_formula =
    L.fold_left (L.tl_exn attributes)
      ~init:(Leaf (L.hd_exn attributes))
      ~f:(fun f a -> And(f, Leaf a))
  in
  let key_attributes, policy = attributes, all_and_formula in
  F.printf "Policy -> %s. Key -> [%a]\n"
           (string_of_boolean_formula policy) (pp_list ", " pp_attribute) key_attributes;

  (* ** Predicate-Encodings *)

  empty_references ();
  let t1 = Unix.gettimeofday() in
  let mpk, msk = ABE1.setup () in
  let t2 = Unix.gettimeofday() in

  F.printf "(PredEnc)\nSetup:\tTime:%Fs " (round (t2 -. t1) 3.0);
  print_references();

  empty_references ();
  let t1 = Unix.gettimeofday() in
  let xM  = ABE1.set_x (Predicates.BoolForm_Policy(n_attributes, rep, and_gates, policy)) in
  let msg = ABE1.rand_msg () in
  let ct_x = ABE1.enc mpk xM msg in
  let t2 = Unix.gettimeofday() in

  F.printf "Enc:\tTime:%Fs " (round (t2 -. t1) 3.0);
  print_references();

  empty_references ();
  let t1 = Unix.gettimeofday() in
  let y =  ABE1.set_y (Predicates.BoolForm_Attrs(n_attributes, rep, key_attributes)) in
  let sk_y = ABE1.keyGen mpk msk y in
  let t2 = Unix.gettimeofday() in

  F.printf "KeyGen:\tTime:%Fs " (round (t2 -. t1) 3.0);
  print_references();

  empty_references ();
  let t1 = Unix.gettimeofday() in
  let msg' = ABE1.dec mpk sk_y ct_x in
  let t2 = Unix.gettimeofday() in

  F.printf "Dec:\tTime:%Fs " (round (t2 -. t1) 3.0);
  print_references();

  assert (B.Gt.equal msg msg');

  (* ** Pair-Encodings *)

  empty_references ();
  let t1 = Unix.gettimeofday() in
  let mpk, msk = ABE2.setup () in
  let t2 = Unix.gettimeofday() in

  F.printf "(PairEnc)\nSetup:\tTime:%Fs " (round (t2 -. t1) 3.0);
  print_references();

  empty_references ();
  let t1 = Unix.gettimeofday() in
  let xM  = ABE2.set_x (Predicates.BoolForm_Policy(max_leaf_nodes, and_gates+1, 0, policy)) in
  let msg = ABE2.rand_msg () in
  let ct_x = ABE2.enc mpk xM msg in
  let t2 = Unix.gettimeofday() in

  F.printf "Enc:\tTime:%Fs " (round (t2 -. t1) 3.0);
  print_references();

  empty_references ();
  let t1 = Unix.gettimeofday() in
  let y =  ABE2.set_y (Predicates.BoolForm_Attrs(0, 0, key_attributes)) in
  let sk_y = ABE2.keyGen mpk msk y in
  let t2 = Unix.gettimeofday() in

  F.printf "KeyGen:\tTime:%Fs " (round (t2 -. t1) 3.0);
  print_references();

  empty_references ();
  let t1 = Unix.gettimeofday() in
  let msg' = ABE2.dec mpk sk_y ct_x in
  let t2 = Unix.gettimeofday() in

  F.printf "Dec:\tTime:%Fs " (round (t2 -. t1) 3.0);
  print_references();

  assert (B.Gt.equal msg msg');
  ()


let predEnc_test  ~out_file ~setup_file ~keygen_file ~enc_file ~dec_file ~n_attributes ~and_gates ~rep ~max_leaf_nodes () =

  let attributes = L.map (list_range 1 (1+n_attributes)) ~f:(fun i -> Att(i)) in

  let module DSG = Hoeteck's_DSG in
  let module B = (val make_BilinearGroup 2) in
  let module PE = (val make_BF_PredEnc (n_attributes * rep + and_gates + 1)) in
  let module ABE = PredEncABE (B) (DSG) (PE) in

  let key_size = 1 + Rand.int n_attributes in
  let key_attributes = random_permutation ~len:key_size attributes in
  let leaf_nodes = 1 + (Rand.int max_leaf_nodes) in
  let policy = generate_bool_formula ~and_gates ~leaf_nodes ~rep attributes in
  let sat = eval_boolean_formula ~attributes:key_attributes policy in

  F.printf "Policy -> %s.  Key -> [%a]. Valid key: %b\n"
    (string_of_boolean_formula policy) (pp_list ", " pp_attribute) key_attributes sat;

  (* ** Predicate-Encodings *)

  let t1 = Unix.gettimeofday() in
  let mpk, msk = ABE.setup () in

  let t2 = Unix.gettimeofday() in
  let xM  = ABE.set_x (Predicates.BoolForm_Policy(n_attributes, rep, and_gates, policy)) in
  let msg = ABE.rand_msg () in
  let ct_x = ABE.enc mpk xM msg in

  let t3 = Unix.gettimeofday() in
  let y =  ABE.set_y (Predicates.BoolForm_Attrs(n_attributes, rep, key_attributes)) in
  let sk_y = ABE.keyGen mpk msk y in

  let t4 = Unix.gettimeofday() in
  let msg' = ABE.dec mpk sk_y ct_x in

  let t5 = Unix.gettimeofday() in

  (if sat then assert (B.Gt.equal msg msg') else assert (not (B.Gt.equal msg msg')));

  F.printf "(PredEnc) Setup: %F s. KeyGen: %F s. Encryption: %F s. Decryption: %F s.\n"
    (round (t2 -. t1) 3.0) (round (t4 -. t3) 3.0) (round (t3 -. t2) 3.0) (round (t5 -. t4) 3.0);

  fprintf out_file "(PredEnc) Setup: %F s. KeyGen: %F s. Encryption: %F s. Decryption: %F s.\n"
    (round (t2 -. t1) 3.0) (round (t4 -. t3) 3.0) (round (t3 -. t2) 3.0) (round (t5 -. t4) 3.0);

  fprintf  setup_file "%F\n" (round (t2 -. t1) 3.0);
  fprintf keygen_file "%F\n" (round (t4 -. t3) 3.0);
  fprintf    enc_file "%F\n" (round (t3 -. t2) 3.0);
  fprintf    dec_file "%F, %d\n" (round (t5 -. t4) 3.0) (if sat then 1 else 0);

  F.print_flush ();
  ()


let bigPredEnc_test n =

  let module DSG = Hoeteck's_DSG in
  let module B = (val make_BilinearGroup 2) in
  let module PE = (val make_BF_PredEnc (n + 1)) in
  let module ABE = PredEncABE (B) (DSG) (PE) in

  let rec create_policy p k e =
    if k = e then create_policy p (k+1) e
    else if k > n then p
    else create_policy (Or(p,Leaf(Att(k)))) (k+1) e
  in
  let policy = create_policy (Leaf(Att(1))) 2 7 in

  let t1 = Unix.gettimeofday() in
  let mpk, msk = ABE.setup () in

  let xM  = ABE.set_x (Predicates.BoolForm_Policy(n, 1, 0, policy)) in
  let msg_rand = ABE.rand_msg () in
  let ct_x = ABE.enc mpk xM msg_rand in

  let y =  ABE.set_y (Predicates.BoolForm_Attrs(n, 1, [Att(5)])) in
  let sk_y = ABE.keyGen mpk msk y in
  let msg = ABE.dec mpk sk_y ct_x in

  let y' =  ABE.set_y (Predicates.BoolForm_Attrs(n, 1, [Att(7)])) in
  let sk_y' = ABE.keyGen mpk msk y' in
  let msg' = ABE.dec mpk sk_y' ct_x in

  let t4 = Unix.gettimeofday() in

  assert (B.Gt.equal msg_rand msg);
  assert (not (B.Gt.equal msg_rand msg'));

  F.printf "%d, %F\n" n (round (t4 -. t1) 3.0); F.print_flush ()


let test algorithm =
  let i1 = 2 in
  let i2 = 21 in

  let n_tests = (i2-i1+1) in
  let counter = ref 1 in

  (match algorithm with
   | "predEnc" -> ()
   | "comparison" ->
      for n = i1 to i2 do
        let n_attributes = n in
        let and_gates = n_attributes - 1 in
        let rep = 1 in
        let max_leaf_nodes = n_attributes * rep in
        F.printf "Test %d/%d:\n" (!counter) (n_tests);
        counter := !counter + 1;
        run_test ~n_attributes ~and_gates ~rep ~max_leaf_nodes ()
      done
   | _ -> assert false
  );

  ()
