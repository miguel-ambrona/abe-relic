open Abbrevs
open Util
open BoolForms
open DualSystemG
open MakeAlgebra
open PredEnc
open PairEnc
open ABE
open Printf

let round int decimals =
  let factor = 10.0**decimals in
  Pervasives.ceil ((factor *. int)) /. factor

let run_test ~out_file ~setup_file ~keygen_file ~enc_file ~dec_file ~n_attributes ~and_gates ~rep ~max_leaf_nodes () =

  let attributes = L.map (list_range 1 (1+n_attributes)) ~f:(fun i -> Att(i)) in

  let module DSG = Hoeteck's_DSG in
  let module B = (val make_BilinearGroup 2) in

  let module Par = struct
    let par_n1 = max_leaf_nodes
    let par_n2 = and_gates+1
    let par_T  = n_attributes
  end
  in
  let module ABE1 = PredEncABE (B) (DSG) (Boolean_Formula_PredEnc) in
  let module ABE2 = PairEncABE (B) (DSG) (Boolean_Formula_PairEnc (Par)) in

  let key_size = 1 + Rand.int n_attributes in
  let key_attributes = random_permutation ~len:key_size attributes in
  let leaf_nodes = 1 + (Rand.int max_leaf_nodes) in
  let policy = generate_bool_formula ~and_gates ~leaf_nodes ~rep attributes in
  let sat = eval_boolean_formula ~attributes:key_attributes policy in
  F.printf "Policy -> %s.  Key -> [%a]. Valid key: %b\n"
    (string_of_boolean_formula policy) (pp_list ", " pp_attribute) key_attributes sat;
  
  (* ** Predicate-Encodings *)
  
  let t1 = Unix.gettimeofday() in
  let mpk, msk = ABE1.setup ~n:(n_attributes * rep + and_gates + 1) () in
  
  let t2 = Unix.gettimeofday() in
  let xM  = ABE1.set_x (Predicates.BoolForm_Policy(n_attributes, rep, policy)) in
  let msg = ABE1.rand_msg () in
  let ct_x = ABE1.enc mpk xM msg in
  
  let t3 = Unix.gettimeofday() in    
  let y =  ABE1.set_y (Predicates.BoolForm_Attrs(n_attributes, rep, key_attributes)) in
  let sk_y = ABE1.keyGen mpk msk y in
  
  let t4 = Unix.gettimeofday() in
  let msg' = ABE1.dec mpk sk_y ct_x in
  
  let t5 = Unix.gettimeofday() in
  
  (if sat then assert (B.Gt.equal msg msg') else assert (not (B.Gt.equal msg msg')));
  
  F.printf "(PredEnc) Setup: %F s. KeyGen: %F s. Encryption: %F s. Decryption: %F s.\n"
    (round (t2 -. t1) 3.0) (round (t4 -. t3) 3.0) (round (t3 -. t2) 3.0) (round (t5 -. t4) 3.0);

  fprintf out_file "(PredEnc) Setup: %F s. KeyGen: %F s. Encryption: %F s. Decryption: %F s.\n"
    (round (t2 -. t1) 3.0) (round (t4 -. t3) 3.0) (round (t3 -. t2) 3.0) (round (t5 -. t4) 3.0);

  fprintf  setup_file "%F" (round (t2 -. t1) 3.0);
  fprintf keygen_file "%F" (round (t4 -. t3) 3.0);
  fprintf    enc_file "%F" (round (t3 -. t2) 3.0);
  fprintf    dec_file "%F, %d" (round (t5 -. t4) 3.0) (if sat then 1 else 0);

  F.print_flush ();
  
  (* ** Pair-Encodings *)
  
  let t1 = Unix.gettimeofday() in
  let mpk, msk = ABE2.setup () in
  
  let t2 = Unix.gettimeofday() in
  let xM  = ABE2.set_x (Predicates.BoolForm_Policy(Par.par_n1, Par.par_n2, policy)) in
  let msg = ABE2.rand_msg () in
  let ct_x = ABE2.enc mpk xM msg in
  
  let t3 = Unix.gettimeofday() in
  let y =  ABE2.set_y (Predicates.BoolForm_Attrs(0, 0, key_attributes)) in
  let sk_y = ABE2.keyGen mpk msk y in
  
  let t4 = Unix.gettimeofday() in
  let msg' = ABE2.dec mpk sk_y ct_x in
  
  let t5 = Unix.gettimeofday() in
  
  (if sat then assert (B.Gt.equal msg msg') else assert (not (B.Gt.equal msg msg')));
  
  F.printf "(PairEnc) Setup: %F s. KeyGen: %F s. Encryption: %F s. Decryption: %F s.\n\n"
    (round (t2 -. t1) 3.0) (round (t4 -. t3) 3.0) (round (t3 -. t2) 3.0) (round (t5 -. t4) 3.0);

  fprintf out_file "(PairEnc) Setup: %F s. KeyGen: %F s. Encryption: %F s. Decryption: %F s.\n\n"
    (round (t2 -. t1) 3.0) (round (t4 -. t3) 3.0) (round (t3 -. t2) 3.0) (round (t5 -. t4) 3.0);

  fprintf  setup_file ", %F\n" (round (t2 -. t1) 3.0);
  fprintf keygen_file ", %F\n" (round (t4 -. t3) 3.0);
  fprintf    enc_file ", %F\n" (round (t3 -. t2) 3.0);
  fprintf    dec_file ", %F, %d\n" (round (t5 -. t4) 3.0) (if sat then 1 else 0);

  F.print_flush ();
  ()


let predEnc_test  ~out_file ~setup_file ~keygen_file ~enc_file ~dec_file ~n_attributes ~and_gates ~rep ~max_leaf_nodes () =

  let attributes = L.map (list_range 1 (1+n_attributes)) ~f:(fun i -> Att(i)) in

  let module DSG = Hoeteck's_DSG in
  let module B = (val make_BilinearGroup 2) in
  let module ABE = PredEncABE (B) (DSG) (Boolean_Formula_PredEnc) in

  let key_size = 1 + Rand.int n_attributes in
  let key_attributes = random_permutation ~len:key_size attributes in
  let leaf_nodes = 1 + (Rand.int max_leaf_nodes) in
  let policy = generate_bool_formula ~and_gates ~leaf_nodes ~rep attributes in
  let sat = eval_boolean_formula ~attributes:key_attributes policy in

  F.printf "Policy -> %s.  Key -> [%a]. Valid key: %b\n"
    (string_of_boolean_formula policy) (pp_list ", " pp_attribute) key_attributes sat;
  
  (* ** Predicate-Encodings *)
  
  let t1 = Unix.gettimeofday() in
  let mpk, msk = ABE.setup ~n:(n_attributes * rep + and_gates + 1) () in
  
  let t2 = Unix.gettimeofday() in
  let xM  = ABE.set_x (Predicates.BoolForm_Policy(n_attributes, rep, policy)) in
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
  

let test algorithm =
  let out_file    = open_out "tests/bf_comparison.txt" in
  let setup_file  = open_out "tests/setup_times.txt" in
  let keygen_file = open_out "tests/keygen_times.txt" in
  let enc_file    = open_out "tests/enc_times.txt" in
  let dec_file    = open_out "tests/dec_times.txt" in

  let i1 = 2 in
  let i2 = 16 in
  let j1 = 3 in
  let j2 = 6 in
  let k1 = 2 in
  let k2 = 16 in

  let n_tests = (i2-i1+1) * (j2-j1+1) * (k2-k1+1) in
  let counter = ref 1 in
    

  (match algorithm with
  | "predEnc" ->
     let n_tests = 200 in
     for n_attributes = 1 to n_tests do
       let max_leaf_nodes = 2*n_attributes in
       let rep = 1 + (max_leaf_nodes / n_attributes) in
       let and_gates = n_attributes in
       F.printf "Test %d/%d:\n" !counter n_tests;
       counter := !counter + 1;
       predEnc_test ~out_file ~setup_file ~keygen_file ~enc_file ~dec_file 
         ~n_attributes ~and_gates ~rep ~max_leaf_nodes ()
     done
       
  | "both" ->
     for n_attributes = i1 to i2 do
       for and_gates = j1 to j2 do
         for max_leaf_nodes = k1 to k2 do
           let rep = 1 + (max_leaf_nodes / n_attributes) in
           F.printf "Test %d/%d:\n" !counter n_tests;
           counter := !counter + 1;
           run_test ~out_file ~setup_file ~keygen_file ~enc_file ~dec_file 
             ~n_attributes:(2*n_attributes) ~and_gates:(2*and_gates) ~rep ~max_leaf_nodes:(2*max_leaf_nodes) ()
         done
       done
     done
  | _ -> assert false
  );
  
  let _ = close_out_noerr out_file in
  let _ = close_out_noerr setup_file in
  let _ = close_out_noerr keygen_file in
  let _ = close_out_noerr enc_file in
  let _ = close_out_noerr dec_file in
  ()
