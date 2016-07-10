open Abbrevs
open DualSystemG
open BoolForms
open MakeAlgebra
open PredEnc
open PairEnc
open Predicates
open ABE


(* ** Test *)

let tall_att     = Att(1)
let dark_att     = Att(2)
let handsome_att = Att(3)
let phd_att      = Att(4)
let cs_att       = Att(5)
let maths_att    = Att(6)

let tall     = Leaf(tall_att)
let dark     = Leaf(dark_att)
let handsome = Leaf(handsome_att)
let phd      = Leaf(phd_att)
let cs       = Leaf(cs_att)
let maths    = Leaf(maths_att)

let policy1 = (tall &. handsome &. dark)
let policy2 = (phd &. cs)

module DSG = Hoeteck's_DSG
module B = (val make_BilinearGroup 2)

let test_predEnc () =
  
  let n_attrs = 6 in      (* Global number of attributes *)
  let repetitions = 2 in  (* Bound on the number of times the same attribute can appear as a Leaf node *)
  let and_bound = 3 in    (* Bound on the number of AND gates *)

  let s = n_attrs * repetitions in
  let r = n_attrs * repetitions + 1 in
  let w = n_attrs * repetitions + and_bound + 1 in

  let module C = (val make_BF_PredEnc_Characterization s r w) in
  let module PE = PredEnc_from_Characterization (C) in
  let module ABE = PredEncABE (B) (DSG) (PE) in

  let t1 = Unix.gettimeofday() in
  let mpk, msk = ABE.setup () in
  let xM = ABE.set_x (BoolForm_Policy(n_attrs, repetitions, and_bound, policy1 |. policy2)) in

  let msg = ABE.rand_msg () in
  let ct_x = ABE.enc mpk xM msg in
  
  let y = ABE.set_y (BoolForm_Attrs(n_attrs, repetitions, [ phd_att; cs_att ])) in

  let sk_y = ABE.keyGen mpk msk y in
  let msg' = ABE.dec mpk sk_y ct_x in

  let y' = ABE.set_y (BoolForm_Attrs(n_attrs, repetitions, [ phd_att; maths_att; handsome_att; dark_att ])) in

  let sk_y' = ABE.keyGen mpk msk y' in
  let msg'' = ABE.dec mpk sk_y' ct_x in

  let t2 = Unix.gettimeofday() in
  
  if (B.Gt.equal msg msg') && not (B.Gt.equal msg msg'') then
    F.printf "Predicate Encodings ABE test succedded!\t Time: \027[32m%F\027[0m seconds\n"
      (Pervasives.ceil ((100.0 *. (t2 -. t1))) /. 100.0)
  else failwith "Predicate Encodings test failed"


let test_predEnc_Disjunction () =
  
  let n_attrs = 6 in      (* Global number of attributes *)
  let repetitions = 2 in  (* Bound on the number of times the same attribute can appear as a Leaf node *)
  let and_bound = 3 in    (* Bound on the number of AND gates *)

  let s = n_attrs * repetitions in
  let r = n_attrs * repetitions + 1 in
  let w = n_attrs * repetitions + and_bound + 1 in

  let module C1 = (val make_BF_PredEnc_Characterization s r w) in
  let module C2 = (val make_BF_PredEnc_Characterization s r w) in
  let module C = Disjunction_Characterization (C1) (C2) in
  let module PE = PredEnc_from_Characterization (C) in
  let module ABE = PredEncABE (B) (DSG) (PE) in

  let t1 = Unix.gettimeofday() in
  let mpk, msk = ABE.setup () in
  let xM = ABE.set_x (Predicates.GenericAttPair(
    BoolForm_Policy(n_attrs, repetitions, and_bound, policy1),
    BoolForm_Policy(n_attrs, repetitions, and_bound, policy2)
  )) in

  let msg = ABE.rand_msg () in
  let ct_x = ABE.enc mpk xM msg in
  
  let attributes = [ phd_att; cs_att ] in
  let y = ABE.set_y (Predicates.GenericAttPair(
    BoolForm_Attrs(n_attrs, repetitions, attributes),
    BoolForm_Attrs(n_attrs, repetitions, attributes)
  )) in


  let sk_y = ABE.keyGen mpk msk y in
  let msg' = ABE.dec mpk sk_y ct_x in

  let attributes = [ phd_att; maths_att; handsome_att; dark_att ] in
  let y' = ABE.set_y (Predicates.GenericAttPair(
    BoolForm_Attrs(n_attrs, repetitions, attributes),
    BoolForm_Attrs(n_attrs, repetitions, attributes)
  )) in

  let sk_y' = ABE.keyGen mpk msk y' in
  let msg'' = ABE.dec mpk sk_y' ct_x in

  let t2 = Unix.gettimeofday() in
  
  if (B.Gt.equal msg msg') && not (B.Gt.equal msg msg'') then
    F.printf "Disj. Pred. Enc. ABE test succedded!\t Time: \027[32m%F\027[0m seconds\n"
      (Pervasives.ceil ((100.0 *. (t2 -. t1))) /. 100.0)
  else failwith "Disjunction Predicate Encodings test failed"


let test_predEnc_Negation () =
  
  let n_attrs = 6 in      (* Global number of attributes *)
  let repetitions = 2 in  (* Bound on the number of times the same attribute can appear as a Leaf node *)
  let and_bound = 3 in    (* Bound on the number of AND gates *)

  let s = n_attrs * repetitions in
  let r = n_attrs * repetitions + 1 in
  let w = n_attrs * repetitions + and_bound + 1 in

  let module C = (val make_BF_PredEnc_Characterization s r w) in
  let module C = Negation_Characterization (C) in
  let module PE = PredEnc_from_Characterization (C) in
  let module ABE = PredEncABE (B) (DSG) (PE) in

  let t1 = Unix.gettimeofday() in
  let mpk, msk = ABE.setup () in
  let xM = ABE.set_x (BoolForm_Policy(n_attrs, repetitions, and_bound, policy1 |. policy2)) in

  let msg = ABE.rand_msg () in
  let ct_x = ABE.enc mpk xM msg in
  
  let y = ABE.set_y (BoolForm_Attrs(n_attrs, repetitions, [ phd_att; cs_att ])) in

  let sk_y = ABE.keyGen mpk msk y in
  let msg' = ABE.dec mpk sk_y ct_x in

  let y' = ABE.set_y (BoolForm_Attrs(n_attrs, repetitions, [ phd_att; maths_att; handsome_att; dark_att ])) in

  let sk_y' = ABE.keyGen mpk msk y' in
  let msg'' = ABE.dec mpk sk_y' ct_x in

  let t2 = Unix.gettimeofday() in
  
  if not (B.Gt.equal msg msg') && (B.Gt.equal msg msg'') then
    F.printf "Negation Pred. Enc. ABE test succedded!\t Time: \027[32m%F\027[0m seconds\n"
      (Pervasives.ceil ((100.0 *. (t2 -. t1))) /. 100.0)
  else failwith "Negation Predicate Encodings test failed"


let test_predEnc_Conjunction () =
  
  let n_attrs = 6 in      (* Global number of attributes *)
  let repetitions = 2 in  (* Bound on the number of times the same attribute can appear as a Leaf node *)
  let and_bound = 3 in    (* Bound on the number of AND gates *)

  let s = n_attrs * repetitions in
  let r = n_attrs * repetitions + 1 in
  let w = n_attrs * repetitions + and_bound + 1 in

  let module C1 = (val make_BF_PredEnc_Characterization s r w) in
  let module C2 = (val make_BF_PredEnc_Characterization s r w) in
  let module C = Conjunction_Characterization (C1) (C2) in
  let module PE = PredEnc_from_Characterization (C) in
  let module ABE = PredEncABE (B) (DSG) (PE) in

  let t1 = Unix.gettimeofday() in
  let mpk, msk = ABE.setup () in
  let xM = ABE.set_x (Predicates.GenericAttPair(
    BoolForm_Policy(n_attrs, repetitions, and_bound, policy1),
    BoolForm_Policy(n_attrs, repetitions, and_bound, policy2)
  )) in

  let msg = ABE.rand_msg () in
  let ct_x = ABE.enc mpk xM msg in
  
  let attributes = [ phd_att; cs_att; dark_att; handsome_att; tall_att ] in
  let y = ABE.set_y (Predicates.GenericAttPair(
    BoolForm_Attrs(n_attrs, repetitions, attributes),
    BoolForm_Attrs(n_attrs, repetitions, attributes)
  )) in


  let sk_y = ABE.keyGen mpk msk y in
  let msg' = ABE.dec mpk sk_y ct_x in

  let attributes = [ phd_att; maths_att; handsome_att; dark_att ] in
  let y' = ABE.set_y (Predicates.GenericAttPair(
    BoolForm_Attrs(n_attrs, repetitions, attributes),
    BoolForm_Attrs(n_attrs, repetitions, attributes)
  )) in

  let sk_y' = ABE.keyGen mpk msk y' in
  let msg'' = ABE.dec mpk sk_y' ct_x in

  let t2 = Unix.gettimeofday() in
  
  if (B.Gt.equal msg msg') && not (B.Gt.equal msg msg'') then
    F.printf "Conj. Pred. Enc. ABE test succedded!\t Time: \027[32m%F\027[0m seconds\n"
      (Pervasives.ceil ((100.0 *. (t2 -. t1))) /. 100.0)
  else failwith "Conjunction Predicate Encodings test failed"


let test_predEnc_Dual () =
  
  let n_attrs = 6 in      (* Global number of attributes *)
  let repetitions = 2 in  (* Bound on the number of times the same attribute can appear as a Leaf node *)
  let and_bound = 3 in    (* Bound on the number of AND gates *)

  let s = n_attrs * repetitions in
  let r = n_attrs * repetitions + 1 in
  let w = n_attrs * repetitions + and_bound + 1 in

  let module C = (val make_BF_PredEnc_Characterization s r w) in
  let module C = Dual_Characterization (C) in
  let module PE = PredEnc_from_Characterization (C) in
  let module ABE = PredEncABE (B) (DSG) (PE) in

  let t1 = Unix.gettimeofday() in
  let mpk, msk = ABE.setup () in
  let attributes = [ phd_att; cs_att; ] in
  let xM = ABE.set_x (BoolForm_Attrs(n_attrs, repetitions, attributes)) in

  let msg = ABE.rand_msg () in
  let ct_x = ABE.enc mpk xM msg in
  
  let y = ABE.set_y (BoolForm_Policy(n_attrs, repetitions, and_bound, policy1 |. policy2)) in

  let sk_y = ABE.keyGen mpk msk y in
  let msg' = ABE.dec mpk sk_y ct_x in

  let y' = ABE.set_y (BoolForm_Policy(n_attrs, repetitions, and_bound, policy1)) in

  let sk_y' = ABE.keyGen mpk msk y' in
  let msg'' = ABE.dec mpk sk_y' ct_x in

  let t2 = Unix.gettimeofday() in
  
  if (B.Gt.equal msg msg') && not (B.Gt.equal msg msg'') then
    F.printf "Dual Predicate Enc. ABE test succedded!\t Time: \027[32m%F\027[0m seconds\n"
      (Pervasives.ceil ((100.0 *. (t2 -. t1))) /. 100.0)
  else failwith "Dual Predicate Encodings test failed"

let test_pairEnc () =
  
  let module Par = struct
    let par_n1 = 5    (* Bound on the number of Leaf nodes in the boolean formula*)
    let par_n2 = 4    (* n2-1 = Bound on the number of AND gates *)
    let par_T = 4     (* Bound on the number of attributes in a key *)
  end
  in
  let module ABE = PairEncABE (B) (DSG) (Boolean_Formula_PairEnc (Par)) in
  
  let t1 = Unix.gettimeofday() in

  let mA, pi = ABE.set_x (Predicates.BoolForm_Policy(Par.par_n1, Par.par_n2, 0, policy1 |. policy2)) in

  let mpk, msk = ABE.setup () in
  let msg = B.Gt.samp () in
  let ct_x = ABE.enc mpk (mA,pi) msg in

  let setS = ABE.set_y (Predicates.BoolForm_Attrs(Par.par_n1, Par.par_n2, [ phd_att; cs_att ])) in
  let sk_y = ABE.keyGen mpk msk setS in
  let msg' = ABE.dec mpk sk_y ct_x in

  let setS' = ABE.set_y (Predicates.BoolForm_Attrs(Par.par_n1, Par.par_n2, [ tall_att; dark_att; phd_att; maths_att ])) in

  let sk_y' = ABE.keyGen mpk msk setS' in
  let msg'' = ABE.dec mpk sk_y' ct_x in

  let t2 = Unix.gettimeofday() in

  if (B.Gt.equal msg msg') && not (B.Gt.equal msg msg'') then
    F.printf "Pair Encodings ABE test succedded!\t Time: \027[32m%F\027[0m seconds\n"
      (Pervasives.ceil ((100.0 *. (t2 -. t1))) /. 100.0)
  else failwith "Pair Encodings test failed"
   
