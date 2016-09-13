open Abbrevs
open DualSystemG
open BoolForms
open NonMonotonicBF
open MakeAlgebra
open Predicates
open ABE
open PredEncTransformations
open MakePredEnc
open MakePredEncChar
open MakePairEnc


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


let test_predEnc_Revocation () =

  let n_attrs = 6 in
  let repetitions = 1 in
  let and_bound = 3 in

  let spanish      = Att(1) in
  let _american    = Att(2) in
  let comedy       = Att(3) in
  let _fiction     = Att(4) in
  let breaking_bad = Att(5) in
  let year_2016    = Att(6) in

  let film_attrs = [ spanish; comedy; year_2016 ] in
  let user_policy = (Leaf(breaking_bad) |. (Leaf(spanish) &. Leaf(comedy))) in

  let s = n_attrs * repetitions in
  let r = n_attrs * repetitions + 1 in
  let w = n_attrs * repetitions + and_bound + 1 in

  let n_attrs_rev = 5 in
  let repetitions_rev = 1 in
  let and_bound_rev = 3 in
  let s' = n_attrs_rev * repetitions_rev in
  let r' = n_attrs_rev * repetitions_rev + 1 in
  let w' = n_attrs_rev * repetitions_rev + and_bound_rev + 1 in

  let revocated = [1; 2] in
  let policy_rev = L.fold_left (L.tl_exn revocated)
    ~init:(Leaf(Att(L.hd_exn revocated)))
    ~f:(fun f i -> Or(f, Leaf(Att(i))) )
  in

  let module C1 = (val make_BF_PredEnc_Characterization s r w) in
  let module C2 = (val make_BF_PredEnc_Characterization s' r' w') in
  let module C1_dual = Dual_Characterization (C1) in
  let module C2_neg = Negation_Characterization (C2) in
  let module C = Conjunction_Characterization (C2_neg) (C1_dual) in
  let module PE = PredEnc_from_Characterization (C) in
  let module ABE = PredEncABE (B) (DSG) (PE) in

  let t1 = Unix.gettimeofday() in
  let mpk, msk = ABE.setup () in
  let movie_info = ABE.set_x (Predicates.GenericAttPair(
    BoolForm_Policy(n_attrs_rev, repetitions_rev, and_bound_rev, policy_rev),
    BoolForm_Attrs(n_attrs, repetitions, film_attrs)
  )) in

  let movie_content = ABE.rand_msg () in
  let ct = ABE.enc mpk movie_info movie_content in

  let user_info = ABE.set_y (Predicates.GenericAttPair(
    BoolForm_Attrs(n_attrs_rev, repetitions_rev, [Att(3)]),
    BoolForm_Policy(n_attrs, repetitions, and_bound, user_policy)
  )) in

  let sk = ABE.keyGen mpk msk user_info in
  let decrypted = ABE.dec mpk sk ct in

  let user_info' = ABE.set_y (Predicates.GenericAttPair(
    BoolForm_Attrs(n_attrs_rev, repetitions_rev, [Att(1)]),
    BoolForm_Policy(n_attrs, repetitions, and_bound, user_policy)
  )) in

  let sk' = ABE.keyGen mpk msk user_info' in
  let decrypted' = ABE.dec mpk sk' ct in

  let t2 = Unix.gettimeofday() in

  if (B.Gt.equal movie_content decrypted) && not (B.Gt.equal movie_content decrypted') then
    F.printf "Revocation. Pred. Enc. test succedded!\t Time: \027[32m%F\027[0m seconds\n"
      (Pervasives.ceil ((100.0 *. (t2 -. t1))) /. 100.0)
  else failwith "Revocation Predicate Encodings test failed"


let test_predEnc_shareRoot () =

  let s = 40 in
  let r = 1 in

  let module C = (val make_ShareRoot_PredEnc_Characterization s r) in
  let module PE = PredEnc_from_Characterization (C) in
  let module ABE = PredEncABE (B) (DSG) (PE) in

  let i = Zp.from_int in

  let t1 = Unix.gettimeofday() in
  let mpk, msk = ABE.setup () in
  let x = ABE.set_x (Discriminant(s,r, [i 5; i 7; i 9; i 10])) in

  let msg = ABE.rand_msg () in
  let ct_x = ABE.enc mpk x msg in

  let y = ABE.set_y (Discriminant(s,r, [i 7])) in

  let sk_y = ABE.keyGen mpk msk y in
  let msg' = ABE.dec mpk sk_y ct_x in

  let y' = ABE.set_y (Discriminant(s,r, [i 11])) in

  let sk_y' = ABE.keyGen mpk msk y' in
  let msg'' = ABE.dec mpk sk_y' ct_x in

  let t2 = Unix.gettimeofday() in

  if (B.Gt.equal msg msg') && not (B.Gt.equal msg msg'') then
    F.printf "Pred Enc Roots ABE test succedded!\t Time: \027[32m%F\027[0m seconds\n"
      (Pervasives.ceil ((100.0 *. (t2 -. t1))) /. 100.0)
  else failwith "Predicate Encodings Roots test failed"

let test_predEnc_ZIP () =

  let n = 50 in

  let module PE = (val make_InnerProduct_PredEnc n) in
  let module ABE = PredEncABE (B) (DSG) (PE) in

  let i = Zp.from_int in

  let t1 = Unix.gettimeofday() in
  let mpk, msk = ABE.setup () in
  let x = ABE.set_x (InnerProduct(n, (i 1) :: (Util.mk_list (i 0) (n-1)) )) in

  let msg = ABE.rand_msg () in
  let ct_x = ABE.enc mpk x msg in

  let y = ABE.set_y (InnerProduct(n, (i 0) :: (Util.mk_list (i 1) (n-1)) )) in

  let sk_y = ABE.keyGen mpk msk y in
  let msg' = ABE.dec mpk sk_y ct_x in

  let y' = ABE.set_y (InnerProduct(n, (i 1) :: (Util.mk_list (i 0) (n-1)) )) in

  let sk_y' = ABE.keyGen mpk msk y' in
  let msg'' = ABE.dec mpk sk_y' ct_x in

  let t2 = Unix.gettimeofday() in

  if (B.Gt.equal msg msg') && not (B.Gt.equal msg msg'') then
    F.printf "Pred Enc ZIP ABE test succedded!\t Time: \027[32m%F\027[0m seconds\n"
      (Pervasives.ceil ((100.0 *. (t2 -. t1))) /. 100.0)
  else failwith "Predicate Encodings ZIP test failed"


let test_predEnc_Broadcast () =

  let t = 10 in
  let t' = 10 in

  let module PE = (val make_BroadcastEnc_PredEnc t t') in
  let module ABE = PredEncABE (B) (DSG) (PE) in

  let t1 = Unix.gettimeofday() in
  let mpk, msk = ABE.setup () in
  let x = ABE.set_x (BroadcastEncVector(t,t', true :: (Util.mk_list false (t*t'-1)) )) in

  let msg = ABE.rand_msg () in
  let ct_x = ABE.enc mpk x msg in

  let id = 0 in
  let y = ABE.set_y (BroadcastEncIndex(t,t', (id/t,id mod t))) in

  let sk_y = ABE.keyGen mpk msk y in
  let msg' = ABE.dec mpk sk_y ct_x in

  let id' = t*t'-1 in
  let y' = ABE.set_y (BroadcastEncIndex(t,t', (id'/t,id' mod t))) in

  let sk_y' = ABE.keyGen mpk msk y' in
  let msg'' = ABE.dec mpk sk_y' ct_x in

  let t2 = Unix.gettimeofday() in

  if (B.Gt.equal msg msg') && not (B.Gt.equal msg msg'') then
    F.printf "Pred Enc. Broadcast test succedded!\t Time: \027[32m%F\027[0m seconds\n"
      (Pervasives.ceil ((100.0 *. (t2 -. t1))) /. 100.0)
  else failwith "Predicate Encodings BroadcastEnc test failed"


let test_ArithmeticSpanProgram () =

  let n = 20 in
  let rep = 2 in

  let module PE = (val make_ArithmeticSpanProgram_PredEnc n rep) in
  let module ABE = PredEncABE (B) (DSG) (PE) in

  let t1 = Unix.gettimeofday() in
  let mpk, msk = ABE.setup () in
  let x = ABE.set_x (BoolForm_Attrs(n, rep, [ Att(4); Att(5) ])) in

  let msg = ABE.rand_msg () in
  let ct_x = ABE.enc mpk x msg in

  let formula = OR (AND (LEAF 1, AND (LEAF 2, LEAF 3)), AND (LEAF 4, LEAF 5)) in
  let y = ABE.set_y (NonMonBoolForm(rep, formula)) in
  let sk_y = ABE.keyGen mpk msk y in
  let msg' = ABE.dec mpk sk_y ct_x in

  let formula' = AND(LEAF 4, NOT(LEAF 5)) in
  let y' = ABE.set_y (NonMonBoolForm(rep, formula')) in
  let sk_y' = ABE.keyGen mpk msk y' in
  let msg'' = ABE.dec mpk sk_y' ct_x in

  let t2 = Unix.gettimeofday() in

  if (B.Gt.equal msg msg') && not(B.Gt.equal msg msg'') then
    F.printf "Pred Enc. ArithSP test succedded!\t Time: \027[32m%F\027[0m seconds\n"
      (Pervasives.ceil ((100.0 *. (t2 -. t1))) /. 100.0)
  else failwith "Predicate Encodings Arithmetic Span Program test failed"

let test_Fast_ArithmeticSpanProgram () =

  let n = 20 in
  let rep = 2 in

  let module PE = (val make_Fast_ArithmeticSpanProgram_PredEnc n rep) in
  let module ABE = PredEncABE (B) (DSG) (PE) in

  let t1 = Unix.gettimeofday() in
  let mpk, msk = ABE.setup () in
  let x = ABE.set_x (BoolForm_Attrs(n, rep, [ Att(4); Att(5) ])) in

  let msg = ABE.rand_msg () in
  let ct_x = ABE.enc mpk x msg in

  let formula = OR (AND (LEAF 1, AND (LEAF 2, LEAF 3)), AND (LEAF 4, LEAF 5)) in
  let y = ABE.set_y (NonMonBoolForm(rep, formula)) in
  let sk_y = ABE.keyGen mpk msk y in
  let msg' = ABE.dec mpk sk_y ct_x in

  let formula' = AND(LEAF 4, NOT(LEAF 5)) in
  let y' = ABE.set_y (NonMonBoolForm(rep, formula')) in
  let sk_y' = ABE.keyGen mpk msk y' in
  let msg'' = ABE.dec mpk sk_y' ct_x in

  let t2 = Unix.gettimeofday() in

  if (B.Gt.equal msg msg') && not(B.Gt.equal msg msg'') then
    F.printf "Pred Enc. Fast ASP test succedded!\t Time: \027[32m%F\027[0m seconds\n"
      (Pervasives.ceil ((100.0 *. (t2 -. t1))) /. 100.0)
  else failwith "Predicate Encodings Fast Arithmetic Span Program test failed"

let test_pairEnc () =
  let n1 = 5 in   (* Bound on the number of Leaf nodes in the boolean formula*)
  let n2 = 4 in   (* n2-1 = Bound on the number of AND gates *)
  let t = 4 in    (* Bound on the number of attributes in a key *)

  let module PE = (val make_BF_PairEnc n1 n2 t) in
  let module ABE = PairEncABE (B) (DSG) (PE) in

  let t1 = Unix.gettimeofday() in

  let x = ABE.set_x (Predicates.BoolForm_Policy(n1, n2, 0, policy1 |. policy2)) in

  let mpk, msk = ABE.setup () in
  let msg = B.Gt.samp () in
  let ct_x = ABE.enc mpk x msg in

  let setS = ABE.set_y (Predicates.BoolForm_Attrs(n1, n2, [ phd_att; cs_att ])) in
  let sk_y = ABE.keyGen mpk msk setS in
  let msg' = ABE.dec mpk sk_y ct_x in

  let setS' = ABE.set_y (Predicates.BoolForm_Attrs(n1, n2, [ tall_att; dark_att; phd_att; maths_att ])) in

  let sk_y' = ABE.keyGen mpk msk setS' in
  let msg'' = ABE.dec mpk sk_y' ct_x in

  let t2 = Unix.gettimeofday() in

  if (B.Gt.equal msg msg') && not (B.Gt.equal msg msg'') then
    F.printf "Pair Encodings ABE test succedded!\t Time: \027[32m%F\027[0m seconds\n"
      (Pervasives.ceil ((100.0 *. (t2 -. t1))) /. 100.0)
  else failwith "Pair Encodings test failed"
