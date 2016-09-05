open Abbrevs
open Util
open MakeAlgebra
       
type non_monotonic_bool_formula =
  | OR  of non_monotonic_bool_formula * non_monotonic_bool_formula
  | AND of non_monotonic_bool_formula * non_monotonic_bool_formula
  | NEG of non_monotonic_bool_formula
  | LEAF of int

let rec negation_normal_form = function
  | NEG (OR  (f1, f2)) -> AND ( negation_normal_form (NEG (f1)), negation_normal_form (NEG (f2)))
  | NEG (AND (f1, f2)) -> OR  ( negation_normal_form (NEG (f1)), negation_normal_form (NEG (f2)))
  | NEG (NEG f)  -> negation_normal_form f                        
  | OR  (f1, f2) -> OR  (negation_normal_form f1, negation_normal_form f2)
  | AND (f1, f2) -> AND (negation_normal_form f1, negation_normal_form f2)
  | f -> f
  
type arithmetic_formula =
  | AF_Add of arithmetic_formula * arithmetic_formula
  | AF_Mul of arithmetic_formula * arithmetic_formula
  | AF_Const of Zp.t
  | AF_Var of int

let rec af_normal_form = function
  | AF_Mul (AF_Add(a,b), c) | AF_Mul (c, AF_Add(a,b)) ->
     let a = af_normal_form a in
     let b = af_normal_form b in
     let c = af_normal_form c in
     af_normal_form (AF_Add( AF_Mul(a,c), AF_Mul(b,c) ))
  | AF_Mul (a, b) ->
     let a = af_normal_form a in
     let b = af_normal_form b in
     begin match a,b with
     | AF_Add(_,_), _ | _, AF_Add(_,_) -> af_normal_form (AF_Mul (a, b))
     | _ -> AF_Mul(a, b)
     end
  | AF_Add (a, b) -> AF_Add (af_normal_form a, af_normal_form b)
  | af -> af

type arithmetic_formula_normal_form = (Zp.t * (int list)) list
                                                             
let af_to_af_normal_form af =
  let af = af_normal_form af in
  let rec collect_term coeff vars = function
    | AF_Mul (t1, t2) ->
       let (c1,v1) = collect_term coeff vars t1 in
       let (c2,v2) = collect_term Zp.one [] t2 in
       (Zp.mul c1 c2), v1 @ v2
    | AF_Const (a) -> (Zp.mul coeff a, vars)
    | AF_Var   (v) -> (coeff, (v :: vars))
    | _ -> assert false
  in
  let rec add_summands output = function
    | [] -> output
    | (coeff,vars) :: rest ->
       let vars = L.sort vars ~cmp:I.compare in
       let f (_,vars') = equal_lists ~equal:I.equal vars vars' in
       match L.find output ~f with
       | None -> add_summands ((coeff,vars) :: output) rest
       | Some (coeff',_) ->
          let output' = L.filter output ~f:(fun a -> not (f a)) in
          add_summands (((Zp.add coeff coeff'), vars) :: output') rest
  in
  let rec aux afn = function
    | AF_Add (af1, af2) -> afn @ (aux [] af1) @ (aux [] af2)
    | af -> (collect_term Zp.one [] af) :: afn
  in
  add_summands [] (aux [] af)

let non_monotonic_bf_to_arithmetic_formula nmbf =
  let rec aux = function
    | OR  (bf1, bf2) -> AF_Add (aux bf1, aux bf2)
    | AND (bf1, bf2) -> AF_Mul (aux bf1, aux bf2)
    | NEG  (bf) -> AF_Add (AF_Const Zp.one, AF_Mul( AF_Const (Zp.neg Zp.one), aux bf))
    | LEAF (s)  -> AF_Var (s)
  in
  aux (negation_normal_form nmbf)
      
let pp_arithmetic_formula_nf _fmt afn =
  let pp_var _ v = F.printf "x%d" v in
  let pp_term _ (c,vars) =
    match vars with
    | []      -> F.printf "%a" Zp.pp c
    | v :: [] -> F.printf "%a * %a" Zp.pp c pp_var v
    | _       -> F.printf "%a * %a" Zp.pp c (pp_list " * " pp_var) vars
  in
  F.printf "%a\n" (pp_list " + " pp_term) afn
