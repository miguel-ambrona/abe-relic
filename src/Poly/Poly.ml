(* * Polynomials
 * Use [Var] and [Ring] types to define [MakePoly] functor.
 * Also define [IntRing]. *)

(* ** Imports *)
open Abbrevs
open Util
open AlgStructures
open PolyInterfaces

(* ** Functor for Polynomials
 * ----------------------------------------------------------------------- *)

module MakePoly (V : Var) (C : Field) = struct
  module Coeffs = C
  type coeff = C.t
  type var   = V.t

  (** We represent polynomials as assoc lists from
      monomials to coefficents. See [norm] for invariants
      that we maintain. *)
  type monom = (V.t * int) list

  type term = monom * C.t

  type t = term list

(* *** Equality and comparison
 * ----------------------------------------------------------------------- *)

  let vexp_equal = equal_pair V.equal (=)

  let vexp_compare = compare_pair V.compare compare

  let mon_equal = equal_list vexp_equal

  let mon_compare = compare_list vexp_compare

  let equal =
    equal_list (fun (m1,c1) (m2,c2) -> C.equal c1 c2 && mon_equal m1 m2)

  let term_compare (m1,c1) (m2,c2) =
    let cmp = C.compare c1 c2 in
    if cmp <> 0 then - cmp else mon_compare m1 m2

  let compare = compare_list term_compare

(* *** Pretty printing
 * ----------------------------------------------------------------------- *)

  let pp_vpow fmt (v,e) =
    if e = 1 then V.pp fmt v
    else F.fprintf fmt "%a^%i" V.pp v e

  let pp_monom fmt m =
    match m with
    | [] -> F.fprintf fmt "1"
    | _  -> F.fprintf fmt "%a" (pp_list "*" pp_vpow) m

  let pp_term fmt (m,c) =
    if m = [] then F.fprintf fmt "%a" C.pp c
    else if C.equal c C.one then pp_monom fmt m
    else if C.use_parens then F.fprintf fmt "[%a]*%a" C.pp c pp_monom m
    else F.fprintf fmt "%a*%a" C.pp c pp_monom m

  let pp_ break fmt f =
    let f = L.sort ~cmp:term_compare f in
    let rec go fmt ts = match ts with
      | [] -> F.fprintf fmt ""
      | (m,c)::ts when C.compare c C.zero < 0->
        F.fprintf fmt " %s- %a%a" (if break then "\n" else "") pp_term (m,C.neg c) go ts
      | t::ts ->
        F.fprintf fmt " %s+ %a%a" (if break then "\n" else "") pp_term t go ts
    in
    match f with
    | []     -> F.fprintf fmt "0"
    | t::ts  ->
      F.fprintf fmt "%a%a" pp_term t go ts

  let pp = pp_ false

  let pp_break = pp_ true

  let pp_coeff = C.pp

(* *** Internal functions
 * ----------------------------------------------------------------------- *)

  let norm_monom (ves : (V.t * int) list) =
    let cmp_var (v1,_) (v2,_) = V.compare v1 v2 in
    let equal_var (v1,_) (v2,_) = V.equal v1 v2 in
    L.sort ~cmp:cmp_var ves
    |> L.group ~break:(fun a b -> not (equal_var a b))
    |> L.map ~f:(fun ves -> (fst (L.hd_exn ves), list_sum ~zero:0 ~add:(+) (L.map ~f:snd ves)))
    |> L.filter ~f:(fun (_,e) -> e <> 0)
    |> L.sort ~cmp:vexp_compare

  (** The [norm] function ensures that:
      \begin{itemize}
      \item Vexp entries
      \item Each monomial is sorted.
      \item Each monomial with non-zero coefficient has exactly one entry.
      \item The list is sorted by the monomials (keys).
      \end{itemize} *)
  let norm (f : t) =
    f |> L.map ~f:(fun (m,c) -> (norm_monom m,c))
      |> L.sort ~cmp:(fun (m1,_) (m2,_) -> mon_compare m1 m2)
      |> L.group ~break:(fun (m1,_) (m2,_) -> not (mon_equal m1 m2))
      |> L.map ~f:(fun ys -> (fst (L.hd_exn ys), C.ladd (L.map ~f:snd ys)))
      |> L.filter ~f:(fun (_,c) -> not (C.equal c C.zero))

  let mult_term_poly_int (m,c) f =
    L.map ~f:(fun (m',c') -> (m @ m', C.mul c c')) f

(* *** Ring operations on polynomials
 * ----------------------------------------------------------------------- *)

  let one  = [([], C.one)]

  let add f g = norm (f @ g)

  (** No [norm] required since the keys (monomials) are unchanged. *)
  let neg f = L.map ~f:(fun (m,c) -> (m,C.neg c)) f

  let mult f g =
    if equal f one then g else if equal g one then f
    else f |> conc_map (fun t -> mult_term_poly_int t g) |> norm

  let minus f g = add f (neg g)

  let zero : t = []

  let var_exp v n = [([(v,n)],C.one)]

  let rec ring_exp f n =
    if n > 0 then mult f (ring_exp f (n-1))
    else if n = 0 then one
    else failwith "Negative exponent in polynomial"

  let var v = [([(v,1)],C.one)]

  let const c = if (C.equal c C.zero) then [] else [([],c)]

  let from_int i = const (C.from_int i)

  let lmult = L.fold_left ~f:(fun acc f -> mult acc f) ~init:one

  let ladd  = L.fold_left ~f:(fun acc f -> add acc f) ~init:zero

  let vars f =
    L.sort ~cmp:V.compare
      (conc_map (fun (m,_) -> L.sort ~cmp:V.compare (L.map ~f:fst m)) f |> L.dedup ~compare:V.compare)
      |> L.dedup ~compare:V.compare

  let partition p f =
    let (t1s, t2s) = L.partition_tf ~f:p f in
    (norm t1s, norm t2s)

  let inst_var env (v,e) =
    match e < 0, env v with
    | true, _ ->
      failwith "impossible: variables with negative exponent"
    | false, f ->
      ring_exp f e

  let eval env f =
    let eval_monom m = lmult (L.map ~f:(inst_var env) m) in
    let eval_term (m,c) = mult (const c) (eval_monom m) in
    ladd (L.map ~f:eval_term f)

  let eval_generic cconv vconv terms =
    let vars_to_poly ves = lmult (L.map ~f:(inst_var vconv) ves) in
    ladd (L.map ~f:(fun (ves, c) ->  mult (vars_to_poly ves) (cconv c)) terms)

  let to_terms f = f

  let lc f = match f with (* FIXME: fix name tc (tail coeff) *)
    | [] -> C.zero
    | x::_ -> snd x (* (Util.last f) *)

  let from_terms f = norm f

  let from_mon m = from_terms [(m, C.one)]

  let is_const = function ([([],_)] | []) -> true | _ -> false

  let is_var = function [([_x],c)] when C.equal c C.one -> true | _ -> false

  let mons (f : t) =
    L.sort ~cmp:(compare_list vexp_compare) (L.map ~f:fst f)
    |> L.dedup ~compare:(compare_list vexp_compare)

  let coeff f m = try list_assoc m f with Not_found -> C.zero

  let monom_of_monomPoly p = 
    let monomials = mons p in
    if (L.length monomials) <> 1 then failwith "The polynomial must have a single monomial"
    else L.hd_exn (mons p)

  let coeff_in_field = coeff
  let coeff_to_field a = a

  let map_coeffs cf f =
    cat_Some
      (L.map ~f:(fun (m,c) -> let c = cf c in if C.equal c C.zero then None else Some (m,c)) f)

  let ( *@) = mult
  let ( +@) = add
  let ( -@) = minus

end
