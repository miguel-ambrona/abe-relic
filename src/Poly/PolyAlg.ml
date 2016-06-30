open Core_kernel.Std
open Abbrevs
open PolyInterfaces
open LinAlg

module PolyAlg (P : Poly) = struct
    
  type t = P.t

  module Gauss = LinAlg (P.Coeffs)

  let find_combination polys target =
    let all_monomials =
      L.fold_left (target :: polys)
        ~init:[]
        ~f:(fun l p -> l @ (P.mons p))
           |> L.dedup ~compare:P.mon_compare
    in
    let matrix = L.map all_monomials ~f:(fun m -> L.map polys ~f:(fun p -> P.coeff_in_field p m)) in
    let vector = L.map all_monomials ~f:(fun m -> P.coeff_in_field target m) in
    Gauss.solve matrix vector
      

   (* This functions takes as input two lists of polynomials k and c and a target polynomial
      and outputs a matrix E of coefficients satisfying the equation
                                   k'*E*c = target                                        *)
  let find_matrix ~requirement k c target =
    F.printf "%a\n" (pp_list ",\n" P.pp) k;
    F.printf "%a\n" (pp_list ",\n" P.pp) c;
    let cross_product = L.map k ~f:(fun p -> L.map c ~f:(fun p' -> P.(p *@ p'))) |> L.concat in
    let forbidden_positions = Util.get_positions_list ~predicate:(fun p -> not (requirement p)) cross_product in
    let cross_product' = Util.set_positions_list ~positions:forbidden_positions ~value:P.zero cross_product in
    match find_combination cross_product' target with
    | None -> raise Not_found
    | Some coeffs ->
       let coeffs = Util.set_positions_list ~positions:forbidden_positions ~value:P.Coeffs.zero coeffs in
       let m = Util.list_to_matrix coeffs (L.length c) in
       F.printf "%a\n" (Util.pp_matrix P.Coeffs.pp) m;
       m
end
