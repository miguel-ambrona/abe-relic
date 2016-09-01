open Abbrevs
open Util
open LinAlg

(*
   vector = 'a list
   matrix = 'a llist list
*)

let sample_list ~f k =
  let rec aux list k =
    if k = 0 then list
    else aux (list @ [f ()]) (k-1)
  in
  aux [] k

let sample_matrix ~f m n =
  let rec aux matrix m =
    if m = 0 then matrix
    else aux (matrix @ [sample_list ~f n]) (m-1)
  in
  aux [] m

let transpose_matrix matrix =
  L.fold_left matrix
    ~init:(L.map (L.hd_exn matrix) ~f:(fun _ -> []))
    ~f:(fun l_output l -> L.map2_exn l_output l ~f:(fun li e -> li @ [e]))

let vector_times_vector ~add ~mul v1 v2 =
  let prods = L.map2_exn v1 v2 ~f:mul in
  L.fold_left (L.tl_exn prods)
    ~init:(L.hd_exn prods)
    ~f:add

let matrix_times_vector ~add ~mul m v = L.map m ~f:(fun row -> vector_times_vector ~add ~mul row v)

let matrix_times_matrix ~add ~mul m1 m2 =
  L.map (transpose_matrix m2) ~f:(fun col -> matrix_times_vector ~add ~mul m1 col)
  |> transpose_matrix

let matrix_map ~f m = L.map m ~f:(L.map ~f)

let create_matrix element ~m ~n =
  let row = mk_list element n in
  mk_list row m

let diagonal_matrix ~zero diag =
  let n = L.length diag in
  let rec aux output k =
    if k >= n then output
    else
      let new_row = (mk_list zero k) @ [L.nth_exn diag k] @ (mk_list zero (n-k-1)) in
      aux (output @ [new_row]) (k+1)
  in
  aux [] 0

let identity_matrix ~zero ~one ~n =
  diagonal_matrix ~zero (mk_list one n)

let join_blocks blocks =
  let join_row row =
    L.fold_left (L.tl_exn row)
      ~init:(L.hd_exn row)
      ~f:(fun m1 m2 -> L.map2_exn m1 m2 ~f:(fun row1 row2 -> row1 @ row2))
  in
  let join_col col =
    L.fold_left (L.tl_exn col)
      ~init:(L.hd_exn col)
      ~f:(fun row1 row2 -> row1 @ row2)
  in
  join_col (L.map blocks ~f:join_row)

let add_matrices ~add m1 m2 =
  L.map2_exn m1 m2 ~f:(fun row1 row2 -> L.map2_exn row1 row2 ~f:add)


module MyGaussElim (Field : Field) = struct

  (* ** Types and utility functions
   * ----------------------------------------------------------------------- *)
  type t = Field.t
  let add = Field.add
  let mul = Field.mul
  let inv = Field.inv
  let neg = Field.neg
  let one = Field.one
  let zero = Field.zero
  let is_zero = Field.is_zero

  let swap_rows i j matrix det =
    let rowi = L.nth_exn matrix i in
    let rowj = L.nth_exn matrix j in
    L.map (list_range 0 (L.length matrix))
          ~f:(fun k -> if k = i then rowj else if k = j then rowi else L.nth_exn matrix k),
    (if i = j then det else Field.neg det)

  let reduce_by_pivot row col pivot matrix det =
    let inv_pivot = inv pivot in
    let relevant_row = L.map (L.nth_exn matrix row) ~f:(Field.mul inv_pivot) in
    L.map (list_range 0 (L.length matrix))
      ~f:(fun k ->
        if k = row then relevant_row
        else
          let this_row = L.nth_exn matrix k in
          let column_element = L.nth_exn this_row col in
          L.map2_exn this_row relevant_row ~f:(fun a b -> add a (neg (mul b column_element)) )
      )
    , Field.mul det inv_pivot

  let search_for_non_zero starting_row col matrix =
    let m = L.length matrix in
    let rec go k =
      if k >= m then None
      else
        let el = L.nth_exn (L.nth_exn matrix k) col in
        if not (is_zero el) then Some (el, k)
        else go (k+1)
    in
    go starting_row

  let only_zeros list = not (L.exists list ~f:(fun el -> not (Field.is_zero el)))

  let prod_diagonal matrix =
    let m = L.length matrix in
    let rec aux prod k =
      if k >= m then prod
      else aux (Field.mul prod (L.nth_exn (L.nth_exn matrix k) k)) (k+1)
    in
    aux Field.one 0

  let gaussian_elimination matrix =
    let n = L.length (L.hd_exn matrix) in
    let rec go reduced k det =
      if k >= n then reduced, Field.mul (prod_diagonal reduced) (Field.inv det)
      else
        (* We search for a non-zero in column k and rows >= k *)
        match search_for_non_zero k k reduced with
        | None -> go reduced (k+1) det
        | Some (el,row) ->
           let reduced, det = swap_rows row k reduced det in
           let reduced, det = reduce_by_pivot k k el reduced det in
           go reduced (k+1) det
    in
    go matrix 0 Field.one

  let determinant matrix =
    let _, det = gaussian_elimination matrix in
    det

  let kernel matrix =
    let m = L.length matrix in
    let n = L.length (L.hd_exn matrix) in
    let id_n = identity_matrix ~zero:Field.zero ~one:Field.one ~n in
    let reduced, _ = gaussian_elimination (transpose_matrix (join_blocks [[matrix]; [id_n]])) in
    reduced
    |> L.filter ~f:(fun col -> only_zeros (L.slice col 0 m))
    |> L.map ~f:(fun col -> L.slice col m (m+n))

  let rec pseudo_inverse matrix =
    let m = L.length matrix in
    let n = L.length (L.hd_exn matrix) in
    let ker = kernel matrix in
    let r = L.length ker in
    let id_m = identity_matrix ~zero:Field.zero ~one:Field.one ~n:m in
    let zeros_rm = create_matrix Field.zero ~m:r ~n:m in
    let reduced, _ = gaussian_elimination (join_blocks [[matrix; id_m]; [ker; zeros_rm]]) in
    let mM = L.map (list_range 0 n) ~f:(fun i -> L.slice (L.nth_exn reduced i) n (n+m)) in
    if r = 0 then mM
    else
      let add = Field.add in
      let mul = Field.mul in
      let mD' = L.map (list_range n (m+r)) ~f:(fun i -> L.slice (L.nth_exn reduced i) n (n+m)) in
      if L.length mD' = 0 then mM
      else
        let mD = transpose_matrix mD' in
        let mD'D_inv = pseudo_inverse (matrix_times_matrix ~add ~mul mD' mD) in
        add_matrices ~add:(fun a b -> add a (Field.neg b))
          mM
          (matrix_times_matrix ~add ~mul mM
             (matrix_times_matrix ~add ~mul mD (matrix_times_matrix ~add ~mul mD'D_inv mD')))
end
