open Abbrevs
open Util

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
