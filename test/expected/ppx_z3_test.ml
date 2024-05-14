type t1 = Foo of int [@@deriving z3 ~flag ~bv_width:52]

let%expect_test _ =
  let msg = Z3.Sort.to_string Z3_datatype_for_t1.sort in
  Fmt.pr "%s" msg ;
  [%expect {| This_sort |}]
