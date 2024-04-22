[@@@warning "-34-37"]

type a = Foo of string * int | Baz of int
[@@deriving_inline z3 ~flag ~bv_width:52]

include struct
  [@@@ocaml.warning "-60"]

  let _ = fun (_ : a) -> ()

  module Z3_this = struct
    module Not_here = struct end
    open Z3

    type t_ml = T
    type t_z3 = Expr.expr
    type the_sort = Sort

    let ctx = mk_context []
    let _ = ctx
    let int_sort = Arithmetic.Integer.mk_sort ctx
    let _ = int_sort
    let bool_sort = Boolean.mk_sort ctx
    let _ = bool_sort
    let string_sort = Seq.mk_string_sort ctx
    let _ = string_sort
    let bitvector_sort w = BitVector.mk_sort ctx w
    let _ = bitvector_sort

    let ctor_foo =
      Datatype.mk_constructor_s ctx "Foo"
        (Symbol.mk_string ctx "is-Foo")
        [ Symbol.mk_string ctx "Foo-0"; Symbol.mk_string ctx "Foo-1" ]
        [ Some string_sort; Some int_sort ]
        [ 1; 1 ]

    let _ = ctor_foo

    let ctor_baz =
      Datatype.mk_constructor_s ctx "Baz"
        (Symbol.mk_string ctx "is-Baz")
        [ Symbol.mk_string ctx "Baz-0" ]
        [ Some int_sort ] [ 1 ]

    let _ = ctor_baz
    let sort = Datatype.mk_sort_s ctx "This_sort" [ ctor_foo; ctor_baz ]
    let _ = sort
    let box : t_ml -> t_z3 = failwith "not yet"
    let _ = box
    let unbox : t_z3 -> t_ml = failwith "not yet"
    let _ = unbox
  end
end [@@ocaml.doc "@inline"]

[@@@end]

let _ = Foo ("3", 42)
