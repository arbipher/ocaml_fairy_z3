[@@@warning "-34-37"]

type a = Foo of string * int | Baz of int
[@@deriving_inline z3 ~flag ~bv_width:52] [@@ocaml.doc "@inline"]

include
  struct
    [@@@ocaml.warning "-60"]
    let _ = fun (_ : a) -> ()
    module Z3_this =
      struct
        module Not_here = struct  end
        open Z3
        type t_ml = a
        type t_z3 = Expr.expr
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
          Datatype.mk_constructor_s ctx "Foo" (Symbol.mk_string ctx "is-Foo")
            [Symbol.mk_string ctx "Foo-0"; Symbol.mk_string ctx "Foo-1"]
            [Some string_sort; Some int_sort] [1; 1]
        let _ = ctor_foo
        let decl_foo = Datatype.Constructor.get_constructor_decl ctor_foo
        let _ = decl_foo
        let ctor_baz =
          Datatype.mk_constructor_s ctx "Baz" (Symbol.mk_string ctx "is-Baz")
            [Symbol.mk_string ctx "Baz-0"] [Some int_sort] [1]
        let _ = ctor_baz
        let decl_baz = Datatype.Constructor.get_constructor_decl ctor_baz
        let _ = decl_baz
        let sort = Datatype.mk_sort_s ctx "This_sort" [ctor_foo; ctor_baz]
        let _ = sort
        let (rzer_foo, rzer_baz) =
          match Datatype.get_recognizers sort with
          | rzer_foo::rzer_baz::[] -> (rzer_foo, rzer_baz)
          | _ -> failwith "recogniziers mismatch"
        let _ = rzer_foo
        and _ = rzer_baz
        let (asor_foo, asor_baz) =
          match Datatype.get_accessors sort with
          | (asor_foo::[])::(asor_baz::[])::[] -> (asor_foo, asor_baz)
          | _ -> failwith "recogniziers mismatch"
        let _ = asor_foo
        and _ = asor_baz
        let inj_foo (e0, e1) = FuncDecl.apply decl_foo [e0; e1]
        let _ = inj_foo
        let is_foo (e0, e1) = FuncDecl.apply rzer_foo [e0; e1]
        let _ = is_foo
        let prj_foo (e0, e1) = FuncDecl.apply asor_foo [e0; e1]
        let _ = prj_foo
        let inj_baz e0 = FuncDecl.apply decl_baz [e0]
        let _ = inj_baz
        let is_baz e0 = FuncDecl.apply rzer_baz [e0]
        let _ = is_baz
        let prj_baz e0 = FuncDecl.apply asor_baz [e0]
        let _ = prj_baz
        let box : t_ml -> t_z3 = failwith "not yet"
        let _ = box
        let unbox : t_z3 -> t_ml = failwith "not yet"
        let _ = unbox
      end
  end[@@ocaml.doc "@inline"]

[@@@end]

let _ = Foo ("3", 42)
