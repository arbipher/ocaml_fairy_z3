[@@@warning "-34-37"]

type a = Foo of string | Baz of int
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
        let bv_width = 52
        let _ = bv_width
        let bitvector_sort = BitVector.mk_sort ctx bv_width
        let _ = bitvector_sort
        let box_int i = Arithmetic.Integer.mk_numeral_i ctx i
        let _ = box_int
        let box_bool b = Boolean.mk_val ctx b
        let _ = box_bool
        let box_string s = Seq.mk_string ctx s
        let _ = box_string
        let box_bitvector i =
          BitVector.mk_numeral ctx (Int.to_string i) bv_width
        let _ = box_bitvector
        let ctor_foo =
          Datatype.mk_constructor_s ctx "Foo" (Symbol.mk_string ctx "is-Foo")
            [Symbol.mk_string ctx "Foo-0"] [Some string_sort] [1]
        let _ = ctor_foo
        let ctor_baz =
          Datatype.mk_constructor_s ctx "Baz" (Symbol.mk_string ctx "is-Baz")
            [Symbol.mk_string ctx "Baz-0"] [Some int_sort] [1]
        let _ = ctor_baz
        let sort = Datatype.mk_sort_s ctx "This_sort" [ctor_foo; ctor_baz]
        let _ = sort
        let decl_foo = Datatype.Constructor.get_constructor_decl ctor_foo
        let _ = decl_foo
        let decl_baz = Datatype.Constructor.get_constructor_decl ctor_baz
        let _ = decl_baz
        let (rzer_foo, rzer_baz) =
          match Datatype.get_recognizers sort with
          | rzer_foo::rzer_baz::[] -> (rzer_foo, rzer_baz)
          | _ -> failwith "recogniziers mismatch"
        let _ = rzer_foo
        and _ = rzer_baz
        let (asor_foo_0, asor_baz_0) =
          match Datatype.get_accessors sort with
          | (asor_foo_0::[])::(asor_baz_0::[])::[] ->
              (asor_foo_0, asor_baz_0)
          | _ -> failwith "accessors mismatch"
        let _ = asor_foo_0
        and _ = asor_baz_0
        let inj_foo e0 = FuncDecl.apply decl_foo [e0]
        let _ = inj_foo
        let is_foo e0 = FuncDecl.apply rzer_foo [e0]
        let _ = is_foo
        let prj_foo_0 e = FuncDecl.apply asor_foo_0 [e]
        let _ = prj_foo_0
        let inj_baz e0 = FuncDecl.apply decl_baz [e0]
        let _ = inj_baz
        let is_baz e0 = FuncDecl.apply rzer_baz [e0]
        let _ = is_baz
        let prj_baz_0 e = FuncDecl.apply asor_baz_0 [e]
        let _ = prj_baz_0
        let box_a =
          function
          | Foo e0 -> inj_foo (box_string e0)
          | Baz e0 -> inj_baz (box_int e0)
        let _ = box_a
        let unbox_a = 42
        let _ = unbox_a
      end
  end[@@ocaml.doc "@inline"]
[@@@end]

open Z3

let dump e = Fmt.pr "%s" (Expr.to_string e)

open Z3_this

let solver = Solver.mk_solver ctx None
let e1 = inj_baz @@ Arithmetic.Integer.mk_numeral_i ctx 3
let e2 = Expr.mk_const_s ctx "x" sort ;;

dump e2

let () = Ppx_z3.Z3_datatype_helper.dump_check solver [ Boolean.mk_eq ctx e1 e2 ]

type t = C1 of int * string | C2 of string * int
[@@deriving_inline z3 ~flag ~bv_width:52]

include
  struct
    [@@@ocaml.warning "-60"]
    let _ = fun (_ : t) -> ()
    module Z3_this =
      struct
        module Not_here = struct  end
        open Z3
        type t_ml = t
        type t_z3 = Expr.expr
        let ctx = mk_context []
        let _ = ctx
        let int_sort = Arithmetic.Integer.mk_sort ctx
        let _ = int_sort
        let bool_sort = Boolean.mk_sort ctx
        let _ = bool_sort
        let string_sort = Seq.mk_string_sort ctx
        let _ = string_sort
        let bv_width = 52
        let _ = bv_width
        let bitvector_sort = BitVector.mk_sort ctx bv_width
        let _ = bitvector_sort
        let box_int i = Arithmetic.Integer.mk_numeral_i ctx i
        let _ = box_int
        let box_bool b = Boolean.mk_val ctx b
        let _ = box_bool
        let box_string s = Seq.mk_string ctx s
        let _ = box_string
        let box_bitvector i =
          BitVector.mk_numeral ctx (Int.to_string i) bv_width
        let _ = box_bitvector
        let ctor_c1 =
          Datatype.mk_constructor_s ctx "C1" (Symbol.mk_string ctx "is-C1")
            [Symbol.mk_string ctx "C1-0"; Symbol.mk_string ctx "C1-1"]
            [Some int_sort; Some string_sort] [1; 1]
        let _ = ctor_c1
        let ctor_c2 =
          Datatype.mk_constructor_s ctx "C2" (Symbol.mk_string ctx "is-C2")
            [Symbol.mk_string ctx "C2-0"; Symbol.mk_string ctx "C2-1"]
            [Some string_sort; Some int_sort] [1; 1]
        let _ = ctor_c2
        let sort = Datatype.mk_sort_s ctx "This_sort" [ctor_c1; ctor_c2]
        let _ = sort
        let decl_c1 = Datatype.Constructor.get_constructor_decl ctor_c1
        let _ = decl_c1
        let decl_c2 = Datatype.Constructor.get_constructor_decl ctor_c2
        let _ = decl_c2
        let (rzer_c1, rzer_c2) =
          match Datatype.get_recognizers sort with
          | rzer_c1::rzer_c2::[] -> (rzer_c1, rzer_c2)
          | _ -> failwith "recogniziers mismatch"
        let _ = rzer_c1
        and _ = rzer_c2
        let ((asor_c1_0, asor_c1_1), (asor_c2_0, asor_c2_1)) =
          match Datatype.get_accessors sort with
          | (asor_c1_0::asor_c1_1::[])::(asor_c2_0::asor_c2_1::[])::[] ->
              ((asor_c1_0, asor_c1_1), (asor_c2_0, asor_c2_1))
          | _ -> failwith "accessors mismatch"
        let _ = asor_c1_0
        and _ = asor_c1_1
        and _ = asor_c2_0
        and _ = asor_c2_1
        let inj_c1 (e0, e1) = FuncDecl.apply decl_c1 [e0; e1]
        let _ = inj_c1
        let is_c1 (e0, e1) = FuncDecl.apply rzer_c1 [e0; e1]
        let _ = is_c1
        let prj_c1_0 e = FuncDecl.apply asor_c1_0 [e]
        let _ = prj_c1_0
        let prj_c1_1 e = FuncDecl.apply asor_c1_1 [e]
        let _ = prj_c1_1
        let inj_c2 (e0, e1) = FuncDecl.apply decl_c2 [e0; e1]
        let _ = inj_c2
        let is_c2 (e0, e1) = FuncDecl.apply rzer_c2 [e0; e1]
        let _ = is_c2
        let prj_c2_0 e = FuncDecl.apply asor_c2_0 [e]
        let _ = prj_c2_0
        let prj_c2_1 e = FuncDecl.apply asor_c2_1 [e]
        let _ = prj_c2_1
        let box_t =
          function
          | C1 (e0, e1) -> inj_c1 ((box_int e0), (box_string e1))
          | C2 (e0, e1) -> inj_c2 ((box_string e0), (box_int e1))
        let _ = box_t
        let unbox_t = 42
        let _ = unbox_t
      end
  end[@@ocaml.doc "@inline"]

[@@@end]

open Z3_this

let solver = Solver.mk_solver ctx None

let e1 =
  inj_c1
    ( Arithmetic.Integer.mk_const_s ctx "x1",
      Expr.mk_const_s ctx "s1" (Seq.mk_string_sort ctx) )

let e2 =
  inj_c2
    ( Expr.mk_const_s ctx "s2" (Seq.mk_string_sort ctx),
      Arithmetic.Integer.mk_const_s ctx "x2" )

let i1 = prj_c1_0 e1
let i2 = prj_c2_1 e2
let () = Ppx_z3.Z3_datatype_helper.dump_check solver [ Boolean.mk_eq ctx i1 i2 ]
let e3 = box_t (C1 (42, "s1"))
let () = Ppx_z3.Z3_datatype_helper.dump_check solver [ Boolean.mk_eq ctx e1 e3 ]
