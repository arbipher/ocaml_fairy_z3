[@@@warning "-34-37"]

type a = Foo of string | Baz of int
[@@deriving_inline z3 ~flag ~bv_width:52] [@@ocaml.doc "@inline"]

include struct
  [@@@ocaml.warning "-60"]

  let _ = fun (_ : a) -> ()

  module Z3_datatype_for_a = struct
    open Z3

    type t_ml = a
    type t_z3 = Expr.expr

    let ctx = mk_context []
    let _ = ctx

    module Z3_primitive =
      Fairy_z3.Make_primitive
        (struct
          let ctx = ctx
          let _ = ctx
        end)
        (struct
          let bv_width = 52
          let _ = bv_width
        end)

    open Z3_primitive

    let ctor_foo =
      Datatype.mk_constructor_s ctx "Foo"
        (Symbol.mk_string ctx "is-Foo")
        [ Symbol.mk_string ctx "Foo-0" ]
        [ Some string_sort ] [ 1 ]

    let _ = ctor_foo

    let ctor_baz =
      Datatype.mk_constructor_s ctx "Baz"
        (Symbol.mk_string ctx "is-Baz")
        [ Symbol.mk_string ctx "Baz-0" ]
        [ Some int_sort ] [ 1 ]

    let _ = ctor_baz
    let sort = Datatype.mk_sort_s ctx "This_sort" [ ctor_foo; ctor_baz ]
    let _ = sort
    let decl_foo = Datatype.Constructor.get_constructor_decl ctor_foo
    let _ = decl_foo
    let decl_baz = Datatype.Constructor.get_constructor_decl ctor_baz
    let _ = decl_baz

    let rzer_foo, rzer_baz =
      match Datatype.get_recognizers sort with
      | [ rzer_foo; rzer_baz ] -> (rzer_foo, rzer_baz)
      | _ -> failwith "recogniziers mismatch"

    let _ = rzer_foo
    and _ = rzer_baz

    let asor_foo_0, asor_baz_0 =
      match Datatype.get_accessors sort with
      | [ asor_foo_0 :: []; asor_baz_0 :: [] ] -> (asor_foo_0, asor_baz_0)
      | _ -> failwith "accessors mismatch"

    let _ = asor_foo_0
    and _ = asor_baz_0

    let inj_foo e0 = FuncDecl.apply decl_foo [ e0 ]
    let _ = inj_foo
    let is_foo e = FuncDecl.apply rzer_foo [ e ]
    let _ = is_foo
    let prj_foo_0 e = FuncDecl.apply asor_foo_0 [ e ]
    let _ = prj_foo_0
    let inj_baz e0 = FuncDecl.apply decl_baz [ e0 ]
    let _ = inj_baz
    let is_baz e = FuncDecl.apply rzer_baz [ e ]
    let _ = is_baz
    let prj_baz_0 e = FuncDecl.apply asor_baz_0 [ e ]
    let _ = prj_baz_0

    let box_a = function
      | Foo e0 -> inj_foo (box_string e0)
      | Baz e0 -> inj_baz (box_int e0)

    let _ = box_a

    let unbox_a e =
      match e with
      | _ when Expr.simplify (is_foo e) None |> unbox_bool ->
          Foo (Expr.simplify (prj_foo_0 e) None |> unbox_string)
      | _ when Expr.simplify (is_baz e) None |> unbox_bool ->
          Baz (Expr.simplify (prj_baz_0 e) None |> unbox_int)
      | _ -> failwith "not here"

    let _ = unbox_a
  end

  open Z3_datatype_for_a
end [@@ocaml.doc "@inline"]

[@@@end]

open Z3

let dump e = Fmt.pr "%s" (Expr.to_string e)

open Z3_datatype_for_a

let solver = Solver.mk_solver ctx None
let e1 = inj_baz @@ Arithmetic.Integer.mk_numeral_i ctx 3
let e2 = Expr.mk_const_s ctx "x" sort ;;

dump e2

let () = Fairy_z3.dump_check_unit solver [ Boolean.mk_eq ctx e1 e2 ]

type t = C1 of int * string | C2 of string * int
[@@deriving_inline z3 ~flag ~bv_width:52]

include struct
  [@@@ocaml.warning "-60"]

  let _ = fun (_ : t) -> ()

  module Z3_datatype_for_t = struct
    open Z3

    type t_ml = t
    type t_z3 = Expr.expr

    let ctx = mk_context []
    let _ = ctx

    module Z3_primitive =
      Fairy_z3.Make_primitive
        (struct
          let ctx = ctx
          let _ = ctx
        end)
        (struct
          let bv_width = 52
          let _ = bv_width
        end)

    open Z3_primitive

    let ctor_c1 =
      Datatype.mk_constructor_s ctx "C1"
        (Symbol.mk_string ctx "is-C1")
        [ Symbol.mk_string ctx "C1-0"; Symbol.mk_string ctx "C1-1" ]
        [ Some int_sort; Some string_sort ]
        [ 1; 1 ]

    let _ = ctor_c1

    let ctor_c2 =
      Datatype.mk_constructor_s ctx "C2"
        (Symbol.mk_string ctx "is-C2")
        [ Symbol.mk_string ctx "C2-0"; Symbol.mk_string ctx "C2-1" ]
        [ Some string_sort; Some int_sort ]
        [ 1; 1 ]

    let _ = ctor_c2
    let sort = Datatype.mk_sort_s ctx "This_sort" [ ctor_c1; ctor_c2 ]
    let _ = sort
    let decl_c1 = Datatype.Constructor.get_constructor_decl ctor_c1
    let _ = decl_c1
    let decl_c2 = Datatype.Constructor.get_constructor_decl ctor_c2
    let _ = decl_c2

    let rzer_c1, rzer_c2 =
      match Datatype.get_recognizers sort with
      | [ rzer_c1; rzer_c2 ] -> (rzer_c1, rzer_c2)
      | _ -> failwith "recogniziers mismatch"

    let _ = rzer_c1
    and _ = rzer_c2

    let (asor_c1_0, asor_c1_1), (asor_c2_0, asor_c2_1) =
      match Datatype.get_accessors sort with
      | [ [ asor_c1_0; asor_c1_1 ]; [ asor_c2_0; asor_c2_1 ] ] ->
          ((asor_c1_0, asor_c1_1), (asor_c2_0, asor_c2_1))
      | _ -> failwith "accessors mismatch"

    let _ = asor_c1_0
    and _ = asor_c1_1
    and _ = asor_c2_0
    and _ = asor_c2_1

    let inj_c1 (e0, e1) = FuncDecl.apply decl_c1 [ e0; e1 ]
    let _ = inj_c1
    let is_c1 e = FuncDecl.apply rzer_c1 [ e ]
    let _ = is_c1
    let prj_c1_0 e = FuncDecl.apply asor_c1_0 [ e ]
    let _ = prj_c1_0
    let prj_c1_1 e = FuncDecl.apply asor_c1_1 [ e ]
    let _ = prj_c1_1
    let inj_c2 (e0, e1) = FuncDecl.apply decl_c2 [ e0; e1 ]
    let _ = inj_c2
    let is_c2 e = FuncDecl.apply rzer_c2 [ e ]
    let _ = is_c2
    let prj_c2_0 e = FuncDecl.apply asor_c2_0 [ e ]
    let _ = prj_c2_0
    let prj_c2_1 e = FuncDecl.apply asor_c2_1 [ e ]
    let _ = prj_c2_1

    let box_t = function
      | C1 (e0, e1) -> inj_c1 (box_int e0, box_string e1)
      | C2 (e0, e1) -> inj_c2 (box_string e0, box_int e1)

    let _ = box_t

    let unbox_t e =
      match e with
      | _ when Expr.simplify (is_c1 e) None |> unbox_bool ->
          C1
            ( Expr.simplify (prj_c1_0 e) None |> unbox_int,
              Expr.simplify (prj_c1_1 e) None |> unbox_string )
      | _ when Expr.simplify (is_c2 e) None |> unbox_bool ->
          C2
            ( Expr.simplify (prj_c2_0 e) None |> unbox_string,
              Expr.simplify (prj_c2_1 e) None |> unbox_int )
      | _ -> failwith "not here"

    let _ = unbox_t
  end

  open Z3_datatype_for_t
end [@@ocaml.doc "@inline"]

[@@@end]

open Z3_datatype_for_t

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
let () = Fairy_z3.dump_check_unit solver [ Boolean.mk_eq ctx i1 i2 ]
let e3 = box_t (C1 (42, "s1"))
let e4 = Expr.mk_const_s ctx "x" sort
let () = Fairy_z3.dump_check_unit solver [ Boolean.mk_eq ctx e1 e3 ]

let () =
  match Fairy_z3.dump_check solver [ Boolean.mk_eq ctx e3 e4 ] with
  | Some model -> (
      let v4 = Z3.Model.eval model e4 false |> Option.get in
      match unbox_t v4 with
      | C1 (i, _) -> Fmt.pr "c1 %d" i
      | C2 (_, i) -> Fmt.pr "c2 %d" i)
  | None -> ()
