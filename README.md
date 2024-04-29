# OCaml Fairy_z3

The library `Fairy_z3` contains two packages `Fairy_z3` and `Ppx_z3`. `Fairy_z3` provides helper functions based on the OCaml [z3](https://opam.ocaml.org/packages/z3/). `Ppx_z3` is a ppx to derive a Z3 datatype and the functions e.g. `box`, `unbox`, `inj`, `prj`.

For a step-by-step explanation for Z3.Datatype functions, check my tutorial post [Using `Z3.Datatype`](https://fairyland-ocaml.github.io/libraries/z3-datatype.html).

## Example

```ocaml
type t = C1 of int * string | C2 of string * int
[@@deriving z3 ~flag ~bv_width:52]

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
```

A document and a tutorial with more details are underway.

## To-do

- [ ] Support more OCaml types e.g. record, recursive types.
- [ ] Add enough testing