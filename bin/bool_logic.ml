[@@@warning "-32-34-37"]

type exp_no_var =
  | Const of bool
  | And of exp_no_var * exp_no_var
  | Or of exp_no_var * exp_no_var
  | Not of exp_no_var

type value = bool

(* catamorphism *)
type value_op =
  | Const_v of bool
  | And_v of value * value
  | Or_v of value * value
  | Not_v of value

type var = Id of string
type assignment = var * value
type assignments = assignment list

let value_meaning = function
  | Const_v b -> b
  | And_v (b1, b2) -> b1 && b2
  | Or_v (b1, b2) -> b1 || b2
  | Not_v b -> not b

type exp =
  | Var of var
  | Const of value
  | And of exp * exp
  | Or of exp * exp
  | Not of exp

(* which is the minimal portant to embed *)

let ctx = Z3.mk_context []
let sort = Z3.Boolean.mk_sort ctx
let z3_exp_of_value _value = Z3.Boolean.mk_val ctx true

let rec z3_exp_of_exp = function
  | Var (Id x) -> Z3.Expr.mk_const_s ctx x sort
  | Const vb -> z3_exp_of_value vb
  | And (e1, e2) -> Z3.Boolean.mk_and ctx [ z3_exp_of_exp e1; z3_exp_of_exp e2 ]
  | Or (e1, e2) -> Z3.Boolean.mk_or ctx [ z3_exp_of_exp e1; z3_exp_of_exp e2 ]
  | Not e -> Z3.Boolean.mk_not ctx (z3_exp_of_exp e)

let solve (_given : assignments) (_exps : exp list) : assignments = []
let () = ()
