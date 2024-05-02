open Z3

type primitive_case = Int_case | Bool_case | String_case | Bitvecetor_case

let string_of_primitive_case = function
  | Int_case -> "int"
  | Bool_case -> "bool"
  | String_case -> "string"
  | Bitvecetor_case -> "int"

module type Z3_context = sig
  val ctx : context
end

module type Config_primitive = sig
  val bv_width : int
end

module Make_primitive (C : Z3_context) (CP : Config_primitive) = struct
  open C
  include CP

  (* let bv_width = 63 *)
  let int_sort = Arithmetic.Integer.mk_sort ctx
  let bool_sort = Boolean.mk_sort ctx
  let string_sort = Seq.mk_string_sort ctx
  let bitvector_sort = BitVector.mk_sort ctx bv_width

  (* let primitive_sort_of_case = function
     | Int_case -> int_sort
     | Bool_case -> bool_sort
     | String_case -> string_sort
     | Bitvecetor_case -> bitvector_sort *)

  let mk_int_s x = Arithmetic.Integer.mk_const_s ctx x
  let mk_bool_s x = Boolean.mk_const_s ctx x
  let mk_string_s x = Expr.mk_const_s ctx x string_sort

  (* boxing and unboxing *)
  let box_int i = Arithmetic.Integer.mk_numeral_i ctx i
  let box_bool b = Boolean.mk_val ctx b
  let box_string s = Seq.mk_string ctx s
  let box_bitvector i = BitVector.mk_numeral ctx (Int.to_string i) bv_width

  let unbox_int e =
    e |> Arithmetic.Integer.get_big_int |> Big_int_Z.int_of_big_int

  let unbox_bool_exn v =
    match Boolean.get_bool_value v with
    | L_TRUE -> true
    | L_FALSE -> false
    | L_UNDEF -> failwith "L_UNDEF"

  let unbox_bool v =
    match Boolean.get_bool_value v with
    | L_TRUE -> true
    | L_FALSE -> false
    | L_UNDEF -> false

  let unbox_string e = Seq.get_string ctx e
  let unbox_bitvector e = BitVector.numeral_to_string e |> int_of_string
end

(* module Make_datatype (C : Z3_context) = struct
     open C
     open Make_primitive (C)

     let foo = 42
   end *)

let dump_check solver exps =
  match Solver.check solver exps with
  | Solver.SATISFIABLE -> (
      match Solver.get_model solver with
      | None ->
          failwith
            ("check is not invoked before; " ^ "the result is not SAT; "
           ^ " the model production is not enabled")
      | Some model ->
          Fmt.pr "sat\n%s" (Model.to_string model) ;
          Some model)
  | Solver.UNSATISFIABLE ->
      Fmt.pr "unsat" ;
      None
  | Solver.UNKNOWN ->
      failwith
      @@ Printf.sprintf "[check_and_get_model] Unknown result in solve: %s"
           (Solver.get_reason_unknown solver)

let dump_check_unit solver exps = ignore @@ dump_check solver exps
