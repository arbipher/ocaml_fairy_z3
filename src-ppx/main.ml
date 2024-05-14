(* it's obviously one working solution to write a minimal macro is
   ppx_z3: ocaml_type -> type_desc
   helper_defs : type_desc -> `let .. code`

   z3_helper: type_desc -> working_code
*)

(* constructor => declaration => injection
   A constructor are sort (type) definition.
   A declaration is a z3 function derived from the constructor.
   A injection is a z3 function application using the declaration.

   variant case sorts => a datatype sort => accessor => projection
   variant case sorts => a datatype sort => recognizer => is_case

   A variant case sort is the sort for an OCaml variant case.
   A datatype sort is the sort for the whole variant.

   An accessor is derived from the datatype sort.
   An accessor is a z3 function to project the datatype.
   A projection is a z3 function application using the accessor.

   A recognizer is derived from the datatype sort.
   A recognizer is a z3 function to check sort case of the datatype case.
   An is_case is a z3 function application using recognizer.
*)

(* ppx.metaquot missing
   1. antiquote %str
   2. antiquote %lid
*)

(*
   how to expree _uninterpreted function_
*)

open Ppxlib
module List = ListLabels
open Ppx_helper
open Ast_builder.Default

[@@@warning "-27"]

let primitive_case_of_lid_exn lid = Option.get (primitive_case_of_lid lid)
let _sort_of_record cdx = []

let ids_of_variant_payload prefix cds =
  List.mapi cds ~f:(fun i cd -> (i, cd))
  |> List.filter_map ~f:(fun (i, cd) ->
         let fid = prefix ^ case_tag_of_Tag cd in
         match cd.pcd_args with
         | Pcstr_tuple cts ->
             Some (List.mapi cts ~f:(fun i _ -> fid ^ "_" ^ string_of_int i))
         | _ -> None)

let payload_cases_of_cts cts =
  List.filter_map cts ~f:(fun ct ->
      match ct.ptyp_desc with
      | Ptyp_constr (lid_loc, _cts) ->
          Some (primitive_case_of_lid_exn lid_loc.txt)
      | _ -> None)

let ctors_of_variant loc cds =
  List.mapi cds ~f:(fun i cd ->
      let case_Tag = cd.pcd_name.txt in
      let case_tag = String.lowercase_ascii case_Tag in
      match cd.pcd_args with
      | Pcstr_tuple cts ->
          let acceesor_code =
            cts
            |> List.mapi ~f:(fun i _ -> i)
            |> List.map ~f:(fun si -> case_Tag ^ "-" ^ string_of_int si)
            |> List.map ~f:(fun id ->
                   [%expr Symbol.mk_string ctx [%e estring ~loc id]])
            |> elist ~loc
          in
          let sorts_code =
            payload_cases_of_cts cts
            |> List.map ~f:(function
                 | Fairy_z3.Int_case -> [%expr Some int_sort]
                 | Fairy_z3.Bool_case -> [%expr Some bool_sort]
                 | Fairy_z3.String_case -> [%expr Some string_sort]
                 | Fairy_z3.Bitvecetor_case -> [%expr Some bitvector_sort])
            |> elist ~loc
          in
          let all_ones_code =
            List.init ~len:(List.length cts) ~f:(fun _ -> 1)
            |> List.map ~f:(eint ~loc)
            |> elist ~loc
          in
          [%str
            let [%p pvar ~loc ("ctor_" ^ case_tag)] =
              Datatype.mk_constructor_s ctx [%e estring ~loc case_Tag]
                (Symbol.mk_string ctx [%e estring ~loc ("is-" ^ case_Tag)])
                [%e acceesor_code] [%e sorts_code] [%e all_ones_code]]
      | Pcstr_record _lds -> [])
  |> List.concat

let decls_of_variant loc cds =
  List.mapi cds ~f:(fun i cd ->
      let case_Tag = cd.pcd_name.txt in
      let case_tag = String.lowercase_ascii case_Tag in
      match cd.pcd_args with
      | Pcstr_tuple cts ->
          [%str
            let [%p pvar ~loc ("decl_" ^ case_tag)] =
              Datatype.Constructor.get_constructor_decl
                [%e evar ~loc ("ctor_" ^ case_tag)]]
      | Pcstr_record _lds ->
          let ext =
            Location.error_extensionf ~loc
              "Cannot derive accessors for non record types"
          in
          [ pstr_extension ~loc ext [] ])
  |> List.concat

module With_loc (L : sig
  val loc : location
  val z3_ctx : Z3.context
  val bv_width : int
  val type_declarations : type_declaration list
end) =
struct
  open L

  open Ast_builder.Make (struct
    let loc = loc
  end)

  let inj_and_prj_of_variant loc cds =
    let recognizer_code =
      let rzer_ids = prefix_cd_names "rzer_" cds in
      let rzer_pats = List.map rzer_ids ~f:pvar in
      let pat_rzers = ppat_tuple rzer_pats in
      let rzer_id_exps = List.map rzer_ids ~f:evar |> pexp_tuple in

      let asor_ids = ids_of_variant_payload "asor_" cds in
      let asor_pats =
        List.map asor_ids ~f:(fun asor_case_ids ->
            List.map asor_case_ids ~f:pvar |> plist)
        |> plist
      in

      let pat_asors =
        List.map asor_ids ~f:(fun asor_case_ids ->
            List.map asor_case_ids ~f:pvar |> ppat_tuple)
        |> ppat_tuple
      in
      let asor_id_exps =
        List.map asor_ids ~f:(fun asor_case_ids ->
            List.map asor_case_ids ~f:evar |> pexp_tuple)
        |> pexp_tuple
      in
      (* TODO: don't have to use this code. The pattern is only used for guarding *)
      [%str
        let [%p pat_rzers] =
          match Datatype.get_recognizers sort with
          | [%p plist rzer_pats] -> [%e rzer_id_exps]
          | _ -> failwith "recogniziers mismatch"

        let [%p pat_asors] =
          match Datatype.get_accessors sort with
          | [%p asor_pats] -> [%e asor_id_exps]
          | _ -> failwith "accessors mismatch"]
    in
    let inj_and_prj_code =
      List.mapi cds ~f:(fun i cd ->
          let case_Tag = cd.pcd_name.txt in
          let case_tag = String.lowercase_ascii case_Tag in
          match cd.pcd_args with
          | Pcstr_tuple cts ->
              let inj_code =
                let len = List.length (payload_cases_of_cts cts) in
                let ps_tuple_of_cts = ps_tuple ~loc "e" len in
                let es_list_of_cts = es_list ~loc "e" len in
                [%str
                  let [%p pvar ("inj_" ^ case_tag)] =
                   fun [%p ps_tuple_of_cts] ->
                    FuncDecl.apply
                      [%e evar ("decl_" ^ case_tag)]
                      [%e es_list_of_cts]

                  let [%p pvar ("is_" ^ case_tag)] =
                   fun e -> FuncDecl.apply [%e evar ("rzer_" ^ case_tag)] [ e ]]
              in
              let prj_code =
                List.mapi cts ~f:(fun i _ ->
                    [%str
                      let [%p pvar ("prj_" ^ case_tag ^ "_" ^ string_of_int i)]
                          =
                       fun e ->
                        FuncDecl.apply
                          [%e evar ("asor_" ^ case_tag ^ "_" ^ string_of_int i)]
                          [ e ]])
                |> List.concat
              in
              inj_code @ prj_code
          | Pcstr_record _lds -> [])
      |> List.concat
    in
    recognizer_code @ inj_and_prj_code

  let box_of_variant loc td cds =
    let box_id = td.ptype_name.txt in
    let box_body =
      List.filter_map cds ~f:(fun cd ->
          let case_Tag = cd.pcd_name.txt in
          let case_tag = String.lowercase_ascii case_Tag in
          let inj_f = evar ("inj_" ^ case_tag) in
          match cd.pcd_args with
          | Pcstr_tuple cts ->
              let lhs =
                let len = List.length (payload_cases_of_cts cts) in
                ps_tuple ~loc "e" len |> fun pat ->
                ppat_construct
                  (Loc.make ~loc (lident cd.pcd_name.txt))
                  (Some pat)
              in

              let rhs =
                let arg =
                  payload_cases_of_cts cts
                  |> List.mapi ~f:(fun i ps ->
                         let f = evar ("box_" ^ name_of_primitive_sort ps) in
                         let a = evar ("e" ^ string_of_int i) in
                         [%expr [%e f] [%e a]])
                  |> pexp_tuple
                in
                [%expr [%e inj_f] [%e arg]]
              in
              Some (case ~lhs ~guard:None ~rhs)
          | Pcstr_record _lds -> None)
    in
    let unbox_body =
      List.filter_map cds ~f:(fun cd ->
          let case_Tag = cd.pcd_name.txt in
          let case_tag = String.lowercase_ascii case_Tag in
          let f_is = evar ("is_" ^ case_tag) in
          match cd.pcd_args with
          | Pcstr_tuple cts ->
              let lhs = ppat_any in
              let guard =
                Some [%expr Expr.simplify ([%e f_is] e) None |> unbox_bool]
              in
              let rhs =
                payload_cases_of_cts cts
                |> List.mapi ~f:(fun i ps ->
                       [%expr
                         Expr.simplify
                           ([%e
                              evar ("prj_" ^ case_tag ^ "_" ^ string_of_int i)]
                              e)
                           None
                         |> [%e evar ("unbox_" ^ name_of_primitive_sort ps)]])
                |> pexp_tuple
                |> fun e ->
                pexp_construct (Loc.make ~loc (lident cd.pcd_name.txt)) (Some e)
              in
              Some (case ~lhs ~guard ~rhs)
          | Pcstr_record _lds -> None)
      @ [ unreachable_case loc ]
    in
    [%str
      let [%p pvar ("box_" ^ box_id)] = [%e pexp_function box_body]

      let [%p pvar ("unbox_" ^ box_id)] =
       fun e -> [%e pexp_match [%expr e] unbox_body]]

  let whole_code =
    List.map type_declarations ~f:(function
      | { ptype_kind = Ptype_variant cds; ptype_loc = loc; ptype_name; _ } as td
        ->
          let t_ml = ptyp_constr (Loc.make ~loc (lident ptype_name.txt)) [] in
          let ctor_ids = prefix_cd_names "ctor_" cds in
          let ctor_sort_opts =
            List.map ctor_ids ~f:(fun pid -> [%expr [%e evar pid]]) |> elist
          in
          let defs =
            [%str
              open Z3

              type t_ml = [%t t_ml]
              type t_z3 = Expr.expr

              let ctx = z3_ctx

              module Z3_primitive =
                Fairy_z3.Make_primitive
                  (struct
                    let ctx = ctx
                  end)
                  (struct
                    let bv_width = [%e eint bv_width]
                  end)

              open Z3_primitive]
            @ ctors_of_variant loc cds
            @ [%str
                let sort =
                  Datatype.mk_sort_s ctx "This_sort" [%e ctor_sort_opts]]
            @ decls_of_variant loc cds
            @ inj_and_prj_of_variant loc cds
            @ box_of_variant loc td cds
          in
          let gen_mod_name = "Z3_datatype_for_" ^ ptype_name.txt in
          [
            pstr_module
            @@ module_binding
                 ~name:(Loc.make ~loc (Some gen_mod_name))
                 ~expr:(pmod_structure defs);
          ]
          (* @
             if open_module
             then
               [
                 pstr_open ~loc
                   (open_infos ~loc
                      ~expr: (mod_id_of_str ~loc "Aaa")
                      ~override:Fresh);
               ]
             else [] *)
      | _ -> [])
    |> List.concat
end

let generate_impl ~ctxt (_rec_flag, type_declarations) z3_ctx_opt bv_width_opt
    flag =
  let loc = Expansion_context.Deriver.derived_item_loc ctxt in
  let module Code_gen = With_loc (struct
    let loc = loc
    let _ = flag
    let z3_ctx = Option.get z3_ctx_opt
    let bv_width = Option.value bv_width_opt ~default:63
    let type_declarations = type_declarations
  end) in
  Code_gen.whole_code

(* let _i = Deriving.Args.int
   let _i42 = Deriving.Args.int 42
   let _1 = Deriving.Args.__
   let _2 = Deriving.Args.eint
   let _3 = Deriving.Args.(eint __)
   let _4 = Deriving.Args.(arg "name")
   let _5 = Deriving.Args.(single_expr_payload __) *)

(* let de_option x = Ast_pattern.map x ~f:Option.get *)

(* let z3_ctx_pattern : (bool, 'a, 'a) Ast_pattern.t =
     Ast_pattern.cst ~to_string:(fun _ -> "Z3 context") true

   (* let e_z3 : (bool, 'a, 'a) Ast_pattern.t -> (expression, 'a, 'a) Ast_pattern.t = *)
   let _ = Ppxlib.Ast_pattern.pconst_integer

   let e_z3 =
     Ast_pattern.of_func (fun _ctx loc x k ->
         match x with
         | true ->
             (* ctx.matched <- ctx.matched + 1; *)
             k
         | _ -> failwith "aha")

   let int' tf =
     let f = Ast_pattern.to_func tf in
     let f' ctx loc x k = f ctx loc (int_of_string x) k in
     Ast_pattern.of_func f'

   let const_int t = Ast_pattern.pconst_integer (int' t) Ast_pattern.none
   let eint t = Ast_pattern.pexp_constant (const_int t)
   let loc = Location.none
   let a = match [%expr Z3.mk_context []] with [%expr [%e? zz]] -> zz *)

let args () = Deriving.Args.(empty +> arg "bv_width" (eint __) +> flag "flag")
let impl_generator () = Deriving.Generator.V2.make (args ()) generate_impl
let add_ppx = Deriving.add "z3" ~str_type_decl:(impl_generator ())
