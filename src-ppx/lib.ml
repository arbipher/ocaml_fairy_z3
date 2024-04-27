(* it's obviously one working solution to write a minimal macro is
   ppx_z3: ocaml_type -> type_desc
   helper_defs : type_desc -> `let .. code`

   z3_helper: type_desc -> working_code
*)

(* ppx.metaquot missing
   1. antiquote %str
   2. antiquote %lid
*)

open Ppxlib
module List = ListLabels

[@@@warning "-27"]

let primitive_case_of_lid lid =
  match lid with
  | Lident "int" -> Some Fairy_z3.Int_case
  | Lident "bool" -> Some Fairy_z3.Bool_case
  | Lident "string" -> Some Fairy_z3.String_case
  | _ -> None

let unreachable_case loc =
  Ast_builder.Default.(
    case ~lhs:(ppat_any ~loc) ~guard:None ~rhs:[%expr failwith "not here"])

let name_of_primitive_sort = function
  | Fairy_z3.Int_case -> "int"
  | Fairy_z3.Bool_case -> "bool"
  | Fairy_z3.String_case -> "string"
  | Fairy_z3.Bitvecetor_case -> "bitvector"

let primitive_case_of_lid_exn lid = Option.get (primitive_case_of_lid lid)

let f payload =
  let checker =
    object
      inherit Ast_traverse.iter as super

      method! extension ext =
        match ext with
        | { txt = "forbidden"; _ }, _ ->
            failwith "Fordidden extension nodes are forbidden!"
        | _ -> super#extension ext (* Continue traversing inside the node *)
    end
  in
  let replace_constant =
    object
      inherit Ast_traverse.map
      method! int i = i + 1
    end
  in
  checker#payload payload ;
  replace_constant#payload payload

let magic = 42
let args () = Deriving.Args.(empty +> arg "bv_width" (eint __) +> flag "flag")
let _sort_of_record cdx = []
let eoo = Ast_builder.Default.estring ~loc:Location.none "42"
let estring s = Ast_builder.Default.estring ~loc:Location.none s
let pvar s = Ast_builder.Default.pvar ~loc:Location.none s
let evar s = Ast_builder.Default.evar ~loc:Location.none s

let ids_of_variant prefix cds =
  List.map cds ~f:(fun cd ->
      let case_Tag = cd.pcd_name.txt in
      let case_tag = String.lowercase_ascii case_Tag in
      prefix ^ case_tag)

let ids_of_variant_payload prefix cds =
  List.mapi cds ~f:(fun i cd -> (i, cd))
  |> List.filter_map ~f:(fun (i, cd) ->
         let case_Tag = cd.pcd_name.txt in
         let case_tag = String.lowercase_ascii case_Tag in
         let fid = prefix ^ case_tag in
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

let payload_pat_of_core_types ~loc cts =
  payload_cases_of_cts cts
  |> List.mapi ~f:(fun i _ -> pvar ("e" ^ string_of_int i))
  |> Ast_builder.Default.ppat_tuple ~loc

let pat_of_variant_case ~loc name cts =
  let tag_name = { txt = Longident.parse name.txt; loc = name.loc } in
  List.filter_map cts ~f:(fun ct ->
      match ct.ptyp_desc with
      | Ptyp_constr (lid_loc, _cts) ->
          Some (primitive_case_of_lid_exn lid_loc.txt)
      | _ -> None)
  |> List.mapi ~f:(fun i _ -> pvar ("e" ^ string_of_int i))
  |> Ast_builder.Default.ppat_tuple ~loc
  |> fun pat -> Ast_builder.Default.ppat_construct ~loc tag_name (Some pat)

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
                   [%expr Symbol.mk_string ctx [%e estring id]])
            |> Ast_builder.Default.elist ~loc:Location.none
          in
          let sorts_code =
            payload_cases_of_cts cts
            |> List.map ~f:(function
                 | Fairy_z3.Int_case -> [%expr Some int_sort]
                 | Fairy_z3.Bool_case -> [%expr Some bool_sort]
                 | Fairy_z3.String_case -> [%expr Some string_sort]
                 | Fairy_z3.Bitvecetor_case -> [%expr Some bitvector_sort])
            |> Ast_builder.Default.elist ~loc:Location.none
          in
          let all_ones_code =
            List.init ~len:(List.length cts) ~f:(fun _ -> 1)
            |> List.map ~f:(Ast_builder.Default.eint ~loc:Location.none)
            |> Ast_builder.Default.elist ~loc:Location.none
          in
          [%str
            let [%p pvar ("ctor_" ^ case_tag)] =
              Datatype.mk_constructor_s ctx [%e estring case_Tag]
                (Symbol.mk_string ctx [%e estring ("is-" ^ case_Tag)])
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
            let [%p pvar ("decl_" ^ case_tag)] =
              Datatype.Constructor.get_constructor_decl
                [%e evar ("ctor_" ^ case_tag)]]
      | Pcstr_record _lds -> [])
  |> List.concat

let inj_and_prj_of_variant loc cds =
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
  let more_code =
    let rzer_ids = ids_of_variant "rzer_" cds in
    let rzer_pats = List.map rzer_ids ~f:pvar in
    let pat_rzers = Ast_builder.Default.ppat_tuple ~loc rzer_pats in
    let rzer_id_exps =
      List.map rzer_ids ~f:evar |> Ast_builder.Default.pexp_tuple ~loc
    in

    let asor_ids = ids_of_variant_payload "asor_" cds in
    let asor_pats =
      List.map asor_ids ~f:(fun asor_case_ids ->
          List.map asor_case_ids ~f:pvar |> Ast_builder.Default.plist ~loc)
      |> Ast_builder.Default.plist ~loc
    in
    (* let asor_pats_listed =
         List.map asor_ids ~f:pvar
         |> List.map ~f:(fun pat -> Ast_builder.Default.plist ~loc [ pat ])
       in *)
    let pat_asors =
      List.map asor_ids ~f:(fun asor_case_ids ->
          List.map asor_case_ids ~f:pvar |> Ast_builder.Default.ppat_tuple ~loc)
      |> Ast_builder.Default.ppat_tuple ~loc
    in
    (* Ast_builder.Default.ppat_tuple ~loc asor_pats in *)
    let asor_id_exps =
      List.map asor_ids ~f:(fun asor_case_ids ->
          List.map asor_case_ids ~f:evar |> Ast_builder.Default.pexp_tuple ~loc)
      |> Ast_builder.Default.pexp_tuple ~loc
    in
    (* TODO: don't have to use this code. The pattern is only used for guarding *)
    let recognizer_code =
      [%str
        let [%p pat_rzers] =
          match Datatype.get_recognizers sort with
          | [%p Ast_builder.Default.plist ~loc rzer_pats] -> [%e rzer_id_exps]
          | _ -> failwith "recogniziers mismatch"

        let [%p pat_asors] =
          match Datatype.get_accessors sort with
          | [%p asor_pats] -> [%e asor_id_exps]
          | _ -> failwith "accessors mismatch"]
    in
    recognizer_code
  in
  let some_code =
    List.mapi cds ~f:(fun i cd ->
        let case_Tag = cd.pcd_name.txt in
        let case_tag = String.lowercase_ascii case_Tag in
        match cd.pcd_args with
        | Pcstr_tuple cts ->
            let list_of_core_types =
              payload_cases_of_cts cts
              |> List.mapi ~f:(fun i _ -> evar ("e" ^ string_of_int i))
              |> Ast_builder.Default.elist ~loc
            in

            let inj_code =
              [%str
                let [%p pvar ("inj_" ^ case_tag)] =
                 fun [%p payload_pat_of_core_types ~loc cts] ->
                  FuncDecl.apply
                    [%e evar ("decl_" ^ case_tag)]
                    [%e list_of_core_types]

                let [%p pvar ("is_" ^ case_tag)] =
                 fun e -> FuncDecl.apply [%e evar ("rzer_" ^ case_tag)] [ e ]]
            in
            let prj_code =
              List.mapi cts ~f:(fun i _ ->
                  [%str
                    let [%p pvar ("prj_" ^ case_tag ^ "_" ^ string_of_int i)] =
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

  more_code @ some_code

let box_of_variant loc td cds =
  let open Ast_builder.Default in
  let box_id = td.ptype_name.txt in
  let box_code =
    List.filter_map cds ~f:(fun cd ->
        let case_Tag = cd.pcd_name.txt in
        let case_tag = String.lowercase_ascii case_Tag in
        let inj_f = evar ~loc ("inj_" ^ case_tag) in
        match cd.pcd_args with
        | Pcstr_tuple cts ->
            let lhs = pat_of_variant_case ~loc cd.pcd_name cts in
            let rhs =
              let arg =
                payload_cases_of_cts cts
                |> List.mapi ~f:(fun i ps ->
                       let f = evar ~loc ("box_" ^ name_of_primitive_sort ps) in
                       let a = evar ~loc ("e" ^ string_of_int i) in
                       [%expr [%e f] [%e a]])
                |> Ast_builder.Default.pexp_tuple ~loc
              in
              [%expr [%e inj_f] [%e arg]]
            in
            Some (case ~lhs ~guard:None ~rhs)
        | Pcstr_record _lds -> None)
  in
  let unbox_code =
    List.filter_map cds ~f:(fun cd ->
        let case_Tag = cd.pcd_name.txt in
        let case_tag = String.lowercase_ascii case_Tag in
        let f_is = evar ~loc ("is_" ^ case_tag) in
        match cd.pcd_args with
        | Pcstr_tuple cts ->
            let lhs = Ast_builder.Default.ppat_any ~loc in
            let guard =
              Some [%expr Expr.simplify ([%e f_is] e) None |> unbox_bool]
            in
            let rhs =
              let tag_name =
                { txt = Longident.parse cd.pcd_name.txt; loc = cd.pcd_name.loc }
              in
              payload_cases_of_cts cts
              |> List.mapi ~f:(fun i ps ->
                     [%expr
                       Expr.simplify
                         ([%e
                            evar ~loc ("prj_" ^ case_tag ^ "_" ^ string_of_int i)]
                            e)
                         None
                       |> [%e evar ~loc ("unbox_" ^ name_of_primitive_sort ps)]])
              |> Ast_builder.Default.pexp_tuple ~loc
              |> fun e ->
              Ast_builder.Default.pexp_construct ~loc tag_name (Some e)
            in
            Some (case ~lhs ~guard ~rhs)
        | Pcstr_record _lds -> None)
    @ [ unreachable_case loc ]
  in
  let box_code =
    [%str
      let [%p pvar ~loc ("box_" ^ box_id)] = [%e pexp_function ~loc box_code]

      let [%p pvar ~loc ("unbox_" ^ box_id)] =
       fun e -> [%e pexp_match ~loc [%expr e] unbox_code]]
  in
  box_code

let generate_impl ~ctxt (_rec_flag, type_declarations) bv_width_opt flag =
  let _b = flag in
  let bv_width = Option.value bv_width_opt ~default:63 in
  let loc = Expansion_context.Deriver.derived_item_loc ctxt in
  let whole_code =
    List.map type_declarations ~f:(function
      | { ptype_kind = Ptype_variant cds; ptype_loc = loc; ptype_name; _ } as td
        ->
          let ctor_ids = ids_of_variant "ctor_" cds in
          let ctor_sort_opts =
            List.map ctor_ids ~f:(fun pid ->
                [%expr [%e Ast_builder.Default.evar ~loc:Location.none pid]])
            |> Ast_builder.Default.elist ~loc:Location.none
          in
          let t_ml =
            Ast_builder.Default.ptyp_constr ~loc:Location.none
              { txt = Longident.parse ptype_name.txt; loc = Location.none }
              []
          in
          let defs =
            [ [%stri module Not_here = struct end] ]
            @ [%str
                open Z3

                type t_ml = [%t t_ml]
                type t_z3 = Expr.expr

                let ctx = mk_context []
                let int_sort = Arithmetic.Integer.mk_sort ctx
                let bool_sort = Boolean.mk_sort ctx
                let string_sort = Seq.mk_string_sort ctx
                let bv_width = [%e Ast_builder.Default.eint ~loc bv_width]
                let bitvector_sort = BitVector.mk_sort ctx bv_width
                let box_int i = Arithmetic.Integer.mk_numeral_i ctx i
                let box_bool b = Boolean.mk_val ctx b
                let box_string s = Seq.mk_string ctx s

                let unbox_int e =
                  e |> Arithmetic.Integer.get_big_int
                  |> Big_int_Z.int_of_big_int

                let unbox_bool v =
                  match Boolean.get_bool_value v with
                  | L_TRUE -> true
                  | L_FALSE -> false
                  | L_UNDEF -> false

                let unbox_bool_exn v =
                  match Boolean.get_bool_value v with
                  | L_TRUE -> true
                  | L_FALSE -> false
                  | L_UNDEF -> failwith "L_UNDEF"

                let unbox_string e = Seq.get_string ctx e

                let box_bitvector i =
                  BitVector.mk_numeral ctx (Int.to_string i) bv_width]
            @ ctors_of_variant loc cds
            @ [%str
                let sort =
                  Datatype.mk_sort_s ctx "This_sort" [%e ctor_sort_opts]]
            @ decls_of_variant loc cds
            @ inj_and_prj_of_variant loc cds
            @ box_of_variant loc td cds
          in
          let mb =
            Ast_builder.Default.module_binding ~loc:Location.none
              ~name:Location.{ txt = Some "Z3_this"; loc = none }
              ~expr:(Ast_builder.Default.pmod_structure ~loc:Location.none defs)
          in
          [ Ast_builder.Default.pstr_module ~loc:Location.none mb ]
      | _ -> [])
    |> List.concat
  in
  whole_code

let impl_generator () = Deriving.Generator.V2.make (args ()) generate_impl
let stringify = Deriving.add "z3" ~str_type_decl:(impl_generator ())
