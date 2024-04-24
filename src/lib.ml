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
  | Lident "int" -> Some Z3_datatype_helper.Int_case
  | Lident "bool" -> Some Z3_datatype_helper.Bool_case
  | Lident "string" -> Some Z3_datatype_helper.String_case
  | _ -> None

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
  List.mapi cds ~f:(fun i pcd -> (i, pcd))
  |> List.filter_map ~f:(fun (i, pcd) ->
         match pcd.pcd_args with
         | Pcstr_tuple cts ->
             let ctor_id = pcd.pcd_name.txt in
             let ctor_lc_id = String.lowercase_ascii ctor_id in
             let ctor_pid = prefix ^ ctor_lc_id in
             Some ctor_pid
         | _ -> None)

let payload_cases_of_cts cts =
  List.filter_map cts ~f:(fun ct ->
      match ct.ptyp_desc with
      | Ptyp_constr (lid_loc, _cts) ->
          Some (primitive_case_of_lid_exn lid_loc.txt)
      | _ -> None)

let sort_of_variant loc cds =
  List.mapi cds ~f:(fun i pcd ->
      match pcd.pcd_args with
      | Pcstr_tuple cts ->
          let ctor_id = pcd.pcd_name.txt in
          let ctor_lc_id = String.lowercase_ascii ctor_id in
          let acceesor_code =
            cts
            |> List.mapi ~f:(fun i _ -> i)
            |> List.map ~f:(fun si -> ctor_id ^ "-" ^ string_of_int si)
            |> List.map ~f:(fun id ->
                   [%expr Symbol.mk_string ctx [%e estring id]])
            |> Ast_builder.Default.elist ~loc:Location.none
          in
          let sorts_code =
            payload_cases_of_cts cts
            |> List.map ~f:(function
                 | Z3_datatype_helper.Int_case -> [%expr Some int_sort]
                 | Z3_datatype_helper.Bool_case -> [%expr Some bool_sort]
                 | Z3_datatype_helper.String_case -> [%expr Some string_sort]
                 | Z3_datatype_helper.Bitvecetor_case ->
                     [%expr Some bitvector_sort])
            |> Ast_builder.Default.elist ~loc:Location.none
          in
          let all_ones_code =
            List.init ~len:(List.length cts) ~f:(fun _ -> 1)
            |> List.map ~f:(Ast_builder.Default.eint ~loc:Location.none)
            |> Ast_builder.Default.elist ~loc:Location.none
          in
          [%str
            let [%p pvar ("ctor_" ^ ctor_lc_id)] =
              Datatype.mk_constructor_s ctx [%e estring ctor_id]
                (Symbol.mk_string ctx [%e estring ("is-" ^ ctor_id)])
                [%e acceesor_code] [%e sorts_code] [%e all_ones_code]

            let [%p pvar ("decl_" ^ ctor_lc_id)] =
              Datatype.Constructor.get_constructor_decl
                [%e evar ("ctor_" ^ ctor_lc_id)]]
      | Pcstr_record _lds -> [])
  |> List.concat

let inj_and_prj_of_sort loc cds =
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
  let _ = loc in

  let more_code =
    let rzer_ids = ids_of_variant "rzer_" cds in
    let rzer_pats = List.map rzer_ids ~f:pvar in
    let pat_rzers = Ast_builder.Default.ppat_tuple ~loc rzer_pats in
    let rzer_id_exps = List.map rzer_ids ~f:evar in
    let asor_ids = ids_of_variant "asor_" cds in
    let asor_pats = List.map asor_ids ~f:pvar in
    let asor_pats_listed =
      List.map asor_ids ~f:pvar
      |> List.map ~f:(fun pat -> Ast_builder.Default.plist ~loc [ pat ])
    in
    let pat_asors = Ast_builder.Default.ppat_tuple ~loc asor_pats in
    let asor_id_exps = List.map asor_ids ~f:evar in
    (* TODO: don't have to use this code. The pattern is only used for guarding *)
    (* TODO: accessor may be buggy *)
    let recognizer_code =
      [%str
        let [%p pat_rzers] =
          match Datatype.get_recognizers sort with
          | [%p Ast_builder.Default.plist ~loc rzer_pats] ->
              [%e Ast_builder.Default.pexp_tuple ~loc rzer_id_exps]
          | _ -> failwith "recogniziers mismatch"

        let [%p pat_asors] =
          match Datatype.get_accessors sort with
          | [%p Ast_builder.Default.plist ~loc asor_pats_listed] ->
              [%e Ast_builder.Default.pexp_tuple ~loc asor_id_exps]
          | _ -> failwith "recogniziers mismatch"]
    in
    recognizer_code
  in
  let some_code =
    List.mapi cds ~f:(fun i cd ->
        match cd.pcd_args with
        | Pcstr_tuple cts ->
            let ctor_id = cd.pcd_name.txt in
            let ctor_lc_id = String.lowercase_ascii ctor_id in
            let pat_of_core_types =
              payload_cases_of_cts cts
              |> List.mapi ~f:(fun i _ -> pvar ("e" ^ string_of_int i))
              |> Ast_builder.Default.ppat_tuple ~loc
            in
            let list_of_core_types =
              payload_cases_of_cts cts
              |> List.mapi ~f:(fun i _ -> evar ("e" ^ string_of_int i))
              |> Ast_builder.Default.elist ~loc
            in
            let code =
              [%str
                let [%p pvar ("inj_" ^ ctor_lc_id)] =
                 fun [%p pat_of_core_types] ->
                  FuncDecl.apply
                    [%e evar ("decl_" ^ ctor_lc_id)]
                    [%e list_of_core_types]

                let [%p pvar ("is_" ^ ctor_lc_id)] =
                 fun [%p pat_of_core_types] ->
                  FuncDecl.apply
                    [%e evar ("rzer_" ^ ctor_lc_id)]
                    [%e list_of_core_types]

                let [%p pvar ("prj_" ^ ctor_lc_id)] =
                 fun [%p pat_of_core_types] ->
                  FuncDecl.apply
                    [%e evar ("asor_" ^ ctor_lc_id)]
                    [%e list_of_core_types]]
            in

            code
        | Pcstr_record _lds -> [])
    |> List.concat
  in

  more_code @ some_code

let generate_impl ~ctxt (_rec_flag, type_declarations) option1 flag =
  let _b = flag in
  let _some_i = option1 in
  let loc = Expansion_context.Deriver.derived_item_loc ctxt in
  let whole_code =
    List.map type_declarations ~f:(function
      | { ptype_kind = Ptype_variant cds; ptype_loc = loc; ptype_name; _ } ->
          let one_full_variant_code = sort_of_variant loc cds in
          let ctor_ids = ids_of_variant "ctor_" cds in
          let ctor_sort_opts =
            List.map ctor_ids ~f:(fun pid ->
                [%expr [%e Ast_builder.Default.evar ~loc:Location.none pid]])
            |> Ast_builder.Default.elist ~loc:Location.none
          in
          let ptype_name = ptype_name.txt in
          let t_ml =
            Ast_builder.Default.ptyp_constr ~loc:Location.none
              { txt = Longident.parse ptype_name; loc = Location.none }
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
                let bitvector_sort w = BitVector.mk_sort ctx w
                (* let x = [%e eoo] *)]
            @ one_full_variant_code
            @ [%str
                let sort =
                  Datatype.mk_sort_s ctx "This_sort" [%e ctor_sort_opts]]
            @ inj_and_prj_of_sort loc cds
            @ [%str
                let box : t_ml -> t_z3 = failwith "not yet"
                let unbox : t_z3 -> t_ml = failwith "not yet"
                (* end *)]
          in
          let me = Ast_builder.Default.pmod_structure ~loc:Location.none defs in
          let mb =
            Ast_builder.Default.module_binding ~loc:Location.none
              ~name:Location.{ txt = Some "Z3_this"; loc = none }
              ~expr:me
          in
          [ Ast_builder.Default.pstr_module ~loc:Location.none mb ]
      | _ -> [])
    |> List.concat
  in
  whole_code

let impl_generator () = Deriving.Generator.V2.make (args ()) generate_impl
let stringify = Deriving.add "z3" ~str_type_decl:(impl_generator ())

(*
               let dynamic_node =
                 Ast_builder.Default.estring ~loc pcd.pcd_name.txt
               in
               (* [%stri type t[%%s "good"] = int] *)
               [%stri let a_ = [%e dynamic_node]]
               (* let dynamic_node =
                    Ast_builder.Default.estring ~loc pcd.pcd_name.txt
                  in
                  [%stri let x = [%e dynamic_node] ^ "some_fixed_suffix"] *)
               (* [%stri
                  type t
                  [@@subst let t : string = name]
                  [@@for name := [ "t1"; "t2"; "t3" ]]] *)
*)

(* See "Generating code" chapter *)
(* [%expr 1 + 1] *)

(* [
     Ast_builder.Default.(pstr_eval ~loc (estring ~loc s) []);
     [%stri let a = 1];
     [%stri type b = Bar];
   ]
   @ [%str "ahhh"] @ dd *)
(* [%type: int -> string] *)

(* let sd = Format.asprintf "%a" Pprintast.core_type (List.hd cts) in *)
