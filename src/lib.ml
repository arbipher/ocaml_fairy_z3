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

let ctor_pids_of_variant cds =
  List.mapi cds ~f:(fun i pcd -> (i, pcd))
  |> List.filter_map ~f:(fun (i, pcd) ->
         match pcd.pcd_args with
         | Pcstr_tuple cts ->
             let ctor_id = pcd.pcd_name.txt in
             let ctor_pid = "ctor_" ^ String.lowercase_ascii ctor_id in
             Some ctor_pid
         | _ -> None)

let sort_of_variant loc cds =
  List.mapi cds ~f:(fun i pcd ->
      match pcd.pcd_args with
      | Pcstr_tuple cts ->
          (* let sd = Format.asprintf "%a" Pprintast.core_type (List.hd cts) in *)

          (* let _aa =
               List.filter_map cts ~f:(fun ct ->
                   match ct.ptyp_desc with
                   | Ptyp_constr (lid_loc, _cts) -> (
                       match primitive_case_of_lid lid_loc.txt with
                       | Some case ->
                           Some
                             (Ast_builder.Default.estring ~loc:lid_loc.loc
                                (Z3_datatype_helper.string_of_primitive_case case))
                       | None -> None)
                   | _ -> None)
             in *)
          let tlen = List.length cts in
          let ctor_id = pcd.pcd_name.txt in
          let ctor_pid = "ctor_" ^ String.lowercase_ascii ctor_id in
          let rzer_id = "is-" ^ ctor_id in
          let accessor_ids =
            List.init ~len:tlen ~f:(fun x -> x)
            |> List.map ~f:(fun si -> ctor_id ^ "-" ^ string_of_int si)
          in
          let acceesor_code =
            List.map
              ~f:(fun id -> [%expr Symbol.mk_string ctx [%e estring id]])
              accessor_ids
            |> Ast_builder.Default.elist ~loc:Location.none
          in
          (* [%expr
                 Some [%e Ast_builder.Default.evar ~loc:Location.none pid]] *)
          let payload_cases =
            List.filter_map cts ~f:(fun ct ->
                match ct.ptyp_desc with
                | Ptyp_constr (lid_loc, _cts) ->
                    Some (primitive_case_of_lid_exn lid_loc.txt)
                | _ -> None)
          in
          let sorts_code =
            List.map payload_cases ~f:(function
              | Z3_datatype_helper.Int_case -> [%expr Some int_sort]
              | Z3_datatype_helper.Bool_case -> [%expr Some bool_sort]
              | Z3_datatype_helper.String_case -> [%expr Some string_sort]
              | Z3_datatype_helper.Bitvecetor_case ->
                  [%expr Some bitvector_sort])
            |> Ast_builder.Default.elist ~loc:Location.none
          in

          let all_ones_code =
            List.init ~len:tlen ~f:(fun _ -> 1)
            |> List.map ~f:(Ast_builder.Default.eint ~loc:Location.none)
            |> Ast_builder.Default.elist ~loc:Location.none
          in
          let ctor_code =
            let pat =
              Ast_builder.Default.ppat_var ~loc:Location.none
                Location.{ txt = ctor_pid; loc = none }
            in
            let ctor_exp_code =
              [%expr
                Datatype.mk_constructor_s ctx [%e estring ctor_id]
                  (Symbol.mk_string ctx [%e estring rzer_id])
                  [%e acceesor_code] [%e sorts_code] [%e all_ones_code]]
            in
            let let_code =
              Ast_builder.Default.value_binding ~loc:Location.none ~pat
                ~expr:ctor_exp_code
            in
            Ast_builder.Default.pstr_value ~loc:Location.none Nonrecursive
              [ let_code ]
          in
          (*
             let ctor =
                             Datatype.mk_constructor_s ctx [%e estring ctor_id]
                               (Symbol.mk_string ctx [%e estring rzer_id])
                               [%e acceesor_code] [%e sorts_code] [%e all_ones_code]
          *)
          (* let sd = Fmt.(str "%a" (Dump.list Pprintast.core_type) cts) in
             [ Ast_builder.Default.estring ~loc ("vt-" ^ sd ^ pcd.pcd_name.txt) ] *)
          [%str [%%i ctor_code]]
      | Pcstr_record _lds ->
          (* Ast_builder.Default.estring ~loc ("vr-" ^ pcd.pcd_name.txt) *)
          [])
  |> List.concat

let generate_impl ~ctxt (_rec_flag, type_declarations) option1 flag =
  let _b = flag in
  let _some_i = option1 in
  let loc = Expansion_context.Deriver.derived_item_loc ctxt in
  let whole_code =
    List.map type_declarations ~f:(function
      | { ptype_kind = Ptype_variant cds; ptype_loc = loc; _ } ->
          let one_full_variant_code = sort_of_variant loc cds in
          let ctor_pids = ctor_pids_of_variant cds in
          let ctor_sort_opts =
            List.map ctor_pids ~f:(fun pid ->
                [%expr [%e Ast_builder.Default.evar ~loc:Location.none pid]])
            |> Ast_builder.Default.elist ~loc:Location.none
          in
          let defs =
            [ [%stri module Not_here = struct end] ]
            @ [%str
                (* module Z3_datatype_a = struct *)
                open Z3

                (* type t_ml = T *)
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
                  Datatype.mk_sort_s ctx "This_sort" [%e ctor_sort_opts]
                (* [
                     [%e Ast_builder.Default.evar ~loc:Location.none ctor_pid];
                   ] *)

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
