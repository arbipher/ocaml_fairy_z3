open Ppxlib
module List = ListLabels
open Ast_builder.Default

(* type ocaml_primitive_type =
   | Typ_Int
   | Typ_float
   | Typ_bool
   | Typ_char
   | Typ_string *)
(* | Typ_bytes
   | Typ_array
   | Typ_list *)

let mod_id_of_str ~loc s =
  pmod_ident ~loc (Loc.make ~loc (lident s)

let primitive_case_of_lid lid =
  match lid with
  | Lident "int" -> Some Fairy_z3.Int_case
  | Lident "bool" -> Some Fairy_z3.Bool_case
  | Lident "string" -> Some Fairy_z3.String_case
  | _ -> None

let name_of_primitive_sort = function
  | Fairy_z3.Int_case -> "int"
  | Fairy_z3.Bool_case -> "bool"
  | Fairy_z3.String_case -> "string"
  | Fairy_z3.Bitvecetor_case -> "bitvector"

let unreachable_case loc =
  case ~lhs:(ppat_any ~loc) ~guard:None ~rhs:[%expr failwith "not here"]

let case_tag_of_Tag cd =
  let case_Tag = cd.pcd_name.txt in
  let case_tag = String.lowercase_ascii case_Tag in
  case_tag

let map_cd_names ~f cds = List.map cds ~f:(fun cd -> f cd.pcd_name.txt)
let mapi_cd_names ~f cds = List.mapi cds ~f:(fun i cd -> f i cd.pcd_name.txt)

let prefix_cd_names prefix cds =
  let f case_Tag =
    let case_tag = String.lowercase_ascii case_Tag in
    prefix ^ case_tag
  in
  map_cd_names ~f cds

let ps_tuple ~loc name len =
  List.init ~len ~f:(fun x -> x)
  |> List.map ~f:(fun i -> pvar ~loc (name ^ string_of_int i))
  |> ppat_tuple ~loc

let es_list ~loc name len =
  List.init ~len ~f:(fun x -> x)
  |> List.map ~f:(fun i -> evar ~loc (name ^ string_of_int i))
  |> elist ~loc

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
