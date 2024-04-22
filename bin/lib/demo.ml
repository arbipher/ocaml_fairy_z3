(* | Baz of int *)
type a = Foo of string * int [@@deriving z3 ~flag ~bv_width:52]
type b = Stdlib.String.t

let foo_string t = t

module M = struct
  let m1 = 1
  let m2 = 2
end
