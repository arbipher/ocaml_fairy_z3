(* | Baz of int *)
type a = Foo of string * int [@@deriving z3 ~flag ~bv_width:52]
type b = Stdlib.String.t
type c = int
type d = c

let f x = match x with Foo (s, i) -> (s, i)
let foo_string t = t
let foo a b = a + b
let a, b, c = (1, 2, 3)

module M = struct
  let m1 = 1
  let m2 = 2
end
