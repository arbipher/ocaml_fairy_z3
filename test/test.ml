module To_test = struct
  let magic = Ppx_z3.Lib.magic
end

let test_magic () =
  Alcotest.(check int) "check magic int" 42 To_test.magic ;
  Alcotest.(check int) "check magic int plus" 52 (To_test.magic + 10)

let () =
  let open Alcotest in
  run "Utils" [ ("magic-case", [ test_case "magic" `Quick test_magic ]) ]
