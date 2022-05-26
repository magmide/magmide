type ast =
  | Add of (ast * ast)
  | Number of int

let rec stringify = function
  | Add (a, b) -> "(" ^ stringify a ^ " + " ^ stringify b ^ ")"
  | Number n -> string_of_int n

module Rust = struct
  external parse : string -> (ast, string) result = "rust_parse"
  external render : ast -> string -> unit = "rust_render"
end

let bloop = function
  | Ok a -> a
  | Error a -> a

let test_twice () = Alcotest.(check int) "Multiply by 2" 20 (10 * 2)
let test_num () = Alcotest.(check string) "parse 4" "4"
        (bloop (Result.map stringify (Rust.parse "4")))

let () =
  let open Alcotest in
  run "Tests"
    [
      ( "basic",
        [
          test_case "twice" `Quick test_twice;
          test_case "four" `Quick test_num;
        ]
      );
    ];
