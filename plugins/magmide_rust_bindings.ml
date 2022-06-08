open Base
open Sexplib.Std

type value =
  | Const of int
  | Ref of int
[@@deriving compare, sexp]

type instruction =
  | Return of value
  | Add of int * value * value
[@@deriving compare, sexp]

module Rust = struct
  external parse : string -> (instruction list, string) Result.t = "rust_parse"
  external parse_one : string -> (instruction, string) Result.t = "rust_parse_one"
  external render : instruction list -> string -> unit = "rust_render"
  external magmide : string -> (instruction list, string) Result.t = "rust_magmide"
end

open Constrexpr

let ref s = CRef (Libnames.qualid_of_string s, None)

let arg x = (CAst.make x, None)

let num n = arg (CPrim (Number (NumTok.Signed.of_string (Int.to_string n))))

let mkNum s n = CApp (CAst.make (ref s), [num n])

let hello_val (v : value) : constr_expr_r CAst.t = CAst.make (match v with
        | Const n -> mkNum "Const" n
        | Ref r -> mkNum "Ref" r
)

let hello (i : instruction) : constr_expr_r CAst.t = CAst.make (match i with
        | Return v -> CApp (CAst.make (ref "Return"), [hello_val v, None])
        | Add (r, op1, op2) -> CApp (CAst.make (ref "Add"), [num r; hello_val op1, None; hello_val op2, None])
)

let rec hellos (is : instruction list) : constr_expr_r CAst.t = CAst.make (match is with
        | x :: xs -> CApp (CAst.make (ref "cons"), [hello x, None; hellos xs, None])
        | [] -> ref "nil"
)

let foo: (instruction list, string) Result.t = Rust.parse ""

let%test_unit "parse noop" =
  [%test_eq: (instruction list, string) Result.t ] (Rust.parse "") (Ok [])
let%test_unit "parse return" =
  [%test_eq: (instruction list, string) Result.t ] (Rust.parse "return 4") (Ok [Return (Const 4)])
let%test_unit "parse return ref" =
  [%test_eq: (instruction list, string) Result.t ] (Rust.parse "return %4") (Ok [Return (Ref 4)])
let%test_unit "parse add" =
  [%test_eq: (instruction list, string) Result.t ] (Rust.parse "%0 = 1 + 1") (Ok [Add (0, Const(1), Const(1))])
let%test_unit "parse prog" =
  [%test_eq: (instruction list, string) Result.t ]
    (Rust.parse "%0 = 1 + 1\n%1 = %0 + %0\nreturn %1")
    (Ok [Add (0, (Const 1), (Const 1)); Add (1, Ref(0), Ref(0)); Return (Ref 1)])
