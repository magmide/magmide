type ast =
  | Add of (ast * ast)
  | Number of int

module Rust = struct
  external parse : string -> (ast, string) result = "rust_parse"
  external render : ast -> string -> unit = "rust_render"
end

(* Debug: (App Ref(Add, None) (App Ref(Number, None) Prim(2)) (App Ref(Number, *)
(* None) Prim(3))) *)

open Constrexpr

(* let foo : constr_expr_r = assert false *)

let ref s = CAst.make (CRef (Libnames.qualid_of_string s, None))

let arg x = (CAst.make x, None)

let rec hello (a : ast) : constr_expr_r CAst.t = CAst.make (match a with
  | Add (a, b) -> CApp (ref "Add", [hello a, None; hello b, None])
  | Number n -> CApp (ref "Number", [arg (CPrim (Number (NumTok.Signed.of_string (string_of_int n))))])
)

(* let show a = sexp_of_ast |> Sexp.to_string_hum *)
let rec show a = match a with
        | Add (a, b) -> "(" ^ show a ^ " + " ^ show b ^ ")"
        | Number n -> string_of_int n

let show_r x = match x with
        | Ok x -> show x
        | Error e -> e

  (* | Add (a, b) -> foo *)
  (* | Number n -> CApp (ref "Number", [(CAst.make (CPrim (Number (NumTok.Signed.of_string (string_of_int n)))), None)]) *)
  (* | Number n -> CApp (CAst.make (CRef (Libnames.qualid_of_string "Number", None)), [(CAst.make (CPrim (Number (NumTok.Signed.of_string (string_of_int n)))), None)]) *)
  (* | Number n -> (CApp (CRef ((Libnames.qualid_of_string "Number"), None)) None) *)
  (* | Number n -> CPrim (Number (NumTok.Signed.of_string (string_of_int n))) *)
