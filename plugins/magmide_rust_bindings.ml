type ast =
  | Add of (ast * ast)
  | Number of int

module Rust = struct
  external parse : string -> (ast, string) result = "rust_parse"
  external render : ast -> string -> unit = "rust_render"
end
