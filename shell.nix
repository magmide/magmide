{ pkgs ? import (fetchTarball "https://github.com/NixOS/nixpkgs/archive/52dc75a4fee3fdbcb792cb6fba009876b912bfe0.tar.gz") {} }:

let coq = pkgs.coq.override { customOCamlPackages = pkgs.ocamlPackages; };
in

pkgs.mkShell {
  buildInputs = with pkgs; [
    cargo
    coq
    dune_2
    just
    libffi
    libiconv
    llvmPackages_13.llvm
    (runCommand "lli-13" {} "mkdir -p $out/bin && ln -s ${llvmPackages_13.llvm}/bin/lli $out/bin/lli-13")
    ocaml
    ocamlPackages.zarith
  ];

  OCAMLPATH = "${coq}/lib:${pkgs.ocamlPackages.zarith}/lib/ocaml/4.13.1/site-lib";
  RUSTFLAGS = "-l LLVM-13";
}
