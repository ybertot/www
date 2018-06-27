{ pkgs ? (import <nixpkgs> {})
, ocamlPackages ? pkgs.ocaml-ng.ocamlPackages_4_06
}:

with pkgs;

stdenv.mkDerivation rec {

  name = "coq_website";
  src = null;

  buildInputs = [
    ocaml
    python3
  ];

}
