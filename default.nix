{ pkgs ? (import <nixpkgs> {}), coq-version-or-url, shell ? false }:

let
  coq-version-parts = builtins.match "([0-9]+).([0-9]+)" coq-version-or-url;
  coqPackages =
    if coq-version-parts == null then
      pkgs.mkCoqPackages (import (fetchTarball coq-version-or-url) {})
    else
      pkgs."coqPackages_${builtins.concatStringsSep "_" coq-version-parts}";
in

with coqPackages;

pkgs.stdenv.mkDerivation {

  name = "coqhammer";

  buildInputs = with coq.ocamlPackages; [ ocaml findlib ]
    ++ pkgs.lib.optionals shell [ merlin ocp-indent ocp-index ];

  propagatedBuildInputs = [ coq ];

  src = if shell then null else ./.;

  installFlags = [
    "COQC=${coq}/bin/coqc"
    "COQTOP=${coq}/bin/coqtop"
    "COQMKFILE=${coq}/bin/coq_makefile"
    "COQBIN=$(out)/bin/"
    "COQLIB=$(out)/lib/coq/${coq.coq-version}/"
  ];
}
