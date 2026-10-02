## Quasi-Borel spaces on top of math-comp analysis.
## https://github.com/LLM4Rocq/mathcomp-qbs
## Not in nixpkgs and has no release, so we pin a commit of `main`.
## It is a `coqPackages` overlay (not `rocqPackages`) because it needs
## `mathcomp-algebra-tactics`, which nixpkgs only ships as a Coq package.
## Doc: https://nixos.org/manual/nixpkgs/stable/#sec-language-coq

{
  lib,
  mkCoqDerivation,
  hierarchy-builder,
  mathcomp-analysis,
  mathcomp-algebra-tactics,
  version ? null,
}:

mkCoqDerivation {
  pname = "mathcomp-qbs";
  owner = "LLM4Rocq";
  repo = "mathcomp-qbs";

  inherit version;
  ## Upstream's opam file: Rocq >= 9.0 < 9.2, analysis >= 1.15 < 1.17.
  defaultVersion = "2026-05-15";
  release."2026-05-15" = {
    rev = "16a6735ed64aea71c417125fbd420eb6af33b002";
    sha256 = "1d7f575syf124i850igk255xsfk1508ibc2ydpg6v6dwlfwlx8jy";
  };

  propagatedBuildInputs = [
    hierarchy-builder
    mathcomp-analysis
    mathcomp-algebra-tactics
  ];

  ## The repository only ships a `_CoqProject` (`-Q theories QBS`).
  preBuild = ''
    rocq makefile -f _CoqProject -o Makefile
  '';

  meta = {
    description = "Quasi-Borel spaces in Rocq, built on math-comp analysis";
    license = lib.licenses.cecill-c;
  };
}
