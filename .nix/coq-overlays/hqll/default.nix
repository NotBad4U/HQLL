## Local package definition for this development.
## It is not in nixpkgs, so we describe it here; the coq-nix-toolbox
## overrides `version` with the local sources when building the main job.
## Doc: https://nixos.org/manual/nixpkgs/stable/#sec-language-coq

{
  lib,
  mkCoqDerivation,
  mathcomp-qbs,
  version ? null,
}:

mkCoqDerivation {
  pname = "hqll";
  owner = "NotBad4U";
  repo = "HQLL";

  inherit version;
  ## No release: the version is always the local sources.
  defaultVersion = null;

  ## mathcomp-qbs propagates math-comp, analysis, HB and algebra-tactics.
  propagatedBuildInputs = [ mathcomp-qbs ];

  preBuild = ''
    rocq makefile -f _CoqProject -o Makefile
  '';

  meta = {
    description = "Higher-order quantitative logic over quasi-Borel spaces";
  };
}
