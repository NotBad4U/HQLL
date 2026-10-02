{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build from the local sources,
  ## either using nixpkgs data or the overlays located in `.nix/rocq-overlays`
  ## and `.nix/coq-overlays`
  ## Will determine the default main-job of the bundles defined below
  attribute = "hqll";

  ## Our package is a `coqPackages` overlay (`.nix/coq-overlays/hqll`), because
  ## mathcomp-qbs needs `mathcomp-algebra-tactics`, which has no `rocqPackages`
  ## version in nixpkgs.
  no-rocq-yet = true;

  ## Indicate the relative location of your _CoqProject
  coqproject = "_CoqProject";

  ## Extra packages to have around.  The toolbox already puts `coq-lsp` and
  ## the Coq-era `vscoq-language-server` in the shell; this adds the Rocq one,
  ## which is what the VsRocq editor extension talks to.
  buildInputs = [ "vsrocq-language-server" ];

  ## select an entry to build in the following `bundles` set
  ## defaults to "default"
  default-bundle = "9.1";

  ## write one `bundles.name` attribute set per
  ## alternative configuration
  ## When generating GitHub Action CI, one workflow file
  ## will be created per bundle
  ##
  ## Pinned to Rocq 9.1 / math-comp 2.5.0: mathcomp-qbs declares
  ## `rocq < 9.2`, and nixpkgs has no `mathcomp-algebra-tactics` for 9.2.
  ## With these choices nixpkgs picks mathcomp-analysis 1.16.0 and
  ## mathcomp-algebra-tactics 1.2.7.

  bundles."9.1" = {
    rocqPackages = {
      rocq-core.override.version = "9.1";
      mathcomp.override.version = "2.5.0";
    };
    coqPackages.coq.override.version = "9.1";
  };

  ## Cachix caches to use in CI
  ## Below we list some standard ones
  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};

  ## If you have write access to one of these caches you can
  ## provide the auth token or signing key through a secret
  ## variable on GitHub. Then, you should give the variable
  ## name here. For instance, coq-community projects can use
  ## the following line instead of the one above:
  # cachix.coq-community.authToken = "CACHIX_AUTH_TOKEN";

  ## Or if you have a signing key for a given Cachix cache:
  # cachix.my-cache.signingKey = "CACHIX_SIGNING_KEY"

  ## Note that here, CACHIX_AUTH_TOKEN and CACHIX_SIGNING_KEY
  ## are the names of secret variables. They are set in
  ## GitHub's web interface.
}
