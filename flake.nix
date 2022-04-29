{
  description = "Denotational Zero Knowledge Proofs";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
  flake-utils.lib.eachDefaultSystem
  (system:
  let
    pkgs = import nixpkgs { inherit system; };
    agdaPkgs = pkgs;
  in
  {
    devShell = pkgs.mkShell {
      buildInputs = [
        pkgs.nixpkgs-fmt
        (agdaPkgs.agda.withPackages (ps: [
          ps.standard-library
        ]))
      ];
    };
  }
  );

}
