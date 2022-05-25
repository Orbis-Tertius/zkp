{
  description = "Denotational Zero Knowledge Proofs";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
    agda.url = "github:agda/agda";
  };

  outputs = { self, nixpkgs, flake-utils, agda, ... }:
  flake-utils.lib.eachDefaultSystem
  (system:
  let
    pkgs = import nixpkgs { inherit system; };
  in
  {
    devShell = pkgs.mkShell {
      buildInputs = [
        pkgs.nixpkgs-fmt
        (pkgs.agda.withPackages (ps: [
          (ps.standard-library.overrideAttrs (oldAttrs: {
            version = "2.0";
            src =  pkgs.fetchFromGitHub {
              repo = "agda-stdlib";
              owner = "agda";
              rev = "6e79234dcd47b7ca1d232b16c9270c33ff42fb84";
              sha256 = "0n1xksqz0d2vxd4l45mxkab2j9hz9g291zgkjl76h5cn0p9wylk3";
            };
          }))
          ps.agda-categories
        ]))
      ];
    };
  }
  );

}
