{
  description = "Denotational Zero Knowledge Proofs";
  inputs = 
  {
    flake-compat = 
    {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
    agda.url = "github:agda/agda";
  };

  outputs = { self, nixpkgs, agda, ... }:
  let
    pkgs = nixpkgs.legacyPackages.x86_64-linux;
  in
  {
    # restrict which systems to build in CI
    herculesCI.ciSystems = ["x86_64-linux"];
    devShells.x86_64-linux.default = pkgs.mkShell 
    {
      buildInputs = 
      [
        pkgs.nixpkgs-fmt
        (pkgs.agda.withPackages (ps: [
          (ps.standard-library.overrideAttrs (oldAttrs: {
            version = "2.0";
            src =  pkgs.fetchFromGitHub 
            {
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
  };
}
