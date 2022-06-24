{
  description = "Denotational Zero Knowledge Proofs";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  inputs.agda-stdlib = { url = "github:agda/agda-stdlib"; flake = false; };

  outputs = { self, nixpkgs, ... }@inputs:
    let
      supportedSystems = [ "x86_64-linux" "x86_64-darwin" "aarch64-linux" "aarch64-darwin" ];
      forAllSystems = nixpkgs.lib.genAttrs supportedSystems;
      nixpkgsFor = forAllSystems (system: nixpkgs.legacyPackages.${system});
    in
    {
      devShells = forAllSystems (system: {
        devShell.${system} = nixpkgsFor.${system}.mkShell {
          packages = [
            (nixpkgsFor.${system}.agda.withPackages (ps: [
              (ps.standard-library.overrideAttrs (oldAttrs: { version = "2.0-dev"; src = inputs.agda-stdlib; }))
              ps.agda-categories
            ]))
          ];
        };
      });
      herculesCI.ciSystems = [ "x86_64-linux" ];
    };
}
