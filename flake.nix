{
  description = "Flake for Julia and Henry's compiler";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    cs4410-flake.url = "github:qubitter/cs4410-flake";
  };

  outputs = { self, nixpkgs, ... } @ inputs :
    inputs.flake-utils.lib.eachDefaultSystem (system: 
      let
        name = "the-water-turned-the-compilers-gay";
        src = ./.;
        pkgs = nixpkgs.legacyPackages.${system};
      in {
        devShells.default = inputs.cs4410-flake.devShells.${system}.default;
      });
}
