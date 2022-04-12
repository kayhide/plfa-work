{
  description = "PLFA working environment";

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages."${system}";
      agda-pkgs = ps: with ps; [
        standard-library
      ];
    in
    {
      devShell."${system}" = pkgs.mkShell {
        buildInputs = [
          (pkgs.agda.withPackages agda-pkgs)
        ];
      };
    };
}
