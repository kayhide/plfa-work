{ overlays ? [ ]
, nixpkgs ? <nixpkgs>
}:

let
  my-agda = pkgs.agda.withPackages (p: with p; [
    standard-library
  ]);

  env-overlay = self: super: {
    my-env = super.buildEnv {
      name = "my-env";
      paths = with self; [
        my-agda
      ];
    };
  };

  pkgs = import nixpkgs {
    overlays = overlays ++ [
      env-overlay
    ];
  };

in

pkgs.mkShell {
  buildInputs = with pkgs; [
    my-env
  ];
}
