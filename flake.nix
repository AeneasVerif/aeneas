{
  description = "Aeneas";

  inputs = {
    charon.url = "github:aeneasverif/charon";
    flake-utils.follows = "charon/flake-utils";
    nixpkgs.follows = "charon/nixpkgs";
  };

  outputs = { self, charon, flake-utils, nixpkgs }:
    flake-utils.lib.eachSystem [ "x86_64-linux" ] (system:
      let
        pkgs = import nixpkgs { inherit system; };
        ocamlPackages = pkgs.ocamlPackages;
        easy_logging = ocamlPackages.buildDunePackage rec {
          pname = "easy_logging";
          version = "0.8.2";
          src = pkgs.fetchFromGitHub {
            owner = "sapristi";
            repo = "easy_logging";
            rev = "v${version}";
            sha256 = "sha256-Xy6Rfef7r2K8DTok7AYa/9m3ZEV07LlUeMQSRayLBco=";
          };
          buildInputs = [ ocamlPackages.calendar ];
        };
        aeneas = ocamlPackages.buildDunePackage {
          pname = "aeneas";
          version = "0.1.0";
          src = ./.;
          buildInputs = [ easy_logging charon.packages.${system}.charon-ml ]
            ++ (with ocamlPackages; [
              calendar
              core_unix
              ppx_deriving
              visitors
              yojson
              zarith
            ]);
        };
      in {
        packages = {
          inherit aeneas;
          default = aeneas;
        };
      });
}
