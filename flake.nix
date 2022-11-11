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
          src = ./compiler;
          buildInputs = [ easy_logging charon.packages.${system}.charon-ml ]
            ++ (with ocamlPackages; [
              calendar
              core_unix
              ppx_deriving
              visitors
              yojson
              zarith
            ]);
          afterBuild = ''
          echo charon.packages.${system}.tests
          '';
        };
        # Make sure we don't need to recompile the package whenever we make
        # unnecessary changes - we list the exact files and folders the package
        # depends upon.
        aeneas-tests = pkgs.stdenv.mkDerivation {
          name = "aeneas_tests";
          src = pkgs.lib.cleanSourceWith {
            src = ./.;
            filter = path: type:
              path == toString ./Makefile
              || pkgs.lib.hasPrefix (toString ./compiler) path
              || pkgs.lib.hasPrefix (toString ./backends) path
              || pkgs.lib.hasPrefix (toString ./tests) path;
          };
          buildPhase = ''
          # We need to provide the paths to the Charon tests derivations
          export CHARON_TESTS_REGULAR_DIR=${charon.checks.${system}.tests}
          export CHARON_TESTS_POLONIUS_DIR=${charon.checks.${system}.tests-polonius}

          # Copy the Aeneas executable, and update the path to it
          cp ${aeneas}/bin/aeneas_driver aeneas.exe
          export AENEAS_EXE=./aeneas.exe

          # Run the tests
          make tests
          '';
          # Tests don't generate anything new as the generated files are
          # versionned, but the installation phase still needs to prodocue
          # something, otherwise Nix will consider the build has failed.
          installPhase = "touch $out";
        };
      in {
        packages = {
          inherit aeneas;
          default = aeneas;
        };
        checks = { inherit aeneas aeneas-tests; };
        hydraJobs = { inherit aeneas aeneas-tests; };
      });
}
