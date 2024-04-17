{
  description = "Aeneas";

  inputs = {
    # Remark: when adding inputs here, don't forget to also add them in the list
    # of outputs below!
    charon.url = "github:aeneasverif/charon";
    flake-utils.follows = "charon/flake-utils";
    nixpkgs.follows = "charon/nixpkgs";
    hacl-nix.url = "github:hacl-star/hacl-nix";
    flake-compat.url = "github:nix-community/flake-compat";
  };

  # Remark: keep the list of outputs in sync with the list of inputs above
  # (see above remark)
  outputs = { self, charon, flake-utils, nixpkgs, hacl-nix, flake-compat }:
    flake-utils.lib.eachSystem [ "x86_64-linux" ] (system:
      let
        pkgs = import nixpkgs { inherit system; };
        ocamlPackages = pkgs.ocamlPackages;
        coqPackages = pkgs.coqPackages;
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
          duneVersion = "3";
          src = ./compiler;
          propagatedBuildInputs = [
            easy_logging charon.packages.${system}.charon-ml
            ] ++ (with ocamlPackages; [
              calendar
              core_unix
              ppx_deriving
              visitors
              yojson
              zarith
              ocamlgraph
              unionFind
            ]);
          afterBuild = ''
          echo charon.packages.${system}.tests
          '';
        };
        # Run the translation on various files.
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
            cp ${aeneas}/bin/aeneas aeneas
            export AENEAS_EXE=./aeneas

            # Copy the tests
            mkdir tests-copy
            cp -r tests tests-copy

            # TODO: remove the test files to make sure we regenerate exactly
            # the files which are checked out (we have to be careful about
            # files like lakefile.lean, and the user hand-written files)

            # Run the tests - remark: we could remove the file
            make test-all -j $NIX_BUILD_CORES

            # Check that there are no differences between the generated tests
            # and the original tests
            if [[ $(diff -rq tests tests-copy) ]]; then
              echo "Ok: the regenerated test files are the same as the checked out files"
            else
              echo "Error: the regenerated test files differ from the checked out files"
              exit 1
            fi
          '';
          # Tests don't generate anything new as the generated files are
          # versionned, but the installation phase still needs to produce
          # something, otherwise Nix will consider the build has failed.
          installPhase = "touch $out";
        };
        # Replay the F* proofs.
        aeneas-verify-fstar = pkgs.stdenv.mkDerivation {
          name = "aeneas_verify_fstar";
          src = ./tests/fstar;
          FSTAR_EXE = "${hacl-nix.packages.${system}.fstar}/bin/fstar.exe";
          buildPhase= ''
            make prepare-projects
            make verify -j $NIX_BUILD_CORES
          '';
          # The tests don't generate anything - TODO: actually they do
          installPhase = "touch $out";
        };
        # Replay the Coq proofs.
        aeneas-verify-coq = pkgs.stdenv.mkDerivation {
          name = "aeneas_verify_coq";
          src = ./tests/coq;
          buildInputs = [ pkgs.coq ];
          buildPhase= ''
            make prepare-projects
            make verify -j $NIX_BUILD_CORES
          '';
          # The tests don't generate anything - TODO: actually they do
          installPhase = "touch $out";
        };
        # Replay the HOL4 proofs
        #
        # Remark: we tried to have two targets, one for ./backends/hol4 and
        # one for ./tests/hol4 but we didn't manage to make ./tests/hol4
        # reuse the build of ./backends/hol4.
        aeneas-verify-hol4 = pkgs.stdenv.mkDerivation {
          name = "aeneas_verify_hol4";
          # Remark: we tried to filter the sources to only include ./backends/hol4
          # and ./tests/hol4 (see comment below), but it didn't work
          src = ./.;
          # src = pkgs.lib.cleanSourceWith {
          #   src = ./.;
          #   filter = path: type:
          #     pkgs.lib.hasPrefix (toString ./backends/hol4) path
          #     || pkgs.lib.hasPrefix (toString ./tests/hol4) path;
          # };
          buildInputs = [ pkgs.hol ];
          buildPhase= ''
            cd ./tests/hol4
            make prepare-projects
            make verify -j $NIX_BUILD_CORES
          '';
          # The build doesn't generate anything
          installPhase = "touch $out";
        };
      in {
        packages = {
          inherit aeneas;
          default = aeneas;
        };
        devShells.default = pkgs.mkShell {
          # By default, tests run some sanity checks which are pretty slow.
          # This disables these checks when developping locally.
          OPTIONS = "";

          packages = [
            pkgs.ocamlPackages.ocaml
            pkgs.ocamlPackages.ocamlformat
            pkgs.ocamlPackages.menhir
            pkgs.ocamlPackages.odoc
          ];

          inputsFrom = [
            self.packages.${system}.aeneas
          ];
        };
        checks = {
          inherit aeneas aeneas-tests
                  aeneas-verify-fstar
                  aeneas-verify-coq
                  aeneas-verify-hol4; };
      });
}
