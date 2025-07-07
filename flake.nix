{
  description = "Aeneas";

  inputs = {
    # Remark: when adding inputs here, don't forget to also add them in the
    # arguments to `outputs` below!
    charon.url = "github:aeneasverif/charon";
    flake-utils.follows = "charon/flake-utils";
    nixpkgs.follows = "charon/nixpkgs";
    fstar.url = "github:FStarLang/fstar";
  };

  # Remark: keep the list of outputs in sync with the list of inputs above
  # (see above remark)
  outputs = { self, charon, flake-utils, nixpkgs, fstar, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;
        coqPackages = pkgs.coqPackages_8_18;
        charon-ml = charon.packages.${system}.charon-ml.override { inherit ocamlPackages; };
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

        aeneas-check-tidiness = pkgs.stdenv.mkDerivation rec {
          name = "aeneas-check-tidiness";
          src = ./.;
          buildInputs = [
            ocamlPackages.dune_3
            ocamlPackages.ocaml
            ocamlPackages.ocamlformat_0_27_0
            charon.packages.${system}.rustToolchain
          ];
          buildPhase = ''
            make format
            rm -rf ./src/_build
            rm -rf ./tests/test_runner/_build
            if ! diff --no-dereference -ru . ${src}; then
              echo 'ERROR: Code is not formatted. Run `make format` to format the project files.'
              exit 1
            fi
          '';
          installPhase = "touch $out";
        };

        aeneas = ocamlPackages.buildDunePackage {
          pname = "aeneas";
          version = "0.1.0";
          duneVersion = "3";
          src = ./src;
          OCAMLPARAM = "_,warn-error=+A"; # Turn all warnings into errors.
          propagatedBuildInputs = [
            easy_logging
            charon-ml
          ] ++ (with ocamlPackages; [
            calendar
            core_unix
            ppx_deriving
            visitors
            yojson
            zarith
            ocamlgraph
          ]);
          postInstall = ''
            ln -s ${charon.packages.${system}.charon}/bin/charon $out/bin
          '';
        };

        test_runner = ocamlPackages.buildDunePackage {
          pname = "aeneas_test_runner";
          version = "0.1.0";
          duneVersion = "3";
          src = ./tests/test_runner;
          OCAMLPARAM = "_,warn-error=+A"; # Turn all warnings into errors.
          propagatedBuildInputs = (with ocamlPackages; [
            core_unix
            ppx_deriving
          ]);
        };

        # This test is a full crate with dependencies. We generate the
        # corresponding llbc file here; this function takes care of cargo
        # dependencies for us.
        betree-llbc = charon.extractCrateWithCharon.${system} {
          name = "betree";
          src = ./tests/src/betree;
          charonFlags = "--rustc-arg=-Zpolonius --opaque=crate::betree_utils --preset=aeneas";
          craneExtraArgs.checkPhaseCargoCommand = ''
            cargo rustc -- --test -Zpolonius
            ./target/debug/betree
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
              || pkgs.lib.hasPrefix (toString ./src) path
              || pkgs.lib.hasPrefix (toString ./backends) path
              || (pkgs.lib.hasPrefix (toString ./tests) path
              && !pkgs.lib.hasSuffix ".llbc" path);
          };
          buildInputs = [ charon.packages.${system}.rustToolchain ];
          buildPhase = ''
            export AENEAS_EXE=${aeneas}/bin/aeneas
            export CHARON_EXE=${aeneas}/bin/charon
            export TEST_RUNNER_EXE=${test_runner}/bin/test_runner

            # Copy the tests
            cp -r tests tests-copy
            make clean-generated-aeneas

            mkdir tests/llbc
            export LLBC_DIR=tests/llbc
            # Copy over the llbc file we can't generate ourselves.
            cp ${betree-llbc}/llbc/betree.llbc $LLBC_DIR

            # Run the tests with extra sanity checks enabled
            IN_CI=1 make test-all -j $NIX_BUILD_CORES
            # Clean generated llbc files so we don't compare them.
            rm -r tests/llbc
            # Remove the `target` cache folder generated by cargo
            rm -rf tests/src/*/target

            # Check that there are no differences between the generated tests
            # and the original tests
            if diff -rq tests tests-copy; then
              echo "Ok: the regenerated test files are the same as the checked out files"
            else
              echo "Error: the regenerated test files differ from the checked out files"
              diff -ru tests tests-copy
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
          FSTAR_EXE = "${fstar.packages.${system}.fstar}/bin/fstar.exe";
          buildPhase = ''
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
          buildInputs = [ coqPackages.coq ];
          buildPhase = ''
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
          src = pkgs.lib.cleanSourceWith {
            src = ./.;
            filter = path: type:
              # If we exclude these, the filter won't recurse into them.
              path == toString ./backends || path == toString ./tests
              || pkgs.lib.hasPrefix (toString ./backends/hol4) path
              || pkgs.lib.hasPrefix (toString ./tests/hol4) path
            ;
          };
          buildInputs = [ pkgs.hol ];
          buildPhase = ''
            cd ./tests/hol4
            make prepare-projects
            make verify -j $NIX_BUILD_CORES
          '';
          # The build doesn't generate anything
          installPhase = "touch $out";
        };

        check-charon-pin = pkgs.runCommand "aeneas-check-charon-pin"
          {
            buildInputs = [ pkgs.jq ];
          } ''
          CHARON_REV_FROM_FLAKE="$(jq -r .nodes.charon.locked.rev ${./flake.lock})"
          CHARON_REV_FROM_PIN="$(tail -1 ${./charon-pin})"
          if [[ "$CHARON_REV_FROM_FLAKE" != "$CHARON_REV_FROM_PIN" ]]; then
            echo 'ERROR: The charon version in `flacke.lock` differs from the one in `charon-pin`.'
            echo '  In `flake.lock`: '"$CHARON_REV_FROM_FLAKE"
            echo '  In `charon-pin`: '"$CHARON_REV_FROM_PIN"
            echo 'Use `make charon-pin` to update the `./charon-pin` file.'
            exit 1
          fi
          touch $out
        '';
      in
      {
        packages = {
          inherit aeneas;
          inherit (charon.packages.${system}) charon;
          inherit charon-ml;
          default = aeneas;
        };
        devShells.default = pkgs.mkShell {
          packages = [
            pkgs.curl
            pkgs.elan
            ocamlPackages.ocaml
            ocamlPackages.ocamlformat_0_27_0
            ocamlPackages.menhir
            ocamlPackages.odoc
            # ocaml-lsp's version must match the ocaml version used. Pinning
            # this here to save everyone a headache.
            ocamlPackages.ocaml-lsp
            pkgs.jq
            pkgs.rustup
            pkgs.rlwrap
            fstar.packages.${system}.fstar
            coqPackages.coq
          ];

          inputsFrom = [
            self.packages.${system}.aeneas
          ];
        };
        checks = {
          default = pkgs.runCommand "aeneas-checks" { } ''
            echo ${aeneas-tests}
            echo ${aeneas-verify-coq}
            echo ${aeneas-verify-fstar}
            echo ${aeneas-verify-hol4}
            touch $out
          '';
          inherit
            aeneas-tests
            aeneas-verify-coq
            aeneas-verify-fstar
            aeneas-verify-hol4
            aeneas-check-tidiness
            check-charon-pin;
        };
      });
}
