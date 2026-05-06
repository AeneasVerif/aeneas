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
  outputs = inputs @ { self, flake-utils, nixpkgs, fstar, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            (final: prev: {
              pkgsStatic = prev.pkgsStatic.appendOverlays [
                (sFinal: sPrev: {
                  # Use the native version of `opaline` as a build tool, as it
                  # avoids bootstrapping issues in the static environment.
                  opaline = prev.opaline;

                  ocaml-ng = sPrev.ocaml-ng // {
                    ocamlPackages_5_2 = sPrev.ocaml-ng.ocamlPackages_5_2.overrideScope (oFinal: oPrev: {
                      buildDunePackage = args: oPrev.buildDunePackage (args // {
                        # Disable tests globally for static OCaml packages, as
                        # many test suites assume a dynamic environment or
                        # non-musl features that are unavailable here.
                        doCheck = false;

                        # Ensure `as` and other basic binutils are available in
                        # the static build environment.
                        nativeBuildInputs = (args.nativeBuildInputs or [ ]) ++ [ sFinal.stdenv.cc.bintools ];

                        # Remove `dynlink` as it is incompatible with the
                        # static compiler.
                        propagatedBuildInputs = builtins.filter (p: (p.pname or "") != "dynlink") (args.propagatedBuildInputs or [ ]);
                      });

                      ppx_deriving = oPrev.ppx_deriving.overrideAttrs (old: {
                        postPatch = (old.postPatch or "") + ''
                          # Remove `findlib.dynload` from the build
                          # dependencies.
                          substituteInPlace src/dune --replace "findlib.dynload" "findlib"

                          # Stub out dynamic loading calls in the source, as
                          # they will fail to link or run otherwise.
                          substituteInPlace src/ppx_deriving_main.cppo.ml \
                            --replace "Dynlink.adapt_filename filename" "filename" \
                            --replace "Dynlink.loadfile filename" "()" \
                            --replace "Dynlink.Error error" "Failure _" \
                            --replace "Dynlink.error_message error" "\"\"" \
                            --replace "Fl_dynload.load_packages [pkg]" "()"
                        '';
                      });

                      core_unix = oPrev.core_unix.overrideAttrs (old: {
                        # Work around a compilation error in `musl` when using
                        # GCC 14, where a `struct msghdr` field is incorrectly
                        # initialized with `NULL` instead of `0`.
                        env.NIX_CFLAGS_COMPILE = (old.env.NIX_CFLAGS_COMPILE or "") + " -Wno-error=int-conversion";
                      });
                    });
                  };
                })
              ];
            })
          ];
        };

        ocamlPackages = pkgs.ocaml-ng.ocamlPackages_5_2;
        ocamlPackagesStatic = pkgs.pkgsStatic.ocaml-ng.ocamlPackages_5_2;
        coqPackages = pkgs.coqPackages_8_18;
        charon = inputs.charon.packages.${system}.charon;
        charon-portable = inputs.charon.packages.${system}.charon-portable;
        charon-ml = inputs.charon.packages.${system}.charon-ml.override { inherit ocamlPackages; };

        easy_logging = pkgs.callPackage
          ({ fetchFromGitHub, ocamlPackages }:
            ocamlPackages.buildDunePackage rec {
              pname = "easy_logging";
              version = "0.8.2";
              src = fetchFromGitHub {
                owner = "sapristi";
                repo = "easy_logging";
                rev = "v${version}";
                sha256 = "sha256-Xy6Rfef7r2K8DTok7AYa/9m3ZEV07LlUeMQSRayLBco=";
              };
              buildInputs = [ ocamlPackages.calendar ];
            }
          )
          { inherit ocamlPackages; };

        aeneas = pkgs.callPackage
          (
            { lib
            , ocamlPackages
            , easy_logging
            , charon
            , charon-ml
            }:
            ocamlPackages.buildDunePackage {
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
                progress
                domainslib
              ]);
              postInstall = ''
                ln -s ${charon}/bin/charon $out/bin
              '';
            }
          )
          {
            inherit ocamlPackages easy_logging charon charon-ml;
          };

        # With statically-linked glibc.
        aeneas-static =
          let ocamlPackages = ocamlPackagesStatic; in
          aeneas.override {
            inherit ocamlPackages charon;
            easy_logging = easy_logging.override
              { inherit ocamlPackages; };
            charon-ml = charon-ml.override { inherit ocamlPackages; };
          };

        mk-aeneas-release = { aeneas, charon-portable }: pkgs.runCommand "aeneas-release.tar.gz" {
          buildInputs = pkgs.lib.optionals pkgs.stdenv.isDarwin [ pkgs.macdylibbundler ];
        } ''
          mkdir release
          cd release
          cp ${charon-portable}/bin/charon ${charon-portable}/bin/charon-driver .
          cp ${aeneas}/bin/aeneas .
          cp -r ${./backends} backends
          cp ${inputs.charon}/rust-toolchain .

          ${pkgs.lib.optionalString pkgs.stdenv.isDarwin ''
            # Make the binary writable so macdylibbundler can modify its load paths
            chmod +w aeneas
            # -od: Overwrite directories
            # -b: fix dependencies of the bundled libraries themselves
            # -x: executable to act upon
            # -d: directory where to put the libraries
            # -p: prefix for the path in the load command
            dylibbundler -od -b -x ./aeneas -d ./libs -p @executable_path/libs
          ''}

          tar -czvf $out *
        '';

        aeneas-release = mk-aeneas-release { inherit charon-portable aeneas; };
        aeneas-static-release = mk-aeneas-release { inherit charon-portable; aeneas = aeneas-static; };

        aeneas-check-tidiness = pkgs.stdenv.mkDerivation rec {
          name = "aeneas-check-tidiness";
          src = ./.;
          buildInputs = [
            ocamlPackages.dune_3
            ocamlPackages.ocaml
            ocamlPackages.ocamlformat_0_27_0
            inputs.charon.packages.${system}.rustToolchain
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
          buildInputs = [ inputs.charon.packages.${system}.rustToolchain ];
          buildPhase = ''
            export AENEAS_EXE=${aeneas}/bin/aeneas
            export CHARON_EXE=${aeneas}/bin/charon
            export TEST_RUNNER_EXE=${test_runner}/bin/test_runner

            # In Nix, the Rust toolchain is already nightly — no need for +nightly
            export RUSTC_CMD=rustc
            export CARGO_CMD=cargo

            # Copy the tests
            cp -r tests tests-copy
            make clean-generated-aeneas

            mkdir tests/llbc
            export LLBC_DIR=tests/llbc

            # Extract the tests with extra sanity checks enabled
            IN_CI=1 make extract-tests -j $NIX_BUILD_CORES
            # Run the Rust unit tests
            make cargo-test
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
          inherit aeneas aeneas-static aeneas-release aeneas-static-release;
          inherit charon charon-ml;
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
