{
  description = "Aeneas";

  inputs = {
    # Remark: when adding inputs here, don't forget to also add them in the list
    # of outputs below!
    charon.url = "github:aeneasverif/charon";
    flake-utils.follows = "charon/flake-utils";
    nixpkgs.follows = "charon/nixpkgs";
    hacl-nix.url = "github:hacl-star/hacl-nix";
    lean.url = "github:leanprover/lean4";
    #lake.url = "github:leanprover/lake";
    lake.url = "github:leanprover/lake/lean4-master";
    #lake.flake = false;
  };

  # Remark: keep the list of outputs in sync with the list of inputs above
  # (see above remark)
  outputs = { self, charon, flake-utils, nixpkgs, hacl-nix, lean, lake }:
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
        ocamlgraph = ocamlPackages.buildDunePackage rec {
          pname = "ocamlgraph";
          version = "2.0.0";
          src = pkgs.fetchurl {
            url = "https://github.com/backtracking/ocamlgraph/releases/download/2.0.0/ocamlgraph-2.0.0.tbz";
            sha256 = "20fe267797de5322088a4dfb52389b2ea051787952a8a4f6ed70fcb697482609";
          };
          buildInputs = [ ocamlPackages.stdlib-shims ocamlPackages.graphics ];
        };
        unionFind = ocamlPackages.buildDunePackage rec {
          pname = "unionFind";
          version = "20220122";
          src = pkgs.fetchurl {
            url = "https://gitlab.inria.fr/fpottier/unionFind/-/archive/20220122/archive.tar.gz";
            sha512 = "c49dd3f9a6689f6a5efe39c26efe2c137f8812b4be6ee76c2cc20068cf86ad73c0ac97ec9a543245dddb63792ce8c1904576b3435bf419cc7837bc5e368eee6d";
          };
          buildInputs = [];
        };
        aeneas = ocamlPackages.buildDunePackage {
          pname = "aeneas";
          version = "0.1.0";
          duneVersion = "3";
          src = ./compiler;
          buildInputs = [ easy_logging ocamlgraph unionFind charon.packages.${system}.charon-ml ]
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
            cp ${aeneas}/bin/aeneas_driver aeneas.exe
            export AENEAS_EXE=./aeneas.exe

            # Run the tests
            make tests -j $NIX_BUILD_CORES
          '';
          # Tests don't generate anything new as the generated files are
          # versionned, but the installation phase still needs to prodocue
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
        # Replay the Lean proofs. TODO: doesn't work
        aeneas-verify-lean = pkgs.stdenv.mkDerivation {
          name = "aeneas_verify_lean";
          src = ./tests/lean;
          #LAKE_EXE = lean.packages.${system};
          #buildInputs = [lean.packages.${system}.lake-dev];
          buildInputs = [lean.packages.${system} lake.packages.${system}.cli];
          #buildInputs = [lake.packages.${system}.cli];
          buildPhase= ''
            make prepare-projects
            #make verify -j $NIX_BUILD_CORES
            make verify
          '';
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
        checks = { inherit aeneas aeneas-tests aeneas-verify-fstar aeneas-verify-coq aeneas-verify-lean aeneas-verify-hol4; };
        hydraJobs = { inherit aeneas aeneas-tests aeneas-verify-fstar aeneas-verify-coq aeneas-verify-lean aeneas-verify-hol4; };
      });
}
