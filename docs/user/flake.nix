# Taken from Lean documentation's flake.nix
{
  description = "Aeneas documentation";

  # When you update Lean in Aeneas, update this URI as well.
  inputs.lean.url = "github:leanprover/lean4/v4.11.0-rc2";
  inputs.flake-utils.follows = "lean/flake-utils";
  inputs.mdBook = {
    url = "github:leanprover/mdBook";
    flake = false;
  };
  inputs.alectryon = {
    url = "github:Kha/alectryon/typeid";
    flake = false;
  };
  inputs.leanInk = {
    url = "github:leanprover/LeanInk";
    flake = false;
  };

  outputs = inputs@{ self, ... }: inputs.flake-utils.lib.eachDefaultSystem (system:
    with inputs.lean.packages.${system}.deprecated; with nixpkgs;
    let
      doc-src = ./.; # lib.sourceByRegex ../. ["doc.*" "tests(/lean(/beginEndAsMacro.lean)?)?"];
      leanLib = callPackage ./nix { };
    in {
    packages = rec {
      lean-mdbook = mdbook.overrideAttrs (drv: rec {
        name = "lean-${mdbook.name}";
        src = inputs.mdBook;
        cargoDeps = drv.cargoDeps.overrideAttrs (_: {
          inherit src;
          outputHash = "sha256-CO3A9Kpp4sIvkT9X3p+GTidazk7Fn4jf0AP2PINN44A=";
        });
        doCheck = false;
      });

      # This is the final book:
      # * We copy the classical mdBook contents.
      # * We interpose the inked Lean files (*.lean.md) in the source tree
      # Finally, we call mdBook to process this soup into a HTML webroot you can deploy.
      book = stdenv.mkDerivation {
        name = "aeneas-doc";
        src = doc-src;
        buildInputs = [ lean-mdbook ];
        buildCommand = ''
          set -x
          mkdir $out
          # necessary for `additional-css`...?
          cp -vr --no-preserve=mode $src/* .
          cp -vr --no-preserve=mode ${inked.out}/* .
          mdbook build -d $out
        '';
      };

      leanInk = (buildLeanPackage {
        name = "Main";
        src = inputs.leanInk;
        deps = [ (buildLeanPackage {
          name = "LeanInk";
          src = inputs.leanInk;
        }) ];
        executableName = "leanInk";
        linkFlags = ["-rdynamic"];
      }).executable;

      alectryon = python3Packages.buildPythonApplication {
        name = "alectryon";
        src = inputs.alectryon;
        propagatedBuildInputs =
          [ leanInk lean-all ] ++
          # https://github.com/cpitclaudel/alectryon/blob/master/setup.cfg
          (with python3Packages; [ pygments dominate beautifulsoup4 docutils ]);
        doCheck = false;
      };

      renderLeanMod = mod: mod.overrideAttrs (final: prev: {
        name = "${prev.name}.md";
        buildInputs = prev.buildInputs ++ [ alectryon ];
        outputs = [ "out" ];
        buildCommand = ''
          dir=$(dirname $relpath)
          mkdir -p $dir out/$dir
          if [ -d $src ]; then cp -r $src/. $dir/; else cp $src $leanPath; fi
          alectryon --frontend lean4+markup $leanPath --backend webpage -o $out/$leanPath.md
        '';
      });

      renderPackage = pkg: symlinkJoin {
        name = "${pkg.name}-mds";
        paths = map renderLeanMod (lib.attrValues pkg.mods);
      };

      aeneas-base = 
      let
        manifest = builtins.fromJSON (builtins.readFile ../../backends/lean/lake-manifest.json);
        fetchFromLakeManifest = leanLib.fetchFromLakeManifest manifest;
        inherit (leanLib) addFakeFiles;

        # To update the dependencies, just ensure that the `lake-manifest.json`
        # in `backends/lean` is up to date. Then, replace each `hash = "...";`
        # by `hash = lib.fakeHash;` Then, perform `nix build .#doc
        # --keep-going` to get all the new hashes. Copy them back here and
        # commit this result.

        # Those are specifically the Mathlib4 dependencies.
        batteries = buildLeanPackage {
          name = "Batteries";
          src = fetchFromLakeManifest {
            name = "batteries";
            hash = "sha256-EGcjOcTu66rtAICAqgPKaR8kBlImoq4lUZfNZR9dHiY=";
          };
        };
        qq = buildLeanPackage {
          name = "Qq";
          src = fetchFromLakeManifest {
            name = "Qq";
            hash = "sha256-iFlAiq8Uxq+QD6ql4EMpRQENvIhKdioaleoEiDmMuDQ=";
          };
        };
        aesop = buildLeanPackage {
          name = "Aesop";
          deps = [ batteries ];
          src = fetchFromLakeManifest {
            name = "aesop";
            hash = "sha256-97xcl82SU9/EZ8L4vT7g/Ureoi11s3c4ZeFlaCd4Az4=";
          };
        };
        import-graph = buildLeanPackage {
          name = "ImportGraph";
          deps = [ batteries ];
          src = fetchFromLakeManifest {
            name = "importGraph";
            hash = "sha256-u8tk5IWU/n47kmNAlxZCmurq7e08oCzANhsk9VJeCCM=";
          };
        };
        proof-widgets = buildLeanPackage {
          name = "ProofWidgets";
          deps = [ batteries ];
          src = fetchFromLakeManifest {
            name = "proofwidgets";
            hash = "sha256-jPvUi73NylxFiU5V0tjK92M0hJfHWZi5ULZldDwctYY=";
          };

          # ProofWidgets require a special Node.js build pass encoded in its
          # Lakefile In principle, we could parse the Node.js lockfile, lock it
          # using Nix, generate these JS files and link them properly in the
          # build process. But we make no use of ProofWidgets in Aeneas manual,
          # so we just polyfill all of these files by empty files, satisfying
          # Lake build process.
          overrideBuildModAttrs = addFakeFiles {
            "ProofWidgets.Compat" = [ ".lake/build/js/compat.js" ];
            "ProofWidgets.Component.Basic" = [ ".lake/build/js/interactiveExpr.js" ];
            "ProofWidgets.Component.GoalTypePanel" = [ ".lake/build/js/goalTypePanel.js" ];
            "ProofWidgets.Component.Recharts" = [ ".lake/build/js/recharts.js" ];
            "ProofWidgets.Component.PenroseDiagram" = [ ".lake/build/js/penroseDisplay.js" ];
            "ProofWidgets.Component.Panel.SelectionPanel" = [ ".lake/build/js/presentSelection.js" ];
            "ProofWidgets.Component.Panel.GoalTypePanel" = [ ".lake/build/js/goalTypePanel.js" ];
            "ProofWidgets.Component.MakeEditLink" = [ ".lake/build/js/makeEditLink.js" ];
            "ProofWidgets.Component.OfRpcMethod" = [ ".lake/build/js/ofRpcMethod.js" ];
            "ProofWidgets.Component.FilterDetails" = [ ".lake/build/js/filterDetails.js" ];
            "ProofWidgets.Component.HtmlDisplay" =
              [ ".lake/build/js/htmlDisplay.js" ".lake/build/js/htmlDisplayPanel.js"];
              "ProofWidgets.Presentation.Expr" = [ ".lake/build/js/exprPresentation.js" ];
          };
        };
        # This is Mathlib4, a dependency of Aeneas standard library.
        mathlib = buildLeanPackage {
          deps = [ qq aesop batteries import-graph proof-widgets ];
          name = "Mathlib";
          src = fetchFromLakeManifest {
            name = "mathlib";
            hash = "sha256-3FnWd0dUVhNyUPxLNNHA41RWF34fwmXulnRSIEmIQXM=";
          };
        };
      in
      # Aeneas standard library does not require any hashing
      # as it is present in this local repository.
      buildLeanPackage {
        name = "Base";
        deps = [ mathlib ];
        src = ../../backends/lean;
      };

      # This is a meta Lean package of all Lean files used in the documentation.
      literate = buildLeanPackage {
        name = "literate";
        # Add here new Lean packages if you need them for the manual
        deps = [ aeneas-base ];
        src = ./.;
        # To add a new directory containing Lean files to be processed
        # by Alectryon, add a new attribute set `{ mod = "path to the lean files"; glob = "submodules"; }`
        roots = [
          {
            mod = "src/lean/basics";
            glob = "submodules";
          }
        ];
      };

      # This is the tree of all inked Lean files, i.e. the *.lean.md files
      # expected by mdBook.
      inked = renderPackage literate;

      # This is the final book.
      doc = book;
    };
    defaultPackage = self.packages.${system}.doc;
    devShells.default = mkShell {
      packages = [
        # If you need to run Alectryon or LeanInk manually for tests
        # This is available in the default development shell.
        self.packages.${system}.alectryon
        self.packages.${system}.leanInk
      ];
    };
  });
}
