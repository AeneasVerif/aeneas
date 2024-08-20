# Taken from Lean documentation's flake.nix
{
  description = "Aeneas documentation";

  inputs.lean.url = "github:leanprover/lean4/v4.10.0";
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
    with inputs.lean.packages.${system}; with nixpkgs;
    let
      doc-src = ./.; # lib.sourceByRegex ../. ["doc.*" "tests(/lean(/beginEndAsMacro.lean)?)?"];
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
        manifest = builtins.fromJSON (builtins.readFile ./lake-manifest.json);
        fetchFromLakeManifest = { name, hash, ... }:
        let 
          dep = lib.findFirst (pkg: pkg.name == name) null manifest.packages;
        in 
        assert dep != null;
        assert dep.type == "git"; fetchGit {
          inherit (dep) url rev;
          narHash = hash;
        } // (if dep.inputRev != null then { ref = dep.inputRev; } else {});

        # Inspired from Loogle scaffolding.
        # addFakeFile can plug into buildLeanPackage’s overrideBuildModAttrs
        # it takes a lean module name and a filename, and makes that file available
        # (as an empty file) in the build tree, e.g. for include_str.
        addFakeFiles = m: self: super:
          if m ? ${super.name}
          then let
            paths = m.${super.name};
          in {
            src = pkgs.runCommandCC "${super.name}-patched" {
              inherit (super) leanPath src relpath;
            } (''
              dir=$(dirname $relpath)
              mkdir -p $out/$dir
              if [ -d $src ]; then cp -r $src/. $out/$dir/; else cp $src $out/$leanPath; fi
            '' + pkgs.lib.concatMapStringsSep "\n" (p : ''
              install -D -m 644 ${pkgs.emptyFile} $out/${p}
            '') paths);
          }
          else {};

        batteries = buildLeanPackage {
          name = "Batteries";
          src = fetchFromLakeManifest {
            name = "batteries";
            hash = "sha256-JbOOKsUiYedNj3oiCNfwgkWyEIXsb1bAUm3uSEWsWPs=";
          };
        };
        qq = buildLeanPackage {
          name = "Qq";
          src = fetchFromLakeManifest {
            name = "Qq";
            hash = "sha256-//sZE32XzebePy81HEwNhIH8YW8iHgk+O8A0y/qNJrg=";
          };
        };
        aesop = buildLeanPackage {
          name = "Aesop";
          deps = [ batteries ];
          src = fetchFromLakeManifest {
            name = "aesop";
            hash = "sha256-LzooSD6NaSQyqKkBcxbSbjIZHrnDBx/lp/s4UdWeHpU=";
          };
        };
        import-graph = buildLeanPackage {
          name = "ImportGraph";
          deps = [ batteries ];
          src = fetchFromLakeManifest {
            name = "importGraph";
            hash = "sha256-3bWWnklUHuY/dA1Y3SK78SSDE+J8syEsMPJ67LnRI3M=";
          };
        };
        proof-widgets = buildLeanPackage {
          name = "ProofWidgets";
          deps = [ batteries ];
          src = fetchFromLakeManifest {
            name = "proofwidgets";
            hash = "sha256-6PzWhCNxxcuh0vEV0JhV0G30NVkYGEDup1j3KvG2VzA=";
          };

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
        mathlib = buildLeanPackage {
          deps = [ qq aesop batteries import-graph proof-widgets ];
          name = "Mathlib";
          src = fetchFromLakeManifest {
            name = "mathlib";
            hash = "sha256-gJYmaNDVus3vgUE3aNQfyMCcQJxw/lq5aYtLjs4OI7I=";
          };
        };
      in
      buildLeanPackage {
        name = "Base";
        deps = [ mathlib ];
        src = ../../backends/lean;
      };

      literate = buildLeanPackage {
        name = "literate";
        deps = [ aeneas-base ];
        src = ./.;
        roots = [
          {
            mod = "src/lean/basics";
            glob = "submodules";
          }
        ];
      };
      inked = renderPackage literate;
      doc = book;
    };
    defaultPackage = self.packages.${system}.doc;
    devShells.default = mkShell {
      packages = [
        self.packages.${system}.alectryon
        self.packages.${system}.leanInk
      ];
    };
  });
}
