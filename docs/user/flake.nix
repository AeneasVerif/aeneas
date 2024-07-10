# Taken from Lean documentation's flake.nix
{
  description = "Aeneas documentation";

  inputs.lean.url = "github:leanprover/lean4";
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
          mkdir $out
          # necessary for `additional-css`...?
          cp -vr --no-preserve=mode $src/* .
          mdbook build -d $out
        '';
      };
      # We use a separate derivation instead of `checkPhase` so we can push it but not `doc` to the binary cache
      test = stdenv.mkDerivation {
        name = "aeneas-doc-test";
        src = doc-src;
        buildInputs = [ lean-mdbook stage1.Lean.lean-package strace ];
        patchPhase = ''
          cd doc
          patchShebangs test
        '';
        buildPhase = ''
          mdbook test
          touch $out
        '';
        dontInstall = true;
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

      literate = buildLeanPackage {
        name = "literate";
        src = ./.;
        roots = [ ];
      };
      inked = renderPackage literate;
      doc = book;
    };
    defaultPackage = self.packages.${system}.doc;
  });
}
