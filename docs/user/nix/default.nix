{ emptyFile, runCommandCC, lib, callPackage, ... }: {
  /* Given a parsed Lake manifest in Nix,
    this will fetch a specific Lake dependency of the manifest.

    This currently only supports Git inputs.
  */
  fetchFromLakeManifest = manifest: { name, hash, ... }:
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
      src = runCommandCC "${super.name}-patched" {
        inherit (super) leanPath src relpath;
      } (''
        dir=$(dirname $relpath)
        mkdir -p $out/$dir
        if [ -d $src ]; then cp -r $src/. $out/$dir/; else cp $src $out/$leanPath; fi
      '' + lib.concatMapStringsSep "\n" (p : ''
        install -D -m 644 ${emptyFile} $out/${p}
      '') paths);
    }
    else {};
}
