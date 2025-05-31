# Aeneas user documentation - developer docs

## Architecture

This is a separate `flake.nix` setup from the root repository's one, but it relies on Aeneas' Lean library from this repository.

We pull Lean 4's upstream flake to build Lean in Nix, use some forked Alectryon-related tooling to assemble a mdBook HTML output.

### How to add new files?

If these files are not supposed to be inked by Alectryon (i.e. display interactive goals in the browser), they can be extended following [the vanilla mdBook documentation](https://rust-lang.github.io/mdBook/guide/creating.html) in the `src/` directory.

If these files are supposed to be inked by Alectryon:

- they need to appear in `src/lean/basics` as `xyz.lean` and `xyz.lean.md`
- the Markdown file version should be included in the `SUMMARY.md` file.
- the contents of `xyz.lean.md` by default should be the same as the others one, i.e. a Lean code block containing `{{#include xyz.lean}}`

### How to add a new directory containing Lean files?

This requires a change in the `flake.nix`, find the place where the `literate` package is defined:

```nix
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
```

Add a new `root` as it follows, assuming your new module is `src/lean/advanced`:

```nix
      literate = buildLeanPackage {
        name = "literate";
        deps = [ aeneas-base ];
        src = ./.;
        roots = [
          {
            mod = "src/lean/basics";
            glob = "submodules";
          }
          {
            mod = "src/lean/advanced";
            glob = "submodules";
         }
        ];
      };
```

### How to add a new Lean dependency to the project?

Each `buildLeanPackage` can take a list of `deps`.

Two cases:

- either, this is a local dependency and this can be built like the `Base` (Aeneas standard library) one.
- or, this is a remote dependency and this is often added to a Lakefile, this can be built like `Mathlib` and the others.

## How to build?

```console
$ nix build .#docs
```

## How to deploy?

The `result/` symlink is a HTML webroot, this can be deployed as a static website.

## How to update the dependencies?

You just updated `backends/lean/lakefile.lean` dependencies or the Lean version.

### Lean version

Update the flake URI in `flake.nix`, this will trigger a mass rebuild of the documentation: rebootstrapping Lean 4 (this may take a couple of minutes), rebuilding Mathlib4 (this may take up to 20 minutes on a fast computer), building Aeneas standard library and finally the documentation.

### Updating Aeneas standard library's dependencies

You may need to change all `hash = "...";` reference between `aeneas-base =` and `in`, which are the dependencies of `Base`, Aeneas standard library.

To do so, you can replace `hash = "...";` by `hash = lib.fakeHash;`, and rebuild, i.e. `nix build .#doc`, Nix will provide the actual SRI hash.

_Advice_ : build with `--keep-going` to get all hashes at once instead of having to copy one hash per one hash.

## My build is failing due to a compilation error but it works outside of Nix

This is highly likely due to a mismatch between the dependencies in the Nix setup and outside.

The Nix setup reads the `lakefile-manifest.json`, but this lockfile is insufficient to lock purely the dependencies (NAR SHA256 serialization are missing).

To overcome this, they are specified manually in `flake.nix`, but each time the Aeneas standard library updates their dependencies, the `flake.nix` needs to have all its hash rewritten. Refer to "How to update" for guidance.

In the future, it could be smart to extend the lockfile format or write another file besides in the Aeneas standard library containing all NAR SHA256 serializations and link it in the Lake build system so that each updates would regenerate this file.

# Reference documentation

## `fetchFromLakeManifest`

This is a simple Nix function that looks inside a Lean manifest and pulls the Git input information, it does not handle yet automatically fetching the NAR SHA256 serialization of the Git input as Lake does not store this information in its lockfile.

This means that whenever you are updating the manifest, you need to replace all `hash = "...";` by `hash = lib.fakeHash;` to bust the cache, otherwise you will run into compilation errors.

## `addFakeFiles`

Mathlib4 depends on `proof-widgets`, a Lean library which depends on Node.js for its build system, to avoid wasting time to package multi-language dependency system, `addFakeFiles` is a function to poly-fill by **empty files** specific modules, fooling the build system into believing that these files have been built externally.

## `renderPackage`

This is a function to analyze an entire Lean package via [Alectryon](https://github.com/cpitclaudel/alectryon) and [LeanInk](https://github.com/leanprover/LeanInk) and assemble this as a tree of symlinks for each module in the package.
