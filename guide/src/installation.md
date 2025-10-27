# Installation

This section explains how to install Creusot, what goes into the installation,
and some configuration options.

## Quick installation

The `INSTALL` script installs Creusot and its accompanying tools.

Requirements to run the `INSTALL` script:

- `cargo`
- [`opam`](https://opam.ocaml.org/) to install `why3` and `why3find`.
- `curl` to download provers: `alt-ergo`, `z3`, `cvc4`, `cvc5`.

```sh
./INSTALL
```

See `./INSTALL --help` for options.

Note that the `INSTALL` script will take a couple minutes to create
a local Opam switch and then to install the many dependencies of `why3`.

The local switch will be located in `$XDG_DATA_HOME/creusot/_opam`
(default on Linux: `~/.local/share/creusot/_opam`). We recommend having this local
switch to prevent accidentally breaking your Creusot setup while working
on other OCaml projects.

## Manual installation

1. You can install the core files from the Creusot repository with Cargo alone:

    ```sh
    # Install cargo-creusot
    cargo install --path cargo-creusot

    # Install creusot-rustc
    TOOLCHAIN=$(grep "nightly-[0-9-]*" --only-matching rust-toolchain)
    cargo install --path cargo-creusot --root $XDG_DATA_HOME/creusot/toolchain/$TOOLCHAIN/bin

    # Install the Creusot prelude with Why3find
    cargo run --bin prelude-generator
    (cd target && why3find install --global creusot)

    # Copy why3find.json in the installation directory
    cp cargo-install/why3find.json $XDG_DATA_HOME/creusot/why3find.json
    ```

2. The following binaries must then be put in `$XDG_DATA_HOME/creusot/bin`, refer to their respective
    project pages for how to get them:

    - [`why3`](https://www.why3.org/) (available on Opam)
    - [`why3find`](https://git.frama-c.com/pub/why3find) (available on Opam)
    - [`alt-ergo`](https://alt-ergo.ocamlpro.com/) (downloadable binaries, also on Opam)
    - [`z3`](https://github.com/Z3Prover/z3) (downloadable binaries, also on Opam)
    - [`cvc5`](https://cvc5.github.io/) (downloadable binaries)
    - [`cvc4`](https://cvc4.github.io/) (downloadable binaries)

## Installed files

Everything Creusot needs to run.

- `cargo-creusot` in `PATH`. This is the entry point of Creusot.

- `$XDG_DATA_HOME/creusot/` (default on Linux: `~/.local/share/creusot`), a directory containing:

    - `toolchain/$TOOLCHAIN/bin/creusot-rustc`, the Creusot compiler, where `$TOOLCHAIN`
        is the toolchain used to build Creusot (set by the file `rust-toolchain` in the Creusot repository).

    - `bin/` containing binaries.

        - `why3` and `why3find`
        - Provers: `alt-ergo`, `z3`, `cvc5`, `cvc4`

    - `why3find.json`, which is used to create new Creusot projects with
        `cargo creusot new` or `cargo creusot init`.

- The Creusot prelude, a Why3find package
    (with the local switch from the Quick installation, on Linux,
    the prelude is located at `~/.local/share/creusot/_opam/lib/why3find/package/creusot`).

## Why3

The Why3 configuration is located at `$XDG_CONFIG_HOME/creusot/why3.conf`
(default on Linux: `~/.config/creusot`). This file is generated at the first invocation
of `cargo creusot prove`. Notable options in this file:

- the location and version of provers (`[partial_prover]`)
  (for the Nix installation, this is not known during the installation of Creusot,
  that's why this file is generated later).
- The maximum number of parallel prover jobs (`running_provers_max = ...`).
- `[strategy]` for solving goals in Why3 IDE.
- `[ide]` options for Why3 IDE (can be modified in the menu `File > Preferences`).

## Why3find

`cargo creusot prove` invokes `why3find`, which looks for the file `why3find.json` in the current working directory or one of its parents.
At the moment we recommend not modifying `why3find.json`. Instead, you should rely on adapting your Rust code to make proofs more robust, for example by adding more assertions.
Please open an issue if this configuration does not work for you.

Nevertheless, you may like to experiment with some of these options:

- `"fast"` and `"time"`: timeout durations in seconds for provers.
- `"depth"`: proof search is pruned after this number of levels.
- `"tactics"`: list of tactics to apply during proof search.
  "Tactics" are [Why3 transformations](https://www.why3.org/doc/technical.html#transformations) that take no arguments.
  For example: `compute_in_goal` and `inline_goal` are tactics; `apply H`, `exists X` are not tactics.

See [the Why3find README](https://git.frama-c.com/pub/why3find#why3find) for more information.
