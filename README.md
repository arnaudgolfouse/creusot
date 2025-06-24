![](/static/marteau.jpg)

*Le marteau-pilon, forges et aciéries de Saint-Chamond, Joseph-Fortuné LAYRAUD, 1889*

# About

**Creusot** is a *deductive verifier* for Rust code. It verifies your code is safe from panics, overflows, and assertion failures. By adding annotations you can take it further and verify your code does the *correct* thing.

Creusot works by translating Rust code to [Coma](https://coma.paulpatault.fr/), an intermediate verification language of the [Why3 Platform](https://www.why3.org). Users can then leverage the full power of Why3 to (semi)-automatically discharge the verification conditions!

See [ARCHITECTURE.md](ARCHITECTURE.md) for technical details.

## Help and Discussions

If you need help using Creusot or would like to discuss, you can post on the [discussions forum](https://github.com/creusot-rs/creusot/discussions) or join our [Zulip chat](https://why3.zulipchat.com/#narrow/stream/341707-creusot)!

## Documentation

- To learn how to write code with Creusot: [guide](https://creusot-rs.github.io/creusot/guide)
- To see the API of `creusot_contracts` (Creusot's "standard library"): [`creusot_contracts` API](https://creusot-rs.github.io/creusot/doc/creusot_contracts)

## Citing Creusot

If you would like to cite Creusot in academic contexts, we encourage you to use our [ICFEM'22 publication](https://hal.inria.fr/hal-03737878/file/main.pdf).

# Examples of Verification

To get an idea of what verifying a program with Creusot looks like, we encourage you to take a look at some of our test suite:

- [Zeroing out a vector](tests/should_succeed/vector/01.rs)
- [Binary search on Vectors](tests/should_succeed/vector/04_binary_search.rs)
- [Sorting a vector](tests/should_succeed/vector/02_gnome.rs)
- [IterMut](tests/should_succeed/iterators/02_iter_mut.rs)
- [Normalizing If-Then-Else Expressions](tests/should_succeed/ite_normalize.rs)

More examples are found in [tests/should_succeed](tests/should_succeed).

## Projects built with Creusot

- [CreuSAT](https://github.com/sarsko/creusat) is a verified SAT solver written in Rust and verified with Creusot. It really pushes the tool to its limits and gives an idea of what 'use in anger' looks like.
- Another big project is in the works :)

# Installing Creusot as a user

1. [Install `rustup`](https://www.rust-lang.org/tools/install), to get the suitable Rust toolchain
2. [Get `opam`](https://opam.ocaml.org/doc/Install.html), the package manager for OCaml
3. Setup the environment for cargo if not done already:
   ```sh
   . .cargo/env
   ```
4. Clone the [creusot](https://github.com/creusot-rs/creusot/) repository,
   then move into the `creusot` directory.
   ```sh
   git clone https://github.com/creusot-rs/creusot
   cd creusot
   ```
5. Install **Creusot**:
   ```sh
   ./INSTALL
   ```
6. Check that the installation succeeded:
   ```sh
   cargo creusot --help
   ```

   A regular installation consists of:
   - the `cargo-creusot` executable in `~/.cargo/bin/`;
   - the `creusot-rustc` executable in `{DATA_DIR}/toolchains/$TOOLCHAIN/bin`;
   - the `why3` and `why3find` executables in `{SWITCH}/bin`;
   - the Creusot prelude in `{SWITCH}/lib/why3find/packages/creusot`;
   - SMT solvers (Alt-Ergo, CVC4, CVC5, Z3) in `{DATA_DIR}/bin`;
   - configuration files in `{CONFIG_DIR}`.

where the directories depend on the OS:

| | Linux | MacOS |
|-|-|-|
| `{DATA_DIR}` | `~/.local/share/creusot` | `~/Library/Application Support/creusot.creusot` |
| `{CONFIG_DIR}` | `~/.config/creusot` | `~/Library/Application Support/creusot.creusot` |
| `{SWITCH}` | `~/.local/share/creusot/_opam` | `~/.creusot/_opam` |

Installation options can be set in a text file `INSTALL.opts`.
They are just space-separated command-line arguments.
Type `./INSTALL --help` for a list of available options.
For example:

```sh
echo "--external z3" > INSTALL.opts
./INSTALL
```

## Upgrading Creusot

1. Enter the cloned Creusot git repository used previously to install Creusot
2. Update Creusot's sources:
   ```sh
   git pull
   ```
3. Update opam's package listing:
   ```sh
   opam update
   ```
4. Reinstall Creusot:
   ```sh
   ./INSTALL
   ```

# Hacking on Creusot

See [CONTRIBUTING.md](CONTRIBUTING.md) for information on the developer workflow for
hacking on the Creusot codebase.
