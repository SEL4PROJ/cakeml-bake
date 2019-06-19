Bake
====

Bake is a build tool for CakeML, written in Rust.

It supports a workflow where you have a collection of CakeML "modules" contained in HOL4
`Script.sml` files, which may depend upon each other and may be accompanied by proofs. Bake allows
you to resolve the dependency order within a subset of these modules, linearise these dependencies
and quickly build an assembly file that you can compile.

## Installation

You'll need [Rust and Cargo](https://www.rust-lang.org/). From this directory, run:

```
cargo install --force --path .
```

This will put a binary called `bake` in `~/.cargo/bin`, which should be on your `$PATH`.

You can check which commit was used to build `bake` by running:

```
$ bake --version
bake 0.1.0-d8bda82
```

## Why Bake?

TODO
