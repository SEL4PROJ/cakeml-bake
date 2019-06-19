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

## Usage

Bake is designed to compile CakeML source code presented in HOL4 `Script.sml`
files. These source files can use standard CakeML constructs, including the
ML translator and the `process_topdecs` function for including concrete syntax.
In addition, Bake also understands a `require` directive which it uses for
dependency analysis. Looking at `example_projs/simple/bananaScript.sml` we see:

```
require basisProg apple;
```

This means that this module (`banana`) depends on two others, `basisProg` and `apple`, which Bake
will fetch and include in the build. For more information about modules, see [Modules](#modules).

To build the sample project, invoke `bake` like this:

```
bake --cakeml-dir /path/to/cakeml --module-names banana --search-dirs example_projs/simple
```

These arguments mean:

* `--cakeml-dir`: path to a checkout of the [CakeML Git repository][cakeml-repo].
* `--module-names`: the names of the top-level Bake modules which we intend to build.
  We don't need to list _all_ the modules we intend to build as Bake will take care of finding the
  dependencies. Often just one entry point module is sufficient – in this case `banana`.
* `--search-dirs`: one or more directories in which we would like Bake to search for the modules it
  needs to build. If more than one directory is provided, to find a single module Bake will search
  the directories in order.

Note that `basisProg` represents the CakeML basis library, and doesn't need to correspond to a
source file in one of the search dirs.

Armed with that information, Bake will do the following:

* Create a `build` directory to hold the results of its work (configurable using `--build-dir`).
* Place _instantiated_ copies of the source code for all of the relevant modules in the build
  directory. To instantiate a module, Bake replaces the `require` directive with a
  `translation_extends` call to the ancestor of the module, as determined by a topological sort
  of the dependencies. If that sounds bizarre, see
  [CakeML's Linear Build Chain](#cakemls-linear-build-chain).
* Build all of the module theory files using `Holmake` (configurable using `--holmake`).
* Produce an S-expression of the CakeML program's AST in a file called `program.sexp`.
* Compile `program.sexp` to an assembly file `program.S` using a binary of the CakeML compiler
  (configurable using `--cakeml-bin`).

You can then compile `program.S` with C implementations of all the necessary FFI functions to get
an executable.

For more configuration options, run `bake --help`.

## Interacting with HOL

It is rare to write a CakeML program in a HOL theory and compile it successfully on the first try,
usually you'll want to construct your program interactively. Unfortunately, because your Bake
modules are not real HOL4 theories, you can't just feed them straight into `hol`. For now the
recommended workflow is to run `bake` once on your partially built source, let it create the
instantiated module files in the build directory, work on those instantiated files interactively,
and copy the working code back to your source directory before running `bake` again.

## Extra Information

### Modules

Currently the term "module" is overloaded to mean:

* A Bake module, which has a camelCase name which matches the name of the theory
  file of which it is a part. E.g. `appleScript.sml` should contain a `new_theory "apple"`
  declaration, and should be referred to by its dependants using `require apple`.
* A CakeML module, which has a PascalCase name, unrelated to the name of the theory
  file of which it is a part. Indeed, you need not use CakeML modules at all to make
  effective use of Bake.
* Meta-level SML modules – as in modules at the `.sml` source level. They tend to come up
  least often in this context.

### CakeML's Linear Build Chain

When constructed as part of a HOL theory, there is a notion of a "CakeML program under
construction" which is stored behind a global mutable reference. For this reason,
the HOL4 theories must form a _linear_ chain, where each theory file adds a little bit to the
CakeML program. This can be rather annoying, particularly if you have modules that are costly
to compile, or that you don't always need. This is one of the problems that Bake attempts to
address: you give it a more complex rendition of your dependency information in the form of a DAG
(through `require` directives), and it will build a linear dependency chain that is compatible
with this DAG (if one exists).

### Debugging and Logging

Bake uses a standard Rust logging library, which is configured via the `RUST_LOG` environment
variable. To get more information out of Bake while it's running you can set `RUST_LOG` to `warn`,
`debug`, `info` or `trace`, listed in increasing order of verbosity.

```
env RUST_LOG=debug bake <args>
```

[cakeml-repo]: https://github.com/CakeML/cakeml
