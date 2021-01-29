`mathport` is a tool for building lean4 `.olean` files from lean3 `.tlean` files.

# Status

A lot of information is preserved, including (kernel) terms, attributes (e.g. reducible, class, instance, simp), mixfix notation, export declarations, and more.
Some definitions and theorems can be restated easily
but most are still very cumbersome to elaborate due to a myriad of differences between the two systems that have yet to be accounted for.

# Experimenting

The most recent release contains lean4 `.olean` files for all of mathlib.
When extracted, it will populate directories `Lib4/Lean3Lib`, `Lib4/Lean3Pkg`, and `Lib4/Mathlib`.
See [Lib4/Examples](https://github.com/dselsam/mathport/tree/master/Lib4/Examples) for a few barebones examples that build on these `.olean` files.
Note that there are many issues still and the experience may not be pleasant yet.
For now these examples will only be tested with [this branch of lean4](https://github.com/dselsam/lean4/tree/mathport).

# Contributing

The best way to help is to find and isolate issues. Pick your favorite mathlib file, start reimplementing it in Lean4,
and file (small, isolated) GitHub issues for any specific pain points you encounter.

# Running the pipeline

The following instructions are for developers who want to experiment with different porting strategies.

- Build [this branch of lean3](https://github.com/dselsam/lean/tree/mathport) in directory `./lean3`.
  - generate `library/all.lean`

- Download a compatible version of [mathlib](https://github.com/leanprover-community/mathlib) in directory `./mathlib`.
  - i.e. one that uses the same version of lean3 that the `mathport` branch builds on
  - we will test the pipeline on [this branch of mathlib](https://github.com/dselsam/mathlib/tree/mathport)
  - generate `src/all.lean`

- Build [this branch of lean4](https://github.com/dselsam/lean4/tree/mathport) in directory `./lean4`.

- `make` should now produce the executable `mathport`.

- To port, use the following commands (for "lib" in [`Lean3`, `Mathlib`]):
  - `make clear<lib>`: removes `.olean` and `.tlean` files
  - `make build<lib>`: builds `.olean` and `.tlean` files
  - `make unport<lib>`: removes lean4 `.olean` files
  - `make port<lib>`: generates lean4 `.olean` files
  - see [Makefile](https://github.com/dselsam/mathport/blob/master/Makefile) for details.
