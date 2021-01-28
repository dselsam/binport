`port34` is a tool for building lean4 `.olean` files from lean3 `.tlean` files.

# Building

- Build [this branch of lean4](https://github.com/dselsam/lean4/tree/port34) in directory `./lean4`.
- `make` should now produce the executable `port34`.

# Porting

- Build [this branch of lean3](https://github.com/dselsam/lean/tree/port34) in directory `./lean3`.
- Build a compatible version of [mathlib](https://github.com/leanprover-community/mathlib) in directory `./mathlib`.
  - ("compatible" just means uses the same version of lean3 that the `port34` branch builds on)
- To port, use the following commands (for "lib" in [`Lean3`, `Mathlib`]):
  - `make clear<lib>`: removes `.olean` and `.tlean` files
  - `make build<lib>`: builds `.olean` and `.tlean` files
  - `make unport<lib>`: removes lean4 `.olean` files
  - `make port<lib>`: generates lean4 `.olean` files
  - see [https://github.com/dselsam/port34/blob/master/Makefile](Makefile) for details.
