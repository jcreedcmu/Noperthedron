# Noperthedron

This project formalizes the main result of
["A convex polyhedron without Rupert's property"](https://arxiv.org/abs/2508.18475)
by Jakob Steininger & Sergey Yurkevich (cited as `[SY25]` herein).

We prove, using the Lean 4 theorem prover, that the Noperthedron does not "[fit through itself](https://en.wikipedia.org/wiki/Prince_Rupert%27s_cube)".

<p align="center">
<img src="./home_page/assets/noperthedron.png" width="200" alt="noperthedron">
</p>

See the [dependency graph](https://jcreedcmu.github.io/Noperthedron/blueprint/dep_graph_document.html) for an overview of the project's structure.

The proof involves constructing a large tree object and verifying that it has certain properties.
The original authors performed [their version of this computation](https://github.com/Jakob256/Rupert) using Sagemath.
We perform the computation in a natively-compiled Lean program that emits a value of a carefully crafted type called `ValidTable`.

## Project Structure

The definition of the main theorem proposition lives in [MainTheorem.lean](Noperthedron/MainTheorem.lean).

The proof of the main theorem, given existence of a valid solution table, lives in
[ProofOfMainTheoremWithHole.lean](Noperthedron/ProofOfMainTheoremWithHole.lean).

The program to construct a valid solution table is [constructValidTable.lean](constructValidTable.lean).

The self-contained proof of the main theorem will live in
[ProofOfMainTheorem.lean](Noperthedron/ProofOfMainTheorem.lean).
This proof currently depends on the `sorry` axiom due to performance problems in
[ComputationalStep.lean](Noperthedron/ComputationalStep.lean).

## Getting Started

[Install Lean](https://lean-lang.org/install/manual/), clone this project, then build it with:

```
lake exe cache get
lake build
```

To build the blueprint, install [leanblueprint](https://github.com/PatrickMassot/leanblueprint) with something like
```
pip install leanblueprint
```
Then you can build all HTML and PDF content and check correspondence of blueprint decls (i.e. uses of `\lean`) with
actual lean identifiers by doing
```
leanblueprint all
```
To run a server hosting the html, run
```
leanblueprint serve
```

## License Information

Portions of this project use Apache License 2.0–licensed code from
https://github.com/badly-drawn-wizards/noperthedron
©2025 Reuben Steenekamp
See LICENSE for details.
