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

The complete proof of the main theorem lives in the build-on-demand
`NativeCaseAnalysis` library ([NativeCaseAnalysis/ProofOfMainTheorem.lean](NativeCaseAnalysis/ProofOfMainTheorem.lean)).
Its expensive step —
[NativeCaseAnalysis/ComputationalStep.lean](NativeCaseAnalysis/ComputationalStep.lean),
which checks all ~2 million solution-table rows with `native_decide` — is kept out
of the default build targets so that every CI run does not take hours to complete.
Run it yourself (about 25 minutes on 16 cores, with `solution_tree_v6.csv` unzipped
at the repo root) with `lake build NativeCaseAnalysis`. A kernel-only variant
(`KernelCaseAnalysis`), which removes the compiler from the trusted base, is in
progress.

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
