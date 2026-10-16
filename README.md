# Noperthedron

This project proves, using the Lean 4 theorem prover, that the Noperthedron of
["A convex polyhedron without Rupert's property"](https://arxiv.org/abs/2508.18475)
by Jakob Steininger & Sergey Yurkevich (`[SY25]`) does not
"[fit through itself](https://en.wikipedia.org/wiki/Prince_Rupert%27s_cube)".

<p align="center">
<img src="./home_page/assets/noperthedron.png" width="200" alt="noperthedron">
</p>

The proof depends only on Lean's three standard axioms `[propext, Classical.choice, Quot.sound]`.
Typechecking it takes about 5.5 minutes (1.3 CPU-hours) on a 16-core machine.

Unlike with the proof from [SY25], this proof uses Cayley coordinates (closely related to quaternions)
to parametrize rotations.
Doing so sidesteps the need for some of [SY25']s more involved calculations
with approximate trigonomtry and vector calculus.
Poses near the aligned configurations are handled via an "exact
blow-up" instead of the Local Theorem of [SY25].
See [cayley/DESIGN.md](cayley/DESIGN.md) for details.

An earlier proof that follows [SY25] closely is preserved at the tag
[`lean-v4.35.0`](https://github.com/jcreedcmu/Noperthedron/tree/lean-v4.35.0).

## Statement

A full problem statement that uses only Mathlib definitions and lives in
[Noperthedron/MainTheorem.lean](Noperthedron/MainTheorem.lean).
The vertices of the Noperthedron are defined as `exactVerts` in [Noperthedron/Vertices/Exact.lean](Noperthedron/Vertices/Exact.lean).
The final top-level proof lives in
[CayleyKernel/Main.lean](CayleyKernel/Main.lean):

```lean
theorem Cayley.KProof.noperthedron_not_rupert : ¬ IsRupert exactVerts
theorem Cayley.KProof.exists_not_rupert : ExistsNonRupertPolyhedron
```

## Layout

| Path | Library | Contents |
| --- | --- | --- |
| `Noperthedron/` | `Noperthedron` | the statement, the exact vertices, and the reduction to rotation-only poses |
| `Cayley/Checker/` | `CayleyChecker` (Mathlib-free) | the checker the kernel runs: Kronecker-packed polynomial bounds, gap and domain leaf tests, tree walk |
| `Cayley/Soundness/` | `Cayley` | `Cayley.Pack.kernel_sound`: if the checker accepts a tree for each of the 15 root boxes, the Noperthedron is not Rupert |
| `CayleyKernel/` | `CayleyKernel` (not a default target) | the elaboration-time loader, the generated chunk modules, and the main theorem |
| `cayley/search/` | Rust | the floating-point search that produces the certificate tree |
| `cayleyCheck.lean` | executable | native validation of a tree, and generation of the kernel chunks |

Soundness, file by file:

* `Shadow`, `Moves`, `Reduction`, `Pose`, `CayleyMatrix`, `Rodrigues`: from
  `IsRupert exactVerts` to a Rupert pair `(s(u,v), s(u,v)·B_j·Cay(r))` in the reduced domain
  (a wedge of outer views, an orbit-maximal relative rotation, a 5-chart Cayley atlas).
* `Trig`, `TrigTable`, `Approx`, `QIReal`: the checker's tables of `cos/sin(2πk/15)`, the
  vertices and the symmetries are within explicit errors of the true values.
* `Pack`, `PackLayout`, `PackPoly`, `PackDecode`, `PackSound`, `PackBern`, `KVtx`: the packed
  polynomial arithmetic and its lower bounds (coefficient bounds and quadratic Bernstein
  bounds) are sound on `[-1,1]⁵`.
* `KSem`, `KGapPoly`, `KGapSound`, `KDomPoly`, `KDomSound`: each leaf kind is sound (gap
  separation, the blown-up paired test, disk, wedge, chart and orbit exclusions).
* `KTreeSound`, `KMain`: the tree walk, the coverage of the reduced domain by the 15 root boxes,
  and `kernel_sound`.

`Rodrigues.lean` and `CayleyMatrix.lean` are ported from
[NopertTriakisTetrahedron](https://github.com/dwrensha/NopertTriakisTetrahedron) (Apache-2.0).

## Building

[Install Lean](https://lean-lang.org/install/manual/), clone this project, then build the
statement, the checker and its soundness proof (no data needed):

```
lake exe cache get
lake build
```

The certificate tree (245,484 leaves, 3.5 MB) is not committed. To generate it (about
8 minutes on 16 cores) and cut it into kernel chunks:

```
cd cayley/search && cargo build --release
LOOK=1 NL=5 QS=12 WIDE=1 NS=12 AMAX=0.12 NA=6 BERN=1 ./export_all.sh ../../.cayley-data/v4
cd ../..
lake build cayleyCheck
.lake/build/bin/cayleyCheck kwalk .cayley-data/v4/cover.txt     # optional native check
.lake/build/bin/cayleyCheck kgen .cayley-data/v4/cover.txt .cayley-data/kernel CayleyKernel/Gen 16 360
```

The export is deterministic, so `kgen` reproduces the committed `CayleyKernel/Gen` modules.
Then run the kernel check:

```
lake build CayleyKernel.Main
```

The build ends by printing the axioms the main theorem depends on:

```
info: CayleyKernel/Main.lean:66:0: 'Cayley.KProof.exists_not_rupert' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Blueprint

The [blueprint](blueprint/src) describes the mathematics of the proof and links each step
to its Lean declaration. To build it, install
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) (`pip install leanblueprint`)
and run

```
leanblueprint all      # HTML and PDF, and check that every \lean{} name exists
leanblueprint serve    # serve the HTML locally
```

## License Information

Portions of this project use Apache License 2.0–licensed code from
https://github.com/badly-drawn-wizards/noperthedron
©2025 Reuben Steenekamp
See LICENSE for details.
