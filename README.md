# Noperthedron

This project formally proves that the Noperthedron of
["A convex polyhedron without Rupert's property"](https://arxiv.org/abs/2508.18475)
by Jakob Steininger & Sergey Yurkevich (`[SY25]`) does not
"[fit through itself](https://en.wikipedia.org/wiki/Prince_Rupert%27s_cube)".

<p align="center">
<img src="./home_page/assets/noperthedron.png" width="200" alt="noperthedron">
</p>

The proof is written in Lean 4 and depends only on the three standard axioms `[propext, Classical.choice, Quot.sound]`.
Typechecking it takes about 5 minutes on a 16-core machine (1.2 CPU-hours).

Unlike the proof from [SY25], this one uses Cayley coordinates (closely related to quaternions)
to parametrize rotations.
Doing so sidesteps the need for much of [SY25]'s more intricate trigonometry and vector calculus.
Poses near the aligned configurations are handled via an "exact
blow-up" instead of the Local Theorem of [SY25].

An earlier proof that follows [SY25] closely is preserved at the tag
[`lean-v4.35.0`](https://github.com/jcreedcmu/Noperthedron/tree/lean-v4.35.0).

## Statement

A full problem statement that uses only Mathlib definitions lives in
[Noperthedron/MainTheorem.lean](Noperthedron/MainTheorem.lean).
The vertices of the Noperthedron are defined as `exactVerts` in [Noperthedron/Vertices/Exact.lean](Noperthedron/Vertices/Exact.lean).
The final top-level proof lives in
[CayleyKernel/Main.lean](CayleyKernel/Main.lean):

```lean
theorem Cayley.Kernel.noperthedron_not_rupert : ¬ IsRupert exactVerts
theorem Cayley.Kernel.exists_not_rupert : ExistsNonRupertPolyhedron
```

## Layout

| Path | Library | Contents |
| --- | --- | --- |
| `Noperthedron/` | `Noperthedron` | the statement, the exact vertices, and the reduction to rotation-only poses |
| `Cayley/Checker/` | `CayleyChecker` (Mathlib-free) | the checker the kernel runs |
| `Cayley/Soundness/` | `Cayley` | `Cayley.kernel_sound`: if the checker accepts a tree for each of the 15 root boxes, the Noperthedron is not Rupert |
| `CayleyKernel/` | `CayleyKernel` (not a default target) | the elaboration-time loader, the generated chunk modules, and the main theorem |
| `search/` | Rust | the floating-point search that produces the certificate tree |
| `CayleyCert.lean` | executable `cayleyCert` | native check of a tree, and generation of the kernel chunks |

The checker, in `Cayley/Checker/`:

* `Geometry`, `Data`: the integer tables (trigonometric constants, vertices, charts) and the
  type `Box` of boxes in pose space. `EvalNat` is a small elaborator that computes the
  packed vertex tables as numerals.
* `Leaf`: Kronecker-packed polynomial bounds, and the gap, blended gap and domain leaf tests
  built on them.
* `Tree`: certificate trees, the 15 root boxes, and the tree walk `checkTree`.

Its soundness proof, in `Cayley/Soundness/`:

* `Reduction/`: from `IsRupert exactVerts` to a Rupert pair `(s(u,v), s(u,v)·B_j·Cay(r))` in
  the reduced domain (a wedge of outer views, an orbit-maximal relative rotation, a 5-chart
  Cayley atlas).
* `Tables/`: the checker's tables of `cos/sin(2πk/15)`, the vertices and the symmetries are
  within explicit errors of the true values.
* `Pack/`: the packed polynomial arithmetic and its lower bounds (coefficient bounds and
  quadratic Bernstein bounds) are sound on `[-1,1]⁵`.
* `Leaf/`: each leaf kind is sound (gap separation by a vertex or by a point on a segment
  between two vertices, the blown-up paired test, disk, wedge, chart and orbit exclusions).
* `Tree`, `Main`: the tree walk, the coverage of the reduced domain by the 15 root boxes, and
  `kernel_sound`.

`Cayley/Soundness/Reduction/CayleyMatrix.lean` is ported from
[NopertTriakisTetrahedron](https://github.com/dwrensha/NopertTriakisTetrahedron) (Apache-2.0).
[`Cayley/DESIGN.md`](Cayley/DESIGN.md) describes the mathematics.

## Building

[Install Lean](https://lean-lang.org/install/manual/), clone this project, then build the
statement, the checker and its soundness proof (no data needed):

```
lake exe cache get
lake build
```

The certificate tree (212,601 leaves, 3.2 MB) is not committed. To generate it (about
15 minutes on 16 cores) and cut it into kernel chunks:

```
cd search && cargo build --release
LOOK=1 NL=5 QS=12 WIDE=1 NS=12 AMAX=0.12 NA=6 BERN=1 BLEND=6 ./export_all.sh ../.cayley-data/tree
cd ..
lake build cayleyCert
.lake/build/bin/cayleyCert check .cayley-data/tree/cover.txt     # optional native check, about 2 minutes
.lake/build/bin/cayleyCert gen .cayley-data/tree/cover.txt .cayley-data/kernel CayleyKernel/Gen 16 360
```

The export is deterministic, so `cayleyCert gen` reproduces the committed `CayleyKernel/Gen` modules.
Each generated module records a hash of its data file, so a different tree changes the
modules and Lake rebuilds them.
Then run the kernel check:

```
lake build CayleyKernel.Main
```

The build ends by printing the axioms the main theorem depends on:

```
info: CayleyKernel/Main.lean:66:0: 'Cayley.Kernel.exists_not_rupert' depends on axioms: [propext, Classical.choice, Quot.sound]
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
