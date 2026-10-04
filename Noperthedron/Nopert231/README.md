# Candidate #231 is a Nopert

This directory, with the generic `Noperthedron/Atlas/` library, formalizes the proof that Candidate #231 is a Nopert (not Rupert, `¬ IsRupert`). Candidate #231 is a convex polyhedron with 20 vertices and 27 faces (2 pentagons, 20 triangles, 5 planar quadrilaterals) and fivefold symmetry about the z axis. The certificate data is produced by the C++ pipeline (the `nopert231` branch of the companion C++ repository); its `README.md` explains how the proof works and how to rebuild it with `rebuild.sh`.

## The main result

The executable `constructNopert231 <tube manifest.txt> <chart directory>` (`constructNopert231.lean`) decodes and checks all certificate tables, then builds

```lean
CheckedChartTables.notRupert : ∀ P : C5Model, ¬ IsRupert P.verts
```

(`NativeExecutable.lean`) and instantiates it for

```lean
¬ IsRupert exactVerts            -- exactModel_verts ▸ proof exactModel
¬ IsRupert Ideal231.model.verts  -- idealized #231, exactly planar quads
```

- `IsRupert` is the upstream statement of the Rupert property (`Noperthedron/MainTheorem.lean`).
- `C5Model` (`Vertices.lean`): four real seeds rotated by 2πk/5 about z, with every vertex within `modelErrorQ` = 6·10⁻¹⁶ of the rational vertices `rationalVertices`.
- Trust: the kernel proves the bridge from valid tables to `¬ IsRupert` and every geometric lemma. The tables are checked by compiled code (`Table.Valid` decided natively, the same trust as `native_decide`), and the program carries the resulting proofs into the final value. It prints `constructed proof: no C5Model ... is Rupert` and then the instantiations.

The other executables check parts of the data: `validate_code_pack` (one identity-tube table), `check_identity_tube` (the whole tube: tables matched to the code triangles), `check_global_rows` (per-code 5D packs, for development) and `exact5d_golden` (golden values for the C++ port of the checks).

## Files

Model and approximation:
- `Vertices.lean`: `rationalVertices` (generated; see below), `exactVertex`, `exactVerts`, `C5Model`.
- `Approximation.lean`, `TightApproximation.lean`: the rational vertices are close to the exact fivefold rotations of the seeds (`tightVertexErrorQ` = 6·10⁻¹⁶); `exactModel` as a `C5Model`.
- `Ideal231.lean`: idealized #231 (seed 1's height chosen so that the quads are exactly planar, `quad_planar`) as a `C5Model`, with its closeness decided by the kernel.
- `GeneratedTangentCones.lean` (generated): tangent-cone generators of each vertex, used by `SparseSupport.lean` to check support with at most seven comparisons.

Symmetry and the pose domain:
- `Symmetry.lean`, `SymmetryLocal.lean`: the fivefold rotation; local rigidity at the symmetry strata.
- `Tightening.lean`: reduction to the view wedge (azimuth in [0, 2π/5], upper hemisphere) and bounded pose parameters.
- `CayleyAtlas.lean`, `AtlasPose.lean`, `AtlasInterval.lean`, `AtlasQuadratic.lean`, `QuadraticBernstein.lean`: the relative rotation in four bounded Cayley charts, rational boxes, exact quadratics and their Bernstein bounds.
- `FundamentalDomain.lean`, `AtlasFundamentalPrune.lean`, `FundamentalChart3.lean`: the max-trace fivefold fundamental domain; the quadratic pruning rows; the fixed table excluding chart 3.
- `AtlasProjectiveView.lean`: projective view triangles, `upperWedgeTriangle` = (1,0,0), (10/41, 31/41, 0), (0,0,1).
- `WedgeCover.lean`, `WedgeCoverData.lean` (generated): `codeTriangles_cover`, the code triangles cover the upper wedge (decision tree checked by `decide +kernel`).

Certificates:
- `Certificate.lean`, `LocalCertificate.lean`, `AtlasLocalCertificate.lean`: balanced-support certificates and symmetry-local certificates.
- `AtlasEdgeCertificate.lean`, `AtlasProjectiveEdgeCertificate.lean`: edge-cycle rows in the Cayley atlas, over projective view triangles.
- `AtlasProjectiveGlobalRigidity.lean`, `AtlasProjectiveGlobalCertificate.lean`, `AtlasProjectiveMixedGlobalCertificate.lean`: balanced-triple certificates away from the identity, and convex mixtures of them.
- `AtlasProjectiveLocalRigidity.lean`, `AtlasProjectiveLocalCertificate.lean`, `AtlasProjectiveAnnularCertificate.lean`, `QuadCoverTree.lean`: local (identity-tube) certificates: axis cages over a view triangle.
- `AtlasProjectiveLocalViewTree.lean`, `SparseLocalViewTree.lean`, `IdentityTube.lean`: identity-tube tables, one per code triangle, and `not_translated_rupert_of_tables`.
- `AtlasProjectiveSolutionTree.lean`: the 5D tables (rows: code root, view and Cayley splits, relaxed regions, certificates, tube citations, prunes) and their soundness.
- `IsNotRupert.lean`: `not_rupert_of_valid_tables`, from four valid chart tables to `¬ IsRupert P.verts`.

Native checking:
- `PackedLocalViewTree.lean`, `PackedSolutionTree.lean`: decoders for the packs written by the C++ tools (untrusted: the decoded tables are what is checked).
- `NativeExecutable.lean`: the parallel native checker and `CheckedChartTables`.

`Noperthedron/Atlas/` holds the polyhedron-independent pieces: Cayley poses and quadratics, projective view triangles, local rigidity, and the Bernstein, edge and local certificate arithmetic.

## Generated files

`Vertices.lean` (the `rationalVertices` and `seedVertex` bodies), `GeneratedTangentCones.lean` and `WedgeCoverData.lean` are written by `scripts/update_vertices.py`, `scripts/emit_tangent_cones.py` and `scripts/emit_wedge_cover.py` from the C++ pipeline's `codebdd` output. The scripts find it through `--model_dir DIR` or `$MODEL_DIR` (which the C++ `rebuild.sh` sets); `scripts/model_vertices.py` loads the vertices.
