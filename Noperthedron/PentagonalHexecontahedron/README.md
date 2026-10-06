# The deltoidal hexecontahedron is a Nopert (Lean)

**Status (2026-10-06): verified.** All modules build without `sorry` (axioms: propext, Classical.choice,
Quot.sound), and `constructDeltoidalHexecontahedron` checked all certificate data (3 h 05 min on 64 cores) and
instantiated the main theorem.

The directory keeps its historical name: this branch reuses the pentagonal hexecontahedron's icosahedral pipeline
(models as I-orbits, the projective view atlas, the 5D solution tree) with the deltoidal hexecontahedron's data
(`Vertices.lean`, `IcoGroupData.lean`, `WedgeCoverData.lean`: 70 vertex slots, I-orbits of sizes 12, 30, 20).

## Main theorem

`DHTies.deltoidalHexecontahedron_not_rupert_of_checks`: checked solution tables, checked cap certificates and
checked tie certificates imply that no deltoidal hexecontahedron (`DHStatement.IsDeltoidalHexecontahedron`: any
similar copy of McCooey's 62 vertices) is Rupert. The executable `constructDeltoidalHexecontahedron` (repository
root) decodes and checks the data natively and instantiates it.

## Structure

- **Statement and the exact solid** — `DHStatement` (McCooey's vertex set; the exact solid over K = ℚ(√5, sin 72°)
  as an `IModel` (`dhIModel`), decided by the kernel: orthonormal frame, McCooey ↔ slots, orbits, stabilizers,
  closeness to the rational model, central symmetry), `DHStatementData` (generated).
- **Half-turn reduction** — `HalfTurnReduce`, `HalfTurnPose` (poses reduced into the half-turn cell; valid for
  centrally symmetric models), `AtlasHalfTurnPrune` (`Row.halfTurnPrune`, pack tag 14).
- **Caps** — `NPoly`, `MultiBernstein`, `CapPoly`, `CapWitness` (witness ⇒ not Rupert), `CapChart`,
  `CapChartEval` (chart polynomials, incl. the ux *tie scheme*, ratio 10–17), `CapCover`, `CapFrame`,
  `CapRealize`, `CapCoverMain` (every cap pose is a chart point: `cap_cover`, `tie_decomp`, `realize_tie`),
  `CapBridge`, `CapTheorem`, `CapTree`, `CapCheck`, `CapCert` (certificate check ⇒ every chart point good ⇒
  `CapCert.claim`), `CapClaim` (images s·g of a cap), `CapRow` (`Row.capLeaf`, tag 16), `DHCapData` (generated),
  `DHCaps` (`capsHold_of_certs`).
- **Tie tubes** — `TieCheck` (tie certificates ⇒ `TieClaim`), `AtlasTiePrune` (the tie row's trace bound),
  `TieRow` (`Row.tieLeaf`, tag 15; `TiesHold`), `DHTieData` (generated), `DHTies` (`tiesHold_of_certs`).
- **Executable glue** — `DHChecks` (parallel checks with kernel bridges), `DHDecode` (untrusted decoding);
  `AtlasProjectiveLocalViewTree.Row.empty` (tag 4) for tube-tree cap leaves.
- The solution tree (`AtlasProjectiveSolutionTree`) takes `ExactClaims` (caps and ties) as a hypothesis; only the
  exact solid satisfies it, which is why the theorem is about the deltoidal hexecontahedron itself and not about
  a neighborhood of models (perturbed models are Rupert).

Generated files: `DHStatementData` (`scripts/dh_statement_data.py`), `DHCapData` and `DHTieData` (nopert229
`dh_cap_lean.py`, `dh_tie_lean.py`), and the model data (`scripts/update_vertices.py`, `snub_ico_group.py`,
`emit_wedge_cover.py`).
