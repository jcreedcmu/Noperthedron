# Can the Lean kernel alone check two million certificates?

*Noperthedron · Lean 4 field note · July 8, 2026*

What we measured when we tried to verify the Noperthedron solution table with
`decide +kernel` — no compiler, no `ofReduceBool`, just the trusted kernel
doing arithmetic.

## Context in three sentences

Steininger & Yurkevich's Noperthedron is the first convex polyhedron proved to
lack Rupert's property, and the proof's computational heart is a tree of
~18.7 million interval certificates. We've been formalizing it in Lean 4 and
spent two days strengthening the certificate (exact second-order Taylor terms,
then per-axis anisotropic radii) and tuning the checker, which shrank the table
to **2,051,521 rows** (978,540 global certificates, 160,543 local ones, the
rest structural splits) and the verified run to **3m25s** on 16 cores. The
question here: what would it cost to remove the last piece of extra trust and
have the kernel itself evaluate the whole check?

## The trust ladder

| Time | Route | What you trust |
|---|---|---|
| **3m25s** (measured) | Standalone native executable | Same Lean functions, compiled. You trust the Lean compiler, the toolchain, and that the printed "ValidTable constructed" means what you think. |
| **25m** (measured) | `native_decide` | The kernel checks every proof *except* the big evaluation, which is compiled and trusted via the `ofReduceBool` axiom. (`precompiledModules` would likely cut this to 5–10m.) |
| **≈1 day** (projected, 16 cores) | Kernel-only `decide +kernel` | No compiler in the trusted base at all. Axioms drop to `propext`, `Classical.choice`, `Quot.sound`. Requires a redesign — see below. |

## What we measured

Kernel cost scales linearly in rows, so we timed tiny self-contained theorems
on real table rows and extrapolated. All runs: `lake env lean`, one file,
wall-clock, 16-core machine (kernel reduction itself is single-threaded).

| Experiment | Result | Reading |
|---|---|---|
| One global certificate, row encoded as a **Lean literal**, `decide +kernel` | ~0.6 s/row marginal | ≈330× slower than the compiled checker (1.8 ms). GMP-backed `Nat` literals carry it; `Rat` ops unfold definitionally on top. |
| Same row, but parsed from a **CSV string** in-kernel | ~9 s for ~300 bytes | `String` reduces through its `List Char` model. The real table is 251 MB — months of parsing. String parsing is dead; literal encoding is mandatory. |
| Scaling: 1 → 25 → 100 literal rows | 3.3 s / 15.9 s / 61.5 s | Cleanly linear after ~2.6 s of fixed import overhead. |
| Kernel memory growth | ~70 MB/row | Term-cache growth means one monolithic `decide` over 978k rows is impossible. Must chunk into many small theorems so state is freed between declarations. |
| One **local** certificate | **OOM at ~52 GB** | The compiled checker's precomputed lookup tables (`Array.ofFn`, 8,100 sqrt entries) get re-reduced per access under the kernel with no sharing. The local check needs a kernel-friendly restructuring. |
| Plain `decide` (no `+kernel`) on the same true proposition | **fails outright** | The elaborator's whnf evaluator gets stuck where the kernel's reducer succeeds — and plain `decide` would evaluate twice anyway. `+kernel` isn't an optimization here; it's required. |

## The projected design

A practical kernel-only run is a small engineering project, not a flag flip:

- **Literal-encoded table.** The generator emits the 2M rows as Lean term
  literals across many `.lean` chunk files (~100–500 rows per theorem to bound
  kernel memory) — no `String` in sight.
- **Parallel checking.** The kernel is single-threaded per declaration, but
  `lake` type-checks chunk files in parallel, recovering the 16 cores.
- **Kernel-friendly local check.** Lookup tables as literals (or the pre-table
  code path) so one local row stops costing 52 GB. *(Done — see update below.)*

Arithmetic: 978,540 globals × 0.6 s ≈ 163 core-hours; locals optimistically
~80 more (the risk term); splits and elaborating ~1–2 GB of generated literals
add tens. Call it **250–350 core-hours ≈ a day of wall time on 16 cores** —
for a verification of the entire computation whose trusted base is the Lean
kernel and three standard axioms.

## How the table got small enough to even ask

The kernel-only idea is thinkable only because the certificate got stronger
while the checker got faster: exact second-order Taylor penalties (median half
the worst-case bound), then per-axis anisotropic radii that let boxes stretch
along the hard set's flat directions (18.7M → 2.05M rows, 9.1×), plus
round-to-10⁻¹³ hoisted vectors, tiered tests that decide most vertices with
one dot product, and precomputed vertex/norm tables — every step proved
equivalent or absorbed into existing κ-budgets, so the full chain stays
kernel-checked end to end. Two days: 2.5 hours → 3m25s.

## Update (same day): the kernel-friendly local check landed

The local-check OOM is fixed by restructuring the lookup table
(`Noperthedron/Checker/SqrtDvLiterals.lean`, generated by
`scripts/gen_sqrtdv_literals.lean`):

- The 8,100 pairwise vertex-difference norms are now **source literals** in
  curried `![…]` form (`sqrtDvCurried : Fin 2 → Fin 3 → Fin 15 → … → ℚ`), so
  a kernel access walks ≤ 40 `Fin.cons` cells. The culprit was `Array.ofFn`'s
  push chain: under the kernel, access cost grows roughly quadratically with
  index — reading entry 8099 of the old table *alone* blew past 600 s / 12 GB
  under `decide +kernel`, while entry 91 took half a second. (The 270-entry
  vertex table and the per-pose 90-entry `rowDots` are ~900× less work and
  measured harmless.)
- Six `decide +kernel` chunk lemmas (1,350 sqrt evaluations each; ~85 s and
  ≤ 7 GB, once per build of the generated file) certify every literal against
  `sqrtApprox.upper_sqrt.norm (pythonVertexA a - pythonVertexA b)`, so
  `sqrtDv_eq` and everything downstream is unchanged. One kernel sqrt
  evaluation costs only ~5 ms / ~2 MB — the sqrt was never the problem.
- The compiled hot loop keeps its O(1) array read via a proven-equal
  `@[csimp]` implementation whose table is built once per process *from* the
  literals. Without this, curried lookups cost the compiled checker
  8.7 ms/row (`checkPy` 11.4 ms vs 2.7 ms); with it, compiled per-row cost is
  unchanged (2.65 ms vs 2.68 ms baseline, and the full 2,051,521-row
  `constructValidTable` run still passes at the same total core-time).
  Axioms stay `propext, Classical.choice, Quot.sound`.

Measured: one full local certificate under `decide +kernel` = **~5 s and
~1.6 GB marginal** (was OOM at ~52 GB); ten real rows sampled across the
table check in 52 s total with flat memory (~130 MB/row marginal, freed
between declarations). Locals thus project to 160,543 × ~5 s ≈ **230
core-hours** — about 3× the optimistic guess above, putting the kernel-only
total at roughly **400–450 core-hours ≈ 1.1–1.2 days of wall time on 16
cores**.

---

*Measurements from the `second-order` branch @ `bd2412e` · projections assume
linear scaling, which held 1→100 rows. Update measurements from `main` @
`1ce7de3` + the literal-table change, on a 10-core / 31 GB machine.*
