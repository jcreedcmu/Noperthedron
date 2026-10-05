module

public import Noperthedron.PentagonalHexecontahedron.CapTheorem
public import Noperthedron.PentagonalHexecontahedron.CapTree

@[expose] public section

/-!
# Checking a cap certificate (witness leaves)

For a chart `id` with root box `B` and a witness (v_k, c):

* `dPoly`: |u × c|² as a polynomial; `dOk` (its Bernstein bound on B is
  positive) gives u × c ≠ 0 on B (`dOk_sound`).
* `screened`: the divided witness polynomials whose bound on B is negative;
  the others are ≥ 0 on B (`screened_sound`).
* `witnessLeafOk`: `dOk` and every screened polynomial ≥ 0 on the leaf box;
  `witnessLeafOk_sound` gives the witness disjunct of `ChartGood` on the leaf
  box (points of B).
-/

namespace Noperthedron.PentagonalHexecontahedron.Cap

open NPoly PVec

def dPoly (st : Setup) (id : ChartId) (c : KVec) : NPoly 5 :=
  let d := PVec.cross (makeChart st id).u (PVec.const c)
  PVec.dot d d

theorem eval_dPoly (st : Setup) (id : ChartId) (c : KVec) (y : Fin 5 → ℝ) :
    NPoly.eval 5 (dPoly st id c) y = rdot (rcross (rChartU st id y) (kv c)) (rcross (rChartU st id y) (kv c)) := by
  simp only [dPoly, PVec.eval_dot, PVec.eval_cross, PVec.eval_const, eval_makeChart_u, kv]

def dOk (st : Setup) (pr : Params) (id : ChartId) (c : KVec) : Bool :=
  let q := dPoly st id c
  decide (0 < NPoly.lowerDeg 5 (degs q) q (rootBox st pr id))

theorem rootBox_width_nonneg (st : Setup) (pr : Params) (id : ChartId) (h : ∀ v, (rootLoHi st pr id v).1 ≤ (rootLoHi st pr id v).2) :
    ∀ i, 0 ≤ (rootBox st pr id i).2 := by
  intro i; simp only [rootBox]; linarith [h i]

theorem dOk_sound (st : Setup) (pr : Params) (id : ChartId) (c : KVec) (h : dOk st pr id c = true)
    (hw : ∀ i, 0 ≤ (rootBox st pr id i).2) (y : Fin 5 → ℝ) (hy : InBoxR (rootBox st pr id) y) :
    rcross (rChartU st id y) (kv c) ≠ 0 := by
  intro h0
  have hl := lowerDeg_le_eval 5 (degs (dPoly st id c)) (dPoly st id c) (rootBox st pr id) y hw hy
  have hpos : (0 : ℚ) < NPoly.lowerDeg 5 (degs (dPoly st id c)) (dPoly st id c) (rootBox st pr id) :=
    of_decide_eq_true h
  rw [eval_dPoly, h0] at hl
  simp [rdot] at hl
  linarith

/-- The divided witness polynomials not already ≥ 0 on the root box. -/
def screened (Q : Array (NPoly 5)) (box : Box) : Array (NPoly 5) :=
  Q.filter fun q => decide (NPoly.lowerDeg 5 (degs q) q box < 0)

theorem screened_sound (Q : Array (NPoly 5)) (box : Box) (hw : ∀ i, 0 ≤ (box i).2)
    (y : Fin 5 → ℝ) (hy : InBoxR box y) (hs : ∀ q ∈ screened Q box, 0 ≤ NPoly.eval 5 q y) :
    ∀ q ∈ Q, 0 ≤ NPoly.eval 5 q y := by
  intro q hq
  by_cases hneg : NPoly.lowerDeg 5 (degs q) q box < 0
  · exact hs q (Array.mem_filter.mpr ⟨hq, by simpa using hneg⟩)
  · push Not at hneg
    have := lowerDeg_le_eval 5 (degs q) q box y hw hy
    exact le_trans (by exact_mod_cast hneg) this

/-- The real value of the witness polynomial of the chart. -/
theorem eval_chart_witnessPoly (st : Setup) (id : ChartId) (vk c vj : KVec) (y : Fin 5 → ℝ) :
    NPoly.eval 5 (witnessPoly (witnessParts (makeChart st id).u (makeChart st id).w vk c) vj) y =
      witnessValue (rChartU st id y) (rChartW st id y) (kv vk) (kv c) (kv vj) := by
  rw [eval_witnessPoly, eval_makeChart_u, eval_makeChart_w]
  rfl

end Noperthedron.PentagonalHexecontahedron.Cap
