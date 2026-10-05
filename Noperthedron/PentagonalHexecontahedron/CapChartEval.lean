module

public import Noperthedron.PentagonalHexecontahedron.CapChart

@[expose] public section

/-!
# The cap charts as real maps

`rChartU`, `rChartW`: the real views and Cayley vectors of a cap chart at a
point y = (μ, τ, p₀, p₁, p₂), written with real arithmetic and the real
values of the exact frame, with the same case structure as `makeChart`;
`eval_makeChart_u`/`_w` say that the polynomial chart evaluates to them.
-/

namespace Noperthedron.PentagonalHexecontahedron.Cap

open NPoly PVec

/-- The real value of an exact vector. -/
noncomputable abbrev kv (v : KVec) : Fin 3 → ℝ := PVec.kval v

theorem kval_kneg (v : KVec) : kv (kneg v) = -kv v := by
  funext i; simp [kv, PVec.kval, kneg, IcoQ.val, IcoQ.neg]; ring

theorem val_kint (n : ℤ) : (kint n).val = n := by simp [kint, IcoQ.val_ofRat]

theorem val_kdot (a b : KVec) : (kdot a b).val = rdot (kv a) (kv b) := by
  simp only [kdot, rdot, kv, PVec.kval]
  rw [show IcoQ.add = (· + ·) from rfl, show IcoQ.mul = (· * ·) from rfl]
  simp only [IcoQ.val_add, IcoQ.val_mul]
  ring

theorem kval_kcross (a b : KVec) : kv (kcross a b) = rcross (kv a) (kv b) := by
  funext i
  fin_cases i <;>
  · simp only [kcross, rcross, kv, PVec.kval]
    rw [show IcoQ.sub = (· - ·) from rfl, show IcoQ.mul = (· * ·) from rfl]
    simp [IcoQ.val_sub, IcoQ.val_mul]

theorem eval_pint (n : ℤ) (y : Fin 5 → ℝ) : NPoly.eval 5 (pint n) y = n := by
  simp [pint, NPoly.eval_const, val_kint]

theorem eval_mu (y : Fin 5 → ℝ) : NPoly.eval 5 mu y = y 0 := NPoly.eval_var 5 0 y
theorem eval_tau (y : Fin 5 → ℝ) : NPoly.eval 5 tau y = y 1 := NPoly.eval_var 5 1 y
theorem eval_pv (k : ℕ) (y : Fin 5 → ℝ) :
    NPoly.eval 5 (pv k) y = y ⟨(2 + k) % 5, Nat.mod_lt _ (by norm_num)⟩ := NPoly.eval_var 5 _ y

/-- The real p variable k. -/
noncomputable def rpv (y : Fin 5 → ℝ) (k : ℕ) : ℝ := y ⟨(2 + k) % 5, Nat.mod_lt _ (by norm_num)⟩

noncomputable def rRatioVar (st : Setup) (id : ChartId) (y : Fin 5 → ℝ) (k : ℕ) : ℝ :=
  if id.ratio = 1 then
    if (List.range 3).any (fun i => !st.strong i && pvarOf id i = some k) then y 0 * rpv y k else rpv y k
  else if id.ratio = 2 ∧ pvarOf id id.ratioCoord = some k then
    let inner := (id.z : ℝ) * y 0 + rpv y k
    if id.ratioSign then inner else -inner
  else rpv y k

theorem eval_ratioVar (st : Setup) (id : ChartId) (y : Fin 5 → ℝ) (k : ℕ) :
    NPoly.eval 5 (ratioVar st id k) y = rRatioVar st id y k := by
  unfold ratioVar rRatioVar
  split_ifs <;> simp [NPoly.eval_mul, NPoly.eval_add, NPoly.eval_scale, eval_mu, eval_pv, eval_pint, rpv]

/-- The real (e, s₀) of tie-scheme chart m. -/
noncomputable def rTieES (m Z Z2 K Kp : ℕ) (y : Fin 5 → ℝ) : ℝ × ℝ :=
  let μ := y 0
  let p0 := rpv y 0
  let q := rpv y 1
  let eK := (K : ℝ) * μ + p0
  if m = 10 then (μ * p0, μ * q)
  else if m = 11 then (μ * p0, (Kp : ℝ) * μ + q)
  else if m = 12 then (μ * p0, -((Kp : ℝ) * μ + q))
  else if m = 13 then (eK, μ * q)
  else if m = 14 then (eK, -((Z : ℝ) * μ + q))
  else if m = 15 then (eK, eK + μ * q)
  else if m = 16 then (eK, eK + (Z2 : ℝ) * μ + q)
  else (eK, (Z : ℝ) * μ + q * (p0 + ((K - Z - Z2 : ℕ) : ℝ) * μ))

theorem eval_tieES (m Z Z2 K Kp : ℕ) (y : Fin 5 → ℝ) :
    NPoly.eval 5 (tieES m Z Z2 K Kp).1 y = (rTieES m Z Z2 K Kp y).1 ∧
      NPoly.eval 5 (tieES m Z Z2 K Kp).2 y = (rTieES m Z Z2 K Kp y).2 := by
  unfold tieES rTieES
  split_ifs <;> simp [NPoly.eval_mul, NPoly.eval_add, NPoly.eval_scale, eval_mu, eval_pv, eval_pint, rpv] <;> ring

noncomputable def Setup.rTieChartES (st : Setup) (id : ChartId) (y : Fin 5 → ℝ) : Option (ℝ × ℝ) :=
  if 10 ≤ id.ratio ∧ id.kind = .face then
    (st.tieOf (id.kind, id.side, id.axis, id.sign)).map fun p => rTieES id.ratio id.z p.1 p.2.1 p.2.2 y
  else none

noncomputable def rFaceS (st : Setup) (id : ChartId) (y : Fin 5 → ℝ) : Fin 3 → ℝ := fun i =>
  if (i : ℕ) = id.axis then (if id.sign then (1 : ℝ) else -1) * (st.range i : ℝ) else
    match pvarOf id i with
    | some k => rRatioVar st id y k
    | none => 0

theorem eval_faceS (st : Setup) (id : ChartId) (y : Fin 5 → ℝ) (i : Fin 3) :
    NPoly.eval 5 (faceS st id i) y = rFaceS st id y i := by
  unfold faceS rFaceS
  by_cases ha : (i : ℕ) = id.axis
  · simp only [ha, if_true, eval_pint]; cases id.sign <;> simp
  · simp only [ha, if_false]
    rcases h : pvarOf id i with _ | k <;> simp [eval_ratioVar, NPoly.eval_zero]

/-- The real (e, s). -/
noncomputable def rES (st : Setup) (id : ChartId) (A B : KVec) (y : Fin 5 → ℝ) : ℝ × (Fin 3 → ℝ) :=
  let sgn : ℝ := if id.sign then 1 else -1
  match id.kind with
  | .fe => (1, fun i => rRatioVar st id y i)
  | .cone | .mcone =>
    let center : Fin 3 → ℝ := fun i =>
      if id.kind = .mcone then
        if st.aniso then (if (i : ℕ) = 0 then 1 else 0)
        else
          if (i : ℕ) = 0 then rdot (rcross (kv st.x) (kv A)) (kv st.e1) + rdot (rcross (kv st.x) (kv B)) (kv st.e1) * y 1
          else if (i : ℕ) = 1 then rdot (rcross (kv st.x) (kv A)) (kv st.e2) + rdot (rcross (kv st.x) (kv B)) (kv st.e2) * y 1
          else 0
      else 0
    (1, fun i =>
      let sig := if (i : ℕ) = id.axis then sgn else
        match pvarOf id i with
        | some k => rRatioVar st id y k
        | none => 0
      center i + ((st.coneScale id.kind i : ℤ) : ℝ) * rpv y 0 * sig)
  | .face =>
    match st.rTieChartES id y with
    | some es => (es.1, fun i => if (i : ℕ) = 0 then es.2 else rFaceS st id y i)
    | none => (rpv y 0, rFaceS st id y)

theorem eval_eAndS (st : Setup) (id : ChartId) (A B : KVec) (y : Fin 5 → ℝ) :
    NPoly.eval 5 (eAndS st id A B).1 y = (rES st id A B y).1 ∧
      ∀ i, NPoly.eval 5 ((eAndS st id A B).2 i) y = (rES st id A B y).2 i := by
  unfold eAndS rES
  rcases hk : id.kind with _ | _ | _ | _
  · simp [eval_pint, eval_ratioVar]
  rotate_left 2
  · -- Faces (possibly tie-scheme charts).
    by_cases hr : 10 ≤ id.ratio ∧ id.kind = .face
    · have e1 : st.tieChartES id = (st.tieOf (id.kind, id.side, id.axis, id.sign)).map
          (fun p => tieES id.ratio id.z p.1 p.2.1 p.2.2) := by simp [Setup.tieChartES, hr]
      have e2 : st.rTieChartES id y = (st.tieOf (id.kind, id.side, id.axis, id.sign)).map
          (fun p => rTieES id.ratio id.z p.1 p.2.1 p.2.2 y) := by simp [Setup.rTieChartES, hr]
      rw [e1, e2]
      cases ht : st.tieOf (id.kind, id.side, id.axis, id.sign) with
      | none => exact ⟨by simp [eval_pv, rpv], eval_faceS st id y⟩
      | some p =>
        simp only [Option.map_some]
        obtain ⟨h1, h2⟩ := eval_tieES id.ratio id.z p.1 p.2.1 p.2.2 y
        refine ⟨h1, fun i => ?_⟩
        by_cases h0 : (i : ℕ) = 0
        · rw [if_pos h0, if_pos h0]; exact h2
        · rw [if_neg h0, if_neg h0]; exact eval_faceS st id y i
    · have e1 : st.tieChartES id = none := by simp [Setup.tieChartES, hr]
      have e2 : st.rTieChartES id y = none := by simp [Setup.rTieChartES, hr]
      rw [e1, e2]
      exact ⟨by simp [eval_pv, rpv], eval_faceS st id y⟩
  all_goals
    refine ⟨by simp [eval_pint, eval_pv, rpv], fun i => ?_⟩
    simp only [hk]
    split_ifs <;>
    first
    | (simp [eval_pint, eval_ratioVar, NPoly.eval_add, NPoly.eval_mul, eval_tau, eval_pv, NPoly.eval_zero,
          NPoly.eval_const, val_kdot, kval_kcross, rpv]; done)
    | (split <;> simp_all [eval_pint, eval_ratioVar, NPoly.eval_add, NPoly.eval_mul, eval_tau, eval_pv,
          NPoly.eval_zero, NPoly.eval_const, val_kdot, kval_kcross, rpv])

/-- The real direction a = A + τ B of the chart's side. -/
noncomputable def rA (st : Setup) (id : ChartId) (y : Fin 5 → ℝ) : Fin 3 → ℝ :=
  kv (st.frameAB id.side).1 + y 1 • kv (st.frameAB id.side).2

noncomputable def rChartU (st : Setup) (id : ChartId) (y : Fin 5 → ℝ) : Fin 3 → ℝ :=
  kv st.x + (y 0 * (rES st id (st.frameAB id.side).1 (st.frameAB id.side).2 y).1) • rA st id y

noncomputable def rChartW (st : Setup) (id : ChartId) (y : Fin 5 → ℝ) : Fin 3 → ℝ :=
  let s := (rES st id (st.frameAB id.side).1 (st.frameAB id.side).2 y).2
  if st.aniso then
    (y 0 * s 0) • rcross (kv st.x) (rA st id y) + ((y 0 * y 0) * s 1) • rA st id y + ((y 0 * y 0) * s 2) • kv st.x
  else
    (y 0 * s 0) • kv st.e1 + (y 0 * s 1) • kv st.e2 + ((y 0 * y 0) * s 2) • kv st.x

theorem eval_chartA (st : Setup) (id : ChartId) (y : Fin 5 → ℝ) :
    (PVec.add (PVec.const (st.frameAB id.side).1) (PVec.smul tau (PVec.const (st.frameAB id.side).2))).eval y =
      rA st id y := by
  simp [PVec.eval_add, PVec.eval_smul, PVec.eval_const, eval_tau, rA, kv]

theorem eval_makeChart_u (st : Setup) (id : ChartId) (y : Fin 5 → ℝ) :
    (makeChart st id).u.eval y = rChartU st id y := by
  obtain ⟨he, -⟩ := eval_eAndS st id (st.frameAB id.side).1 (st.frameAB id.side).2 y
  simp only [makeChart, rChartU, PVec.eval_add, PVec.eval_smul, PVec.eval_const, NPoly.eval_mul, eval_mu, he,
    eval_tau, rA, kv]

theorem eval_makeChart_w (st : Setup) (id : ChartId) (y : Fin 5 → ℝ) :
    (makeChart st id).w.eval y = rChartW st id y := by
  obtain ⟨-, hs⟩ := eval_eAndS st id (st.frameAB id.side).1 (st.frameAB id.side).2 y
  unfold makeChart rChartW
  split_ifs <;>
  simp only [PVec.eval_add, PVec.eval_smul, PVec.eval_const, PVec.eval_cross, NPoly.eval_mul, eval_mu, hs,
    eval_tau, rA, kv, add_assoc]

end Noperthedron.PentagonalHexecontahedron.Cap
