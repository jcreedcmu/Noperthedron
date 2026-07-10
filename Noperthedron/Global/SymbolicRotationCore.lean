/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Noperthedron.Global.SecondPartialHelpers

/-!
# Shared semantic core for symbolic rotation derivatives

Facts shared by the inner (`SymbolicRotationSemantics`) and outer
(`SymbolicRotationOuter`) semantic bridges:

* the `Sign` action calculus (`act_apply`, `mul_act`, `clm_act`, `act_hasDerivAt`);
* extraction forms of the certified body transitions
  (`Body.derivθ_correct_of_eq`, `Body.derivφ_correct_of_eq`);
* `Body.differentiable_comp` — joint differentiability of every body family,
  generic in the domain;
* the Euclidean coordinate-perturbation lemmas `coord_single_same` /
  `coord_single_other`, generic in the dimension.
-/

open scoped RealInnerProductSpace

namespace GlobalTheorem

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-! ### Coordinate perturbation along a basis direction, generic in the dimension -/

lemma coord_single_same {n : ℕ} (i : Fin n) (y : E n) (t : ℝ) :
    (y + t • (EuclideanSpace.single i 1 : E n)).ofLp i = y.ofLp i + t := by
  simp

lemma coord_single_other {n : ℕ} {i j : Fin n} (hij : j ≠ i) (y : E n) (t : ℝ) :
    (y + t • (EuclideanSpace.single i 1 : E n)).ofLp j = y.ofLp j := by
  simp [hij]

namespace SymbolicRotation

/-! ### Sign bookkeeping -/

namespace Sign

lemma act_apply (s : Sign) (A : ℝ³ →L[ℝ] ℝ²) (v : ℝ³) :
    (s.act A) v = s.act (A v) := by
  cases s <;> simp [act]

lemma mul_act {A : Type*} [InvolutiveNeg A] (s s' : Sign) (a : A) :
    (s.mul s').act a = s.act (s'.act a) := by
  cases s <;> cases s' <;> simp [mul, act]

lemma clm_act (s : Sign) (A : ℝ² →L[ℝ] ℝ²) (v : ℝ²) :
    A (s.act v) = s.act (A v) := by
  cases s <;> simp [act]

lemma act_hasDerivAt {f : ℝ → ℝ²} {f' : ℝ²} {x : ℝ} (s : Sign)
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t => s.act (f t)) (s.act f') x := by
  cases s
  · exact hf
  · exact hf.neg

end Sign

/-! ### Body transitions and differentiability -/

namespace Body

/-- `Body.derivθ_correct`, extracted for a transition known to be defined. -/
lemma derivθ_correct_of_eq {b b' : Body} {s : Sign}
    (h : Term.derivBodyθ b = some (s, b')) (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun x => b.eval x φ S) (s.act (b'.eval θ φ S)) θ := by
  have hc := Body.derivθ_correct b θ φ S
  rw [h] at hc
  exact hc

/-- `Body.derivφ_correct`, extracted for a transition known to be defined. -/
lemma derivφ_correct_of_eq {b b' : Body} {s : Sign}
    (h : Term.derivBodyφ b = some (s, b')) (θ φ : ℝ) (S : ℝ³) :
    HasDerivAt (fun x => b.eval θ x S) (s.act (b'.eval θ φ S)) φ := by
  have hc := Body.derivφ_correct b θ φ S
  rw [h] at hc
  exact hc

/-- Joint differentiability of every body family in the two angles and the vector,
generic in the domain. -/
lemma differentiable_comp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f g : X → ℝ} {S : X → ℝ³} (b : Body)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (hS : Differentiable ℝ S) :
    Differentiable ℝ fun x => b.eval (f x) (g x) (S x) := by
  cases b <;> simp only [Body.eval] <;> fun_prop

end Body

end SymbolicRotation

end GlobalTheorem
