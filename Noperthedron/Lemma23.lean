import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.CompleteField

namespace Local

open scoped RealInnerProductSpace Real
open scoped Matrix

notation "Euc(" n:arg ")" => EuclideanSpace ℝ (Fin n)

/-- The positive cone of a finite collection of vectors -/
def Spanp {n : ℕ} (v : Fin n → Euc(n)) : Set Euc(n) :=
  {w | ∃ c : Fin n → ℝ, (∀ i, 0 < c i) ∧ w = ∑ i, c i • v i }

def componentwise_gt (v w : Fin 3 → ℝ) : Prop := ∀ i : Fin 3, v i > w i

infixr:20 " ≫ " => componentwise_gt

/--
Three ℝ³ vectors
--/

def Vec3 : Type := Fin 3 → Euc(3)

namespace Vec3
@[simp]
def mat (V : Vec3) : Matrix (Fin 3) (Fin 3) ℝ := fun i j => V j i
end Vec3

theorem V_apply (i : Fin 3) (V : Vec3) (X : Euc(3)): (V.matᵀ *ᵥ X) i = ⟪V i, X⟫ := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.isValue, inner,
    RCLike.inner_apply, Real.ringHom_apply, Matrix.transpose, Fin.isValue, Matrix.of_apply, Vec3.mat]
  ring_nf

instance : Coe (Matrix (Fin 1) (Fin 1) ℝ) ℝ where
  coe x := x 0 0

/--
Convert a vector to a single-column matrix
-/
def matOfVec (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 1) ℝ := fun i _ => v i

lemma matOfVec_def (v : Fin 3 → ℝ) : ((matOfVec v)ᵀ * matOfVec v : ℝ)  =
    v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  simp [Matrix.mul_apply, matOfVec, Fin.sum_univ_three]
  ring_nf

@[simp]
lemma matOfVec_mulVec (A : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    matOfVec (A *ᵥ v) = A * matOfVec v := by
  ext i j
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, matOfVec]

theorem pos_mul_lem (X : Fin 3 → ℝ) (M1 M2 : Matrix (Fin 3) (Fin 1) ℝ)
    (Xpos : ∀ (i : Fin 3), 0 < X i)
    (Mpos : ∀ (i : Fin 3), M1 i 0 < M2 i 0) :
    ((matOfVec X)ᵀ * M1) 0 0 < ((matOfVec X)ᵀ * M2) 0 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_three]
  have (i : Fin 3) : 0 < matOfVec X i 0 := by simp only [matOfVec]; exact Xpos i
  have (i : Fin 3) : matOfVec X i 0 * M1 i 0 < matOfVec X i 0 * M2 i 0  := by
    simp_all only [Fin.isValue, mul_lt_mul_iff_right₀]
  grind

/-- [SY25] Lemma 23 -/
theorem langles {Y Z : Euc(3)} {V : Vec3} (hYZ : ‖Y‖ = ‖Z‖)
    (hY : Y ∈ Spanp V) (hZ : Z ∈ Spanp V) :
    ⟪V 0, Y⟫ ≤ ⟪V 0, Z⟫ ∨ ⟪V 1, Y⟫ ≤ ⟪V 1, Z⟫ ∨ ⟪V 2, Y⟫ ≤ ⟪V 2, Z⟫ := by
  by_contra h
  simp only [Fin.isValue, not_or, not_le] at h
  obtain ⟨h1, h2, h3⟩ := h

  let Vm := V.mat

  have compwise : Vmᵀ *ᵥ Y ≫ Vmᵀ *ᵥ Z := by
    intro i; rw [V_apply, V_apply]; fin_cases i <;> assumption

  let ⟨Yco, ⟨Ypos, Ysum⟩⟩ := hY -- [SY25] calls these
  let ⟨Zco, ⟨Zpos, Zsum⟩⟩ := hZ -- Yco = λ and Zco = ν

  have Yvec : Y = Vm *ᵥ Yco := by
    ext i
    simp [Vm, Matrix.mulVec, dotProduct]
    ring_nf
    have : Y.ofLp i = (∑ x, Yco x • V x).ofLp i :=
      congrFun (congrArg WithLp.ofLp Ysum) i
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at this
    conv at this => rhs; arg 2; intro x; rw [mul_comm]; skip
    exact this

  have Zvec : Z = Vm *ᵥ Zco := by
    ext i
    simp [Vm, Matrix.mulVec, dotProduct]
    ring_nf
    have : Z.ofLp i = (∑ x, Zco x • V x).ofLp i :=
      congrFun (congrArg WithLp.ofLp Zsum) i
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at this
    conv at this => rhs; arg 2; intro x; rw [mul_comm]; skip
    exact this

  have helper (co : Fin 3 → ℝ) (i : Fin 3) : (Vmᵀ * Vm * matOfVec co) i 0 = (Vmᵀ *ᵥ Vm *ᵥ co) i := by
    simp only [Fin.isValue, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, matOfVec,
      Matrix.mulVec, dotProduct]
    ring_nf

  have main_ineq (i : Fin 3) : (Vmᵀ * Vm * matOfVec Yco) i 0 > (Vmᵀ * Vm * matOfVec Zco) i 0 := by
    specialize compwise i
    rw [Yvec, Zvec] at compwise
    rw [helper Yco i, helper Zco i]
    exact compwise

  -- For the next few steps, we need to convert a vector to a matrix
  -- so we can reason about matrix product associativity and transposes.
  -- We want to go ⟪Y, Y⟫ = YᵀY = (Vλ)ᵀ(Vλ) = λᵀVᵀVλ
  -- so that we can use the fact that `compwise` says VᵀVλ ≫ VᵀVμ.
  let Ym := matOfVec Y
  let Zm := matOfVec Z

  have hz := by calc
    ‖Y‖^2 = ⟪Y, Y⟫ := by rw [real_inner_self_eq_norm_sq Y]
    _     = Ymᵀ * Ym := by rfl
    _     = (matOfVec Y)ᵀ * (matOfVec Y) := by rfl
    _     = (matOfVec (Vm *ᵥ Yco))ᵀ * (matOfVec (Vm *ᵥ Yco)) := by rw [Yvec]
    _     = (matOfVec Yco)ᵀ * (Vmᵀ * Vm * matOfVec Yco) := by
              simp only [matOfVec_mulVec, Matrix.transpose_mul, Fin.isValue]
              repeat rw [Matrix.mul_assoc]
    _     > ((matOfVec Yco)ᵀ * (Vmᵀ * Vm * matOfVec Zco)):= pos_mul_lem Yco _ _ Ypos main_ineq
    _     = ((matOfVec Zco)ᵀ * (Vmᵀ * Vm * matOfVec Yco))ᵀ := by
              simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
              repeat rw [← Matrix.mul_assoc]
    _     > ((matOfVec Zco)ᵀ * (Vmᵀ * Vm * matOfVec Zco)) := pos_mul_lem Zco _ _ Zpos main_ineq
    _     = ((Vm * matOfVec Zco)ᵀ * (Vm * matOfVec Zco)) := by
              simp only [Fin.isValue, Matrix.transpose_mul];
              repeat rw [Matrix.mul_assoc]
    _     = ((matOfVec (Vm *ᵥ Zco))ᵀ * (matOfVec (Vm *ᵥ Zco))) := by rw [matOfVec_mulVec]
    _     = ((matOfVec Z)ᵀ * (matOfVec Z)) := by rw [Zvec]
    _     = Zmᵀ * Zm := by rfl
    _     = ⟪Z, Z⟫ := by rfl
    _     = ‖Z‖^2 := by rw [real_inner_self_eq_norm_sq Z]

  rw [show ‖Y‖^2 = ‖Z‖^2 from congrFun (congrArg HPow.hPow hYZ) 2] at hz
  simp_all only [lt_self_iff_false]
