import Mathlib.Data.Nat.ModEq
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

import Noperthedron.Basic
import Noperthedron.Bounding.OpNorm
import Noperthedron.Local.EpsSpanning
import Noperthedron.SolutionTable.Basic
import Noperthedron.SolutionTable.NopertList

namespace Solution

open Real
open Local (Triangle)
open scoped RealInnerProductSpace Real Matrix

/-- `(-1 : ℝ) ^ n` only depends on `n % 2`. -/
lemma sign_flip_from_mod (n : ℕ) : (-1 : ℝ) ^ (n % 2) = (-1 : ℝ) ^ n := by
  have h : n % 2 + 2 * (n / 2) = n := Nat.mod_add_div n 2
  -- Rewrite `n` as `n % 2 + 2 * (n / 2)` and use `(-1)^2 = 1`.
  have : (-1 : ℝ) ^ n = (-1 : ℝ) ^ (n % 2) := by
    calc
      (-1 : ℝ) ^ n = (-1 : ℝ) ^ (n % 2 + 2 * (n / 2)) := by simp [h]
      _ = (-1 : ℝ) ^ (n % 2) * (-1 : ℝ) ^ (2 * (n / 2)) := by
        simp [pow_add]
      _ = (-1 : ℝ) ^ (n % 2) * ((-1 : ℝ) ^ 2) ^ (n / 2) := by
        simp [pow_mul]
      _ = (-1 : ℝ) ^ (n % 2) := by
        simp
  simpa using this.symm

/--
The `15`-fold rotation map `RzL (2π*k/15)` only depends on `k % 15`.

This is the concrete periodicity fact needed when translating modular arithmetic on the table’s
`k`-indices into equalities of the corresponding rotated points.
-/
lemma RzL_natMod_15 (k : ℕ) :
    RzL (2 * π * (k : ℝ) / 15) = RzL (2 * π * ((k % 15 : ℕ) : ℝ) / 15) := by
  set m : ℕ := k % 15
  set r : ℕ := k / 15

  have hkNat : m + 15 * r = k := by
    simpa [m, r] using (Nat.mod_add_div k 15)
  have hk : (k : ℝ) = (m : ℝ) + 15 * (r : ℝ) := by
    have hkCast := congrArg (fun n : ℕ => (n : ℝ)) hkNat
    simpa [Nat.cast_add, Nat.cast_mul, mul_assoc] using hkCast.symm

  let x : ℝ := 2 * π * (m : ℝ) / 15
  let z : ℤ := r
  have hangle : 2 * π * (k : ℝ) / 15 = x + z * (2 * π) := by
    have : 2 * π * (k : ℝ) / 15 = 2 * π * ((m : ℝ) + 15 * (r : ℝ)) / 15 := by
      simp [hk]
    -- `ring_nf` handles the linear arithmetic over `ℝ`.
    -- The `z`-cast is definitional since `z := (r : ℤ)`.
    simpa [x, z] using (this.trans (by ring_nf))

  have hmat : Rz_mat (2 * π * (k : ℝ) / 15) = Rz_mat x := by
    -- `Rz_mat (x + z*(2π)) = Rz_mat x`, and `2π*k/15 = x + z*(2π)`.
    simp [hangle]

  -- Transport the matrix equality across `toEuclideanLin.toContinuousLinearMap`.
  have hlin :
      (Rz_mat (2 * π * (k : ℝ) / 15)).toEuclideanLin.toContinuousLinearMap =
        (Rz_mat x).toEuclideanLin.toContinuousLinearMap := by
    simpa using congrArg (fun M => M.toEuclideanLin.toContinuousLinearMap) hmat
  simpa [RzL, x] using hlin

lemma RzL_add_int_mul_two_pi (z : ℤ) (x : ℝ) : RzL (x + z * (2 * π)) = RzL x := by
  have hlin :
      (Rz_mat (x + z * (2 * π))).toEuclideanLin.toContinuousLinearMap =
        (Rz_mat x).toEuclideanLin.toContinuousLinearMap := by
    simp
  simp [RzL]

namespace Row

/-! ### Turning vertex indices into the concrete `nopertPt` points -/

lemma decodeI_lt_three (idx : ℕ) : Solution.decodeI idx < 3 := by
  dsimp [Solution.decodeI]
  have hmod : idx % 45 < 45 := Nat.mod_lt _ (by decide)
  have hmul : idx % 45 < 15 * 3 := by simpa using hmod
  exact Nat.div_lt_of_lt_mul hmul

def decodeIFin (idx : ℕ) : Fin 3 :=
  ⟨Solution.decodeI idx, decodeI_lt_three idx⟩

noncomputable def indexPoint (idx : ℕ) : ℝ³ :=
  Nopert.nopertPt (Solution.decodeK idx) (Solution.decodeL idx) (decodeIFin idx)

noncomputable def PTriangle (row : Solution.Row) : Triangle :=
  ![indexPoint row.P1_index, indexPoint row.P2_index, indexPoint row.P3_index]

noncomputable def QTriangle (row : Solution.Row) : Triangle :=
  ![indexPoint row.Q1_index, indexPoint row.Q2_index, indexPoint row.Q3_index]

end Row

/-! ### Membership of indexed points in the noperthedron vertex set -/

lemma c15_cpt_sub_half (i : Fin 3) : Nopert.C15 (Nopert.Cpt i) ⊆ halfNopertVerts := by
  intro v hv
  fin_cases i
  · have hv' : v ∈ Nopert.C15 Nopert.C1R := by
      simpa [Nopert.Cpt] using hv
    simp [halfNopertVerts, hv']
  · have hv' : v ∈ Nopert.C15 Nopert.C2R := by
      simpa [Nopert.Cpt] using hv
    simp [halfNopertVerts, hv']
  · have hv' : v ∈ Nopert.C15 Nopert.C3R := by
      simpa [Nopert.Cpt] using hv
    simp [halfNopertVerts, hv']

lemma Row.indexPoint_mem_nopertVerts (idx : ℕ) :
    Row.indexPoint idx ∈ Nopert.poly.vertices := by
  classical
  have hk : Solution.decodeK idx < 15 := by
    simpa [Solution.decodeK] using (Nat.mod_lt idx (by decide))
  have hv :
      RzL (2 * π * (Solution.decodeK idx : ℝ) / 15) (Nopert.Cpt (Row.decodeIFin idx)) ∈
        Nopert.C15 (Nopert.Cpt (Row.decodeIFin idx)) := by
    unfold Nopert.C15
    refine Finset.mem_image.mpr ?_
    refine ⟨Solution.decodeK idx, ?_, rfl⟩
    simpa [Finset.mem_range] using hk
  have hv_half :
      RzL (2 * π * (Solution.decodeK idx : ℝ) / 15) (Nopert.Cpt (Row.decodeIFin idx)) ∈
        halfNopertVerts :=
    c15_cpt_sub_half (Row.decodeIFin idx) hv
  have hpar : Even (Solution.decodeL idx) ∨ Odd (Solution.decodeL idx) :=
    Nat.even_or_odd (Solution.decodeL idx)
  have hmem : Row.indexPoint idx ∈ pointsymmetrize halfNopertVerts := by
    rcases hpar with hEven | hOdd
    · have hsign : (-1 : ℤ) ^ Solution.decodeL idx = 1 := by
        simpa using (Even.neg_one_pow (α := ℤ) hEven)
      apply (pointsymmetrize_mem halfNopertVerts _).2
      left
      have hidx :
          Row.indexPoint idx =
            RzL (2 * π * (Solution.decodeK idx : ℝ) / 15)
              (Nopert.Cpt (Row.decodeIFin idx)) := by
        dsimp [Row.indexPoint, Nopert.nopertPt]
        have hsign' :
            (-1 : ℤ) ^ Solution.decodeL idx •
              RzL (2 * π * (Solution.decodeK idx : ℝ) / 15)
                (Nopert.Cpt (Row.decodeIFin idx)) =
            (1 : ℤ) •
              RzL (2 * π * (Solution.decodeK idx : ℝ) / 15)
                (Nopert.Cpt (Row.decodeIFin idx)) := by
          exact congrArg (fun t => t •
            RzL (2 * π * (Solution.decodeK idx : ℝ) / 15)
              (Nopert.Cpt (Row.decodeIFin idx))) hsign
        calc
          (-1 : ℤ) ^ Solution.decodeL idx •
              RzL (2 * π * (Solution.decodeK idx : ℝ) / 15)
                (Nopert.Cpt (Row.decodeIFin idx)) =
              (1 : ℤ) •
                RzL (2 * π * (Solution.decodeK idx : ℝ) / 15)
                  (Nopert.Cpt (Row.decodeIFin idx)) := hsign'
          _ = RzL (2 * π * (Solution.decodeK idx : ℝ) / 15)
                (Nopert.Cpt (Row.decodeIFin idx)) := by simp
      simpa [hidx] using hv_half
    · have hsign : (-1 : ℤ) ^ Solution.decodeL idx = -1 := by
        simpa using (Odd.neg_one_pow (α := ℤ) hOdd)
      apply (pointsymmetrize_mem halfNopertVerts _).2
      right
      have hidx :
          Row.indexPoint idx =
            - RzL (2 * π * (Solution.decodeK idx : ℝ) / 15)
              (Nopert.Cpt (Row.decodeIFin idx)) := by
        dsimp [Row.indexPoint, Nopert.nopertPt]
        have hsign' :
            (-1 : ℤ) ^ Solution.decodeL idx •
              RzL (2 * π * (Solution.decodeK idx : ℝ) / 15)
                (Nopert.Cpt (Row.decodeIFin idx)) =
            (-1 : ℤ) •
              RzL (2 * π * (Solution.decodeK idx : ℝ) / 15)
                (Nopert.Cpt (Row.decodeIFin idx)) := by
          exact congrArg (fun t => t •
            RzL (2 * π * (Solution.decodeK idx : ℝ) / 15)
              (Nopert.Cpt (Row.decodeIFin idx))) hsign
        calc
          (-1 : ℤ) ^ Solution.decodeL idx •
              RzL (2 * π * (Solution.decodeK idx : ℝ) / 15)
                (Nopert.Cpt (Row.decodeIFin idx)) =
              (-1 : ℤ) •
                RzL (2 * π * (Solution.decodeK idx : ℝ) / 15)
                  (Nopert.Cpt (Row.decodeIFin idx)) := hsign'
          _ = - RzL (2 * π * (Solution.decodeK idx : ℝ) / 15)
                (Nopert.Cpt (Row.decodeIFin idx)) := by simp
      have hidx' :
          -Row.indexPoint idx =
            RzL (2 * π * (Solution.decodeK idx : ℝ) / 15)
              (Nopert.Cpt (Row.decodeIFin idx)) := by
        simp [hidx]
      simpa [hidx'] using hv_half
  simpa [Nopert.poly, nopertVerts] using hmem

lemma Row.PTriangle_mem_nopertVerts (row : Row) :
    ∀ i, Row.PTriangle row i ∈ Nopert.poly.vertices := by
  intro i
  fin_cases i <;> simp [Row.PTriangle, Row.indexPoint_mem_nopertVerts]

lemma Row.QTriangle_mem_nopertVerts (row : Row) :
    ∀ i, Row.QTriangle row i ∈ Nopert.poly.vertices := by
  intro i
  fin_cases i <;> simp [Row.QTriangle, Row.indexPoint_mem_nopertVerts]

/-! ### Linear isometries used for congruence witnesses -/

noncomputable def signedRzIsom (dl dk : ℕ) : Euc(3) →ₗᵢ[ℝ] Euc(3) :=
  { toLinearMap := ((-1 : ℝ) ^ dl) • (RzL (2 * π * (dk : ℝ) / 15)).toLinearMap
    norm_map' := by
      intro v
      simp [LinearMap.smul_apply, norm_smul, Bounding.Rz_preserves_norm] }

/-! ### Reflections for the dihedral congruence branch -/

noncomputable def xyProj (c : ℝ³) : ℝ³ :=
  WithLp.toLp 2 fun
    | 0 => c 0
    | 1 => c 1
    | 2 => 0

noncomputable def xyPerp (c : ℝ³) : ℝ³ :=
  WithLp.toLp 2 fun
    | 0 => -c 1
    | 1 => c 0
    | 2 => 0

noncomputable def ez : ℝ³ :=
  WithLp.toLp 2 fun
    | 0 => 0
    | 1 => 0
    | 2 => 1

noncomputable def reflPlane (c : ℝ³) : Submodule ℝ ℝ³ := (ℝ ∙ xyPerp c)ᗮ

lemma xyProj_mem_reflPlane (c : ℝ³) : xyProj c ∈ reflPlane c := by
  -- `xyProj c ⟂ xyPerp c`.
  rw [reflPlane, Submodule.mem_orthogonal_singleton_iff_inner_right]
  -- Expand the Euclidean inner product (dot product) coordinatewise.
  simp [xyProj, xyPerp, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_three]
  ring

lemma ez_mem_reflPlane (c : ℝ³) : ez ∈ reflPlane c := by
  rw [reflPlane, Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [ez, xyPerp, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_three]

lemma RzL_apply_decomp (θ : ℝ) (c : ℝ³) :
    RzL θ c = (Real.cos θ) • xyProj c + (Real.sin θ) • xyPerp c + (c 2) • ez := by
  ext i
  fin_cases i <;>
    (simp [RzL, Rz_mat, xyProj, xyPerp, ez, Matrix.toLpLin_apply,
      Matrix.vecHead, Matrix.vecTail]; try ring)

lemma reflPlane_reflection_apply_RzL (θ : ℝ) (c : ℝ³) :
    (reflPlane c).reflection (RzL θ c) = RzL (-θ) c := by
  classical
  have hfix_xy : (reflPlane c).reflection (xyProj c) = xyProj c := by
    simpa using
      Submodule.reflection_mem_subspace_eq_self (K := reflPlane c) (xyProj_mem_reflPlane c)
  have hfix_ez : (reflPlane c).reflection ez = ez := by
    simpa using
      Submodule.reflection_mem_subspace_eq_self (K := reflPlane c) (ez_mem_reflPlane c)
  have hneg_perp : (reflPlane c).reflection (xyPerp c) = -xyPerp c := by
    -- Here `reflPlane c = (ℝ ∙ xyPerp c)ᗮ`.
    simpa [reflPlane] using
      (Submodule.reflection_orthogonalComplement_singleton_eq_neg (v := xyPerp c))
  -- Reflect the decomposition and use `cos (-θ)=cos θ`, `sin (-θ)=-sin θ`.
  calc
    (reflPlane c).reflection (RzL θ c)
        = (reflPlane c).reflection
            ((Real.cos θ) • xyProj c + (Real.sin θ) • xyPerp c + (c 2) • ez) := by
              simp [RzL_apply_decomp]
    _ = (Real.cos θ) • xyProj c + (Real.sin θ) • (-xyPerp c) + (c 2) • ez := by
          simp [map_add, map_smul, hfix_xy, hfix_ez, hneg_perp]
    _ = (Real.cos (-θ)) • xyProj c + (Real.sin (-θ)) • xyPerp c + (c 2) • ez := by
          simp [Real.cos_neg, Real.sin_neg, add_left_comm, add_comm]
    _ = RzL (-θ) c := by
          simp [RzL_apply_decomp]

noncomputable def reflPlaneIsom (c : ℝ³) : Euc(3) →ₗᵢ[ℝ] Euc(3) :=
  ((reflPlane c).reflection).toLinearIsometry

noncomputable def signedRzRefIsom (c : ℝ³) (dl dk : ℕ) : Euc(3) →ₗᵢ[ℝ] Euc(3) :=
  { toLinearMap :=
      ((-1 : ℝ) ^ dl) •
        ((RzL (2 * π * (dk : ℝ) / 15)).toLinearMap.comp (reflPlaneIsom c).toLinearMap)
    norm_map' := by
      intro v
      simp [reflPlaneIsom, LinearMap.smul_apply, norm_smul, Bounding.Rz_preserves_norm] }

lemma RzL_add_apply (a b : ℝ) (v : ℝ³) :
    RzL (a + b) v = RzL a (RzL b v) := by
  have h := congrArg (fun f : (ℝ³ →L[ℝ] ℝ³) => f v) (RzC.map_add_eq_mul a b)
  -- `*` on continuous linear maps is composition.
  simpa [RzC_coe, ContinuousLinearMap.mul_apply'] using h

lemma Row.indexPoint_eq_signedRzIsom_apply
    (p q dl dk : ℕ)
    (hI : Solution.decodeI p = Solution.decodeI q)
    (hL : (Solution.decodeL q + dl) % 2 = Solution.decodeL p)
    (hK : (Solution.decodeK q + dk) % 15 = Solution.decodeK p) :
    Row.indexPoint p = signedRzIsom dl dk (Row.indexPoint q) := by
  have hIFin : Row.decodeIFin p = Row.decodeIFin q := by
    ext
    simpa [Row.decodeIFin] using hI

  set kp : ℕ := Solution.decodeK p
  set kq : ℕ := Solution.decodeK q
  set lp : ℕ := Solution.decodeL p
  set lq : ℕ := Solution.decodeL q
  set ip : Fin 3 := Row.decodeIFin p
  set iq : Fin 3 := Row.decodeIFin q

  have hip : ip = iq := by simpa [ip, iq] using hIFin

  -- Turn the parity statement into an equality of sign scalars.
  have hsign : (-1 : ℝ) ^ lp = (-1 : ℝ) ^ (lq + dl) := by
    calc
      (-1 : ℝ) ^ lp = (-1 : ℝ) ^ ((lq + dl) % 2) := by simp [lp, lq, hL]
      _ = (-1 : ℝ) ^ (lq + dl) := by simpa using (sign_flip_from_mod (lq + dl))

  -- Turn the modular `k`-equality into an equality of `RzL` maps.
  have hRz :
      RzL (2 * π * ((kq + dk : ℕ) : ℝ) / 15) = RzL (2 * π * (kp : ℝ) / 15) := by
    calc
      RzL (2 * π * ((kq + dk : ℕ) : ℝ) / 15)
          = RzL (2 * π * ((((kq + dk) % 15 : ℕ)) : ℝ) / 15) := by
              simpa using (RzL_natMod_15 (kq + dk))
      _ = RzL (2 * π * (kp : ℝ) / 15) := by
            simp [kp, kq, hK]

  have hAngle :
      (2 * π * (dk : ℝ) / 15) + (2 * π * (kq : ℝ) / 15) =
        2 * π * ((kq + dk : ℕ) : ℝ) / 15 := by
    simp [Nat.cast_add, add_comm, mul_add, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

  have hp :
      Row.indexPoint p =
        ((-1 : ℝ) ^ lp) • RzL (2 * π * (kp : ℝ) / 15) (Nopert.Cpt iq) := by
    have hp' :
        Row.indexPoint p =
          ((-1 : ℝ) ^ lp) • RzL (2 * π * (kp : ℝ) / 15) (Nopert.Cpt ip) := by
      -- `Nopert.nopertPt` uses a `ℤ`-smul by `(-1)^ℓ`; convert it to an `ℝ`-smul.
      simp [Row.indexPoint, Nopert.nopertPt, kp, lp, ip]
      simpa using
        (Int.cast_smul_eq_zsmul (R := ℝ)
          ((-1 : ℤ) ^ lp)
          (RzL (2 * π * (kp : ℝ) / 15) (Nopert.Cpt ip))).symm
    simpa [hip] using hp'

  have hq :
      Row.indexPoint q =
        ((-1 : ℝ) ^ lq) • RzL (2 * π * (kq : ℝ) / 15) (Nopert.Cpt iq) := by
    simp [Row.indexPoint, Nopert.nopertPt, kq, lq, iq]
    simpa using
      (Int.cast_smul_eq_zsmul (R := ℝ)
        ((-1 : ℤ) ^ lq)
        (RzL (2 * π * (kq : ℝ) / 15) (Nopert.Cpt iq))).symm

  have hRz_apply :
      RzL (2 * π * ((kq + dk : ℕ) : ℝ) / 15) (Nopert.Cpt iq) =
        RzL (2 * π * (kp : ℝ) / 15) (Nopert.Cpt iq) := by
    simpa using congrArg (fun f : (ℝ³ →L[ℝ] ℝ³) => f (Nopert.Cpt iq)) hRz

  rw [hp]
  simp [signedRzIsom, LinearMap.smul_apply, hq]

  have hRz_comp :
      RzL (2 * π * (dk : ℝ) / 15)
            (RzL (2 * π * (kq : ℝ) / 15) (Nopert.Cpt iq)) =
          RzL (2 * π * ((kq + dk : ℕ) : ℝ) / 15) (Nopert.Cpt iq) := by
    have := (RzL_add_apply (2 * π * (dk : ℝ) / 15) (2 * π * (kq : ℝ) / 15) (Nopert.Cpt iq)).symm
    simpa [hAngle] using this

  have hpow :
      ((-1 : ℝ) ^ dl) * ((-1 : ℝ) ^ lq) = (-1 : ℝ) ^ (lq + dl) := by
    calc
      ((-1 : ℝ) ^ dl) * ((-1 : ℝ) ^ lq) = ((-1 : ℝ) ^ lq) * ((-1 : ℝ) ^ dl) := by
        simp [mul_comm]
      _ = (-1 : ℝ) ^ (lq + dl) := by
        simp [pow_add]

  calc
    ((-1 : ℝ) ^ lp) • RzL (2 * π * (kp : ℝ) / 15) (Nopert.Cpt iq)
        =
        ((-1 : ℝ) ^ (lq + dl)) • RzL (2 * π * (kp : ℝ) / 15) (Nopert.Cpt iq) := by
          simp [hsign]
    _ =
        ((-1 : ℝ) ^ (lq + dl)) •
          RzL (2 * π * ((kq + dk : ℕ) : ℝ) / 15) (Nopert.Cpt iq) := by
          simpa using congrArg (fun t => ((-1 : ℝ) ^ (lq + dl)) • t) hRz_apply.symm
    _ =
        ((-1 : ℝ) ^ dl) •
          ((-1 : ℝ) ^ lq •
            RzL (2 * π * (dk : ℝ) / 15)
              (RzL (2 * π * (kq : ℝ) / 15) (Nopert.Cpt iq))) := by
          rw [hRz_comp]
          simp [smul_smul, hpow]
    _ =
        ((-1 : ℝ) ^ lq) •
          ((-1 : ℝ) ^ dl •
            RzL (2 * π * (dk : ℝ) / 15)
              (RzL (2 * π * (kq : ℝ) / 15) (Nopert.Cpt iq))) := by
          simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]

lemma Row.indexPoint_eq_signedRzRefIsom_apply
    (p q dl dk : ℕ)
    (hI : Solution.decodeI p = Solution.decodeI q)
    (hL : (Solution.decodeL q + dl) % 2 = Solution.decodeL p)
    (hK : (dk + 15 - Solution.decodeK q) % 15 = Solution.decodeK p) :
    Row.indexPoint p =
      signedRzRefIsom (Nopert.Cpt (Row.decodeIFin p)) dl dk (Row.indexPoint q) := by
  have hIFin : Row.decodeIFin p = Row.decodeIFin q := by
    ext
    simpa [Row.decodeIFin] using hI

  set kp : ℕ := Solution.decodeK p
  set kq : ℕ := Solution.decodeK q
  set lp : ℕ := Solution.decodeL p
  set lq : ℕ := Solution.decodeL q
  set ip : Fin 3 := Row.decodeIFin p
  set iq : Fin 3 := Row.decodeIFin q

  have hip : ip = iq := by simpa [ip, iq] using hIFin

  have hsign : (-1 : ℝ) ^ lp = (-1 : ℝ) ^ (lq + dl) := by
    calc
      (-1 : ℝ) ^ lp = (-1 : ℝ) ^ ((lq + dl) % 2) := by simp [lp, lq, hL]
      _ = (-1 : ℝ) ^ (lq + dl) := by simpa using (sign_flip_from_mod (lq + dl))

  have hkq_lt : kq < 15 := by
    simpa [kq, Solution.decodeK] using (Nat.mod_lt q (by decide))
  have hkq_le : kq ≤ 15 := Nat.le_of_lt hkq_lt

  have hneg :
      RzL (-2 * π * (kq : ℝ) / 15) = RzL (2 * π * ((15 - kq : ℕ) : ℝ) / 15) := by
    -- Work in the normalized form `-(2π*kq)/15`, which is what `simp` prefers.
    have hangle :
        (-(2 * π * (kq : ℝ)) / 15) + 2 * π =
          2 * π * ((15 - kq : ℕ) : ℝ) / 15 := by
      simp [Nat.cast_sub hkq_le, div_eq_mul_inv]
      ring
    have hper :
        RzL ((-(2 * π * (kq : ℝ)) / 15) + 2 * π) = RzL (-(2 * π * (kq : ℝ)) / 15) := by
      simpa using
        (RzL_add_int_mul_two_pi (z := (1 : ℤ)) (x := (-(2 * π * (kq : ℝ)) / 15)))
    have : RzL (-(2 * π * (kq : ℝ)) / 15) = RzL (2 * π * ((15 - kq : ℕ) : ℝ) / 15) := by
      simpa [hangle] using hper.symm
    -- Convert back to the `-2 * π * kq / 15` normal form.
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

  have hRz :
      RzL (2 * π * ((dk + 15 - kq : ℕ) : ℝ) / 15) = RzL (2 * π * (kp : ℝ) / 15) := by
    calc
      RzL (2 * π * ((dk + 15 - kq : ℕ) : ℝ) / 15)
          = RzL (2 * π * ((((dk + 15 - kq) % 15 : ℕ)) : ℝ) / 15) := by
              simpa using (RzL_natMod_15 (dk + 15 - kq))
      _ = RzL (2 * π * (kp : ℝ) / 15) := by
            simp [kp, kq, hK]

  have href :
      (reflPlaneIsom (Nopert.Cpt iq)) (RzL (2 * π * (kq : ℝ) / 15) (Nopert.Cpt iq)) =
        RzL (-(2 * π * (kq : ℝ) / 15)) (Nopert.Cpt iq) := by
    simpa [reflPlaneIsom] using
      (reflPlane_reflection_apply_RzL (θ := (2 * π * (kq : ℝ) / 15)) (c := Nopert.Cpt iq))

  have hAngle :
      (2 * π * (dk : ℝ) / 15) + (2 * π * ((15 - kq : ℕ) : ℝ) / 15) =
        2 * π * ((dk + (15 - kq : ℕ) : ℕ) : ℝ) / 15 := by
    simp [Nat.cast_add, mul_add, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

  have hRz_comp :
      RzL (2 * π * (dk : ℝ) / 15)
            (RzL (-2 * π * (kq : ℝ) / 15) (Nopert.Cpt iq)) =
          RzL (2 * π * ((dk + 15 - kq : ℕ) : ℝ) / 15) (Nopert.Cpt iq) := by
    -- Rewrite the negative-angle rotation using `15 - kq` and then combine angles.
    have hadd : dk + 15 - kq = dk + (15 - kq) :=
      Nat.add_sub_assoc (m := 15) (k := kq) hkq_le dk
    have hneg_apply :
        RzL (-(2 * π * (kq : ℝ)) / 15) (Nopert.Cpt iq) =
          RzL (2 * π * ((15 - kq : ℕ) : ℝ) / 15) (Nopert.Cpt iq) := by
      have h :=
        congrArg (fun f : (ℝ³ →L[ℝ] ℝ³) => f (Nopert.Cpt iq)) hneg
      -- Normalize the left-hand angle into `-(2π*kq)/15`.
      have hang : (-(2 * π * (kq : ℝ)) / 15) = (-2 * π * (kq : ℝ) / 15) := by ring
      simpa [hang] using h
    have hcomp :
        RzL (2 * π * (dk : ℝ) / 15)
              (RzL (2 * π * ((15 - kq : ℕ) : ℝ) / 15) (Nopert.Cpt iq)) =
            RzL (2 * π * ((dk + (15 - kq : ℕ) : ℕ) : ℝ) / 15) (Nopert.Cpt iq) := by
      have :=
        (RzL_add_apply (2 * π * (dk : ℝ) / 15) (2 * π * ((15 - kq : ℕ) : ℝ) / 15)
            (Nopert.Cpt iq)).symm
      simpa [hAngle] using this
    calc
      RzL (2 * π * (dk : ℝ) / 15)
            (RzL (-2 * π * (kq : ℝ) / 15) (Nopert.Cpt iq)) =
          RzL (2 * π * (dk : ℝ) / 15)
            (RzL (-(2 * π * (kq : ℝ)) / 15) (Nopert.Cpt iq)) := by
              have hang0 : (-(2 * π * (kq : ℝ)) / 15) = (-2 * π * (kq : ℝ) / 15) := by ring
              simp [hang0]
      _ =
          RzL (2 * π * (dk : ℝ) / 15)
            (RzL (2 * π * ((15 - kq : ℕ) : ℝ) / 15) (Nopert.Cpt iq)) := by
              simp [hneg_apply]
      _ = RzL (2 * π * ((dk + (15 - kq : ℕ) : ℕ) : ℝ) / 15) (Nopert.Cpt iq) := hcomp
      _ = RzL (2 * π * ((dk + 15 - kq : ℕ) : ℝ) / 15) (Nopert.Cpt iq) := by
            simp [hadd]

  have hp :
      Row.indexPoint p =
        ((-1 : ℝ) ^ lp) • RzL (2 * π * (kp : ℝ) / 15) (Nopert.Cpt iq) := by
    have hp' :
        Row.indexPoint p =
          ((-1 : ℝ) ^ lp) • RzL (2 * π * (kp : ℝ) / 15) (Nopert.Cpt ip) := by
      simp [Row.indexPoint, Nopert.nopertPt, kp, lp, ip]
      simpa using
        (Int.cast_smul_eq_zsmul (R := ℝ)
          ((-1 : ℤ) ^ lp)
          (RzL (2 * π * (kp : ℝ) / 15) (Nopert.Cpt ip))).symm
    simpa [hip] using hp'

  have hq :
      Row.indexPoint q =
        ((-1 : ℝ) ^ lq) • RzL (2 * π * (kq : ℝ) / 15) (Nopert.Cpt iq) := by
    simp [Row.indexPoint, Nopert.nopertPt, kq, lq, iq]
    simpa using
      (Int.cast_smul_eq_zsmul (R := ℝ)
        ((-1 : ℤ) ^ lq)
        (RzL (2 * π * (kq : ℝ) / 15) (Nopert.Cpt iq))).symm

  have hpow :
      ((-1 : ℝ) ^ dl) * ((-1 : ℝ) ^ lq) = (-1 : ℝ) ^ (lq + dl) := by
    calc
      ((-1 : ℝ) ^ dl) * ((-1 : ℝ) ^ lq) = ((-1 : ℝ) ^ lq) * ((-1 : ℝ) ^ dl) := by
        simp [mul_comm]
      _ = (-1 : ℝ) ^ (lq + dl) := by
        simp [pow_add]

  have hRz_apply :
      RzL (2 * π * (dk : ℝ) / 15)
            (RzL (-2 * π * (kq : ℝ) / 15) (Nopert.Cpt iq)) =
          RzL (2 * π * (kp : ℝ) / 15) (Nopert.Cpt iq) := by
    have hRz' :
        RzL (2 * π * ((dk + 15 - kq : ℕ) : ℝ) / 15) (Nopert.Cpt iq) =
          RzL (2 * π * (kp : ℝ) / 15) (Nopert.Cpt iq) := by
      simpa using congrArg (fun f : (ℝ³ →L[ℝ] ℝ³) => f (Nopert.Cpt iq)) hRz
    exact hRz_comp.trans hRz'

  -- Finish by expanding both sides and using the reflection+rotation identity.
  have hc : Nopert.Cpt ip = Nopert.Cpt iq := by simp [hip]

  have href_q :
      (reflPlaneIsom (Nopert.Cpt iq)) (Row.indexPoint q) =
        ((-1 : ℝ) ^ lq) • RzL (-2 * π * (kq : ℝ) / 15) (Nopert.Cpt iq) := by
    -- Expand `Row.indexPoint q`, pull out the sign, and use the reflection identity.
    rw [hq]
    calc
      (reflPlaneIsom (Nopert.Cpt iq))
            (((-1 : ℝ) ^ lq) • RzL (2 * π * (kq : ℝ) / 15) (Nopert.Cpt iq))
          =
          ((-1 : ℝ) ^ lq) •
            (reflPlaneIsom (Nopert.Cpt iq))
              (RzL (2 * π * (kq : ℝ) / 15) (Nopert.Cpt iq)) := by
            simp
      _ = ((-1 : ℝ) ^ lq) • RzL (-2 * π * (kq : ℝ) / 15) (Nopert.Cpt iq) := by
            simpa [neg_mul, mul_assoc, div_eq_mul_inv] using congrArg (fun t => ((-1 : ℝ) ^ lq) • t) href

  -- Rewrite the goal using `hp`/`hc` and then simplify `signedRzRefIsom` using `href_q` and `hRz_apply`.
  rw [hp]
  -- Move the basepoint in `signedRzRefIsom` from `ip` to `iq`.
  have hsigned :
      signedRzRefIsom (Nopert.Cpt ip) dl dk (Row.indexPoint q) =
        ((-1 : ℝ) ^ dl) •
          RzL (2 * π * (dk : ℝ) / 15)
            ((reflPlaneIsom (Nopert.Cpt iq)) (Row.indexPoint q)) := by
    simp [signedRzRefIsom, LinearMap.smul_apply, LinearMap.comp_apply, hc]
  -- Replace the RHS using `href_q`, then use `hRz_apply` to identify the resulting rotation.
  rw [hsigned, href_q]
  -- Pull out the `(-1)^lq` scalar through the rotation.
  simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]
  -- Discharge the remaining scalar+geometric goal by rewriting `hRz_apply.symm` into the normal form used by `simp`.
  have hRz_apply_norm :
      RzL (π * (2 * (kp : ℝ)) / 15) (Nopert.Cpt iq) =
        RzL (π * ((dk : ℝ) * 2) / 15)
          (RzL (-(π * (2 * (kq : ℝ)) / 15)) (Nopert.Cpt iq)) := by
    have h := hRz_apply.symm
    have ha1 : (2 * π * (kp : ℝ) / 15) = (π * (2 * (kp : ℝ)) / 15) := by ring
    have ha2 : (2 * π * (dk : ℝ) / 15) = (π * ((dk : ℝ) * 2) / 15) := by ring
    have ha3a : (-2 * π * (kq : ℝ) / 15) = (-(2 * π * (kq : ℝ)) / 15) := by ring
    have ha3b : (-(2 * π * (kq : ℝ)) / 15) = (-(π * (2 * (kq : ℝ)) / 15)) := by ring
    simpa [ha1, ha2, ha3a, ha3b] using h
  have hscal : ((-1 : ℝ) ^ dl) * ((-1 : ℝ) ^ lq) = (-1 : ℝ) ^ lp := by
    calc
      ((-1 : ℝ) ^ dl) * ((-1 : ℝ) ^ lq) = (-1 : ℝ) ^ (lq + dl) := hpow
      _ = (-1 : ℝ) ^ lp := by simpa using hsign.symm
  -- Reduce to the pure geometric identity by rewriting scalars, then apply `hRz_apply_norm`.
  have hang :
      (-(π * (2 * (kq : ℝ)) / 15)) = (-(π * (2 * (kq : ℝ))) / 15) := by
    ring
  simp [hscal, hRz_apply_norm, hang]

/--
Soundness of `Row.localCongruenceIndexCheck`: if the index-level check passes, then the
corresponding `P`/`Q` triangles are congruent (by a global sign flip and a fixed dihedral symmetry
in the `15`-fold `Rz` orbit).
-/
theorem localCongruenceIndexCheck_sound (row : Solution.Row)
    (h : row.localCongruenceIndexCheck) :
    (Row.PTriangle row).Congruent (Row.QTriangle row) := by
  classical
  rcases h with ⟨_hbounds, hI, hL, hK⟩
  rcases hK with hKrot | hKref
  · refine ⟨signedRzIsom row.dl row.dkRot, ?_⟩
    intro i
    fin_cases i
    · -- vertex 0
      have hI' : Solution.decodeI row.P1_index = Solution.decodeI row.Q1_index := by
        simpa using hI.1
      have hL' :
          (Solution.decodeL row.Q1_index + row.dl) % 2 = Solution.decodeL row.P1_index := by
        simpa using hL.1
      have hK' :
          (Solution.decodeK row.Q1_index + row.dkRot) % 15 = Solution.decodeK row.P1_index := by
        simpa using hKrot.1
      simpa [Row.PTriangle, Row.QTriangle] using
        (Row.indexPoint_eq_signedRzIsom_apply (p := row.P1_index) (q := row.Q1_index)
          (dl := row.dl) (dk := row.dkRot) hI' hL' hK')
    · -- vertex 1
      have hI' : Solution.decodeI row.P2_index = Solution.decodeI row.Q2_index := by
        simpa using hI.2.1
      have hL' :
          (Solution.decodeL row.Q2_index + row.dl) % 2 = Solution.decodeL row.P2_index := by
        simpa using hL.2.1
      have hK' :
          (Solution.decodeK row.Q2_index + row.dkRot) % 15 = Solution.decodeK row.P2_index := by
        simpa using hKrot.2.1
      simpa [Row.PTriangle, Row.QTriangle] using
        (Row.indexPoint_eq_signedRzIsom_apply (p := row.P2_index) (q := row.Q2_index)
          (dl := row.dl) (dk := row.dkRot) hI' hL' hK')
    · -- vertex 2
      have hI' : Solution.decodeI row.P3_index = Solution.decodeI row.Q3_index := by
        simpa using hI.2.2
      have hL' :
          (Solution.decodeL row.Q3_index + row.dl) % 2 = Solution.decodeL row.P3_index := by
        simpa using hL.2.2
      have hK' :
          (Solution.decodeK row.Q3_index + row.dkRot) % 15 = Solution.decodeK row.P3_index := by
        simpa using hKrot.2.2
      simpa [Row.PTriangle, Row.QTriangle] using
        (Row.indexPoint_eq_signedRzIsom_apply (p := row.P3_index) (q := row.Q3_index)
          (dl := row.dl) (dk := row.dkRot) hI' hL' hK')
  · rcases hKref with ⟨hK1, hK2, hK3, hI12, hI13⟩
    refine ⟨signedRzRefIsom (Nopert.Cpt (Row.decodeIFin row.P1_index)) row.dl row.dkRef, ?_⟩
    intro i
    fin_cases i
    · -- vertex 0
      have hI' : Solution.decodeI row.P1_index = Solution.decodeI row.Q1_index := by
        simpa using hI.1
      have hL' :
          (Solution.decodeL row.Q1_index + row.dl) % 2 = Solution.decodeL row.P1_index := by
        simpa using hL.1
      have hK' :
          (row.dkRef + 15 - Solution.decodeK row.Q1_index) % 15 = Solution.decodeK row.P1_index := by
        simpa using hK1
      simpa [Row.PTriangle, Row.QTriangle] using
        (Row.indexPoint_eq_signedRzRefIsom_apply (p := row.P1_index) (q := row.Q1_index)
          (dl := row.dl) (dk := row.dkRef) hI' hL' hK')
    · -- vertex 1
      have hI' : Solution.decodeI row.P2_index = Solution.decodeI row.Q2_index := by
        simpa using hI.2.1
      have hL' :
          (Solution.decodeL row.Q2_index + row.dl) % 2 = Solution.decodeL row.P2_index := by
        simpa using hL.2.1
      have hK' :
          (row.dkRef + 15 - Solution.decodeK row.Q2_index) % 15 = Solution.decodeK row.P2_index := by
        simpa using hK2
      have hIFin : Row.decodeIFin row.P2_index = Row.decodeIFin row.P1_index := by
        ext
        simpa [Row.decodeIFin] using hI12.symm
      simpa [Row.PTriangle, Row.QTriangle, hIFin] using
        (Row.indexPoint_eq_signedRzRefIsom_apply (p := row.P2_index) (q := row.Q2_index)
          (dl := row.dl) (dk := row.dkRef) hI' hL' hK')
    · -- vertex 2
      have hI' : Solution.decodeI row.P3_index = Solution.decodeI row.Q3_index := by
        simpa using hI.2.2
      have hL' :
          (Solution.decodeL row.Q3_index + row.dl) % 2 = Solution.decodeL row.P3_index := by
        simpa using hL.2.2
      have hK' :
          (row.dkRef + 15 - Solution.decodeK row.Q3_index) % 15 = Solution.decodeK row.P3_index := by
        simpa using hK3
      have hIFin : Row.decodeIFin row.P3_index = Row.decodeIFin row.P1_index := by
        ext
        simpa [Row.decodeIFin] using hI13.symm
      simpa [Row.PTriangle, Row.QTriangle, hIFin] using
        (Row.indexPoint_eq_signedRzRefIsom_apply (p := row.P3_index) (q := row.Q3_index)
          (dl := row.dl) (dk := row.dkRef) hI' hL' hK')

theorem validLocal_congruent (tab : Solution.Table) (row : Solution.Row)
    (h : row.ValidLocal tab) :
    (Row.PTriangle row).Congruent (Row.QTriangle row) :=
  localCongruenceIndexCheck_sound row h.congruence_check

end Solution
