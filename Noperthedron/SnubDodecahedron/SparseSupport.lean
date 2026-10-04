module

public import Noperthedron.SnubDodecahedron.AtlasProjectiveLocalCertificate

@[expose] public section

/-!
# Sparse support checks

For a linear functional to be maximized at a vertex of a polytope, it is
enough to compare that vertex with the generators of its tangent cone.  The
rational checker model has at most seven such generators at
each vertex.  This reduces the repeated local-certificate support check from
twenty vertices to seven (with padding entries equal to the selected vertex).
-/

namespace Noperthedron.SnubDodecahedron.SparseSupport


open Noperthedron.Checker
open AtlasProjectiveView
open AtlasProjectiveLocalCertificate

/-- Tangent-cone generators for each rational checker vertex.  Entries beyond
the actual degree are padded by the vertex itself. -/
def supportGenerator : VertexIndex → Fin 7 → VertexIndex := ![
  ![1, 2, 12, 48, 49, 0, 0],
  ![0, 2, 3, 12, 14, 1, 1],
  ![0, 1, 3, 4, 49, 2, 2],
  ![1, 2, 4, 5, 6, 3, 3],
  ![2, 3, 6, 53, 55, 4, 4],
  ![3, 6, 7, 8, 16, 5, 5],
  ![3, 4, 5, 8, 55, 6, 6],
  ![5, 8, 9, 16, 18, 7, 7],
  ![5, 6, 7, 9, 10, 8, 8],
  ![7, 8, 10, 11, 22, 9, 9],
  ![8, 9, 11, 57, 59, 10, 10],
  ![9, 10, 22, 23, 59, 11, 11],
  ![0, 1, 13, 14, 24, 12, 12],
  ![12, 14, 15, 24, 26, 13, 13],
  ![1, 12, 13, 15, 16, 14, 14],
  ![13, 14, 16, 17, 18, 15, 15],
  ![5, 7, 14, 15, 18, 16, 16],
  ![15, 18, 19, 20, 28, 17, 17],
  ![7, 15, 16, 17, 20, 18, 18],
  ![17, 20, 21, 28, 30, 19, 19],
  ![17, 18, 19, 21, 22, 20, 20],
  ![19, 20, 22, 23, 34, 21, 21],
  ![9, 11, 20, 21, 23, 22, 22],
  ![11, 21, 22, 34, 35, 23, 23],
  ![12, 13, 25, 26, 36, 24, 24],
  ![24, 26, 27, 36, 38, 25, 25],
  ![13, 24, 25, 27, 28, 26, 26],
  ![25, 26, 28, 29, 30, 27, 27],
  ![17, 19, 26, 27, 30, 28, 28],
  ![27, 30, 31, 32, 40, 29, 29],
  ![19, 27, 28, 29, 32, 30, 30],
  ![29, 32, 33, 40, 42, 31, 31],
  ![29, 30, 31, 33, 34, 32, 32],
  ![31, 32, 34, 35, 46, 33, 33],
  ![21, 23, 32, 33, 35, 34, 34],
  ![23, 33, 34, 46, 47, 35, 35],
  ![24, 25, 37, 38, 48, 36, 36],
  ![36, 38, 39, 48, 50, 37, 37],
  ![25, 36, 37, 39, 40, 38, 38],
  ![37, 38, 40, 41, 42, 39, 39],
  ![29, 31, 38, 39, 42, 40, 40],
  ![39, 42, 43, 44, 52, 41, 41],
  ![31, 39, 40, 41, 44, 42, 42],
  ![41, 44, 45, 52, 54, 43, 43],
  ![41, 42, 43, 45, 46, 44, 44],
  ![43, 44, 46, 47, 58, 45, 45],
  ![33, 35, 44, 45, 47, 46, 46],
  ![35, 45, 46, 58, 59, 47, 47],
  ![0, 36, 37, 49, 50, 48, 48],
  ![0, 2, 48, 50, 51, 49, 49],
  ![37, 48, 49, 51, 52, 50, 50],
  ![49, 50, 52, 53, 54, 51, 51],
  ![41, 43, 50, 51, 54, 52, 52],
  ![4, 51, 54, 55, 56, 53, 53],
  ![43, 51, 52, 53, 56, 54, 54],
  ![4, 6, 53, 56, 57, 55, 55],
  ![53, 54, 55, 57, 58, 56, 56],
  ![10, 55, 56, 58, 59, 57, 57],
  ![45, 47, 56, 57, 59, 58, 58],
  ![10, 11, 47, 57, 58, 59, 59]
]

structure TangentCombination where
  generator : Fin 3 → Fin 7
  coefficient : Fin 3 → ℚ
deriving DecidableEq

def TangentCombination.Valid (combination : TangentCombination)
    (base target : VertexIndex) : Prop :=
  (∀ l, 0 ≤ combination.coefficient l) ∧
  1 ≤ ∑ l, combination.coefficient l ∧
  (∀ l, combination.coefficient l ≠ 0 →
    supportGenerator base (combination.generator l) ≠ base) ∧
  rationalVertex target - rationalVertex base =
    ∑ l, combination.coefficient l •
      (rationalVertex (supportGenerator base (combination.generator l)) -
        rationalVertex base)

instance (combination : TangentCombination) (base target : VertexIndex) :
    Decidable (combination.Valid base target) := by
  unfold TangentCombination.Valid
  infer_instance

def TangentTableValid
    (combination : VertexIndex → VertexIndex → TangentCombination) : Prop :=
  ∀ base target, target ≠ base → (combination base target).Valid base target

instance (combination : VertexIndex → VertexIndex → TangentCombination) :
    Decidable (TangentTableValid combination) := by
  unfold TangentTableValid
  infer_instance

theorem crossQ_sum3 (u : Fin 3 → ℚ) (coefficient : Fin 3 → ℚ)
    (v : Fin 3 → Fin 3 → ℚ) :
    LocalCertificate.crossQ u (∑ l, coefficient l • v l) =
      ∑ l, coefficient l • LocalCertificate.crossQ u (v l) := by
  funext coordinate
  fin_cases coordinate <;>
    simp [LocalCertificate.crossQ, Fin.sum_univ_three] <;>
    ring

theorem dotQ_sum3 (u : Fin 3 → ℚ) (coefficient : Fin 3 → ℚ)
    (v : Fin 3 → Fin 3 → ℚ) :
    AtlasProjectiveEdgeCertificate.dotQ u (∑ l, coefficient l • v l) =
      ∑ l, coefficient l * AtlasProjectiveEdgeCertificate.dotQ u (v l) := by
  simp [AtlasProjectiveEdgeCertificate.dotQ, Fin.sum_univ_three]
  ring

theorem supportAt_eq_sum
    (combination : TangentCombination) (box : Box)
    (j : Fin 4) (corner : Fin 3) (i : Fin 3) (target : VertexIndex)
    (hcombination : combination.Valid
      ((box.certificate j).supportIndex box i) target) :
    box.supportAt j corner i target =
      ∑ l, combination.coefficient l *
        box.supportAt j corner i
          (supportGenerator ((box.certificate j).supportIndex box i)
            (combination.generator l)) := by
  have hdelta := hcombination.2.2.2
  unfold Box.supportAt AxisCertificate.deltaQ
  rw [hdelta]
  rw [crossQ_sum3, dotQ_sum3]

/-- Fast decision of one contact's tangent-generator support checks in
compiled code (the contact's edge is evaluated once; see
`Box.supportListOK`). -/
instance (priority := high) (box : Box) (j : Fin 4) (i : Fin 3) :
    Decidable (∀ generator : Fin 7, box.supportUpper j i
      (supportGenerator ((box.certificate j).supportIndex box i) generator) ≤ 0) :=
  decidable_of_iff (box.supportListOK j i ((List.finRange 7).map
      (supportGenerator ((box.certificate j).supportIndex box i))) = true)
    (by simp [Box.supportListOK_iff, List.mem_finRange])

@[mk_iff]
structure Box.SparseViewValid (box : Box) : Prop where
  triangle_valid :
    AtlasProjectiveEdgeCertificate.SignedTriangleValid box.root box.triangle
  c_nonneg : 0 ≤ box.c
  delta_nonneg : 0 ≤ box.δ
  r_nonneg : 0 ≤ box.r
  B_pos : ∀ j, 0 < (box.certificate j).B
  weight_nonneg : ∀ j i, 0 ≤ box.weightLower j i
  weight_pos : ∀ j, ∃ i, 0 < box.weightLower j i
  support_generators : ∀ j i generator,
    box.supportUpper j i
      (supportGenerator ((box.certificate j).supportIndex box i) generator) ≤ 0
  /-- Exact cone-boundary directions can tie a second edge endpoint.  The
  tangent-generator reduction spends strict approximation slack and therefore
  cannot propagate through that zero-slack generator; for just these rare
  axes, check all twenty support vertices directly. -/
  support_boundary : ∀ j i,
    ((box.certificate j).mix i = 0 ∨
      (box.certificate j).mix i = 1000) →
    ∀ target, box.supportUpper j i target ≤ 0
  direction_nonzero : ∀ j i,
    box.supportUpper j i ((box.certificate j).nonzeroWitness i) < 0
  budget : ∀ j, box.weightBudget j ≤ (box.certificate j).B
  variation : ∀ j,
    box.variationRadiusSum j + 3 * variationError ≤
      (box.certificate j).B * box.δ
  barycentric : box.barycentricValid
  angle_bound : box.r ^ 2 * (1 + box.c ^ 2) ≤ 4 * box.c ^ 2

instance (box : Box) : Decidable (Box.SparseViewValid box) :=
  decidable_of_iff _ (Box.sparseViewValid_iff box).symm

theorem Box.SparseViewValid.support_all {box : Box}
    (h : Box.SparseViewValid box)
    (combination : VertexIndex → VertexIndex → TangentCombination)
    (htangent : TangentTableValid combination) :
    ∀ j i target, box.supportUpper j i target ≤ 0 := by
  intro j i target
  by_cases hboundary : (box.certificate j).mix i = 0 ∨
      (box.certificate j).mix i = 1000
  · exact h.support_boundary j i hboundary target
  · have hzero : (box.certificate j).mix i ≠ 0 :=
      fun hz => hboundary (Or.inl hz)
    have hthousand : (box.certificate j).mix i ≠ 1000 :=
      fun ht => hboundary (Or.inr ht)
    let base := (box.certificate j).supportIndex box i
    by_cases htie : target = base
    · simp [Box.supportUpper, Box.exactSupportTie, base, htie]
    · let selected := combination base target
      have htie' : target ≠ (box.certificate j).supportIndex box i := by
        simpa [base] using htie
      have hselected : selected.Valid base target := htangent base target htie
      have hat (corner : Fin 3) :
          box.supportAt j corner i target ≤ -supportError := by
        rw [supportAt_eq_sum selected box j corner i target hselected]
        calc
          ∑ l, selected.coefficient l *
                box.supportAt j corner i
                  (supportGenerator base (selected.generator l)) ≤
              ∑ l, selected.coefficient l * (-supportError) := by
            apply Finset.sum_le_sum
            intro l _
            by_cases hcoefficient : selected.coefficient l = 0
            · simp [hcoefficient]
            · have hgenerator :
                  supportGenerator base (selected.generator l) ≠ base :=
                hselected.2.2.1 l hcoefficient
              have hsparse := h.support_generators j i (selected.generator l)
              have hgenerator' :
                  supportGenerator
                      ((box.certificate j).supportIndex box i)
                      (selected.generator l) ≠
                    (box.certificate j).supportIndex box i := by
                simpa [base] using hgenerator
              have hcorner := AtlasProjectiveEdgeCertificate.le_max3
                (fun c => box.supportAt j c i
                  (supportGenerator base (selected.generator l))) corner
              have hraw : box.supportAt j corner i
                    (supportGenerator base (selected.generator l)) ≤
                  -supportError := by
                simp [Box.supportUpper, Box.exactSupportTie, hgenerator',
                  hzero, hthousand] at hsparse
                linarith
              exact mul_le_mul_of_nonneg_left hraw (hselected.1 l)
          _ = -supportError * ∑ l, selected.coefficient l := by
            simp only [Fin.sum_univ_three]
            ring
          _ ≤ -supportError := by
            have herror : 0 < supportError := by
              norm_num [supportError, tightVertexErrorQ]
            nlinarith [hselected.2.1]
      simp [Box.supportUpper, Box.exactSupportTie, htie', hzero,
        hthousand]
      have hmax :
          AtlasProjectiveEdgeCertificate.max3
              (fun corner => box.supportAt j corner i target) ≤
            -supportError := by
        simp only [AtlasProjectiveEdgeCertificate.max3, max_le_iff]
        exact ⟨hat 0, hat 1, hat 2⟩
      linarith

theorem Box.SparseViewValid.toViewValid {box : Box}
    (h : Box.SparseViewValid box)
    (combination : VertexIndex → VertexIndex → TangentCombination)
    (htangent : TangentTableValid combination) : box.ViewValid where
  triangle_valid := h.triangle_valid
  c_nonneg := h.c_nonneg
  delta_nonneg := h.delta_nonneg
  r_nonneg := h.r_nonneg
  B_pos := h.B_pos
  weight_nonneg := h.weight_nonneg
  weight_pos := h.weight_pos
  support := h.support_all combination htangent
  direction_nonzero := h.direction_nonzero
  budget := h.budget
  variation := h.variation
  barycentric := h.barycentric
  angle_bound := h.angle_bound

end Noperthedron.SnubDodecahedron.SparseSupport

end
