import IntegralCode
import ImageAlgebra
import MixedConsequences

/-! Integral images and their minimum norm, without an abstract lattice interface. -/

namespace Conway99

open scoped BigOperators Matrix
open Finset Incidence

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def integralImageCoeff (u : V) (J L : TriangleIndex G) : ℤ :=
  -7 * (if L = J then 1 else 0) +
    ((triangleNeighborCount G u L : ℤ) - 3 * (if u ∈ L.val then 1 else 0)) *
      integerTriangleGram G L J

theorem integralImageCoeff_cast (u : V) (J L : TriangleIndex G) :
    (integralImageCoeff G u J L : ℚ) =
      rationalImageCoeff (triangleGram G) (mixedGram G) u J L := by
  unfold integralImageCoeff rationalImageCoeff
  rw [mixedGram_entry]
  split_ifs <;> push_cast <;> simp only [integerTriangleGram_cast] <;> ring

theorem integralImageCoeff_cast_function (u : V) (J : TriangleIndex G) :
    (fun L => (integralImageCoeff G u J L : ℚ)) =
      rationalImageCoeff (triangleGram G) (mixedGram G) u J := by
  funext L
  exact integralImageCoeff_cast G u J L

theorem integralImage_code_at_self (h : G.IsSRGWith 99 14 1 2)
    (u : V) (J : TriangleIndex G) :
    integralCode G (integralImageCoeff G u J) u = integerMixedGram G u J := by
  have hc : (integralCode G (integralImageCoeff G u J) u : ℚ) = mixedGram G u J := by
    rw [integralCode_cast]
    change (mixedGram G).mulVec (fun L => (integralImageCoeff G u J L : ℚ)) u = _
    rw [integralImageCoeff_cast_function, imageCoeff_code_mulVec (triangleGram G)
      (mixedGram G) u J (mixedGram_mul_triangleGram G h)]
    change (-1 / 3 : ℚ) * (∑ L, mixedGram G u L *
      (mixedGram G u L * triangleGram G L J)) = mixedGram G u J
    have hp : (∑ L, mixedGram G u L * (mixedGram G u L * triangleGram G L J)) =
        ∑ L, mixedGram G u L ^ 2 * triangleGram G L J := by
      apply sum_congr rfl
      intro L _
      ring
    rw [hp, mixedGram_squared_weighted_sum G h]
    ring
  rw [← integerMixedGram_cast G u J] at hc
  exact_mod_cast hc

theorem integralImage_norm_cast (h : G.IsSRGWith 99 14 1 2)
    (u : V) (J : TriangleIndex G) :
    (integerGramNorm G (integralImageCoeff G u J) : ℚ) =
      weightedImageNorm (triangleGram G) (mixedGram G) u J := by
  rw [integerGramNorm_cast, integralImageCoeff_cast_function]
  exact imageCoeff_gram_norm (triangleGram G) (mixedGram G) u J
    (triangleGram_symmetric G) (triangleGram_square G h)

/-- The decisive image gap is now a theorem from the SRG parameters alone. -/
theorem graph_image_norm_ge_four (h : G.IsSRGWith 99 14 1 2)
    (u : V) (J : TriangleIndex G) :
    4 ≤ integerGramNorm G (integralImageCoeff G u J) := by
  apply integralCode_norm_gap G h (integralImageCoeff G u J) u
  rw [integralImage_code_at_self G h]
  have hh := mixedGram_values G h u J
  simp_rw [← integerMixedGram_cast G u J] at hh
  exact_mod_cast hh

theorem graph_diagonal_contraction_gap (h : G.IsSRGWith 99 14 1 2)
    (J : TriangleIndex G) :
    396 ≤ 7 * diagonalContraction (integerTriangleGram G) J := by
  have htotal := weightedImageNorm_total (triangleGram G) (mixedGram G) J
    (triangleGram_symmetric G) (mixedGram_transpose_mul_self G h)
  have hq : (∑ u, (integerGramNorm G (integralImageCoeff G u J) : ℚ)) =
      7 * (diagonalContraction (integerTriangleGram G) J : ℚ) := by
    simpa only [integralImage_norm_cast G h, diagonalContraction, Int.cast_sum,
      Int.cast_mul, Int.cast_pow, integerTriangleGram_cast] using htotal
  have hi : (∑ u, integerGramNorm G (integralImageCoeff G u J)) =
      7 * diagonalContraction (integerTriangleGram G) J := by exact_mod_cast hq
  have hb := sum_le_sum (s := (univ : Finset V))
    (fun u _ => graph_image_norm_ge_four G h u J)
  simp only [sum_const, card_univ, h.card, nsmul_eq_mul, hi] at hb
  norm_num at hb
  exact hb

theorem graph_diagonal_contraction_ge_sixty (h : G.IsSRGWith 99 14 1 2)
    (J : TriangleIndex G) : 60 ≤ diagonalContraction (integerTriangleGram G) J :=
  diagonal_rounding _ (graph_diagonal_contraction_divisible_four G h J)
    (graph_diagonal_contraction_gap G h J)

#print axioms integralImage_code_at_self
#print axioms integralImage_norm_cast
#print axioms graph_image_norm_ge_four
#print axioms graph_diagonal_contraction_gap
#print axioms graph_diagonal_contraction_ge_sixty

end Conway99
