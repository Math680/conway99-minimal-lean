import MixedEntries
import IntegralGram
import FrameContraction

/-! Codes of arbitrary integral triangle combinations, constructed from the graph. -/

namespace Conway99

open scoped BigOperators
open Finset Incidence

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def integralCode (c : TriangleIndex G → ℤ) (u : V) : ℤ :=
  ∑ L, integerMixedGram G u L * c L

theorem integralCode_cast (c : TriangleIndex G → ℤ) (u : V) :
    (integralCode G c u : ℚ) = ∑ L, mixedGram G u L * (c L : ℚ) := by
  simp only [integralCode, Int.cast_sum, Int.cast_mul, integerMixedGram_cast]

theorem integralCode_sum_zero (h : G.IsSRGWith 99 14 1 2)
    (c : TriangleIndex G → ℤ) : (∑ u, integralCode G c u) = 0 := by
  have hq : (∑ u, (integralCode G c u : ℚ)) = 0 := by
    simp_rw [integralCode_cast]
    rw [sum_comm]
    simp_rw [← sum_mul, mixedGram_column_sum_zero G h]
    simp
  exact_mod_cast hq

theorem integralCode_square_sum (h : G.IsSRGWith 99 14 1 2)
    (c : TriangleIndex G → ℤ) :
    (∑ u, integralCode G c u ^ 2) = 63 * integerGramNorm G c := by
  have hh := frame_code_square_sum (triangleGram G) (mixedGram G)
    (fun L => (c L : ℚ)) (mixedGram_transpose_mul_self G h)
  have hq : ((∑ u, integralCode G c u ^ 2 : ℤ) : ℚ) =
      63 * (integerGramNorm G c : ℚ) := by
    simpa only [Int.cast_sum, Int.cast_pow, integralCode_cast, integerGramNorm,
      Int.cast_mul, integerTriangleGram_cast] using hh
  exact_mod_cast hq

theorem integralCode_common_residue (c : TriangleIndex G → ℤ) (u : V) :
    integralCode G c u % 3 = (∑ L, c L) % 3 := by
  unfold integralCode
  calc
    (∑ L, integerMixedGram G u L * c L) % 3 =
        (∑ L, (integerMixedGram G u L * c L) % 3) % 3 := sum_int_mod _ _ _
    _ = (∑ L, c L % 3) % 3 := by
      congr 1
      apply sum_congr rfl
      intro L _
      rw [Int.mul_emod, integerMixedGram_mod_three]
      simp
    _ = (∑ L, c L) % 3 := (sum_int_mod _ _ _).symm

/-- If one code coordinate is a mixed Gram entry, the norm is at least four.
All integrality, parity and frame identities here come from the actual graph. -/
theorem integralCode_norm_gap (h : G.IsSRGWith 99 14 1 2)
    (c : TriangleIndex G → ℤ) (u : V)
    (hu : integralCode G c u = 4 ∨ integralCode G c u = -2 ∨ integralCode G c u = 1) :
    4 ≤ integerGramNorm G c := by
  exact integer_image_norm_gap_of_card h.card (integerGramNorm G c)
    (integralCode G c) (∑ L, c L) u
    (integerGramNorm_nonneg G h c) (integerGramNorm_even G c)
    (integralCode_sum_zero G h c) (integralCode_square_sum G h c)
    (integralCode_common_residue G c) hu

#print axioms integralCode_sum_zero
#print axioms integralCode_square_sum
#print axioms integralCode_common_residue
#print axioms integralCode_norm_gap

end Conway99
