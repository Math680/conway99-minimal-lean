import Core

/-!
Finite rational frame contractions. The frame equation is an explicit premise,
and must be supplied by the graph/Gram construction at application sites.
-/

namespace Conway99

open scoped BigOperators
open Finset

def weightedImageNorm {U T : Type*} [Fintype T]
    (S : Matrix T T ℚ) (D : Matrix U T ℚ) (u : U) (J : T) : ℚ :=
  (1 / 9 : ℚ) * ∑ L, ∑ M,
    (D u L * S L J) * (D u M * S M J) * S L M

theorem weightedImageNorm_total {U T : Type*} [Fintype U] [Fintype T]
    (S : Matrix T T ℚ) (D : Matrix U T ℚ) (J : T)
    (hsym : ∀ L M, S L M = S M L)
    (hframe : D.transpose * D = (63 : ℚ) • S) :
    (∑ u, weightedImageNorm S D u J) =
      7 * ∑ L, ∑ M, S J L * S J M * (S L M) ^ 2 := by
  have hc (L M : T) : (∑ u, D u L * D u M) = 63 * S L M := by
    have hh := congrArg (fun R : Matrix T T ℚ => R L M) hframe
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      smul_eq_mul] using hh
  calc
    (∑ u, weightedImageNorm S D u J) =
        (1 / 9 : ℚ) * ∑ u, ∑ L, ∑ M,
          (D u L * S L J) * (D u M * S M J) * S L M := by
      simp only [weightedImageNorm, mul_sum]
    _ = (1 / 9 : ℚ) * ∑ L, ∑ M, ∑ u,
          (D u L * S L J) * (D u M * S M J) * S L M := by
      congr 1
      rw [sum_comm]
      apply sum_congr rfl
      intro L _
      rw [sum_comm]
    _ = (1 / 9 : ℚ) * ∑ L, ∑ M,
          (∑ u, D u L * D u M) * (S L J * S M J * S L M) := by
      congr 1
      apply sum_congr rfl
      intro L _
      apply sum_congr rfl
      intro M _
      rw [sum_mul]
      apply sum_congr rfl
      intro u _
      ring
    _ = (1 / 9 : ℚ) * ∑ L, ∑ M,
          (63 * S L M) * (S L J * S M J * S L M) := by
      simp_rw [hc]
    _ = 7 * ∑ L, ∑ M, S J L * S J M * (S L M) ^ 2 := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro L _
      apply sum_congr rfl
      intro M _
      rw [hsym L J, hsym M J]
      ring

/-- The squared norm of a frame code is 63 times its Gram norm. -/
theorem frame_code_square_sum {U T : Type*} [Fintype U] [Fintype T]
    (S : Matrix T T ℚ) (D : Matrix U T ℚ) (c : T → ℚ)
    (hframe : D.transpose * D = (63 : ℚ) • S) :
    (∑ u, (∑ L, D u L * c L) ^ 2) =
      63 * ∑ L, ∑ M, c L * c M * S L M := by
  have hc (L M : T) : (∑ u, D u L * D u M) = 63 * S L M := by
    have hh := congrArg (fun R : Matrix T T ℚ => R L M) hframe
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      smul_eq_mul] using hh
  calc
    (∑ u, (∑ L, D u L * c L) ^ 2) =
        ∑ u, ∑ L, ∑ M, (D u L * c L) * (D u M * c M) := by
      apply sum_congr rfl
      intro u _
      simp only [pow_two, sum_mul, mul_sum]
      rw [sum_comm]
    _ = ∑ L, ∑ M, ∑ u, (D u L * c L) * (D u M * c M) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro L _
      rw [sum_comm]
    _ = ∑ L, ∑ M, (∑ u, D u L * D u M) * (c L * c M) := by
      apply sum_congr rfl
      intro L _
      apply sum_congr rfl
      intro M _
      rw [sum_mul]
      apply sum_congr rfl
      intro u _
      ring
    _ = ∑ L, ∑ M, (63 * S L M) * (c L * c M) := by
      simp_rw [hc]
    _ = 63 * ∑ L, ∑ M, c L * c M * S L M := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro L _
      apply sum_congr rfl
      intro M _
      ring

#print axioms weightedImageNorm_total
#print axioms frame_code_square_sum

end Conway99
