import FrameContraction

/-!
Rational algebra for the integral image coefficients in section 3.
No integrality or graph property is claimed here: the matrix equations used
below are explicit assumptions, to be supplied by graph-derived matrices.
-/

namespace Conway99

open scoped BigOperators Matrix
open Finset

def rationalImageCoeff {U T : Type*} [DecidableEq T]
    (S : Matrix T T ℚ) (D : Matrix U T ℚ) (u : U) (J L : T) : ℚ :=
  -7 * (if L = J then 1 else 0) + ((1 - D u L) / 3) * S L J

def rationalImageWeight {U T : Type*}
    (S : Matrix T T ℚ) (D : Matrix U T ℚ) (u : U) (J L : T) : ℚ :=
  D u L * S L J

/-- Any matrix R satisfying RS=21R obeys the image coefficient identity. -/
theorem imageCoeff_mulVec_of_product {U T R : Type*} [Fintype T] [DecidableEq T]
    (S : Matrix T T ℚ) (D : Matrix U T ℚ) (M : Matrix R T ℚ)
    (u : U) (J : T) (hMS : M * S = (21 : ℚ) • M) :
    M.mulVec (rationalImageCoeff S D u J) =
      (-1 / 3 : ℚ) • M.mulVec (rationalImageWeight S D u J) := by
  ext i
  have hrow : (∑ L, M i L * S L J) = 21 * M i J := by
    have hh := congrArg (fun A : Matrix R T ℚ => A i J) hMS
    simpa only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] using hh
  have hdelta : (∑ L, M i L * (if L = J then 1 else 0)) = M i J := by
    simp
  change (∑ L, M i L * rationalImageCoeff S D u J L) =
    (-1 / 3 : ℚ) * ∑ L, M i L * rationalImageWeight S D u J L
  calc
    (∑ L, M i L * rationalImageCoeff S D u J L) =
        ∑ L, (-7 * (M i L * (if L = J then 1 else 0)) +
          (1 / 3 : ℚ) * (M i L * S L J) -
          (1 / 3 : ℚ) * (M i L * rationalImageWeight S D u J L)) := by
      apply sum_congr rfl
      intro L _
      unfold rationalImageCoeff rationalImageWeight
      ring
    _ = -7 * M i J + (1 / 3 : ℚ) * (21 * M i J) -
          (1 / 3 : ℚ) * ∑ L, M i L * rationalImageWeight S D u J L := by
      rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum,
        hdelta, hrow]
    _ = (-1 / 3 : ℚ) * ∑ L, M i L * rationalImageWeight S D u J L := by ring

theorem imageCoeff_gram_mulVec {U T : Type*} [Fintype T] [DecidableEq T]
    (S : Matrix T T ℚ) (D : Matrix U T ℚ) (u : U) (J : T)
    (hS : S * S = (21 : ℚ) • S) :
    S.mulVec (rationalImageCoeff S D u J) =
      (-1 / 3 : ℚ) • S.mulVec (rationalImageWeight S D u J) :=
  imageCoeff_mulVec_of_product S D S u J hS

theorem imageCoeff_code_mulVec {U T : Type*} [Fintype T] [DecidableEq T]
    (S : Matrix T T ℚ) (D : Matrix U T ℚ) (u : U) (J : T)
    (hDS : D * S = (21 : ℚ) • D) :
    D.mulVec (rationalImageCoeff S D u J) =
      (-1 / 3 : ℚ) • D.mulVec (rationalImageWeight S D u J) :=
  imageCoeff_mulVec_of_product S D D u J hDS

theorem imageCoeff_gram_norm {U T : Type*} [Fintype T] [DecidableEq T]
    (S : Matrix T T ℚ) (D : Matrix U T ℚ) (u : U) (J : T)
    (hsym : ∀ L M, S L M = S M L)
    (hS : S * S = (21 : ℚ) • S) :
    rationalImageCoeff S D u J ⬝ᵥ S.mulVec (rationalImageCoeff S D u J) =
      weightedImageNorm S D u J := by
  let c := rationalImageCoeff S D u J
  let a := rationalImageWeight S D u J
  have hSc : S.mulVec c = (-1 / 3 : ℚ) • S.mulVec a :=
    imageCoeff_gram_mulVec S D u J hS
  have hpair : c ⬝ᵥ S.mulVec a = a ⬝ᵥ S.mulVec c := by
    simp only [dotProduct, Matrix.mulVec, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro L _
    apply sum_congr rfl
    intro M _
    rw [hsym M L]
    ring
  change c ⬝ᵥ S.mulVec c = weightedImageNorm S D u J
  calc
    c ⬝ᵥ S.mulVec c = (-1 / 3 : ℚ) * (c ⬝ᵥ S.mulVec a) := by
      rw [hSc, dotProduct_smul, smul_eq_mul]
    _ = (-1 / 3 : ℚ) * (a ⬝ᵥ S.mulVec c) := by rw [hpair]
    _ = (1 / 9 : ℚ) * (a ⬝ᵥ S.mulVec a) := by
      rw [hSc, dotProduct_smul, smul_eq_mul]
      ring
    _ = weightedImageNorm S D u J := by
      simp only [weightedImageNorm, dotProduct, Matrix.mulVec, mul_sum]
      apply sum_congr rfl
      intro L _
      apply sum_congr rfl
      intro M _
      dsimp [a, rationalImageWeight]
      ring

#print axioms imageCoeff_mulVec_of_product
#print axioms imageCoeff_gram_mulVec
#print axioms imageCoeff_code_mulVec
#print axioms imageCoeff_gram_norm

end Conway99
