import GramEntries
import IntegerNorm

/-! The abstract Gram congruence is now connected to the actual graph. -/

namespace Conway99

open scoped BigOperators Matrix
open Finset Incidence

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem integerTriangleGram_symmetric (L M : TriangleIndex G) :
    integerTriangleGram G L M = integerTriangleGram G M L := by
  have hh : (integerTriangleGram G L M : ℚ) = (integerTriangleGram G M L : ℚ) := by
    rw [integerTriangleGram_cast, integerTriangleGram_cast]
    exact triangleGram_symmetric G L M
  exact_mod_cast hh

theorem integerTriangleGram_square (h : G.IsSRGWith 99 14 1 2) :
    integerTriangleGram G * integerTriangleGram G = (21 : ℤ) • integerTriangleGram G := by
  ext L M
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  have hh := congrArg (fun S : Matrix (TriangleIndex G) (TriangleIndex G) ℚ => S L M)
    (triangleGram_square G h)
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at hh
  simp_rw [← integerTriangleGram_cast G] at hh
  exact_mod_cast hh

theorem graph_diagonal_contraction_divisible_four (h : G.IsSRGWith 99 14 1 2)
    (L : TriangleIndex G) : 4 ∣ diagonalContraction (integerTriangleGram G) L :=
  diagonal_contraction_divisible_four (integerTriangleGram G) L
    (integerTriangleGram_symmetric G) (integerTriangleGram_diag G)
    (integerTriangleGram_square G h)

theorem graph_contraction_total (h : G.IsSRGWith 99 14 1 2) :
    (∑ L, diagonalContraction (integerTriangleGram G) L) =
      21 * ∑ L, ∑ M, integerTriangleGram G L M ^ 3 :=
  contraction_total (integerTriangleGram G) (integerTriangleGram_symmetric G)
    (integerTriangleGram_square G h)

def integerGramNorm (c : TriangleIndex G → ℤ) : ℤ :=
  ∑ L, ∑ M, c L * c M * integerTriangleGram G L M

theorem integerGramNorm_even (c : TriangleIndex G → ℤ) :
    2 ∣ integerGramNorm G c :=
  diagonal_four_integral_norm_even (integerTriangleGram G) c
    (integerTriangleGram_symmetric G) (integerTriangleGram_diag G)

theorem integerGramNorm_cast (c : TriangleIndex G → ℤ) :
    (integerGramNorm G c : ℚ) =
      (fun L => (c L : ℚ)) ⬝ᵥ (triangleGram G *ᵥ (fun L => (c L : ℚ))) := by
  simp only [integerGramNorm, Int.cast_sum, Int.cast_mul, integerTriangleGram_cast,
    dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply sum_congr rfl
  intro L _
  apply sum_congr rfl
  intro M _
  ring

theorem integerGramNorm_nonneg (h : G.IsSRGWith 99 14 1 2)
    (c : TriangleIndex G → ℤ) : 0 ≤ integerGramNorm G c := by
  have hp := (triangleGram_posSemidef G h).2 (fun L => (c L : ℚ))
  simp only [star_trivial] at hp
  rw [← integerGramNorm_cast G c] at hp
  exact_mod_cast hp

#print axioms integerTriangleGram_square
#print axioms graph_diagonal_contraction_divisible_four
#print axioms graph_contraction_total
#print axioms integerGramNorm_even
#print axioms integerGramNorm_nonneg

end Conway99
