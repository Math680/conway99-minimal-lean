import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-! Graph-level starting point. No use is made of the open `conway_99` declaration. -/

namespace Conway99

open scoped BigOperators Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def allOnes : Matrix V V ℚ := fun _ _ => 1

theorem adjacency_square (h : G.IsSRGWith 99 14 1 2) :
    G.adjMatrix ℚ * G.adjMatrix ℚ =
      (12 : ℕ) • (1 : Matrix V V ℚ) - G.adjMatrix ℚ + (2 : ℕ) • allOnes := by
  have hh := h.matrix_eq (α := ℚ)
  rw [pow_two] at hh
  rw [hh]
  ext u v
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
  by_cases huv : u = v
  · subst v
    norm_num [SimpleGraph.adjMatrix_apply, allOnes, Matrix.one_apply]
  · by_cases ha : G.Adj u v <;>
      norm_num [SimpleGraph.adjMatrix_apply, SimpleGraph.compl_adj, allOnes, huv, ha,
        Matrix.one_apply]

theorem common_neighbors_at_most_two (h : G.IsSRGWith 99 14 1 2)
    (u v : V) (hne : u ≠ v) : Fintype.card (G.commonNeighbors u v) ≤ 2 := by
  by_cases ha : G.Adj u v
  · rw [h.of_adj u v ha]
    norm_num
  · rw [h.of_not_adj hne ha]

theorem adjacency_mul_ones (h : G.IsSRGWith 99 14 1 2) :
    G.adjMatrix ℚ * allOnes = (14 : ℕ) • allOnes := by
  ext u v
  simp [allOnes, h.regular.degree_eq]

theorem ones_mul_adjacency (h : G.IsSRGWith 99 14 1 2) :
    allOnes * G.adjMatrix ℚ = (14 : ℕ) • allOnes := by
  ext u v
  simp [allOnes, h.regular.degree_eq]

theorem ones_square (h : G.IsSRGWith 99 14 1 2) :
    (allOnes : Matrix V V ℚ) * allOnes = (99 : ℕ) • allOnes := by
  ext u v
  simp [allOnes, Matrix.mul_apply, h.card]

private def gramPolynomial {R : Type*} [Ring R] (A J : R) : R := 27 - 9 * A + J

private theorem gramPolynomial_square {R : Type*} [Ring R] (A J : R)
    (hAA : A * A = 12 - A + 2 * J) (hAJ : A * J = 14 * J)
    (hJA : J * A = 14 * J) (hJJ : J * J = 99 * J) :
    gramPolynomial A J * gramPolynomial A J = 63 * gramPolynomial A J := by
  unfold gramPolynomial
  calc
    (27 - 9 * A + J) * (27 - 9 * A + J) =
        729 - 486 * A + 81 * (A * A) + 54 * J - 9 * (A * J) -
          9 * (J * A) + J * J := by
            noncomm_ring
            norm_num [nsmul_eq_mul, zsmul_eq_mul]
            noncomm_ring
    _ = _ := by
      rw [hAA, hAJ, hJA, hJJ]
      noncomm_ring
      norm_num [nsmul_eq_mul, zsmul_eq_mul]
      noncomm_ring
      rw [show (1701 : R) = 729 + 972 by norm_num]
      abel

private theorem gramPolynomial_mul_A {R : Type*} [Ring R] (A J : R)
    (hAA : A * A = 12 - A + 2 * J) (hJA : J * A = 14 * J) :
    gramPolynomial A J * A = -4 * gramPolynomial A J := by
  unfold gramPolynomial
  calc
    (27 - 9 * A + J) * A = 27 * A - 9 * (A * A) + J * A := by noncomm_ring
    _ = _ := by
      rw [hAA, hJA]
      noncomm_ring
      norm_num [nsmul_eq_mul, zsmul_eq_mul]
      noncomm_ring

private theorem gramPolynomial_mul_J {R : Type*} [Ring R] (A J : R)
    (hAJ : A * J = 14 * J) (hJJ : J * J = 99 * J) :
    gramPolynomial A J * J = 0 := by
  unfold gramPolynomial
  calc
    (27 - 9 * A + J) * J = 27 * J - 9 * (A * J) + J * J := by noncomm_ring
    _ = 0 := by rw [hAJ, hJJ]; noncomm_ring

def vertexGram : Matrix V V ℚ := gramPolynomial (G.adjMatrix ℚ) allOnes

theorem vertexGram_eq : vertexGram G =
    (27 : ℕ) • (1 : Matrix V V ℚ) - (9 : ℕ) • G.adjMatrix ℚ + allOnes := by
  simp only [vertexGram, gramPolynomial, nsmul_eq_mul, mul_one, Nat.cast_ofNat]

theorem vertexGram_apply (u v : V) : vertexGram G u v =
    if u = v then 28 else if G.Adj u v then -8 else 1 := by
  rw [vertexGram_eq]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
  by_cases huv : u = v
  · subst v
    norm_num [SimpleGraph.adjMatrix_apply, Matrix.one_apply, allOnes]
  · by_cases ha : G.Adj u v <;>
      norm_num [SimpleGraph.adjMatrix_apply, Matrix.one_apply, allOnes, huv, ha]

theorem vertexGram_isHermitian : (vertexGram G).IsHermitian := by
  change (vertexGram G).conjTranspose = vertexGram G
  ext u v
  simp [Matrix.conjTranspose_apply, vertexGram_apply, eq_comm, SimpleGraph.adj_comm]

theorem vertexGram_square (h : G.IsSRGWith 99 14 1 2) :
    vertexGram G * vertexGram G = (63 : ℕ) • vertexGram G := by
  simpa only [vertexGram, nsmul_eq_mul] using
    gramPolynomial_square (G.adjMatrix ℚ) (allOnes : Matrix V V ℚ)
      (by simpa only [nsmul_eq_mul, mul_one] using adjacency_square G h)
      (by simpa only [nsmul_eq_mul] using adjacency_mul_ones G h)
      (by simpa only [nsmul_eq_mul] using ones_mul_adjacency G h)
      (by simpa only [nsmul_eq_mul] using ones_square G h)

theorem vertexGram_mul_adjacency (h : G.IsSRGWith 99 14 1 2) :
    vertexGram G * G.adjMatrix ℚ = (-4 : ℤ) • vertexGram G := by
  simpa only [vertexGram, zsmul_eq_mul, Int.cast_neg, Int.cast_ofNat] using
    gramPolynomial_mul_A (G.adjMatrix ℚ) (allOnes : Matrix V V ℚ)
      (by simpa only [nsmul_eq_mul, mul_one] using adjacency_square G h)
      (by simpa only [nsmul_eq_mul] using ones_mul_adjacency G h)

theorem vertexGram_mul_ones (h : G.IsSRGWith 99 14 1 2) :
    vertexGram G * allOnes = 0 := by
  exact gramPolynomial_mul_J (G.adjMatrix ℚ) (allOnes : Matrix V V ℚ)
    (by simpa only [nsmul_eq_mul] using adjacency_mul_ones G h)
    (by simpa only [nsmul_eq_mul] using ones_square G h)

theorem vertexGram_posSemidef (h : G.IsSRGWith 99 14 1 2) :
    (vertexGram G).PosSemidef := by
  refine ⟨vertexGram_isHermitian G, ?_⟩
  intro x
  have ht : (vertexGram G).transpose = vertexGram G := by
    ext u v
    simp [Matrix.transpose_apply, vertexGram_apply, eq_comm, SimpleGraph.adj_comm]
  have hx : 0 ≤ x ⬝ᵥ ((vertexGram G * vertexGram G) *ᵥ x) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ht]
    exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  rw [vertexGram_square G h, Matrix.smul_mulVec, dotProduct_smul] at hx
  simp only [nsmul_eq_mul] at hx
  simp only [star_trivial]
  norm_num at hx
  exact hx

#print axioms vertexGram_square
#print axioms vertexGram_mul_adjacency
#print axioms vertexGram_mul_ones
#print axioms vertexGram_apply
#print axioms vertexGram_posSemidef

#print axioms adjacency_square
#print axioms common_neighbors_at_most_two

end Conway99
