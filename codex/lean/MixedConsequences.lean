import MixedEntries

/-! Zero sums, adjacency action, and the quadratic mixed-Gram identity. -/

namespace Conway99

open scoped BigOperators
open Incidence

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem incidence_row_sum (h : G.IsSRGWith 99 14 1 2) (u : V) :
    (∑ L : TriangleIndex G, vertexTriangleIncidence G u L) = 7 := by
  have hh : (∑ L : TriangleIndex G, vertexTriangleIncidence G u L) =
      ((trianglesAt G u).card : ℚ) := by
    simp only [vertexTriangleIncidence]
    rw [Finset.sum_coe_sort (G.cliqueFinset 3)
      (fun s : Finset V => if u ∈ s then (1 : ℚ) else 0)]
    simp [trianglesAt]
  rw [hh, vertex_triangle_count G h u]
  norm_num

theorem mixedGram_row_sum_zero (h : G.IsSRGWith 99 14 1 2) (u : V) :
    (∑ L : TriangleIndex G, mixedGram G u L) = 0 := by
  simp only [mixedGram, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, incidence_row_sum G h]
  rw [← Finset.sum_mul, vertexGram_row_sum_zero G h u]
  norm_num

theorem triangleGram_row_sum_zero (h : G.IsSRGWith 99 14 1 2)
    (L : TriangleIndex G) : (∑ M : TriangleIndex G, triangleGram G L M) = 0 := by
  have hz : (∑ M : TriangleIndex G,
      ((vertexTriangleIncidence G).transpose * mixedGram G) L M) = 0 := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, mixedGram_row_sum_zero G h]
    simp
  have hh := congrArg
    (fun Q : Matrix (TriangleIndex G) (TriangleIndex G) ℚ => ∑ M, Q L M)
    (transpose_incidence_mul_mixedGram G)
  change (∑ M, ((vertexTriangleIncidence G).transpose * mixedGram G) L M) =
    ∑ M, 3 * triangleGram G L M at hh
  rw [hz, ← Finset.mul_sum] at hh
  linarith

theorem triangleGram_column_sum_zero (h : G.IsSRGWith 99 14 1 2)
    (J : TriangleIndex G) : (∑ L : TriangleIndex G, triangleGram G L J) = 0 := by
  have hs (L : TriangleIndex G) : triangleGram G L J = triangleGram G J L :=
    triangleGram_symmetric G L J
  simpa only [hs] using triangleGram_row_sum_zero G h J

theorem adjacency_mul_mixedGram (h : G.IsSRGWith 99 14 1 2) :
    G.adjMatrix ℚ * mixedGram G = (-4 : ℚ) • mixedGram G := by
  have hFA : vertexGram G * G.adjMatrix ℚ = (-4 : ℚ) • vertexGram G := by
    convert vertexGram_mul_adjacency G h using 1
  have hh := congrArg Matrix.transpose hFA
  have hAF : G.adjMatrix ℚ * vertexGram G = (-4 : ℚ) • vertexGram G := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_smul, vertexGram_transpose,
      SimpleGraph.transpose_adjMatrix] using hh
  simp only [mixedGram]
  rw [Matrix.mul_smul, ← Matrix.mul_assoc, hAF, Matrix.smul_mul]
  simp only [smul_smul]
  norm_num

def mixedGramPointwiseSquare : Matrix V (TriangleIndex G) ℚ :=
  fun u L => mixedGram G u L ^ 2

def mixedGramRectOnes : Matrix V (TriangleIndex G) ℚ := fun _ _ => 1

theorem mixedGramPointwiseSquare_eq (h : G.IsSRGWith 99 14 1 2) :
    mixedGramPointwiseSquare G = mixedGramRectOnes G +
      (9 : ℚ) • vertexTriangleIncidence G +
      (3 : ℚ) • (G.adjMatrix ℚ * vertexTriangleIncidence G) := by
  ext u L
  simpa only [mixedGramPointwiseSquare, mixedGramRectOnes, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
    using mixedGram_entry_square G h u L

theorem mixedGramPointwiseSquare_mul_triangleGram (h : G.IsSRGWith 99 14 1 2) :
    mixedGramPointwiseSquare G * triangleGram G = (-3 : ℚ) • mixedGram G := by
  have hones : mixedGramRectOnes G * triangleGram G = 0 := by
    ext u J
    simpa only [Matrix.mul_apply, mixedGramRectOnes, one_mul, Matrix.zero_apply]
      using triangleGram_column_sum_zero G h J
  rw [mixedGramPointwiseSquare_eq G h]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc,
    incidence_mul_triangleGram G h]
  rw [hones, adjacency_mul_mixedGram G h, zero_add, smul_smul, ← add_smul]
  norm_num

/-- The graph-level quadratic identity used to construct the images M_u x_J. -/
theorem mixedGram_squared_weighted_sum (h : G.IsSRGWith 99 14 1 2)
    (u : V) (J : TriangleIndex G) :
    (∑ L : TriangleIndex G, mixedGram G u L ^ 2 * triangleGram G L J) =
      -3 * mixedGram G u J := by
  have hh := congrArg (fun M : Matrix V (TriangleIndex G) ℚ => M u J)
    (mixedGramPointwiseSquare_mul_triangleGram G h)
  simpa only [Matrix.mul_apply, mixedGramPointwiseSquare, Matrix.smul_apply, smul_eq_mul]
    using hh

#print axioms incidence_row_sum
#print axioms mixedGram_row_sum_zero
#print axioms triangleGram_row_sum_zero
#print axioms triangleGram_column_sum_zero
#print axioms adjacency_mul_mixedGram
#print axioms mixedGramPointwiseSquare_eq
#print axioms mixedGramPointwiseSquare_mul_triangleGram
#print axioms mixedGram_squared_weighted_sum

end Conway99
