import Gram

/-! Mixed vertex--triangle Gram identities from the actual SRG. -/

namespace Conway99

open scoped BigOperators Matrix
open Incidence

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def mixedGram : Matrix V (TriangleIndex G) ℚ :=
  (1 / 3 : ℚ) • (vertexGram G * vertexTriangleIncidence G)

theorem incidence_mul_triangleGram (h : G.IsSRGWith 99 14 1 2) :
    vertexTriangleIncidence G * triangleGram G = mixedGram G := by
  let B := vertexTriangleIncidence G
  let F := vertexGram G
  have hBB : B * B.transpose = (7 : ℚ) • (1 : Matrix V V ℚ) + G.adjMatrix ℚ := by
    simpa only [ofNat_smul_eq_nsmul] using incidence_product G h
  have hAF : G.adjMatrix ℚ * F = (-4 : ℚ) • F := by
    have hFA : F * G.adjMatrix ℚ = (-4 : ℚ) • F := by
      convert vertexGram_mul_adjacency G h using 1
    have hh := congrArg Matrix.transpose hFA
    simpa only [Matrix.transpose_mul, Matrix.transpose_smul, F,
      vertexGram_transpose, SimpleGraph.transpose_adjMatrix] using hh
  have hBF : (B * B.transpose) * F = (3 : ℚ) • F := by
    rw [hBB, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hAF, ← add_smul]
    norm_num
  change B * ((1 / 9 : ℚ) • (B.transpose * F * B)) = (1 / 3 : ℚ) • (F * B)
  rw [Matrix.mul_smul]
  have he : B * (B.transpose * F * B) = ((B * B.transpose) * F) * B := by
    simp only [Matrix.mul_assoc]
  rw [he, hBF, Matrix.smul_mul, smul_smul]
  norm_num

theorem transpose_incidence_mul_mixedGram :
    (vertexTriangleIncidence G).transpose * mixedGram G = (3 : ℚ) • triangleGram G := by
  simp only [mixedGram, triangleGram, Matrix.mul_smul, Matrix.mul_assoc, smul_smul]
  norm_num

theorem mixedGram_mul_triangleGram (h : G.IsSRGWith 99 14 1 2) :
    mixedGram G * triangleGram G = (21 : ℚ) • mixedGram G := by
  rw [← incidence_mul_triangleGram G h, Matrix.mul_assoc, triangleGram_square G h,
    Matrix.mul_smul]

theorem mixedGram_transpose_mul_self (h : G.IsSRGWith 99 14 1 2) :
    (mixedGram G).transpose * mixedGram G = (63 : ℚ) • triangleGram G := by
  let B := vertexTriangleIncidence G
  let F := vertexGram G
  have hF2 : F * F = (63 : ℚ) • F := by
    simpa only [ofNat_smul_eq_nsmul] using vertexGram_square G h
  have hFtrans : F.transpose = F := vertexGram_transpose G
  change ((1 / 3 : ℚ) • (F * B)).transpose * ((1 / 3 : ℚ) • (F * B)) =
    (63 : ℚ) • ((1 / 9 : ℚ) • (B.transpose * F * B))
  rw [Matrix.transpose_smul, Matrix.transpose_mul, hFtrans,
    Matrix.smul_mul, Matrix.mul_smul]
  have he : (B.transpose * F) * (F * B) = B.transpose * (F * F) * B := by
    simp only [Matrix.mul_assoc]
  rw [he, hF2, Matrix.mul_smul, Matrix.smul_mul]
  simp only [smul_smul]
  norm_num

theorem vertexGram_row_sum_zero (h : G.IsSRGWith 99 14 1 2) (u : V) :
    (∑ v, vertexGram G u v) = 0 := by
  have hh := congrArg (fun M : Matrix V V ℚ => M u u) (vertexGram_mul_ones G h)
  simpa [Matrix.mul_apply, allOnes] using hh

theorem vertexGram_column_sum_zero (h : G.IsSRGWith 99 14 1 2) (v : V) :
    (∑ u, vertexGram G u v) = 0 := by
  have hs (u : V) : vertexGram G u v = vertexGram G v u := by
    have hh := congrArg (fun M : Matrix V V ℚ => M v u) (vertexGram_transpose G)
    exact hh
  simpa only [hs] using vertexGram_row_sum_zero G h v

theorem mixedGram_column_sum_zero (h : G.IsSRGWith 99 14 1 2)
    (L : TriangleIndex G) : (∑ u, mixedGram G u L) = 0 := by
  simp only [mixedGram, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  rw [← Finset.mul_sum]
  have hz : (∑ u, ∑ v, vertexGram G u v * vertexTriangleIncidence G v L) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, vertexGram_column_sum_zero G h]
    simp
  rw [hz, mul_zero]

#print axioms incidence_mul_triangleGram
#print axioms mixedGram_mul_triangleGram
#print axioms mixedGram_transpose_mul_self
#print axioms mixedGram_column_sum_zero

end Conway99
