import SRG
import Incidence

/-! The rational triangle Gram is constructed from the actual graph.
The frame identity below is not a hypothesis on an abstract matrix.
-/

namespace Conway99

open scoped BigOperators Matrix
open Incidence

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def triangleGram : Matrix (TriangleIndex G) (TriangleIndex G) ℚ :=
  (1 / 9 : ℚ) • ((vertexTriangleIncidence G).transpose * vertexGram G *
    vertexTriangleIncidence G)

theorem vertexGram_transpose : (vertexGram G).transpose = vertexGram G := by
  ext u v
  simp [Matrix.transpose_apply, vertexGram_apply, eq_comm, SimpleGraph.adj_comm]

theorem triangleGram_transpose : (triangleGram G).transpose = triangleGram G := by
  simp only [triangleGram, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose, vertexGram_transpose, Matrix.mul_assoc]

theorem triangleGram_symmetric (L M : TriangleIndex G) :
    triangleGram G L M = triangleGram G M L := by
  have hh := congrArg (fun S : Matrix (TriangleIndex G) (TriangleIndex G) ℚ => S M L)
    (triangleGram_transpose G)
  exact hh

theorem triangleGram_square (h : G.IsSRGWith 99 14 1 2) :
    triangleGram G * triangleGram G = (21 : ℚ) • triangleGram G := by
  let B := vertexTriangleIncidence G
  let F := vertexGram G
  have hBB : B * B.transpose = (7 : ℚ) • (1 : Matrix V V ℚ) + G.adjMatrix ℚ := by
    simpa only [ofNat_smul_eq_nsmul] using incidence_product G h
  have hF2 : F * F = (63 : ℚ) • F := by
    simpa only [ofNat_smul_eq_nsmul] using vertexGram_square G h
  have hFA : F * G.adjMatrix ℚ = (-4 : ℚ) • F := by
    convert vertexGram_mul_adjacency G h using 1
  have hmid : F * (B * B.transpose) * F = (189 : ℚ) • F := by
    rw [hBB, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.add_mul,
      Matrix.smul_mul, hFA, Matrix.smul_mul, hF2]
    simp only [smul_smul, ← add_smul]
    norm_num
  have hH : (B.transpose * F * B) * (B.transpose * F * B) =
      (189 : ℚ) • (B.transpose * F * B) := by
    calc
      (B.transpose * F * B) * (B.transpose * F * B) =
          B.transpose * (F * (B * B.transpose) * F) * B := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hmid, Matrix.mul_smul, Matrix.smul_mul]
  change ((1 / 9 : ℚ) • (B.transpose * F * B)) *
      ((1 / 9 : ℚ) • (B.transpose * F * B)) =
    (21 : ℚ) • ((1 / 9 : ℚ) • (B.transpose * F * B))
  rw [Matrix.smul_mul, Matrix.mul_smul, hH]
  simp only [smul_smul]
  norm_num

theorem triangleGram_posSemidef (h : G.IsSRGWith 99 14 1 2) :
    (triangleGram G).PosSemidef := by
  have hp := (vertexGram_posSemidef G h).conjTranspose_mul_mul_same
    (vertexTriangleIncidence G)
  have ht : (vertexTriangleIncidence G).conjTranspose =
      (vertexTriangleIncidence G).transpose := by
    ext u v
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  rw [ht] at hp
  constructor
  · change ((1 / 9 : ℚ) • ((vertexTriangleIncidence G).transpose * vertexGram G *
        vertexTriangleIncidence G)).conjTranspose = _
    rw [Matrix.conjTranspose_smul, star_trivial, hp.1]
    rfl
  · intro x
    change 0 ≤ star x ⬝ᵥ (((1 / 9 : ℚ) •
      ((vertexTriangleIncidence G).transpose * vertexGram G * vertexTriangleIncidence G)) *ᵥ x)
    rw [Matrix.smul_mulVec, dotProduct_smul]
    exact mul_nonneg (by norm_num) (hp.2 x)

#print axioms triangleGram_square
#print axioms triangleGram_symmetric
#print axioms triangleGram_posSemidef

end Conway99
