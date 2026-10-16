import MixedEntries
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Exact dimensions of the graph's rational frames, without spectral assumptions. -/

namespace Conway99

open scoped BigOperators Matrix
open Incidence

theorem scaled_idempotent_trace_rank {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℚ) (c : ℚ) (hc : c ≠ 0)
    (hA : A * A = c • A) : A.trace = c * (A.rank : ℚ) := by
  let P := c⁻¹ • A
  have hP : P * P = P := by
    dsimp [P]
    rw [Matrix.smul_mul, Matrix.mul_smul, hA, smul_smul, smul_smul]
    congr 1
    field_simp
  have hf : IsIdempotentElem P.toLin' := by
    change P.toLin' * P.toLin' = P.toLin'
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP]
  have ht := ((LinearMap.isProj_range_iff_isIdempotentElem P.toLin').2 hf).trace
  have hr : LinearMap.range P.toLin' = LinearMap.range A.mulVecLin := by
    rw [Matrix.toLin'_apply']
    have he : P.mulVecLin = c⁻¹ • A.mulVecLin := by
      ext x i
      simp [P, Matrix.smul_mulVec]
    rw [he, LinearMap.range_smul _ _ (inv_ne_zero hc)]
  rw [Matrix.trace_toLin'_eq, hr] at ht
  change P.trace = (A.rank : ℚ) at ht
  have hs : P.trace = c⁻¹ * A.trace := by
    simp [P, Matrix.trace_smul]
  rw [hs] at ht
  field_simp at ht
  nlinarith

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem vertexGram_trace (h : G.IsSRGWith 99 14 1 2) :
    (vertexGram G).trace = 2772 := by
  norm_num [Matrix.trace, Matrix.diag, vertexGram_apply, h.card]

theorem vertexGram_rank (h : G.IsSRGWith 99 14 1 2) :
    (vertexGram G).rank = 44 := by
  have hh := scaled_idempotent_trace_rank (vertexGram G) 63 (by norm_num)
    (by simpa only [ofNat_smul_eq_nsmul] using vertexGram_square G h)
  rw [vertexGram_trace G h] at hh
  have he : ((vertexGram G).rank : ℚ) = 44 := by linarith
  exact_mod_cast he

theorem triangleGram_trace (h : G.IsSRGWith 99 14 1 2) :
    (triangleGram G).trace = 924 := by
  have hc : Fintype.card (TriangleIndex G) = 231 := by
    simpa only [Fintype.card_coe] using triangle_count_231 G h
  simp only [Matrix.trace, Matrix.diag, triangleGram_diag, Finset.sum_const,
    Finset.card_univ, hc]
  norm_num

theorem triangleGram_rank (h : G.IsSRGWith 99 14 1 2) :
    (triangleGram G).rank = 44 := by
  have hh := scaled_idempotent_trace_rank (triangleGram G) 21 (by norm_num)
    (triangleGram_square G h)
  rw [triangleGram_trace G h] at hh
  have he : ((triangleGram G).rank : ℚ) = 44 := by linarith
  exact_mod_cast he

#print axioms vertexGram_rank
#print axioms triangleGram_rank

end Conway99
