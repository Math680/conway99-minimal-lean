import TensorLower
import TriangleSecondMoments

/-! End-to-end graph-level authentication of the minimal proof's delta result.
No frame, norm-gap, cubic-count or lattice premise is left in the theorem.
-/

namespace Conway99

open TriangleSecondMoments

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem graph_delta_ge_165 (h : G.IsSRGWith 99 14 1 2) : 165 ≤ triangleDelta G := by
  have hh := graph_integer_cubic_sum_ge_660 G h
  rw [integerGram_cube_total G h] at hh
  omega

theorem graph_minimal_delta_conclusions (h : G.IsSRGWith 99 14 1 2) :
    3 ∣ triangleDelta G ∧ 165 ≤ triangleDelta G ∧
      858 ≤ crossingPairCount G 2 ∧ crossingPairCount G 3 ≤ 1100 := by
  have hb := graph_delta_ge_165 G h
  have he := triangleDelta_eq_third_count G h
  refine ⟨triangleDelta_divisible_three G h, hb, ?_, ?_⟩
  · dsimp [triangleDelta] at hb
    omega
  · omega

#print axioms graph_delta_ge_165
#print axioms graph_minimal_delta_conclusions

end Conway99
