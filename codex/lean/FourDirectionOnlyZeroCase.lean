import FourDirectionSignedRootBridge
import FourDirectionArcContradiction
import ZeroCaseAllPackings

/-! The entire one-zero branch is eliminated. The remaining finite zero
branch is explicit; this module does not claim its exclusion. -/

namespace Conway99

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem four_directions_zero_count_eq_zero (h : G.IsSRGWith 99 14 1 2)
    (F : FourDirectionSystem G) (hc : F.HasSignedCells) : F.weightCount 0 = 0 := by
  have hh := F.zero_weight_count_le_one h
  by_contra hn
  have hz : F.weightCount 0 = 1 := by omega
  exact four_directions_one_zero_impossible F h hc hz

theorem canonicalLift_rank_four_forces_zero_case (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G))
    (hH : ∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0)
    (hrank : Module.finrank ℚ (rootSubspace G H) = 4) :
    ∃ F : FourDirectionSystem G,
      F.HasSignedCells ∧ F.W.card = 39 ∧ F.weightCount 0 = 0 ∧
      F.weightCount 4 ≤ 2 ∧ F.highSignatures ∈ zeroCaseHighPackings (F.weightCount 4) := by
  obtain ⟨F, hc, hW, _⟩ := canonicalLift_root_rank_four_signed_cover G h H hH hrank
  have hz := four_directions_zero_count_eq_zero G h F hc
  have hb := F.weight_count_balance h
  exact ⟨F, hc, hW, hz, by omega, zero_case_actual_high_packing_mem F h hc hz⟩

theorem canonicalLift_root_rank_le_three_of_zero_case_exclusion
    (h : G.IsSRGWith 99 14 1 2)
    (hzero : ∀ F : FourDirectionSystem G, F.HasSignedCells → F.weightCount 0 = 0 → False)
    (H : Submodule ℤ (CanonicalDiscriminant G))
    (hH : ∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0) :
    Module.finrank ℚ (rootSubspace G H) ≤ 3 := by
  have hfour := canonicalLift_rootSubspace_finrank_le_four G h H hH
  by_contra hn
  have hrank : Module.finrank ℚ (rootSubspace G H) = 4 := by omega
  obtain ⟨F, hc, _, hz, _, _⟩ := canonicalLift_rank_four_forces_zero_case G h H hH hrank
  exact hzero F hc hz

#print axioms four_directions_zero_count_eq_zero
#print axioms canonicalLift_rank_four_forces_zero_case
#print axioms canonicalLift_root_rank_le_three_of_zero_case_exclusion

end Conway99
