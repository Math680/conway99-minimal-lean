import FourDirectionOnlyZeroCase
import ZeroCaseSystemSymmetry
import ZeroCaseTripleGraph
import ZeroCaseOrbitFour

/-! End-to-end exclusion of four root directions. Every finite certificate
is connected to the actual graph; no zero-case exclusion is assumed. -/

namespace Conway99

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem four_directions_zero_impossible (h : G.IsSRGWith 99 14 1 2)
    (F : FourDirectionSystem G) (hc : F.HasSignedCells)
    (hz : F.weightCount 0 = 0) : False := by
  obtain ⟨F', j, hc', hz', hrep⟩ := zero_case_exists_normalized_system F h hc hz
  fin_cases j
  · exact ZeroHighRows.high_configuration_orbit_zero_impossible
      (F'.actualHighConfiguration hc' 0 hrep h hz')
  · exact F'.normalized_orbit_one_impossible h hc' hz' hrep
  · exact ZeroHighRows.high_configuration_orbit_two_impossible
      (F'.actualHighConfiguration hc' 2 hrep h hz')
  · exact F'.normalized_orbit_three_impossible h hc' hz' hrep
  · exact F'.zero_case_orbit_four_impossible h hc' hz' hrep

theorem four_signed_directions_impossible (h : G.IsSRGWith 99 14 1 2)
    (F : FourDirectionSystem G) (hc : F.HasSignedCells) : False :=
  four_directions_zero_impossible G h F hc (four_directions_zero_count_eq_zero G h F hc)

theorem canonicalLift_rootSubspace_finrank_le_three (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G))
    (hH : ∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0) :
    Module.finrank ℚ (rootSubspace G H) ≤ 3 :=
  canonicalLift_root_rank_le_three_of_zero_case_exclusion G h
    (fun F hc hz => four_directions_zero_impossible G h F hc hz) H hH

#print axioms four_directions_zero_impossible
#print axioms four_signed_directions_impossible
#print axioms canonicalLift_rootSubspace_finrank_le_three

end Conway99
