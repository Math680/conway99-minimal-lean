import DeltaBound
import RootRankThree
import CanonicalDet49Lift

/-! Summary of the unconditional delta and root-rank conclusions.
Existence of the determinant-49 lift is separately labelled as conditional
on the still-unproved analytic Poisson property. -/

namespace Conway99

open TriangleSecondMoments

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem graph_delta_and_root_rank (h : G.IsSRGWith 99 14 1 2) :
    (3 ∣ triangleDelta G ∧ 165 ≤ triangleDelta G ∧
      858 ≤ crossingPairCount G 2 ∧ crossingPairCount G 3 ≤ 1100) ∧
    (∀ H : Submodule ℤ (CanonicalDiscriminant G),
      (∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0) →
        Module.finrank ℚ (rootSubspace G H) ≤ 3) := by
  exact ⟨graph_minimal_delta_conclusions G h,
    fun H hH => canonicalLift_rootSubspace_finrank_le_three G h H hH⟩

set_option maxRecDepth 4096 in
theorem graph_det49_and_root_rank_of_poisson (h : G.IsSRGWith 99 14 1 2)
    [Fintype (CanonicalDiscriminant G)] (hP : CanonicalThetaPoisson G h) :
    letI : Module (ZMod 7) (CanonicalDiscriminant G) := canonicalDiscriminant_zmodModule G h
    ∃ H : Submodule (ZMod 7) (CanonicalDiscriminant G),
    ∃ hH : ∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0,
    ∃ c : Module.Basis (Fin 44) ℤ (canonicalLiftInAmbient G (H.restrictScalars ℤ)),
    ∃ A : Matrix (Fin 44) (Fin 44) ℤ,
      (∀ i j, (A i j : ℚ) = codePair ((c i : rationalAmbient G) : V → ℚ)
        ((c j : rationalAmbient G) : V → ℚ)) ∧ A.det = 49 ∧
      Module.finrank ℚ (rootSubspace G (H.restrictScalars ℤ)) ≤ 3 := by
  letI : Module (ZMod 7) (CanonicalDiscriminant G) := canonicalDiscriminant_zmodModule G h
  obtain ⟨H, hH, c, A, _, _, _, _, _, _, _, _, hgram, hdet⟩ :=
    canonicalDet49Lift_of_poisson G h hP
  exact ⟨H, hH, c, A, hgram, hdet,
    canonicalLift_rootSubspace_finrank_le_three G h (H.restrictScalars ℤ) hH⟩

#print axioms graph_delta_and_root_rank
#print axioms graph_det49_and_root_rank_of_poisson

end Conway99
