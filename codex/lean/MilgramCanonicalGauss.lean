import MilgramCanonicalGluing
import MilgramOrthogonalCoordinates
import MilgramDiagonalGauss
import MilgramDiscriminantFourier

/-! Unconditional Milgram sign for the actual canonical discriminant.
The analytic proof is diagonal; exact isotropic gluing transfers it to N. -/
noncomputable section
namespace Conway99
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem canonicalDiscriminant_gauss (h : G.IsSRGWith 99 14 1 2)
    [Fintype (CanonicalDiscriminant G)] :
    (∑ d, canonicalDiscriminantPhase G h d) / canonicalDiscriminantVolume G = -1 := by
  classical
  obtain ⟨e,he,ho,a,ha,hn⟩ := canonicalLattice_orthogonal_integral_basis G h
  let M : Fin 44 → ℕ := fun i => 2 * (a i).natAbs
  letI : ∀ i, NeZero (M i) := fun i =>
    ⟨Nat.mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr (ne_of_gt (ha i)))⟩
  letI : Finite (OrthogonalDiscriminant G e) := orthogonalDiscriminant_finite G h e he
  letI : Fintype (OrthogonalDiscriminant G e) := Fintype.ofFinite _
  let eqv := orthogonalDiscriminantCoordinateEquiv G h e he a ha ho hn
  have hs : (∑ x : OrthogonalDiscriminant G e, orthogonalDiscriminantPhase G h e he x) =
      ∑ x : DiagonalPhase.Discriminant M, DiagonalPhase.phase M x := by
    simp_rw [orthogonalDiscriminantCoordinateEquiv_phase G h e he a ha ho hn]
    exact eqv.toEquiv.sum_comp _
  have hc : Fintype.card (OrthogonalDiscriminant G e) =
      Fintype.card (DiagonalPhase.Discriminant M) := Fintype.card_congr eqv.toEquiv
  change (∑ d, canonicalDiscriminantPhase G h d) /
    (Real.sqrt (Fintype.card (CanonicalDiscriminant G)) : ℂ) = -1
  rw [canonicalDiscriminant_normalized_gauss_eq_orthogonal G h e he, hs, hc]
  exact DiagonalTheta.normalized_gauss_sqrt_card_eq_neg_one M (fun i => even_two_mul _)

theorem canonicalDiscriminant_gauss_sum (h : G.IsSRGWith 99 14 1 2)
    [Fintype (CanonicalDiscriminant G)] :
    (∑ d, canonicalDiscriminantPhase G h d) = -canonicalDiscriminantVolume G := by
  have hh := (div_eq_iff (canonicalDiscriminantVolume_ne_zero G)).mp
    (canonicalDiscriminant_gauss G h)
  simpa only [neg_one_mul] using hh

#print axioms canonicalDiscriminant_gauss
#print axioms canonicalDiscriminant_gauss_sum
end Conway99
