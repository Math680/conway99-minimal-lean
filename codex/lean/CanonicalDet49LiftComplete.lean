import MilgramCanonicalGauss
import CanonicalDet49Lift
import MinimalConclusions

/-! Unconditional closure of the determinant-49 and root-rank conclusions.
No Poisson, Gauss-sum sign, or configuration exclusion is an input. -/
noncomputable section
namespace Conway99
open Module
open TriangleSecondMoments
open scoped BigOperators
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

set_option maxRecDepth 4096 in
theorem canonicalDet49Lift (h : G.IsSRGWith 99 14 1 2)
    [Fintype (CanonicalDiscriminant G)] :
    letI : Module (ZMod 7) (CanonicalDiscriminant G) := canonicalDiscriminant_zmodModule G h
    ∃ H : Submodule (ZMod 7) (CanonicalDiscriminant G),
    ∃ hH : ∀ x ∈ H, canonicalDiscriminantQuadratic G h x = 0,
    ∃ c : Basis (Fin 44) ℤ (canonicalLiftInAmbient G (H.restrictScalars ℤ)),
    ∃ A : Matrix (Fin 44) (Fin 44) ℤ,
      Module.finrank (ZMod 7) (CanonicalDiscriminant G) =
        2 * Module.finrank (ZMod 7) H + 2 ∧
      canonicalLattice G ≤ canonicalLift G (H.restrictScalars ℤ) ∧
      canonicalLift G (H.restrictScalars ℤ) ≤ canonicalDual G ∧
      (canonicalLift G (H.restrictScalars ℤ)).FG ∧
      Module.finrank ℤ (canonicalLift G (H.restrictScalars ℤ)) = 44 ∧
      (∀ x ∈ canonicalLift G (H.restrictScalars ℤ),
        ∀ y ∈ canonicalLift G (H.restrictScalars ℤ),
          ∃ a : ℤ, codePair x y = (a : ℚ)) ∧
      (∀ x ∈ canonicalLift G (H.restrictScalars ℤ),
          ∃ a : ℤ, codePair x x = (2*a : ℤ)) ∧
      (∀ x ∈ canonicalLift G (H.restrictScalars ℤ), x ≠ 0 → 0 < codePair x x) ∧
      (∀ i j, (A i j : ℚ) = codePair ((c i : rationalAmbient G) : V → ℚ)
        ((c j : rationalAmbient G) : V → ℚ)) ∧ A.det = 49 := by
  letI : Module (ZMod 7) (CanonicalDiscriminant G) := canonicalDiscriminant_zmodModule G h
  letI : Module.Finite (ZMod 7) (CanonicalDiscriminant G) := Module.Finite.of_finite
  obtain ⟨H,hH,he⟩ := canonicalDiscriminant_codim_two_of_gauss G h
    (canonicalDiscriminant_gauss_sum G h)
  let J := H.restrictScalars ℤ
  letI : Module.Finite (ZMod 7) H := Module.Finite.of_finite
  letI : Submodule.IsLattice ℚ (canonicalInAmbient G) := canonicalInAmbient_isLattice G
  letI : Submodule.IsLattice ℚ (canonicalLiftInAmbient G J) := canonicalLiftInAmbient_isLattice G h J
  have hbRank : Module.finrank ℤ (canonicalInAmbient G) = 44 := by
    apply Module.finrank_eq_of_rank_eq
    rw [Submodule.IsLattice.rank' ℚ, ← Module.finrank_eq_rank, rationalAmbient_finrank G h]
  have hcRank : Module.finrank ℤ (canonicalLiftInAmbient G J) = 44 := by
    apply Module.finrank_eq_of_rank_eq
    rw [Submodule.IsLattice.rank' ℚ, ← Module.finrank_eq_rank, rationalAmbient_finrank G h]
  let b : Basis (Fin 44) ℤ (canonicalInAmbient G) := Module.finBasisOfFinrankEq ℤ _ hbRank
  let c : Basis (Fin 44) ℤ (canonicalLiftInAmbient G J) := Module.finBasisOfFinrankEq ℤ _ hcRank
  have hD : Nat.card (CanonicalDiscriminant G) =
      7 ^ Module.finrank (ZMod 7) (CanonicalDiscriminant G) := by
    simpa using Module.natCard_eq_pow_finrank (K := ZMod 7) (V := CanonicalDiscriminant G)
  have hJ : Nat.card J = 7 ^ Module.finrank (ZMod 7) H := by
    change Nat.card H = 7 ^ Module.finrank (ZMod 7) H
    simpa using Module.natCard_eq_pow_finrank (K := ZMod 7) (V := H)
  have hdet := canonicalLiftIntegralGram_det_eq49 G h J hH b c
    (Module.finrank (ZMod 7) (CanonicalDiscriminant G)) (Module.finrank (ZMod 7) H) hD hJ he
  refine ⟨H,hH,c,canonicalLiftIntegralGram G h J hH c,he,canonicalLattice_le_lift G h J,
    canonicalLift_le_dual G J,canonicalLift_fg G h J,canonicalLift_finrank G h J,?_,?_,?_,?_,?_⟩
  · exact fun x hx y hy => canonicalLift_integral G h J hH hx hy
  · exact fun x hx => canonicalLift_even G h J hH hx
  · exact fun x _ hx => codePair_pos x hx
  · exact canonicalLiftIntegralGram_spec G h J hH c
  · exact hdet

set_option maxRecDepth 4096 in
theorem graph_minimal_conclusions (h : G.IsSRGWith 99 14 1 2) :
    (3 ∣ triangleDelta G ∧ 165 ≤ triangleDelta G ∧
      858 ≤ crossingPairCount G 2 ∧ crossingPairCount G 3 ≤ 1100) ∧
    ∃ H : Submodule ℤ (CanonicalDiscriminant G),
    ∃ hH : ∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0,
    ∃ c : Basis (Fin 44) ℤ (canonicalLiftInAmbient G H),
    ∃ A : Matrix (Fin 44) (Fin 44) ℤ,
      (∀ i j, (A i j : ℚ) = codePair ((c i : rationalAmbient G) : V → ℚ)
        ((c j : rationalAmbient G) : V → ℚ)) ∧ A.det = 49 ∧
      Module.finrank ℚ (rootSubspace G H) ≤ 3 := by
  classical
  letI : Finite (CanonicalDiscriminant G) := canonicalDiscriminant_finite G h
  letI : Fintype (CanonicalDiscriminant G) := Fintype.ofFinite _
  letI : Module (ZMod 7) (CanonicalDiscriminant G) := canonicalDiscriminant_zmodModule G h
  obtain ⟨H,hH,c,A,_,_,_,_,_,_,_,_,hgram,hdet⟩ := canonicalDet49Lift G h
  exact ⟨graph_minimal_delta_conclusions G h, H.restrictScalars ℤ, hH, c,A,hgram,hdet,
    canonicalLift_rootSubspace_finrank_le_three G h (H.restrictScalars ℤ) hH⟩

set_option maxRecDepth 4096 in
theorem graph_minimal_article_theorem (h : G.IsSRGWith 99 14 1 2) :
    crossingPairCount G 2 + 3 * crossingPairCount G 3 = 4158 ∧
    triangleDelta G = 3465 - 3 * (crossingPairCount G 3 : ℤ) ∧
    (3 ∣ triangleDelta G ∧ 165 ≤ triangleDelta G ∧
      858 ≤ crossingPairCount G 2 ∧ crossingPairCount G 3 ≤ 1100) ∧
    ∃ H : Submodule ℤ (CanonicalDiscriminant G),
    ∃ hH : ∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0,
    ∃ c : Basis (Fin 44) ℤ (canonicalLiftInAmbient G H),
    ∃ A : Matrix (Fin 44) (Fin 44) ℤ,
      triangleLattice G ≤ canonicalLift G H ∧
      (canonicalLift G H).FG ∧ Module.finrank ℤ (canonicalLift G H) = 44 ∧
      (∀ x ∈ canonicalLift G H, ∀ y ∈ canonicalLift G H, ∃ n : ℤ, codePair x y = (n : ℚ)) ∧
      (∀ x ∈ canonicalLift G H, ∃ n : ℤ, codePair x x = (2*n : ℤ)) ∧
      (∀ x ∈ canonicalLift G H, x ≠ 0 → 0 < codePair x x) ∧
      (∀ i j, (A i j : ℚ) = codePair ((c i : rationalAmbient G) : V → ℚ)
        ((c j : rationalAmbient G) : V → ℚ)) ∧ A.det = 49 ∧
      (∀ x : V → ℚ, IsCanonicalLiftDual G H x → x ≠ 0 → 2 ≤ codePair x x) ∧
      (∀ x ∈ canonicalLift G H, ∀ y ∈ canonicalLift G H,
        codePair x x = 2 → codePair y y = 2 → x ≠ y → x ≠ -y → codePair x y = 0) ∧
      Module.finrank ℚ (rootSubspace G H) ≤ 3 := by
  classical
  letI : Finite (CanonicalDiscriminant G) := canonicalDiscriminant_finite G h
  letI : Fintype (CanonicalDiscriminant G) := Fintype.ofFinite _
  letI : Module (ZMod 7) (CanonicalDiscriminant G) := canonicalDiscriminant_zmodModule G h
  obtain ⟨H,hH,c,A,_,hinc,_,hfg,hrank,hint,heven,hpos,hgram,hdet⟩ := canonicalDet49Lift G h
  refine ⟨crossing_pair_second_factorial G h,triangleDelta_eq_third_count G h,
    graph_minimal_delta_conclusions G h,H.restrictScalars ℤ,hH,c,A,
    (triangleLattice_le_canonical G).trans hinc,hfg,hrank,hint,heven,hpos,hgram,hdet,?_,?_,?_⟩
  · exact fun x hx hx0 => canonicalLiftDual_minimum_two G h _ hx hx0
  · exact fun x hx y hy hnx hny hne hnopp =>
      canonicalLift_distinct_root_directions_orthogonal G h _ hH hx hy hnx hny hne hnopp
  · exact canonicalLift_rootSubspace_finrank_le_three G h _ hH

#print axioms canonicalDet49Lift
#check graph_minimal_conclusions
#print axioms graph_minimal_conclusions
#print axioms graph_minimal_article_theorem
end Conway99
