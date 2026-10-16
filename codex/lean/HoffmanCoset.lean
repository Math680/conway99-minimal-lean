import HoffmanCocliques
import RootHoffman
import LatticeLift
import RootCode

/-! Odd discriminant exponent replaces the tensor-column detour for the
canonical Hoffman coset: 2g and 7g in the lift imply g in the lift. -/

namespace Conway99

open scoped BigOperators Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem integer_common_residue_mem_dual (h : G.IsSRGWith 99 14 1 2)
    {x : V → ℚ} (hx : x ∈ rationalAmbient G) (r : ℤ) (a : V → ℤ)
    (hxa : ∀ u, x u = (r : ℚ) + 3 * (a u : ℚ)) : IsCanonicalDual G x := by
  refine ⟨hx, ?_⟩
  rintro y ⟨c, hc, rfl⟩
  change 3 ∣ ∑ u, c u at hc
  obtain ⟨s, hs⟩ := hc
  have hsum : (∑ u, (c u : ℚ)) = 3 * (s : ℚ) := by exact_mod_cast hs
  refine ⟨r * s + ∑ u, a u * c u, ?_⟩
  rw [codePair_coefficientCode G h hx]
  push_cast
  simp_rw [hxa, add_mul, mul_assoc]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum]
  ring

theorem hoffman_anchor_difference_dual (h : G.IsSRGWith 99 14 1 2)
    {H : Finset V} (hH : G.IsIndepSet (H : Set V)) (hc : H.card = 22) (u₀ : V) :
    IsCanonicalDual G (hoffmanCocliqueCode G H - (1 / 3 : ℚ) • vertexCode G u₀) := by
  have hE := (rationalAmbient G).sub_mem (hoffmanCocliqueCode_mem_ambient G H)
    ((rationalAmbient G).smul_mem (1 / 3 : ℚ) (vertexCode_mem_ambient G u₀))
  let a : V → ℤ := fun u => (if u ∈ H then 1 else 0) -
    3 * (if u = u₀ then 1 else 0) + (if G.Adj u u₀ then 1 else 0)
  apply integer_common_residue_mem_dual G h hE (-1) a
  intro u
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    hoffmanCocliqueCode_apply G h hH hc, cocliqueIndicator, vertexCode,
    vertexGram_apply, a]
  by_cases heq : u = u₀
  · subst u
    by_cases hu : u₀ ∈ H <;> norm_num [hu]
  · by_cases ha : G.Adj u u₀ <;> by_cases hu : u ∈ H <;> norm_num [heq, ha, hu]

theorem canonicalLift_two_saturated_in_dual (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G)) {g : V → ℚ}
    (hg : IsCanonicalDual G g) (h2 : (2 : ℚ) • g ∈ canonicalLift G H) :
    g ∈ canonicalLift G H := by
  have h7 := canonicalLattice_le_lift G h H (canonicalDual_exponent_seven G h hg)
  have h8 := (canonicalLift G H).smul_mem (4 : ℤ) h2
  have hsub := (canonicalLift G H).sub_mem h8 h7
  convert hsub using 1
  ext u
  simp only [Pi.sub_apply, Pi.smul_apply, zsmul_eq_mul, smul_eq_mul]
  norm_num
  ring

def rootSupportCode (b : V → ℤ) : V → ℚ :=
  coefficientCode G (cocliqueCoefficients (rootSupport b))

theorem rootSupportCode_apply (h : G.IsSRGWith 99 14 1 2)
    (b : V → ℤ) (hb : SignedBiplaneCode G b)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u) (u : V) :
    rootSupportCode G b u = -3 * finiteIndicator (rootSupport b) u -
      6 * finiteIndicator (rootShell G b) u + 14 / 3 := by
  have hF : vertexGram G = (27 : ℚ) • (1 : Matrix V V ℚ) -
      (9 : ℚ) • G.adjMatrix ℚ + allOnes := by
    simpa only [ofNat_smul_eq_nsmul] using vertexGram_eq G
  have hAC := signed_biplane_support_adjacency G h b hb he
  have hJ : allOnes *ᵥ finiteIndicator (rootSupport b) = (fun _ => (14 : ℚ)) := by
    ext v
    simp [Matrix.mulVec, dotProduct, allOnes, finiteIndicator_sum,
      signed_biplane_support_card G b hb]
  change coefficientCode G (cocliqueCoefficients (rootSupport b)) u = _
  rw [coefficientCode_coclique]
  change ((1 / 3 : ℚ) • (vertexGram G *ᵥ finiteIndicator (rootSupport b))) u = _
  rw [hF, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, hAC, hJ]
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem canonicalHoffman_half_identity (h : G.IsSRGWith 99 14 1 2)
    (b : V → ℤ) (hb : SignedBiplaneCode G b)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u) :
    (2 : ℚ) • hoffmanCocliqueCode G (rootPositiveHoffman G b) =
      rootSupportCode G b + (3 : ℚ) • (fun u => (b u : ℚ)) ∧
    (2 : ℚ) • hoffmanCocliqueCode G (rootNegativeHoffman G b) =
      rootSupportCode G b - (3 : ℚ) • (fun u => (b u : ℚ)) := by
  obtain ⟨hPc, hPi, hNc, hNi⟩ := signed_biplane_canonical_hoffman G h b hb he
  constructor <;> ext u
  · rw [Pi.smul_apply, smul_eq_mul, hoffmanCocliqueCode_apply G h hPi hPc,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, rootSupportCode_apply G h b hb he]
    rcases hb.signs u with hu | hu | hu
    · norm_num [cocliqueIndicator, finiteIndicator, rootPositiveHoffman, rootSupport,
        positiveCodeSupport, negativeCodeSupport, rootShell, rootIsolated, hu]
    · rcases signed_biplane_zero_degrees G h b hb he u hu with hh | hh <;>
        simp only [cocliqueIndicator, finiteIndicator, rootPositiveHoffman, rootSupport,
          rootShell, rootIsolated, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
          hu, hh.1] <;> norm_num [positiveCodeSupport, negativeCodeSupport, hu]
    · norm_num [cocliqueIndicator, finiteIndicator, rootPositiveHoffman, rootSupport,
        positiveCodeSupport, negativeCodeSupport, rootShell, rootIsolated, hu]
  · rw [Pi.smul_apply, smul_eq_mul, hoffmanCocliqueCode_apply G h hNi hNc,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, rootSupportCode_apply G h b hb he]
    rcases hb.signs u with hu | hu | hu
    · norm_num [cocliqueIndicator, finiteIndicator, rootNegativeHoffman, rootSupport,
        positiveCodeSupport, negativeCodeSupport, rootShell, rootIsolated, hu]
    · rcases signed_biplane_zero_degrees G h b hb he u hu with hh | hh <;>
        simp only [cocliqueIndicator, finiteIndicator, rootNegativeHoffman, rootSupport,
          rootShell, rootIsolated, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
          hu, hh.1] <;> norm_num [positiveCodeSupport, negativeCodeSupport, hu]
    · norm_num [cocliqueIndicator, finiteIndicator, rootNegativeHoffman, rootSupport,
        positiveCodeSupport, negativeCodeSupport, rootShell, rootIsolated, hu]

theorem rootSupportCode_anchor_difference_mem (h : G.IsSRGWith 99 14 1 2)
    (b : V → ℤ) (hb : SignedBiplaneCode G b) (u₀ : V) :
    rootSupportCode G b - (2 : ℚ) • ((1 / 3 : ℚ) • vertexCode G u₀) ∈ canonicalLattice G := by
  have hsingle : coefficientCode G (Pi.single u₀ 1) = (1 / 3 : ℚ) • vertexCode G u₀ := by
    ext u
    simp [coefficientCode, vertexCode, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite]
  let c : V → ℤ := cocliqueCoefficients (rootSupport b) - (2 : ℤ) • Pi.single u₀ 1
  have hc : c ∈ canonicalCoefficients (V := V) := by
    change 3 ∣ ∑ u, c u
    simp only [c, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_pi_single]
    have hs : ∑ u, cocliqueCoefficients (rootSupport b) u = 14 := by
      simp [cocliqueCoefficients, signed_biplane_support_card G b hb]
    rw [hs]
    norm_num
  have hm : coefficientCode G c ∈ canonicalLattice G := ⟨c, hc, rfl⟩
  have hec : coefficientCode G c = rootSupportCode G b -
      (2 : ℚ) • ((1 / 3 : ℚ) • vertexCode G u₀) := by
    dsimp only [c]
    rw [map_sub, map_smul, hsingle]
    rfl
  rwa [hec] at hm

theorem canonicalHoffman_anchor_cosets (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G))
    (b : V → ℤ) (hb : SignedBiplaneCode G b)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u)
    (hr : (3 : ℚ) • (fun u => (b u : ℚ)) ∈ canonicalLift G H) (u₀ : V) :
    hoffmanCocliqueCode G (rootPositiveHoffman G b) -
        (1 / 3 : ℚ) • vertexCode G u₀ ∈ canonicalLift G H ∧
    hoffmanCocliqueCode G (rootNegativeHoffman G b) -
        (1 / 3 : ℚ) • vertexCode G u₀ ∈ canonicalLift G H := by
  obtain ⟨hPc, hPi, hNc, hNi⟩ := signed_biplane_canonical_hoffman G h b hb he
  obtain ⟨hplus, hminus⟩ := canonicalHoffman_half_identity G h b hb he
  have hC := canonicalLattice_le_lift G h H (rootSupportCode_anchor_difference_mem G h b hb u₀)
  constructor
  · apply canonicalLift_two_saturated_in_dual G h H
      (hoffman_anchor_difference_dual G h hPi hPc u₀)
    have hm := (canonicalLift G H).add_mem hC hr
    convert hm using 1
    rw [smul_sub, hplus]
    ext u
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · apply canonicalLift_two_saturated_in_dual G h H
      (hoffman_anchor_difference_dual G h hNi hNc u₀)
    have hm := (canonicalLift G H).sub_mem hC hr
    convert hm using 1
    rw [smul_sub, hminus]
    ext u
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

theorem anchor_pair_root_integral (h : G.IsSRGWith 99 14 1 2)
    {x : V → ℚ} (hx : IsCanonicalDual G x) (hn : codePair x x = 2) (u₀ : V) :
    ∃ a : ℤ, codePair ((1 / 3 : ℚ) • vertexCode G u₀) x = (a : ℚ) := by
  obtain ⟨b, hxb, _, _, _, _⟩ := canonicalDual_root_integral_code G h hx hn
  refine ⟨b u₀, ?_⟩
  rw [codePair_symm, codePair_smul_right, codePair_vertexCode G h hx.1, hxb]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem canonicalHoffman_pair_root_integral (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G))
    (hH : ∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0)
    (b : V → ℤ) (hb : SignedBiplaneCode G b)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u)
    (hr : (3 : ℚ) • (fun u => (b u : ℚ)) ∈ canonicalLift G H)
    {x : V → ℚ} (hx : x ∈ canonicalLift G H) (hn : codePair x x = 2) :
    (∃ a : ℤ, codePair (hoffmanCocliqueCode G (rootPositiveHoffman G b)) x = (a : ℚ)) ∧
    (∃ a : ℤ, codePair (hoffmanCocliqueCode G (rootNegativeHoffman G b)) x = (a : ℚ)) := by
  let u₀ : V := Classical.choice (Fintype.card_pos_iff.mp (by rw [h.card]; norm_num))
  obtain ⟨hp, hm⟩ := canonicalHoffman_anchor_cosets G h H b hb he hr u₀
  obtain ⟨a, ha⟩ := anchor_pair_root_integral G h (canonicalLift_le_dual G H hx) hn u₀
  have combine (y : V → ℚ) (hy : y - (1 / 3 : ℚ) • vertexCode G u₀ ∈ canonicalLift G H) :
      ∃ c : ℤ, codePair y x = (c : ℚ) := by
    obtain ⟨c, hc⟩ := canonicalLift_integral G h H hH hy hx
    refine ⟨c + a, ?_⟩
    have heq := codePair_add_left (y - (1 / 3 : ℚ) • vertexCode G u₀)
      ((1 / 3 : ℚ) • vertexCode G u₀) x
    simp only [sub_add_cancel, hc, ha] at heq
    simpa only [Int.cast_add] using heq
  exact ⟨combine _ hp, combine _ hm⟩

#print axioms hoffman_anchor_difference_dual
#print axioms canonicalLift_two_saturated_in_dual
#print axioms canonicalHoffman_anchor_cosets
#print axioms canonicalHoffman_pair_root_integral

end Conway99
