import HoffmanCoset
import HoffmanSingleActive
import RootCentersBound
import RootOrthogonality

/-! The first uniform root-rank bound, for actual roots of any isotropic lift. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem canonicalHoffman_own_root_pair (h : G.IsSRGWith 99 14 1 2)
    (b : V → ℤ) (hb : SignedBiplaneCode G b)
    (hE : (fun u => (b u : ℚ)) ∈ rationalAmbient G) (s : Bool) :
    codePair (hoffmanCocliqueCode G (rootSignedHoffman G b s))
      ((3 : ℚ) • (fun u => (b u : ℚ))) = if s then 1 else -1 := by
  have hp : rootPositiveHoffman G b ∩ positiveCodeSupport b = positiveCodeSupport b := by
    apply Finset.inter_eq_right.mpr
    exact Finset.subset_union_left
  have hn : rootNegativeHoffman G b ∩ negativeCodeSupport b = negativeCodeSupport b := by
    apply Finset.inter_eq_right.mpr
    exact Finset.subset_union_left
  have hp0 : rootPositiveHoffman G b ∩ negativeCodeSupport b = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    obtain ⟨huH, huN⟩ := Finset.mem_inter.mp hu
    have hv := (Finset.mem_filter.mp huN).2
    change u ∈ positiveCodeSupport b ∪ rootIsolated G b at huH
    rcases Finset.mem_union.mp huH with huP | huI
    · have hh := (Finset.mem_filter.mp huP).2
      omega
    · have hh := (Finset.mem_filter.mp huI).2.1
      omega
  have hn0 : rootNegativeHoffman G b ∩ positiveCodeSupport b = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    obtain ⟨huH, huP⟩ := Finset.mem_inter.mp hu
    have hv := (Finset.mem_filter.mp huP).2
    change u ∈ negativeCodeSupport b ∪ rootIsolated G b at huH
    rcases Finset.mem_union.mp huH with huN | huI
    · have hh := (Finset.mem_filter.mp huN).2
      omega
    · have hh := (Finset.mem_filter.mp huI).2.1
      omega
  cases s
  · change codePair (hoffmanCocliqueCode G (rootNegativeHoffman G b)) _ = -1
    rw [hoffmanCocliqueCode_signed_root_pair G h b hE hb.signs, hn0, hn,
      Finset.card_empty, hb.negative_card]
    norm_num
  · change codePair (hoffmanCocliqueCode G (rootPositiveHoffman G b)) _ = 1
    rw [hoffmanCocliqueCode_signed_root_pair G h b hE hb.signs, hp0, hp,
      Finset.card_empty, hb.positive_card]
    norm_num

theorem canonicalHoffman_cross_orthogonal (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G))
    (hH : ∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0)
    (b : V → ℤ) (hb : SignedBiplaneCode G b)
    (hE : (fun u => (b u : ℚ)) ∈ rationalAmbient G)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u)
    (hr : (3 : ℚ) • (fun u => (b u : ℚ)) ∈ canonicalLift G H)
    (hnr : codePair ((3 : ℚ) • (fun u => (b u : ℚ)))
      ((3 : ℚ) • (fun u => (b u : ℚ))) = 2)
    {x : V → ℚ} (hx : x ∈ canonicalLift G H) (hnx : codePair x x = 2)
    (ho : codePair ((3 : ℚ) • (fun u => (b u : ℚ))) x = 0) (s : Bool) :
    codePair (hoffmanCocliqueCode G (rootSignedHoffman G b s)) x = 0 := by
  obtain ⟨hc, hI⟩ := rootSignedHoffman_specs G h b hb he s
  have hints (y : V → ℚ) (hy : y ∈ canonicalLift G H) (hny : codePair y y = 2) :
      ∃ a : ℤ, codePair (hoffmanCocliqueCode G (rootSignedHoffman G b s)) y = (a : ℚ) := by
    obtain ⟨hp, hn⟩ := canonicalHoffman_pair_root_integral G h H hH b hb he hr hy hny
    cases s <;> assumption
  by_contra hnot
  apply hoffman_two_orthogonal_integral_active_roots_impossible G h hI hc
    (canonicalLift_le_dual G H hr) (canonicalLift_le_dual G H hx) hnr hnx ho
    (hints _ hr hnr) (hints _ hx hnx) _ hnot
  rw [canonicalHoffman_own_root_pair G h b hb hE]
  cases s <;> norm_num

theorem canonicalLift_root_family_card_le_four (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G))
    (hH : ∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → V → ℚ)
    (hr : ∀ i, r i ∈ canonicalLift G H) (hn : ∀ i, codePair (r i) (r i) = 2)
    (hne : ∀ i j, i ≠ j → r i ≠ r j)
    (hnopp : ∀ i j, i ≠ j → r i ≠ -r j) : Fintype.card ι ≤ 4 := by
  have hcodes (i : ι) : ∃ b : V → ℤ,
      r i = (3 : ℚ) • (fun u => (b u : ℚ)) ∧
      (fun u => (b u : ℚ)) ∈ rationalAmbient G ∧ SignedBiplaneCode G b := by
    obtain ⟨b, heq, hE, _, _, hb⟩ := canonicalLift_root_biplane G h H (hr i) (hn i)
    exact ⟨b, heq, hE, hb⟩
  choose b heq hE hb using hcodes
  have he := fun i => integerAmbient_eigen G h (b i) (hE i)
  apply root_centers_card_le_four G h b hb hE he
  intro i j hij s
  have hri : (3 : ℚ) • (fun u => (b i u : ℚ)) ∈ canonicalLift G H := by rw [← heq]; exact hr i
  have hrj : (3 : ℚ) • (fun u => (b j u : ℚ)) ∈ canonicalLift G H := by rw [← heq]; exact hr j
  apply canonicalHoffman_cross_orthogonal G h H hH (b i) (hb i) (hE i) (he i) hri
  · rw [← heq]; exact hn i
  · exact hrj
  · rw [← heq]; exact hn j
  · rw [← heq, ← heq]
    exact canonicalLift_distinct_root_directions_orthogonal G h H hH (hr i) (hr j)
      (hn i) (hn j) (hne i j hij) (hnopp i j hij)

#print axioms canonicalHoffman_cross_orthogonal
#print axioms canonicalLift_root_family_card_le_four

end Conway99
