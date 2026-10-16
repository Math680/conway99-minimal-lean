import HoffmanCocliques
import RootPartition
import RootCode
import RootOrthogonality

/-! A Hoffman coclique cannot contain the positive supports and avoid the negative
supports of two orthogonal signed root biplanes. The edge budget is proved explicitly.
-/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def PositiveActiveSupport (H : Finset V) (b : V → ℤ) : Prop :=
  positiveCodeSupport b ⊆ H ∧ ∀ u ∈ negativeCodeSupport b, u ∉ H

theorem active_orthogonal_code_products_zero {H : Finset V} {b c : V → ℤ}
    (hb : SignedBiplaneCode G b) (hc : SignedBiplaneCode G c)
    (hHb : PositiveActiveSupport H b) (hHc : PositiveActiveSupport H c)
    (horth : ∑ u, b u * c u = 0) (u : V) : b u * c u = 0 := by
  have hnonneg (v : V) : 0 ≤ b v * c v := by
    have hbv := hb.signs v
    have hcv := hc.signs v
    have hbc : ¬(b v = 1 ∧ c v = -1) := by
      rintro ⟨h1, h2⟩
      exact hHc.2 v (by simp [negativeCodeSupport, h2])
        (hHb.1 (by simp [positiveCodeSupport, h1]))
    have hcb : ¬(b v = -1 ∧ c v = 1) := by
      rintro ⟨h1, h2⟩
      exact hHb.2 v (by simp [negativeCodeSupport, h1])
        (hHc.1 (by simp [positiveCodeSupport, h2]))
    rcases hbv with hbv | hbv | hbv <;> rcases hcv with hcv | hcv | hcv <;>
      simp_all
  have hle := Finset.single_le_sum (fun v _ => hnonneg v) (Finset.mem_univ u)
  rw [horth] at hle
  exact le_antisymm hle (hnonneg u)

theorem active_orthogonal_supports_disjoint {H : Finset V} {b c : V → ℤ}
    (hb : SignedBiplaneCode G b) (hc : SignedBiplaneCode G c)
    (hHb : PositiveActiveSupport H b) (hHc : PositiveActiveSupport H c)
    (horth : ∑ u, b u * c u = 0) :
    Disjoint (positiveCodeSupport b) (positiveCodeSupport c) ∧
      Disjoint (negativeCodeSupport b) (negativeCodeSupport c) := by
  constructor <;> apply Finset.disjoint_left.mpr <;> intro u hu hv
  · have hp := active_orthogonal_code_products_zero G hb hc hHb hHc horth u
    have hbu := (Finset.mem_filter.mp hu).2
    have hcu := (Finset.mem_filter.mp hv).2
    rw [hbu, hcu] at hp
    norm_num at hp
  · have hp := active_orthogonal_code_products_zero G hb hc hHb hHc horth u
    have hbu := (Finset.mem_filter.mp hu).2
    have hcu := (Finset.mem_filter.mp hv).2
    rw [hbu, hcu] at hp
    norm_num at hp

theorem active_negative_hoffman_neighbors (h : G.IsSRGWith 99 14 1 2)
    {H : Finset V} (hH : G.IsIndepSet (H : Set V)) (hcard : H.card = 22)
    {b : V → ℤ} (hb : SignedBiplaneCode G b) (ha : PositiveActiveSupport H b)
    (v : V) (hv : v ∈ negativeCodeSupport b) :
    H.filter (G.Adj v) = (positiveCodeSupport b).filter (G.Adj v) := by
  have hsub : (positiveCodeSupport b).filter (G.Adj v) ⊆ H.filter (G.Adj v) :=
    Finset.filter_subset_filter _ ha.1
  have hleft := hb.negative_cross v hv
  have hright := hoffman_coclique_neighbor_count G h hH hcard (ha.2 v hv)
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

theorem hoffman_two_positive_active_impossible (h : G.IsSRGWith 99 14 1 2)
    {H : Finset V} (hH : G.IsIndepSet (H : Set V)) (hcard : H.card = 22)
    {b c : V → ℤ} (hb : SignedBiplaneCode G b) (hc : SignedBiplaneCode G c)
    (hHb : PositiveActiveSupport H b) (hHc : PositiveActiveSupport H c)
    (horth : ∑ u, b u * c u = 0) : False := by
  classical
  let P := positiveCodeSupport b
  let Q := positiveCodeSupport c
  let N := negativeCodeSupport b
  let M := negativeCodeSupport c
  let D := H \ (P ∪ Q)
  let Z := Finset.univ \ (H ∪ N ∪ M)
  have hpq : Disjoint P Q := (active_orthogonal_supports_disjoint G hb hc hHb hHc horth).1
  have hnm : Disjoint N M := (active_orthogonal_supports_disjoint G hb hc hHb hHc horth).2
  have hhn : Disjoint H N := Finset.disjoint_left.mpr (by
    intro u hu hn
    exact hHb.2 u hn hu)
  have hhm : Disjoint H M := Finset.disjoint_left.mpr (by
    intro u hu hm
    exact hHc.2 u hm hu)
  have hpqu : P ∪ Q ⊆ H := Finset.union_subset hHb.1 hHc.1
  have hD : D.card = 8 := by
    rw [Finset.card_sdiff_of_subset hpqu, Finset.card_union_of_disjoint hpq,
      hcard, hb.positive_card, hc.positive_card]
  have hhnm : Disjoint (H ∪ N) M := Finset.disjoint_union_left.mpr ⟨hhm, hnm⟩
  have hZ : Z.card = 63 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, h.card,
      Finset.card_union_of_disjoint hhnm, Finset.card_union_of_disjoint hhn,
      hcard, hb.negative_card, hc.negative_card]
  have hDneighbor (u : V) (hu : u ∈ D) (v : V) (huv : G.Adj u v) : v ∈ Z := by
    have huH := (Finset.mem_sdiff.mp hu).1
    have huPQ := (Finset.mem_sdiff.mp hu).2
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_union.mp hv with hvH | hvN
      · have hne : u ≠ v := fun he => G.loopless u (he ▸ huv)
        exact (G.isIndepSet_iff.mp hH) huH hvH hne huv
      · have he := active_negative_hoffman_neighbors G h hH hcard hb hHb v hvN
        have hum : u ∈ H.filter (G.Adj v) := Finset.mem_filter.mpr ⟨huH, huv.symm⟩
        rw [he] at hum
        exact huPQ (Finset.mem_union_left _ (Finset.mem_filter.mp hum).1)
    · have he := active_negative_hoffman_neighbors G h hH hcard hc hHc v hv
      have hum : u ∈ H.filter (G.Adj v) := Finset.mem_filter.mpr ⟨huH, huv.symm⟩
      rw [he] at hum
      exact huPQ (Finset.mem_union_right _ (Finset.mem_filter.mp hum).1)
  have hDdeg (u : V) (hu : u ∈ D) : (Z.filter (G.Adj u)).card = 14 := by
    have heq : Z.filter (G.Adj u) = Finset.univ.filter (G.Adj u) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨And.right, fun hv => ⟨hDneighbor u hu v hv, hv⟩⟩
    rw [heq]
    simpa [SimpleGraph.degree, SimpleGraph.neighborFinset_def] using h.regular.degree_eq u
  have hZdeg (v : V) (hv : v ∈ Z) : 2 ≤ (D.filter (G.Adj v)).card := by
    have hvall := (Finset.mem_sdiff.mp hv).2
    have hvH : v ∉ H := fun ht => hvall (Finset.mem_union_left _ (Finset.mem_union_left _ ht))
    have hvN : v ∉ N := fun ht => hvall (Finset.mem_union_left _ (Finset.mem_union_right _ ht))
    have hvM : v ∉ M := fun ht => hvall (Finset.mem_union_right _ ht)
    have hnb := biplane_external_degree_le_one G h P N hb.positive_pairs v hvN
    have hnc := biplane_external_degree_le_one G h Q M hc.positive_pairs v hvM
    have hnh := hoffman_coclique_neighbor_count G h hH hcard hvH
    have hsub : H.filter (G.Adj v) ⊆
        ((P.filter (G.Adj v)) ∪ (Q.filter (G.Adj v))) ∪ (D.filter (G.Adj v)) := by
      intro u hu
      have huH := (Finset.mem_filter.mp hu).1
      have huv := (Finset.mem_filter.mp hu).2
      by_cases hup : u ∈ P
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hup, huv⟩))
      by_cases huq : u ∈ Q
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨huq, huv⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_sdiff.mpr ⟨huH, by simp only [Finset.mem_union]; tauto⟩, huv⟩)
    have hbound := Finset.card_le_card hsub
    have hb1 := Finset.card_union_le (P.filter (G.Adj v)) (Q.filter (G.Adj v))
    have hb2 := Finset.card_union_le ((P.filter (G.Adj v)) ∪ (Q.filter (G.Adj v)))
      (D.filter (G.Adj v))
    omega
  have hdouble : (∑ u ∈ D, (Z.filter (G.Adj u)).card) =
      ∑ v ∈ Z, (D.filter (G.Adj v)).card := by
    simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow, SimpleGraph.adj_comm] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj (s := D) (t := Z))
  have hlow : (∑ _v ∈ Z, 2) ≤ ∑ v ∈ Z, (D.filter (G.Adj v)).card :=
    Finset.sum_le_sum hZdeg
  rw [← hdouble, Finset.sum_congr rfl hDdeg] at hlow
  simp only [Finset.sum_const, nsmul_eq_mul, hD, hZ] at hlow
  omega

theorem sign_code_sum_on (b : V → ℤ) (hs : ∀ u, b u = -1 ∨ b u = 0 ∨ b u = 1)
    (H : Finset V) :
    (∑ u ∈ H, b u) = ((H ∩ positiveCodeSupport b).card : ℤ) -
      ((H ∩ negativeCodeSupport b).card : ℤ) := by
  have hv (u : V) : b u = (if b u = 1 then 1 else 0) - (if b u = -1 then 1 else 0) := by
    rcases hs u with h | h | h <;> simp [h]
  rw [Finset.sum_congr rfl (fun u _ => hv u), Finset.sum_sub_distrib]
  simp [positiveCodeSupport, negativeCodeSupport, Finset.inter_filter]

theorem hoffmanCocliqueCode_pair_signed_root (h : G.IsSRGWith 99 14 1 2)
    (H : Finset V) {x : V → ℚ} (hx : x ∈ rationalAmbient G)
    (b : V → ℤ) (hxb : x = (3 : ℚ) • (fun u => (b u : ℚ))) :
    codePair (hoffmanCocliqueCode G H) x = ((∑ u ∈ H, b u : ℤ) : ℚ) / 7 := by
  rw [hoffmanCocliqueCode, codePair_smul_left, codePair_symm,
    codePair_coefficientCode G h hx, hxb]
  simp only [Pi.smul_apply, smul_eq_mul, cocliqueCoefficients, Int.cast_ite,
    Int.cast_one, Int.cast_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite, Finset.sum_const_zero, add_zero]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.mul_sum, Int.cast_sum]
  ring

theorem hoffman_signed_root_pair_one_active (h : G.IsSRGWith 99 14 1 2)
    (H : Finset V) {x : V → ℚ} (hx : x ∈ rationalAmbient G)
    {b : V → ℤ} (hb : SignedBiplaneCode G b)
    (hxb : x = (3 : ℚ) • (fun u => (b u : ℚ)))
    (hpair : codePair (hoffmanCocliqueCode G H) x = 1) : PositiveActiveSupport H b := by
  rw [hoffmanCocliqueCode_pair_signed_root G h H hx b hxb] at hpair
  have hsum : (∑ u ∈ H, b u) = (7 : ℤ) := by
    exact_mod_cast (show ((∑ u ∈ H, b u : ℤ) : ℚ) = 7 by linarith)
  rw [sign_code_sum_on b hb.signs H] at hsum
  have hposle := Finset.card_le_card (Finset.inter_subset_right (s₁ := H) (s₂ := positiveCodeSupport b))
  rw [hb.positive_card] at hposle
  have hpos : (H ∩ positiveCodeSupport b).card = 7 := by omega
  have hneg : (H ∩ negativeCodeSupport b).card = 0 := by omega
  have heq : H ∩ positiveCodeSupport b = positiveCodeSupport b :=
    Finset.eq_of_subset_of_card_le (Finset.inter_subset_right) (by rw [hpos, hb.positive_card])
  constructor
  · intro u hu
    have ht : u ∈ H ∩ positiveCodeSupport b := by rw [heq]; exact hu
    exact (Finset.mem_inter.mp ht).1
  · intro u hu hn
    have ht : u ∈ H ∩ negativeCodeSupport b := Finset.mem_inter.mpr ⟨hn, hu⟩
    rw [Finset.card_eq_zero.mp hneg] at ht
    exact Finset.notMem_empty _ ht

theorem scaled_integer_codes_pair (b c : V → ℤ) :
    codePair ((3 : ℚ) • (fun u => (b u : ℚ))) ((3 : ℚ) • (fun u => (c u : ℚ))) =
      ((∑ u, b u * c u : ℤ) : ℚ) / 7 := by
  unfold codePair dotProduct
  simp only [Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul]
  have hs : (∑ u, (3 * (b u : ℚ)) * (3 * (c u : ℚ))) =
      9 * ∑ u, (b u : ℚ) * (c u : ℚ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [hs]
  ring

theorem hoffman_two_orthogonal_positive_roots_impossible (h : G.IsSRGWith 99 14 1 2)
    {H : Finset V} (hH : G.IsIndepSet (H : Set V)) (hcard : H.card = 22)
    {x y : V → ℚ} (hx : IsCanonicalDual G x) (hy : IsCanonicalDual G y)
    (hnx : codePair x x = 2) (hny : codePair y y = 2) (horth : codePair x y = 0)
    (hpx : codePair (hoffmanCocliqueCode G H) x = 1)
    (hpy : codePair (hoffmanCocliqueCode G H) y = 1) : False := by
  obtain ⟨b, hxb, _, _, _, hb⟩ := canonicalDual_root_biplane G h hx hnx
  obtain ⟨c, hyc, _, _, _, hc⟩ := canonicalDual_root_biplane G h hy hny
  have hHb := hoffman_signed_root_pair_one_active G h H hx.1 hb hxb hpx
  have hHc := hoffman_signed_root_pair_one_active G h H hy.1 hc hyc hpy
  rw [hxb, hyc, scaled_integer_codes_pair] at horth
  have hbc : ∑ u, b u * c u = 0 := by
    exact_mod_cast (show ((∑ u, b u * c u : ℤ) : ℚ) = 0 by linarith)
  exact hoffman_two_positive_active_impossible G h hH hcard hb hc hHb hHc hbc

theorem hoffmanCocliqueCode_root_pair_bounds (h : G.IsSRGWith 99 14 1 2)
    (H : Finset V) {x : V → ℚ} (hx : IsCanonicalDual G x) (hn : codePair x x = 2) :
    (-1 : ℚ) ≤ codePair (hoffmanCocliqueCode G H) x ∧
      codePair (hoffmanCocliqueCode G H) x ≤ 1 := by
  obtain ⟨b, hxb, _, _, _, hb⟩ := canonicalDual_root_biplane G h hx hn
  rw [hoffmanCocliqueCode_pair_signed_root G h H hx.1 b hxb, sign_code_sum_on b hb.signs H]
  have hp := Finset.card_le_card (Finset.inter_subset_right (s₁ := H) (s₂ := positiveCodeSupport b))
  have hm := Finset.card_le_card (Finset.inter_subset_right (s₁ := H) (s₂ := negativeCodeSupport b))
  rw [hb.positive_card] at hp
  rw [hb.negative_card] at hm
  have hpQ : ((H ∩ positiveCodeSupport b).card : ℚ) ≤ 7 := by exact_mod_cast hp
  have hmQ : ((H ∩ negativeCodeSupport b).card : ℚ) ≤ 7 := by exact_mod_cast hm
  have hp0 : (0 : ℚ) ≤ (H ∩ positiveCodeSupport b).card := Nat.cast_nonneg _
  have hm0 : (0 : ℚ) ≤ (H ∩ negativeCodeSupport b).card := Nat.cast_nonneg _
  push_cast
  constructor <;> linarith

theorem hoffmanCocliqueCode_root_pair_integer_values (h : G.IsSRGWith 99 14 1 2)
    (H : Finset V) {x : V → ℚ} (hx : IsCanonicalDual G x) (hn : codePair x x = 2)
    (hint : ∃ a : ℤ, codePair (hoffmanCocliqueCode G H) x = (a : ℚ)) :
    codePair (hoffmanCocliqueCode G H) x = -1 ∨
      codePair (hoffmanCocliqueCode G H) x = 0 ∨
      codePair (hoffmanCocliqueCode G H) x = 1 := by
  obtain ⟨a, ha⟩ := hint
  obtain ⟨hlo, hhi⟩ := hoffmanCocliqueCode_root_pair_bounds G h H hx hn
  rw [ha] at hlo hhi ⊢
  have hloZ : (-1 : ℤ) ≤ a := by exact_mod_cast hlo
  have hhiZ : a ≤ (1 : ℤ) := by exact_mod_cast hhi
  have hv : a = -1 ∨ a = 0 ∨ a = 1 := by omega
  rcases hv with rfl | rfl | rfl <;> norm_num

theorem hoffman_two_orthogonal_unit_active_roots_impossible (h : G.IsSRGWith 99 14 1 2)
    {H : Finset V} (hH : G.IsIndepSet (H : Set V)) (hcard : H.card = 22)
    {x y : V → ℚ} (hx : IsCanonicalDual G x) (hy : IsCanonicalDual G y)
    (hnx : codePair x x = 2) (hny : codePair y y = 2) (horth : codePair x y = 0)
    (hpx : codePair (hoffmanCocliqueCode G H) x = -1 ∨
      codePair (hoffmanCocliqueCode G H) x = 1)
    (hpy : codePair (hoffmanCocliqueCode G H) y = -1 ∨
      codePair (hoffmanCocliqueCode G H) y = 1) : False := by
  have orient {z : V → ℚ} (hz : IsCanonicalDual G z) (hnz : codePair z z = 2)
      (hpz : codePair (hoffmanCocliqueCode G H) z = -1 ∨
        codePair (hoffmanCocliqueCode G H) z = 1) :
      ∃ w : V → ℚ, IsCanonicalDual G w ∧ codePair w w = 2 ∧
        codePair (hoffmanCocliqueCode G H) w = 1 ∧ (w = z ∨ w = -z) := by
    rcases hpz with hpz | hpz
    · exact ⟨-z, (canonicalDual G).neg_mem hz, by rwa [codePair_neg_norm],
        by rw [codePair_neg_right, hpz]; norm_num, Or.inr rfl⟩
    · exact ⟨z, hz, hnz, hpz, Or.inl rfl⟩
  obtain ⟨x', hx', hnx', hpx', hex⟩ := orient hx hnx hpx
  obtain ⟨y', hy', hny', hpy', hey⟩ := orient hy hny hpy
  have ho : codePair x' y' = 0 := by
    rcases hex with rfl | rfl <;> rcases hey with rfl | rfl <;>
      simp only [codePair_neg_left, codePair_neg_right, horth, neg_zero]
  exact hoffman_two_orthogonal_positive_roots_impossible G h hH hcard hx' hy' hnx' hny' ho hpx' hpy'

theorem hoffman_two_orthogonal_integral_active_roots_impossible (h : G.IsSRGWith 99 14 1 2)
    {H : Finset V} (hH : G.IsIndepSet (H : Set V)) (hcard : H.card = 22)
    {x y : V → ℚ} (hx : IsCanonicalDual G x) (hy : IsCanonicalDual G y)
    (hnx : codePair x x = 2) (hny : codePair y y = 2) (horth : codePair x y = 0)
    (hix : ∃ a : ℤ, codePair (hoffmanCocliqueCode G H) x = (a : ℚ))
    (hiy : ∃ a : ℤ, codePair (hoffmanCocliqueCode G H) y = (a : ℚ))
    (hpx : codePair (hoffmanCocliqueCode G H) x ≠ 0)
    (hpy : codePair (hoffmanCocliqueCode G H) y ≠ 0) : False := by
  have hvx := hoffmanCocliqueCode_root_pair_integer_values G h H hx hnx hix
  have hvy := hoffmanCocliqueCode_root_pair_integer_values G h H hy hny hiy
  exact hoffman_two_orthogonal_unit_active_roots_impossible G h hH hcard hx hy hnx hny horth
    (by tauto) (by tauto)

#print axioms hoffman_two_positive_active_impossible
#print axioms hoffman_two_orthogonal_positive_roots_impossible
#print axioms hoffman_two_orthogonal_integral_active_roots_impossible

end Conway99
