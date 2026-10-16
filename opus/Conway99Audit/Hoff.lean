import Conway99Audit.Part

/-!
# Part B, step 5: Hoffman pairs and the first root ceiling `ρ ≤ 4` (§§6.2–6.4)

All statements are about *root vectors*: `IsM4 G b ∧ Biplane G b`, pairwise orthogonal.
-/

open Finset SimpleGraph Matrix

namespace Conway99

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `b · x = Σ_P x - Σ_N x` for a biplane `b`. -/
lemma dot_biplane {b : V → ℤ} (hb : Biplane G b) (x : V → ℤ) :
    b ⬝ᵥ x = ∑ u ∈ pos b, x u - ∑ u ∈ neg b, x u := by
  have : ∀ u, b u * x u = (if u ∈ pos b then x u else 0) - (if u ∈ neg b then x u else 0) := by
    intro u; rcases hb.vals u with h | h | h <;> simp [mem_pos, mem_neg, h]
  simp only [dotProduct]
  rw [Finset.sum_congr rfl (fun u _ => this u), Finset.sum_sub_distrib, Finset.sum_ite_mem,
    Finset.sum_ite_mem, univ_inter, univ_inter]

lemma sum_over_set {b : V → ℤ} (hb : Biplane G b) (S : Finset V) :
    ∑ u ∈ S, b u = ((S ∩ pos b).card : ℤ) - (S ∩ neg b).card := sum_over hb.vals S

section SRG

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

/-- Integrality of `h⁺_r · s` (29), using orthogonality: `Σ_{H⁺_r} b_s = 7 Σ_{P_r} b_s`. -/
lemma sum_Hp {r s : V → ℤ} (hrM : IsM4 G r) (hr : Biplane G r) (hsM : IsM4 G s)
    (horth : r ⬝ᵥ s = 0) : ∑ u ∈ Hp G r, s u = 7 * ∑ u ∈ pos r, s u := by
  have hd : Disjoint (pos r) (Iset G r) :=
    Finset.disjoint_of_subset_left (pos_sub_C r) (I_disj_C (G := G) r).symm
  rw [Hp, Finset.sum_union hd, sum_I_eq hG hrM hr hsM, Cset,
    Finset.sum_union (pos_neg_disj r)]
  rw [dot_biplane hr] at horth
  linarith

/-- §6.3: a Hoffman coclique cannot be active on two orthogonal directions. -/
lemma two_active {H : Finset V} (hH : H.card = 22) (hcocl : ∀ u ∈ H, ∀ v ∈ H, ¬ G.Adj u v)
    (hnex : ∀ u ∉ H, (G.neighborFinset u ∩ H).card = 4)
    {b1 b2 : V → ℤ} (h1 : Biplane G b1) (h2 : Biplane G b2) (horth : b1 ⬝ᵥ b2 = 0)
    (hP1 : pos b1 ⊆ H) (hN1 : Disjoint (neg b1) H) (hP2 : pos b2 ⊆ H) (hN2 : Disjoint (neg b2) H) :
    False := by
  -- orthogonality forces P1 ∩ P2 = N1 ∩ N2 = ∅
  have hPN : Disjoint (pos b1) (neg b2) := Finset.disjoint_of_subset_left hP1 hN2.symm
  have hNP : Disjoint (neg b1) (pos b2) := Finset.disjoint_of_subset_right hP2 hN1
  have e1 : (pos b1 ∩ neg b2).card = 0 := by
    rw [card_eq_zero]; exact Finset.disjoint_iff_inter_eq_empty.1 hPN
  have e2 : (neg b1 ∩ pos b2).card = 0 := by
    rw [card_eq_zero]; exact Finset.disjoint_iff_inter_eq_empty.1 hNP
  have hdot := dot_biplane h1 b2
  rw [horth, sum_over_set h2, sum_over_set h2, e1, e2] at hdot
  push_cast at hdot
  have hPP : (pos b1 ∩ pos b2).card = 0 := by omega
  have hNN : (neg b1 ∩ neg b2).card = 0 := by omega
  rw [card_eq_zero] at hPP hNN
  -- D = H \ (P1 ∪ P2) has 8 points, Z = V \ (H ∪ N1 ∪ N2) has 63 points
  set D := H \ (pos b1 ∪ pos b2) with hD
  set Z := ((H ∪ neg b1) ∪ neg b2)ᶜ with hZ
  have hcardD : D.card = 8 := by
    rw [hD, card_sdiff_of_subset (union_subset hP1 hP2),
      card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.2 hPP), h1.card_pos, h2.card_pos,
      hH]
  have hcardZ : Z.card = 63 := by
    rw [hZ, card_compl, card_union_of_disjoint, card_union_of_disjoint hN1.symm, hH, h1.card_neg,
      h2.card_neg, card_V hG]
    rw [Finset.disjoint_union_left]
    exact ⟨hN2.symm, Finset.disjoint_iff_inter_eq_empty.2 hNN⟩
  -- every neighbour of a point of D lies in Z
  have hNjD : ∀ (b : V → ℤ), Biplane G b → pos b ⊆ H → Disjoint (neg b) H →
      ∀ n ∈ neg b, ∀ d ∈ H, d ∉ pos b → ¬ G.Adj n d := by
    intro b hb hP hN n hn d hd hdP hadj
    have hnH : n ∉ H := Finset.disjoint_left.1 hN hn
    have h4 := hnex n hnH
    have hsub : G.neighborFinset n ∩ pos b ⊆ G.neighborFinset n ∩ H :=
      Finset.inter_subset_inter_left hP
    have heq := eq_of_subset_of_card_le hsub (by rw [h4, hb.four_neg n hn])
    have : d ∈ G.neighborFinset n ∩ H := mem_inter.2 ⟨(G.mem_neighborFinset n d).2 hadj, hd⟩
    rw [← heq] at this
    exact hdP (mem_inter.1 this).2
  have hDZ : ∀ d ∈ D, (G.neighborFinset d ∩ Z).card = 14 := by
    intro d hd
    rw [hD, mem_sdiff, mem_union, not_or] at hd
    have : G.neighborFinset d ∩ Z = G.neighborFinset d := by
      apply Finset.inter_eq_left.2
      intro w hw
      rw [mem_neighborFinset] at hw
      rw [hZ, mem_compl, mem_union, mem_union, not_or, not_or]
      refine ⟨⟨fun hwH => hcocl d hd.1 w hwH hw, fun hwN => ?_⟩, fun hwN => ?_⟩
      · exact hNjD b1 h1 hP1 hN1 w hwN d hd.1 hd.2.1 hw.symm
      · exact hNjD b2 h2 hP2 hN2 w hwN d hd.1 hd.2.2 hw.symm
    rw [this, card_neighborFinset_eq_degree, hG.regular d]
  -- every point of Z has at least two neighbours in D
  have hZD : ∀ z ∈ Z, 2 ≤ (G.neighborFinset z ∩ D).card := by
    intro z hz
    rw [hZ, mem_compl, mem_union, mem_union, not_or, not_or] at hz
    have h4 := hnex z hz.1.1
    have hle1 : ∀ (b : V → ℤ), Biplane G b → z ∉ neg b → pos b ⊆ H →
        (G.neighborFinset z ∩ pos b).card ≤ 1 := by
      intro b hb hzN hP
      rw [Finset.card_le_one]; intro v hv v' hv'; by_contra hne
      simp only [mem_inter, mem_neighborFinset] at hv hv'
      exact hzN (hb.cn_pos v hv.2 v' hv'.2 hne ((mem_cn G).2 ⟨hv.1.symm, hv'.1.symm⟩))
    have hsplit : G.neighborFinset z ∩ H ⊆
        (G.neighborFinset z ∩ pos b1) ∪ (G.neighborFinset z ∩ pos b2) ∪ (G.neighborFinset z ∩ D) := by
      intro w hw
      rw [mem_inter] at hw
      by_cases w1 : w ∈ pos b1
      · exact mem_union.2 (Or.inl (mem_union.2 (Or.inl (mem_inter.2 ⟨hw.1, w1⟩))))
      · by_cases w2 : w ∈ pos b2
        · exact mem_union.2 (Or.inl (mem_union.2 (Or.inr (mem_inter.2 ⟨hw.1, w2⟩))))
        · refine mem_union.2 (Or.inr (mem_inter.2 ⟨hw.1, ?_⟩))
          rw [hD, mem_sdiff, mem_union, not_or]; exact ⟨hw.2, w1, w2⟩
    have := card_le_card hsplit
    have := card_union_le (G.neighborFinset z ∩ pos b1 ∪ G.neighborFinset z ∩ pos b2)
      (G.neighborFinset z ∩ D)
    have := card_union_le (G.neighborFinset z ∩ pos b1) (G.neighborFinset z ∩ pos b2)
    have := hle1 b1 h1 hz.1.2 hP1
    have := hle1 b2 h2 hz.2 hP2
    omega
  -- count the edges between D and Z
  have hcount := cross_nat (G := G) D Z
  rw [Finset.sum_congr rfl hDZ, sum_const, hcardD, smul_eq_mul] at hcount
  have : Z.card * 2 ≤ ∑ v ∈ Z, (G.neighborFinset v ∩ D).card := by
    rw [← smul_eq_mul, ← sum_const]; exact Finset.sum_le_sum hZD
  rw [hcardZ] at this
  omega

/-- (30): a Hoffman coclique inactive on a root `s` meets each side of `s` once and avoids `I_s`. -/
lemma inactive {H : Finset V} (hH : H.card = 22) (hcocl : ∀ u ∈ H, ∀ v ∈ H, ¬ G.Adj u v)
    (hnex : ∀ u ∉ H, (G.neighborFinset u ∩ H).card = 4)
    {s : V → ℤ} (hsM : IsM4 G s) (hs : Biplane G s)
    (hbal : (H ∩ pos s).card = (H ∩ neg s).card) :
    (H ∩ pos s).card = 1 ∧ (H ∩ neg s).card = 1 ∧ Disjoint H (Iset G s) := by
  set τ := (H ∩ pos s).card with hτ
  -- τ ≤ 1
  have hτ1 : τ ≤ 1 := by
    by_contra h2
    push_neg at h2
    obtain ⟨p, hp, p', hp', hne⟩ := Finset.one_lt_card.1 h2
    rw [mem_inter] at hp hp'
    -- every point of H ∩ N_s is adjacent to neither p nor p', but p, p' see 6 points of N_s
    have hunion : ((G.neighborFinset p ∪ G.neighborFinset p') ∩ neg s).card = 6 := by
      rw [Finset.union_inter_distrib_right]
      have hi : (G.neighborFinset p ∩ neg s) ∩ (G.neighborFinset p' ∩ neg s) = cn G p p' := by
        ext w; simp only [mem_inter, cn, mem_neighborFinset]
        constructor
        · rintro ⟨⟨h1, _⟩, h2, _⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          have hw := hs.cn_pos p hp.2 p' hp'.2 hne ((mem_cn G).2 ⟨h1, h2⟩)
          exact ⟨⟨h1, hw⟩, h2, hw⟩
      have := card_union_add_card_inter (G.neighborFinset p ∩ neg s) (G.neighborFinset p' ∩ neg s)
      rw [hi, hs.four_pos p hp.2, hs.four_pos p' hp'.2,
        cn_nadj hG hne (hs.cocl_pos p hp.2 p' hp'.2)] at this
      omega
    have hsub : H ∩ neg s ⊆ neg s \ ((G.neighborFinset p ∪ G.neighborFinset p') ∩ neg s) := by
      intro w hw
      rw [mem_inter] at hw
      simp only [mem_sdiff, mem_inter, mem_union, not_and]
      refine ⟨hw.2, fun h _ => ?_⟩
      rcases h with h | h
      · exact absurd ((G.mem_neighborFinset p w).1 h) (hcocl p hp.1 w hw.1)
      · exact absurd ((G.mem_neighborFinset p' w).1 h) (hcocl p' hp'.1 w hw.1)
    have := card_le_card hsub
    rw [card_sdiff_of_subset inter_subset_right, hunion, hs.card_neg] at this
    omega
  -- edge count between C_s and H
  set c := (H ∩ Cset s).card with hc
  have hcτ : c = 2 * τ := by
    rw [hc, Cset, Finset.inter_union_distrib_left, card_union_of_disjoint
      (Finset.disjoint_of_subset_left inter_subset_right
        (Finset.disjoint_of_subset_right inter_subset_right (pos_neg_disj s)))]
    omega
  have hcross := cross_nat (G := G) (Cset s) H
  have hL : ∑ x ∈ Cset s, (G.neighborFinset x ∩ H).card = 4 * (14 - c) := by
    have : ∀ x ∈ Cset s, (G.neighborFinset x ∩ H).card = if x ∈ H then 0 else 4 := by
      intro x _
      split_ifs with hx
      · rw [card_eq_zero, eq_empty_iff_forall_notMem]; intro w hw
        rw [mem_inter, mem_neighborFinset] at hw; exact hcocl x hx w hw.2 hw.1
      · exact hnex x hx
    rw [Finset.sum_congr rfl this, Finset.sum_ite, sum_const_zero, zero_add, sum_const,
      smul_eq_mul]
    have hf : (Cset s).filter (fun x => x ∉ H) = Cset s \ (H ∩ Cset s) := by
      ext x; simp [mem_sdiff]
    rw [hf, card_sdiff_of_subset inter_subset_right, card_C hG hs, hc, mul_comm]
  have hR : ∑ h ∈ H, (G.neighborFinset h ∩ Cset s).card
      = 4 * c + 2 * (H ∩ Sset G s).card := by
    have : ∀ h, (G.neighborFinset h ∩ Cset s).card
        = (if h ∈ Cset s then 4 else 0) + (if h ∈ Sset G s then 2 else 0) := by
      intro h
      rw [nbC_card hG hsM hs h]
      rcases partCSI hG hs h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, h3⟩
      · simp [h1, h2]
      · simp only [Sset, mem_filter] at h2; simp [h1, Sset, h2.2.2]
      · simp only [Iset, mem_filter] at h3; simp [h1, h2, h3.2.2]
    rw [Finset.sum_congr rfl (fun h _ => this h), Finset.sum_add_distrib, Finset.sum_ite_mem,
      Finset.sum_ite_mem, sum_const, sum_const, smul_eq_mul, smul_eq_mul, hc]
    ring
  rw [hL, hR] at hcross
  have hsplitH := card_split hG hs H
  rw [hH] at hsplitH
  -- d = 3 c - 6 ≥ 0 forces c = 2
  have hc2 : c = 2 := by omega
  refine ⟨by omega, by omega, ?_⟩
  have hI0 : (H ∩ Iset G s).card = 0 := by omega
  rw [card_eq_zero] at hI0
  exact Finset.disjoint_iff_inter_eq_empty.2 hI0

end SRG

end Conway99
