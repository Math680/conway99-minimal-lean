import Conway99Audit.Delta

/-!
# Part A, assembled: Theorem 1.1 (first line) of the minimal proof

For a strongly regular graph with parameters `(99,14,1,2)`, let `N m` be the number of
unordered pairs of disjoint triangles with exactly `m` edges between them.  Then
`N 2 + 3 N 3 = 4158`, `δ := N 2 - 693 ∈ 3ℤ`, and `δ ≥ 165`
(equivalently `N 2 ≥ 858`, `N 3 ≤ 1100`).
-/

open Finset SimpleGraph Matrix

namespace Conway99

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- `x_L · x_M` at the level of finsets of vertices. -/
def Sf (L M : Finset V) : ℤ := 3 * ((L ∩ M).card : ℤ) - (eLM G L M : ℤ) + 1

variable (G) in
/-- Ordered pairs of disjoint triangles with exactly `m` edges between them
(`eLM` counts ordered adjacent pairs `(u,v) ∈ L × M`, i.e. edges between disjoint `L`, `M`). -/
def aOrd (m : ℕ) : ℕ :=
  ((T (G := G) ×ˢ T (G := G)).filter (fun p => Disjoint p.1 p.2 ∧ eLM G p.1 p.2 = m)).card

variable (G) in
/-- Unordered pairs: `N m = aOrd m / 2` (we prove `aOrd m` is even). -/
def Nm (m : ℕ) : ℕ := aOrd G m / 2

lemma S_eq_Sf (L M : Tr G) : S G L M = Sf G L.1 M.1 := rfl

lemma T_nonempty {L : Finset V} (hL : L ∈ T (G := G)) : L.Nonempty := by
  rw [← card_pos, T_card3 hL]; norm_num

lemma ne_of_disj {L M : Finset V} (hL : L ∈ T (G := G)) (hd : Disjoint L M) : L ≠ M := by
  rintro rfl
  obtain ⟨x, hx⟩ := T_nonempty hL
  exact Finset.disjoint_left.1 hd hx hx

section SRG

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

lemma inter_card_le_one {L M : Finset V} (hL : L ∈ T (G := G)) (hM : M ∈ T (G := G))
    (hne : L ≠ M) : (L ∩ M).card ≤ 1 := by
  by_contra h
  push_neg at h
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h
  rw [mem_inter] at ha hb
  have hadj : G.Adj a b := T_adj hL ha.1 hb.1 hab
  have h1 := T_through_edge hG hadj
  have hLm : L ∈ (T (G := G)).filter (fun t => a ∈ t ∧ b ∈ t) :=
    mem_filter.2 ⟨hL, ha.1, hb.1⟩
  have hMm : M ∈ (T (G := G)).filter (fun t => a ∈ t ∧ b ∈ t) :=
    mem_filter.2 ⟨hM, ha.2, hb.2⟩
  exact hne (Finset.card_le_one.1 (le_of_eq h1) L hLm M hMm)

lemma Sf_disj {L M : Finset V} (hL : L ∈ T (G := G)) (hM : M ∈ T (G := G)) (hd : Disjoint L M) :
    Sf G L M = 1 - (eLM G L M : ℤ) ∧ eLM G L M ≤ 3 := by
  have hi : (L ∩ M).card = 0 := by rw [Finset.disjoint_iff_inter_eq_empty.1 hd]; rfl
  refine ⟨by simp [Sf, hi]; ring, ?_⟩
  unfold eLM
  calc ∑ u ∈ L, nb G u M ≤ ∑ u ∈ L, 1 := by
        apply Finset.sum_le_sum; intro u hu
        exact T_card_filter_adj_out hG hM (Finset.disjoint_left.1 hd hu)
    _ = 3 := by rw [sum_const, T_card3 hL]; rfl

lemma Sf_inter {L M : Finset V} (hL : L ∈ T (G := G)) (hM : M ∈ T (G := G)) (hne : L ≠ M)
    (hnd : ¬ Disjoint L M) : Sf G L M = 0 := by
  rw [Finset.not_disjoint_iff] at hnd
  obtain ⟨x, hxL, hxM⟩ := hnd
  have hcard : (L ∩ M).card = 1 := by
    have h1 := inter_card_le_one hG hL hM hne
    have h2 : 0 < (L ∩ M).card := card_pos.2 ⟨x, mem_inter.2 ⟨hxL, hxM⟩⟩
    omega
  have hinter : L ∩ M = {x} := by
    obtain ⟨y, hy⟩ := Finset.card_eq_one.1 hcard
    have : x ∈ L ∩ M := mem_inter.2 ⟨hxL, hxM⟩
    rw [hy, mem_singleton] at this; rw [hy, this]
  have he : eLM G L M = 4 := by
    unfold eLM
    have hx2 : nb G x M = 2 := T_card_filter_adj_mem hM hxM
    rw [← Finset.add_sum_erase L _ hxL, hx2]
    have : ∀ u ∈ L.erase x, nb G u M = 1 := by
      intro u hu
      rw [mem_erase] at hu
      have huM : u ∉ M := by
        intro huM
        have : u ∈ L ∩ M := mem_inter.2 ⟨hu.2, huM⟩
        rw [hinter, mem_singleton] at this; exact hu.1 this
      have hle := T_card_filter_adj_out hG hM huM
      have hpos : 0 < nb G u M := by
        unfold nb
        exact card_pos.2 ⟨x, mem_filter.2 ⟨hxM, T_adj hL hu.2 hxL hu.1⟩⟩
      unfold nb at hpos ⊢; omega
    rw [Finset.sum_congr rfl this, sum_const, card_erase_of_mem hxL, T_card3 hL]
    rfl
  simp [Sf, hcard, he]

lemma Sf_diag {L : Finset V} (hL : L ∈ T (G := G)) : Sf G L L = 4 :=
  S_diag hG ⟨L, hL⟩

lemma Sf_symm {L M : Finset V} (hL : L ∈ T (G := G)) (hM : M ∈ T (G := G)) :
    Sf G L M = Sf G M L :=
  S_symm_apply hG ⟨L, hL⟩ ⟨M, hM⟩

/-- Every `aOrd m` is even: the swap `(L,M) ↦ (M,L)` has no fixed point. -/
lemma aOrd_even (m : ℕ) : Even (aOrd G m) := by
  set s := (T (G := G) ×ˢ T (G := G)).filter (fun p => Disjoint p.1 p.2 ∧ eLM G p.1 p.2 = m)
  have h0 : ((s.card : ℕ) : ZMod 2) = 0 := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    push_cast
    apply Finset.sum_involution (fun p _ => (p.2, p.1))
    · intro p _; exact CharTwo.add_self_eq_zero _
    · intro p hp _ h
      rw [mem_filter, mem_product] at hp
      have := ne_of_disj hp.1.1 hp.2.1
      exact this (by simpa using (Prod.ext_iff.1 h).2)
    · intro p hp
      rw [mem_filter, mem_product] at hp ⊢
      refine ⟨⟨hp.1.2, hp.1.1⟩, hp.2.1.symm, ?_⟩
      have h1 := (Sf_disj hG hp.1.1 hp.1.2 hp.2.1).1
      have h2 := (Sf_disj hG hp.1.2 hp.1.1 hp.2.1.symm).1
      rw [Sf_symm hG hp.1.1 hp.1.2] at h1
      rw [h1] at h2
      have : (eLM G p.2 p.1 : ℤ) = eLM G p.1 p.2 := by linarith
      rw [← hp.2.2]; exact_mod_cast this
    · intro p _; rfl
  show Even s.card
  rw [even_iff_two_dvd]
  exact (ZMod.natCast_eq_zero_iff _ 2).1 h0

lemma aOrd_eq_two_Nm (m : ℕ) : aOrd G m = 2 * Nm G m := by
  obtain ⟨k, hk⟩ := aOrd_even hG m
  unfold Nm; omega

/-- Sum of `φ(x_L·x_M)` over ordered pairs of triangles, for `φ 0 = 0`. -/
lemma sum_phi (φ : ℤ → ℤ) (h0 : φ 0 = 0) :
    ∑ L : Tr G, ∑ M : Tr G, φ (S G L M)
      = 231 * φ 4 + ∑ m ∈ range 4, (aOrd G m : ℤ) * φ (1 - m) := by
  have e1 : ∑ L : Tr G, ∑ M : Tr G, φ (S G L M)
      = ∑ p ∈ T (G := G) ×ˢ T (G := G), φ (Sf G p.1 p.2) := by
    rw [Finset.sum_product]
    simp only [S_eq_Sf]
    simp only [Finset.univ_eq_attach, Finset.sum_attach (T (G := G))
      (fun L => ∑ M ∈ (T (G := G)).attach, φ (Sf G L M.1))]
    apply Finset.sum_congr rfl; intro L _
    exact Finset.sum_attach (T (G := G)) (fun M => φ (Sf G L M))
  rw [e1, ← Finset.sum_filter_add_sum_filter_not _ (fun p => p.1 = p.2)]
  -- diagonal
  have hdiag : ∑ p ∈ (T (G := G) ×ˢ T (G := G)).filter (fun p => p.1 = p.2), φ (Sf G p.1 p.2)
      = 231 * φ 4 := by
    have h4 : ∀ p ∈ (T (G := G) ×ˢ T (G := G)).filter (fun p => p.1 = p.2),
        φ (Sf G p.1 p.2) = φ 4 := by
      intro p hp
      rw [mem_filter, mem_product] at hp
      rw [← hp.2, Sf_diag hG hp.1.1]
    rw [Finset.sum_congr rfl h4, sum_const, ← Finset.diag_eq_filter, Finset.diag_card, card_T hG]
    simp
  rw [hdiag, ← Finset.sum_filter_add_sum_filter_not _ (fun p => Disjoint p.1 p.2)]
  -- intersecting off-diagonal pairs contribute 0
  have hint : ∑ p ∈ ((T (G := G) ×ˢ T (G := G)).filter (fun p => ¬ p.1 = p.2)).filter
      (fun p => ¬ Disjoint p.1 p.2), φ (Sf G p.1 p.2) = 0 := by
    apply Finset.sum_eq_zero; intro p hp
    rw [mem_filter, mem_filter, mem_product] at hp
    rw [Sf_inter hG hp.1.1.1 hp.1.1.2 hp.1.2 hp.2, h0]
  rw [hint, add_zero]
  -- disjoint pairs, fibred by the number of edges
  set D := ((T (G := G) ×ˢ T (G := G)).filter (fun p => ¬ p.1 = p.2)).filter
      (fun p => Disjoint p.1 p.2) with hD
  have hmaps : ∀ p ∈ D, eLM G p.1 p.2 ∈ range 4 := by
    intro p hp
    rw [hD, mem_filter, mem_filter, mem_product] at hp
    rw [mem_range]
    have := (Sf_disj hG hp.1.1.1 hp.1.1.2 hp.2).2; omega
  have hval : ∑ p ∈ D, φ (Sf G p.1 p.2) = ∑ p ∈ D, φ (1 - (eLM G p.1 p.2 : ℤ)) := by
    apply Finset.sum_congr rfl; intro p hp
    rw [hD, mem_filter, mem_filter, mem_product] at hp
    rw [(Sf_disj hG hp.1.1.1 hp.1.1.2 hp.2).1]
  rw [hval, ← Finset.sum_fiberwise_of_maps_to' hmaps (fun m : ℕ => φ (1 - (m : ℤ)))]
  congr 1
  apply Finset.sum_congr rfl; intro m _
  rw [sum_const, nsmul_eq_mul]
  congr 2
  unfold aOrd
  congr 1
  ext p
  simp only [hD, mem_filter, mem_product]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, h3⟩, h4⟩; exact ⟨h1, h3, h4⟩
  · rintro ⟨h1, h3, h4⟩; exact ⟨⟨⟨h1, ne_of_disj h1.1 h3⟩, h3⟩, h4⟩

/-- The first identity: `Σ_{L,M} x_L·x_M = 0`. -/
lemma sum_S_all : ∑ L : Tr G, ∑ M : Tr G, S G L M = 0 := by
  apply Finset.sum_eq_zero; intro L _
  rw [Finset.sum_congr rfl (fun M _ => S_symm_apply hG L M)]
  exact sum_S_col hG L

lemma card_Tr : Fintype.card (Tr G) = 231 := by
  rw [Fintype.card_coe, card_T hG]

lemma sum_S_sq : ∑ L : Tr G, ∑ M : Tr G, S G L M ^ 2 = 19404 := by
  have : ∀ L : Tr G, ∑ M, S G L M ^ 2 = 21 * S G L L := by
    intro L
    rw [← S_sq_apply hG L L]
    apply Finset.sum_congr rfl; intro M _
    rw [S_symm_apply hG M L]; ring
  rw [Finset.sum_congr rfl (fun L _ => this L)]
  simp only [S_diag hG, sum_const, card_univ, card_Tr hG]
  norm_num

lemma sum_K : ∑ J : Tr G, K G J = 21 * ∑ L : Tr G, ∑ M : Tr G, S G L M ^ 3 := by
  simp only [K]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro L _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro M _
  have : ∀ J, S G J L * S G J M * S G L M ^ 2 = S G L M ^ 2 * (S G L J * S G J M) := by
    intro J; rw [S_symm_apply hG J L]; ring
  rw [Finset.sum_congr rfl (fun J _ => this J), ← Finset.mul_sum, S_sq_apply hG]
  ring

/-- **Theorem 1.1, first line** (minimal proof, §§2–3). -/
theorem part_A :
    Nm G 2 + 3 * Nm G 3 = 4158 ∧
    ((Nm G 2 : ℤ) - 693) = 3465 - 3 * (Nm G 3 : ℤ) ∧
    (3 : ℤ) ∣ ((Nm G 2 : ℤ) - 693) ∧
    165 ≤ (Nm G 2 : ℤ) - 693 ∧ 858 ≤ Nm G 2 ∧ Nm G 3 ≤ 1100 := by
  have E1 := sum_phi hG (fun x => x) rfl
  have E2 := sum_phi hG (fun x => x ^ 2) (by norm_num)
  have E3 := sum_phi hG (fun x => x ^ 3) (by norm_num)
  simp only [sum_range_succ, sum_range_zero] at E1 E2 E3
  rw [sum_S_all hG] at E1
  rw [sum_S_sq hG] at E2
  have hK := sum_K hG
  have hlow : ∑ J : Tr G, (60 : ℤ) ≤ ∑ J : Tr G, K G J :=
    Finset.sum_le_sum (fun J _ => K_ge60 hG J)
  rw [sum_const, card_univ, card_Tr hG, hK, E3] at hlow
  have a2 := aOrd_eq_two_Nm hG 2
  have a3 := aOrd_eq_two_Nm hG 3
  push_cast at E1 E2 hlow
  norm_num at E1 E2 hlow
  have hN : Nm G 2 + 3 * Nm G 3 = 4158 := by
    have : (aOrd G 2 : ℤ) + 3 * aOrd G 3 = 8316 := by linarith
    have h2 : (aOrd G 2 : ℤ) = 2 * Nm G 2 := by exact_mod_cast a2
    have h3 : (aOrd G 3 : ℤ) = 2 * Nm G 3 := by exact_mod_cast a3
    rw [h2, h3] at this
    omega
  have hN3 : Nm G 3 ≤ 1100 := by
    have h3 : (aOrd G 3 : ℤ) = 2 * Nm G 3 := by exact_mod_cast a3
    have h2 : (aOrd G 2 : ℤ) = 2 * Nm G 2 := by exact_mod_cast a2
    have : (Nm G 3 : ℤ) ≤ 1100 := by nlinarith
    exact_mod_cast this
  refine ⟨hN, ?_, ?_, ?_, ?_, hN3⟩
  · have : (Nm G 2 : ℤ) + 3 * Nm G 3 = 4158 := by exact_mod_cast hN
    linarith
  · exact ⟨1155 - (Nm G 3 : ℤ), by
      have : (Nm G 2 : ℤ) + 3 * Nm G 3 = 4158 := by exact_mod_cast hN
      linarith⟩
  · have : (Nm G 2 : ℤ) + 3 * Nm G 3 = 4158 := by exact_mod_cast hN
    have : (Nm G 3 : ℤ) ≤ 1100 := by exact_mod_cast hN3
    linarith
  · omega

end SRG

end Conway99
