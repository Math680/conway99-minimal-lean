import Conway99Audit.Eig

/-!
# Lemma 5.1 (equality case): the biplane structure of a norm-14 `-4` eigenvector
-/

open Finset SimpleGraph Matrix

namespace Conway99

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The conclusion of Lemma 5.1 at equality. -/
structure Biplane (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℤ) : Prop where
  vals : ∀ u, b u = 0 ∨ b u = 1 ∨ b u = -1
  card_pos : (pos b).card = 7
  card_neg : (neg b).card = 7
  cocl_pos : ∀ u ∈ pos b, ∀ v ∈ pos b, ¬ G.Adj u v
  cocl_neg : ∀ u ∈ neg b, ∀ v ∈ neg b, ¬ G.Adj u v
  four_pos : ∀ u ∈ pos b, (G.neighborFinset u ∩ neg b).card = 4
  four_neg : ∀ u ∈ neg b, (G.neighborFinset u ∩ pos b).card = 4
  cn_pos : ∀ u ∈ pos b, ∀ v ∈ pos b, u ≠ v → cn G u v ⊆ neg b
  cn_neg : ∀ u ∈ neg b, ∀ v ∈ neg b, u ≠ v → cn G u v ⊆ pos b
  norm : b ⬝ᵥ b = 14

lemma vals_of_abs {b : V → ℤ} (h : ∀ v, |b v| ≤ 1) (v : V) : b v = 0 ∨ b v = 1 ∨ b v = -1 := by
  have := h v; rw [abs_le] at this; omega

lemma eq_ind {b : V → ℤ} (h : ∀ v, b v = 0 ∨ b v = 1 ∨ b v = -1) (v : V) :
    b v = (if v ∈ pos b then 1 else 0) - (if v ∈ neg b then 1 else 0) := by
  rcases h v with h0 | h1 | h2
  · simp [mem_pos, mem_neg, h0]
  · simp [mem_pos, mem_neg, h1]
  · simp [mem_pos, mem_neg, h2]

lemma sum_over {b : V → ℤ} (h : ∀ v, b v = 0 ∨ b v = 1 ∨ b v = -1) (S : Finset V) :
    ∑ v ∈ S, b v = ((S ∩ pos b).card : ℤ) - ((S ∩ neg b).card : ℤ) := by
  rw [Finset.sum_congr rfl (fun v _ => eq_ind h v), Finset.sum_sub_distrib, Finset.sum_boole,
    Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.filter_mem_eq_inter]

lemma norm_vals {b : V → ℤ} (h : ∀ v, b v = 0 ∨ b v = 1 ∨ b v = -1) :
    b ⬝ᵥ b = ((pos b).card : ℤ) + (neg b).card := by
  have : ∀ v, b v * b v = (if v ∈ pos b then 1 else 0) + (if v ∈ neg b then 1 else 0) := by
    intro v; rcases h v with h0 | h1 | h2
    · simp [mem_pos, mem_neg, h0]
    · simp [mem_pos, mem_neg, h1]
    · simp [mem_pos, mem_neg, h2]
  simp only [dotProduct]
  rw [Finset.sum_congr rfl (fun v _ => this v), Finset.sum_add_distrib, Finset.sum_boole,
    Finset.sum_boole]
  simp [pos, neg]

lemma pos_neg_disj (b : V → ℤ) : Disjoint (pos b) (neg b) := by
  rw [Finset.disjoint_left]; intro u hu hv; rw [mem_pos] at hu; rw [mem_neg] at hv; omega

lemma card_inter_eq_sum (u : V) (X : Finset V) :
    ((G.neighborFinset u ∩ X).card : ℤ) = ∑ v ∈ X, (if G.Adj u v then (1 : ℤ) else 0) := by
  rw [Finset.sum_boole]; norm_cast; congr 1; ext v; simp [mem_neighborFinset, and_comm]

lemma cross_symm (X Y : Finset V) :
    ∑ u ∈ X, ((G.neighborFinset u ∩ Y).card : ℤ) = ∑ v ∈ Y, ((G.neighborFinset v ∩ X).card : ℤ) := by
  simp_rw [card_inter_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro v _; apply Finset.sum_congr rfl; intro u _
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd h1.symm h2 | exact absurd h2.symm h1

lemma pos_neg_neg (b : V → ℤ) : pos (-b) = neg b := by
  ext u; simp only [mem_pos, mem_neg, Pi.neg_apply]; omega

lemma neg_neg_pos (b : V → ℤ) : neg (-b) = pos b := by
  ext u; simp only [mem_pos, mem_neg, Pi.neg_apply]; omega

/-- Double counting of common neighbours in `Y` of ordered pairs in `X`. -/
lemma double_count_cn (X Y : Finset V) :
    ∑ w ∈ Y, ((G.neighborFinset w ∩ X).offDiag).card
      = ∑ q ∈ X.offDiag, (cn G q.1 q.2 ∩ Y).card := by
  have e1 : ∀ w, ((G.neighborFinset w ∩ X).offDiag).card
      = ∑ q ∈ X.offDiag, (if G.Adj w q.1 ∧ G.Adj w q.2 then 1 else 0) := by
    intro w
    rw [Finset.sum_boole]
    congr 1; ext q
    simp only [mem_offDiag, mem_inter, mem_neighborFinset, mem_filter]
    tauto
  have e2 : ∀ q : V × V, (cn G q.1 q.2 ∩ Y).card
      = ∑ w ∈ Y, (if G.Adj w q.1 ∧ G.Adj w q.2 then 1 else 0) := by
    intro q
    rw [Finset.sum_boole]
    congr 1; ext w
    simp only [mem_inter, mem_cn, mem_filter, G.adj_comm q.1 w, G.adj_comm q.2 w]
    tauto
  simp_rw [e1, e2]
  exact Finset.sum_comm

section SRG

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

/-- Parity of the number of ordered adjacent pairs inside a set. -/
lemma inner_even (X : Finset V) : Even (∑ u ∈ X, (G.neighborFinset u ∩ X).card) := by
  have h := sum_symm_offdiag_even
    (fun u v => if u ∈ X ∧ v ∈ X ∧ G.Adj u v then (1 : ℤ) else 0)
    (fun u v => by simp only [G.adj_comm v u]; congr 1; apply propext; tauto)
  have hdiag : ∑ u, (if u ∈ X ∧ u ∈ X ∧ G.Adj u u then (1 : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero; intro u _; simp
  rw [hdiag, sub_zero] at h
  have hrow : ∀ u, ∑ v, (if u ∈ X ∧ v ∈ X ∧ G.Adj u v then (1 : ℤ) else 0)
      = if u ∈ X then ((G.neighborFinset u ∩ X).card : ℤ) else 0 := by
    intro u
    rw [Finset.sum_boole]
    by_cases hu : u ∈ X
    · rw [if_pos hu]; norm_cast; congr 1; ext v; simp [hu, mem_neighborFinset, and_comm]
    · rw [if_neg hu]; simp [hu]
  rw [Finset.sum_congr rfl (fun u _ => hrow u), ← Finset.sum_filter, Finset.filter_mem_eq_inter,
    univ_inter] at h
  exact_mod_cast h

/-- Half of Lemma 5.1 (statements about the positive side, and the two cocliques). -/
lemma lemma51_half {b : V → ℤ} (hb : IsM4 G b) (hne : b ≠ 0) (h14 : b ⬝ᵥ b ≤ 14) :
    (∀ u, b u = 0 ∨ b u = 1 ∨ b u = -1) ∧ (pos b).card = 7 ∧ (neg b).card = 7 ∧
    (∀ u ∈ pos b, ∀ v ∈ pos b, ¬ G.Adj u v) ∧ (∀ u ∈ neg b, ∀ v ∈ neg b, ¬ G.Adj u v) ∧
    (∀ u ∈ pos b, (G.neighborFinset u ∩ neg b).card = 4) ∧
    (∀ u ∈ neg b, (G.neighborFinset u ∩ pos b).card = 4) ∧
    (∀ u ∈ pos b, ∀ v ∈ pos b, u ≠ v → cn G u v ⊆ neg b) ∧ b ⬝ᵥ b = 14 := by
  have hv := vals_of_abs (hb.entries hG h14)
  set P := pos b with hP
  set N := neg b with hN
  have hs := hb.sum_zero hG
  rw [sum_over hv univ, univ_inter, univ_inter] at hs
  have hPN : (P.card : ℤ) = N.card := by linarith
  have hPNn : P.card = N.card := by exact_mod_cast hPN
  have hnorm := norm_vals hv
  -- P nonempty
  have hPne : P.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hN0 : N = ∅ := by rw [← card_eq_zero, ← hPNn, hemp, card_empty]
    apply hne; funext v
    rcases hv v with h0 | h1 | h2
    · exact h0
    · exfalso; have : v ∈ P := mem_pos.2 h1; rw [hemp] at this; simp at this
    · exfalso; have : v ∈ N := mem_neg.2 h2; rw [hN0] at this; simp at this
  obtain ⟨u0, hu0⟩ := hPne
  have hb0 : b u0 = 1 := mem_pos.1 hu0
  have hmaxeq : ∑ v, max (b v) 0 = (P.card : ℤ) := by
    have : ∀ v, max (b v) 0 = if v ∈ P then 1 else 0 := by
      intro v; rcases hv v with h | h | h <;> simp [hP, mem_pos, h]
    rw [Finset.sum_congr rfl (fun v _ => this v), Finset.sum_boole, Finset.filter_mem_eq_inter,
      univ_inter]
  have hm4 : 4 ≤ (P.card : ℤ) := by
    have := hb.posmass hG u0 (fun v => by rcases hv v with h | h | h <;> rw [h, hb0] <;> norm_num)
      (by rw [hb0])
    rw [hb0, hmaxeq] at this; linarith
  have hm7 : (P.card : ℤ) ≤ 7 := by linarith
  -- eigen equations on both sides
  have hrowP : ∀ u ∈ P,
      ((G.neighborFinset u ∩ P).card : ℤ) - (G.neighborFinset u ∩ N).card = -4 := by
    intro u hu
    have := hb.apply u
    rw [sum_over hv, mem_pos.1 hu] at this
    linarith
  have hrowN : ∀ u ∈ N,
      ((G.neighborFinset u ∩ P).card : ℤ) - (G.neighborFinset u ∩ N).card = 4 := by
    intro u hu
    have := hb.apply u
    rw [sum_over hv, mem_neg.1 hu] at this
    linarith
  set ePP := ∑ u ∈ P, ((G.neighborFinset u ∩ P).card : ℤ) with hePP
  set D := ∑ u ∈ P, ((G.neighborFinset u ∩ N).card : ℤ) with hD
  set D' := ∑ u ∈ N, ((G.neighborFinset u ∩ P).card : ℤ) with hD'
  set eNN := ∑ u ∈ N, ((G.neighborFinset u ∩ N).card : ℤ) with heNN
  have h1 : ePP - D = -4 * P.card := by
    rw [hePP, hD, ← Finset.sum_sub_distrib, Finset.sum_congr rfl hrowP, sum_const, nsmul_eq_mul]
    ring
  have h2 : D' - eNN = 4 * N.card := by
    rw [hD', heNN, ← Finset.sum_sub_distrib, Finset.sum_congr rfl hrowN, sum_const, nsmul_eq_mul]
    ring
  have hDD : D = D' := cross_symm P N
  -- positivity of G0 on the support
  have hdisj := pos_neg_disj b
  set x : V → ℤ := fun v => if v ∈ P ∪ N then 1 else 0 with hx
  have hpsd := G0_psd hG x
  rw [G0_quad] at hpsd
  have hxx : x ⬝ᵥ x = P.card + N.card := by
    simp only [dotProduct]
    rw [Finset.sum_congr rfl (fun v _ => (show x v * x v = (if v ∈ P ∪ N then (1 : ℤ) else 0) by
      simp only [hx]; split_ifs <;> simp))]
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, univ_inter, card_union_of_disjoint hdisj]
    push_cast; ring
  have hsx : ∑ u, x u = P.card + N.card := by
    simp only [hx]
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, univ_inter, card_union_of_disjoint hdisj]
    push_cast; ring
  have hxAx : x ⬝ᵥ (A G *ᵥ x) = ePP + D + D' + eNN := by
    have hrow : ∀ u, (A G *ᵥ x) u
        = ((G.neighborFinset u ∩ P).card : ℤ) + (G.neighborFinset u ∩ N).card := by
      intro u
      rw [Av_apply]
      simp only [hx]
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_union_distrib_left,
        card_union_of_disjoint (Finset.disjoint_of_subset_left inter_subset_right
          (Finset.disjoint_of_subset_right inter_subset_right hdisj))]
      push_cast; ring
    calc x ⬝ᵥ (A G *ᵥ x)
        = ∑ u, (if u ∈ P ∪ N then (((G.neighborFinset u ∩ P).card : ℤ)
            + (G.neighborFinset u ∩ N).card) else 0) := by
          simp only [dotProduct]
          apply Finset.sum_congr rfl; intro u _
          rw [hrow u]
          simp only [hx]
          split_ifs <;> simp
      _ = ∑ u ∈ P ∪ N, (((G.neighborFinset u ∩ P).card : ℤ) + (G.neighborFinset u ∩ N).card) := by
          rw [Finset.sum_ite_mem, univ_inter]
      _ = ePP + D + D' + eNN := by
          rw [Finset.sum_union hdisj, Finset.sum_add_distrib, Finset.sum_add_distrib]
          ring
  rw [hxx, hsx, hxAx] at hpsd
  have hev := inner_even hG P
  have hePPnat : ePP = ((∑ u ∈ P, (G.neighborFinset u ∩ P).card : ℕ) : ℤ) := by
    rw [hePP]; push_cast; rfl
  -- numeric conclusion: ePP = 0 and m ≥ 5
  have hkey : 36 * ePP ≤ 4 * (P.card : ℤ) ^ 2 - 18 * P.card := by
    rw [← hPN] at hpsd h2; nlinarith
  have hePPz : ePP = 0 := by
    obtain ⟨k, hk⟩ := hev
    have hk' : ePP = 2 * (k : ℤ) := by rw [hePPnat, hk]; push_cast; ring
    have hk0 : 0 ≤ (k : ℤ) := by positivity
    have hPc : P.card ≤ 7 := by exact_mod_cast hm7
    have hPc4 : 4 ≤ P.card := by exact_mod_cast hm4
    rw [hk'] at hkey ⊢
    interval_cases hc : P.card <;> push_cast at hkey <;> omega
  have hm5 : 5 ≤ (P.card : ℤ) := by
    by_contra hlt
    have : (P.card : ℤ) = 4 := by linarith
    rw [this, hePPz] at hkey; norm_num at hkey
  -- cocliques and four neighbours
  have hzero : ∀ u ∈ P, (G.neighborFinset u ∩ P).card = 0 := by
    intro u hu
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => by positivity : ∀ u ∈ P,
      (0 : ℤ) ≤ ((G.neighborFinset u ∩ P).card : ℤ))).1 (by rw [← hePP]; exact hePPz) u hu
    exact_mod_cast this
  have hcoclP : ∀ u ∈ P, ∀ v ∈ P, ¬ G.Adj u v := by
    intro u hu v hv' hadj
    have h0 := hzero u hu
    rw [card_eq_zero] at h0
    have : v ∈ G.neighborFinset u ∩ P := mem_inter.2 ⟨(G.mem_neighborFinset u v).2 hadj, hv'⟩
    rw [h0] at this; simp at this
  have hfourP : ∀ u ∈ P, (G.neighborFinset u ∩ N).card = 4 := by
    intro u hu
    have := hrowP u hu; rw [hzero u hu] at this; push_cast at this; omega
  have heNN0 : eNN = 0 := by linarith
  have hzeroN : ∀ u ∈ N, (G.neighborFinset u ∩ N).card = 0 := by
    intro u hu
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => by positivity : ∀ u ∈ N,
      (0 : ℤ) ≤ ((G.neighborFinset u ∩ N).card : ℤ))).1 (by rw [← heNN]; exact heNN0) u hu
    exact_mod_cast this
  have hcoclN : ∀ u ∈ N, ∀ v ∈ N, ¬ G.Adj u v := by
    intro u hu v hv' hadj
    have h0 := hzeroN u hu
    rw [card_eq_zero] at h0
    have : v ∈ G.neighborFinset u ∩ N := mem_inter.2 ⟨(G.mem_neighborFinset u v).2 hadj, hv'⟩
    rw [h0] at this; simp at this
  have hfourN : ∀ u ∈ N, (G.neighborFinset u ∩ P).card = 4 := by
    intro u hu
    have := hrowN u hu; rw [hzeroN u hu] at this; push_cast at this; omega
  -- common neighbours: 12 m ≤ 2 m (m - 1), hence m = 7 and equality
  have hdc := double_count_cn (G := G) P N
  have hC1 : ∑ w ∈ N, ((G.neighborFinset w ∩ P).offDiag).card = 12 * N.card := by
    rw [Finset.sum_congr rfl (fun w hw => by rw [Finset.offDiag_card, hfourN w hw]), sum_const,
      smul_eq_mul]
    ring
  have hterm : ∀ q ∈ P.offDiag, (cn G q.1 q.2 ∩ N).card ≤ 2 := by
    intro q hq
    rw [mem_offDiag] at hq
    have h2' := cn_nadj hG hq.2.2 (hcoclP q.1 hq.1 q.2 hq.2.1)
    rw [← h2']; exact card_le_card inter_subset_left
  have hC2le : ∑ q ∈ P.offDiag, (cn G q.1 q.2 ∩ N).card ≤ 2 * (P.card * P.card - P.card) := by
    calc _ ≤ ∑ q ∈ P.offDiag, 2 := Finset.sum_le_sum hterm
      _ = 2 * (P.card * P.card - P.card) := by
        rw [sum_const, Finset.offDiag_card, smul_eq_mul]; ring
  have hm7' : P.card = 7 := by
    have hPc : P.card ≤ 7 := by exact_mod_cast hm7
    have hPc5 : 5 ≤ P.card := by exact_mod_cast hm5
    rw [← hdc, hC1, ← hPNn] at hC2le
    interval_cases hc : P.card <;> omega
  have hcnP : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → cn G u v ⊆ N := by
    intro u hu v hv' huv
    have hsumeq : ∑ q ∈ P.offDiag, (cn G q.1 q.2 ∩ N).card = ∑ q ∈ P.offDiag, 2 := by
      apply le_antisymm (Finset.sum_le_sum hterm)
      rw [sum_const, Finset.offDiag_card, smul_eq_mul, ← hdc, hC1, ← hPNn, hm7']
    have hq : (u, v) ∈ P.offDiag := mem_offDiag.2 ⟨hu, hv', huv⟩
    have heq := (Finset.sum_eq_sum_iff_of_le hterm).1 hsumeq (u, v) hq
    have h2' := cn_nadj hG huv (hcoclP u hu v hv')
    have hsub : cn G u v ∩ N ⊆ cn G u v := inter_subset_left
    have := Finset.eq_of_subset_of_card_le hsub (by simp only at heq; rw [heq, h2'])
    rw [← this]; exact inter_subset_right
  refine ⟨hv, hm7', by omega, hcoclP, hcoclN, hfourP, hfourN, hcnP, ?_⟩
  rw [hnorm, ← hPN, hm7']
  norm_num

/-- Lemma 5.1 of the minimal proof (equality case). -/
theorem lemma51 {b : V → ℤ} (hb : IsM4 G b) (hne : b ≠ 0) (h14 : b ⬝ᵥ b ≤ 14) :
    Biplane G b := by
  obtain ⟨hv, hP, hN, hcP, hcN, hfP, hfN, hcnP, hnorm⟩ := lemma51_half hG hb hne h14
  have hb' : IsM4 G (-b) := hb.neg
  have hne' : -b ≠ 0 := by intro h; apply hne; simpa using congrArg Neg.neg h
  have h14' : (-b) ⬝ᵥ (-b) ≤ 14 := by simpa using h14
  obtain ⟨-, -, -, -, -, -, -, hcnP', -⟩ := lemma51_half hG hb' hne' h14'
  rw [pos_neg_neg, neg_neg_pos] at hcnP'
  exact ⟨hv, hP, hN, hcP, hcN, hfP, hfN, hcnP, hcnP', hnorm⟩

/-- Lemma 5.1, inequality: a nonzero integer `-4` eigenvector has norm at least 14. -/
theorem lemma51_ge {b : V → ℤ} (hb : IsM4 G b) (hne : b ≠ 0) : 14 ≤ b ⬝ᵥ b := by
  by_contra h
  push_neg at h
  have := (lemma51 hG hb hne h.le).norm
  omega

end SRG

end Conway99
