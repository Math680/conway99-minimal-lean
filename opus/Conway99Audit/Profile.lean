import Conway99Audit.Cover

/-!
# Part B, step 8: the profile budget of §9.2

A *profile* is an integer vector `ℓ` with `A ℓ = -4 ℓ - 2·𝟏` (i.e. `𝟏 + 9 ℓ` is a `-4`
eigenvector).  If `ℓ` takes only the values `-1, 0, 1` and `Σ ℓ² = 23`, then (with
`P = {ℓ = 1}`, `B = {ℓ = -1}`) one gets `|P| = 6`, `|B| = 17`, `e_B = e_P + 1`, and the
common-neighbour count of the pairs of `P` gives `e_P ≤ 1`, hence `e_B ≤ 2`.
We state the conclusion with ordered pairs: `Σ_{u ∈ B} |N(u) ∩ B| ≤ 4`.
-/

open Finset SimpleGraph Matrix

namespace Conway99

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Ordered adjacent pairs inside `X`. -/
lemma card_adj_pairs (X : Finset V) :
    ((X ×ˢ X).filter (fun p => G.Adj p.1 p.2)).card = ∑ u ∈ X, (G.neighborFinset u ∩ X).card := by
  rw [card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl; intro u _
  rw [← card_filter]
  congr 1; ext x; simp [mem_neighborFinset, and_comm]

section SRG

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

lemma sum_nbr_sum (x : V → ℤ) : ∑ u, ∑ v ∈ G.neighborFinset u, x v = 14 * ∑ u, x u := by
  have : ∀ u, ∑ v ∈ G.neighborFinset u, x v = ∑ v, A G u v * x v := by
    intro u; rw [← Av_apply]; rfl
  simp_rw [this]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro v _
  rw [← Finset.sum_mul, colsum_A hG]

/-- **Profile budget** (§9.2). -/
theorem profile_budget (ℓ : V → ℤ) (hvals : ∀ u, ℓ u = 0 ∨ ℓ u = 1 ∨ ℓ u = -1)
    (heig : ∀ u, ∑ x ∈ G.neighborFinset u, ℓ x = -4 * ℓ u - 2)
    (hsq : ∑ u, ℓ u * ℓ u = 23) :
    ∑ u ∈ neg ℓ, (G.neighborFinset u ∩ neg ℓ).card ≤ 4 := by
  set P := pos ℓ with hP
  set B := neg ℓ with hB
  -- total sum
  have hsum : ∑ u, ℓ u = -11 := by
    have h1 := sum_nbr_sum hG ℓ
    rw [Finset.sum_congr rfl (fun u _ => heig u), Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_const, card_univ, card_V hG] at h1
    norm_num at h1
    linarith
  have hs2 := sum_over hvals univ
  rw [univ_inter, univ_inter, hsum] at hs2
  have hn2 := norm_vals hvals
  have hdd : ℓ ⬝ᵥ ℓ = ∑ u, ℓ u * ℓ u := rfl
  rw [hdd, hsq] at hn2
  have hPc : (P.card : ℤ) = 6 := by linarith
  have hBc : (B.card : ℤ) = 17 := by linarith
  -- local equations
  have hp : ∀ p ∈ P, ((G.neighborFinset p ∩ P).card : ℤ) - (G.neighborFinset p ∩ B).card = -6 := by
    intro p hp
    have := heig p
    rw [sum_over hvals, (mem_pos.1 hp)] at this
    linarith
  have hq : ∀ q ∈ B, ((G.neighborFinset q ∩ P).card : ℤ) - (G.neighborFinset q ∩ B).card = 2 := by
    intro q hq
    have := heig q
    rw [sum_over hvals, (mem_neg.1 hq)] at this
    linarith
  set eP : ℤ := ∑ p ∈ P, ((G.neighborFinset p ∩ P).card : ℤ) with heP
  set eB : ℤ := ∑ q ∈ B, ((G.neighborFinset q ∩ B).card : ℤ) with heB
  have hcross := cross_symm (G := G) P B
  have hPB : ∑ p ∈ P, ((G.neighborFinset p ∩ B).card : ℤ) = eP + 36 := by
    rw [heP, show (36 : ℤ) = ∑ p ∈ P, (6 : ℤ) by rw [sum_const, nsmul_eq_mul, hPc]; norm_num,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro p hp'; have := hp p hp'; linarith
  have hBP : ∑ q ∈ B, ((G.neighborFinset q ∩ P).card : ℤ) = eB + 34 := by
    rw [heB, show (34 : ℤ) = ∑ q ∈ B, (2 : ℤ) by rw [sum_const, nsmul_eq_mul, hBc]; norm_num,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro q hq'; have := hq q hq'; linarith
  have hrel : eB = eP + 2 := by linarith
  -- common neighbours of pairs of P inside B
  have hdc := double_count_cn (G := G) P B
  have hL : ∀ q ∈ B, (4 : ℤ) * (G.neighborFinset q ∩ P).card - 6 ≤
      (((G.neighborFinset q ∩ P).offDiag).card : ℤ) := by
    intro q _
    rw [offDiag_card]
    set d := (G.neighborFinset q ∩ P).card
    have hd : d * d - d = d * (d - 1) := by rw [Nat.mul_sub_one]
    rw [hd]
    rcases Nat.lt_or_ge d 1 with h | h
    · interval_cases d; norm_num
    · push_cast [Nat.cast_sub h]
      have : (0 : ℤ) ≤ ((d : ℤ) - 2) * ((d : ℤ) - 3) := by
        rcases le_or_gt (d : ℤ) 2 with h2 | h2
        · nlinarith
        · nlinarith
      nlinarith
  have hLsum : ∑ q ∈ B, ((4 : ℤ) * (G.neighborFinset q ∩ P).card - 6)
      ≤ ∑ q ∈ B, (((G.neighborFinset q ∩ P).offDiag).card : ℤ) := Finset.sum_le_sum hL
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hBP, sum_const, nsmul_eq_mul, hBc] at hLsum
  have hR : ∑ pr ∈ P.offDiag, ((cn G pr.1 pr.2 ∩ B).card : ℤ)
      ≤ ∑ pr ∈ P.offDiag, (if G.Adj pr.1 pr.2 then (1 : ℤ) else 2) := by
    apply Finset.sum_le_sum; intro pr hpr
    rw [mem_offDiag] at hpr
    have hle : (cn G pr.1 pr.2 ∩ B).card ≤ (cn G pr.1 pr.2).card := card_le_card inter_subset_left
    split_ifs with ha
    · rw [cn_adj hG ha] at hle; exact_mod_cast hle
    · rw [cn_nadj hG hpr.2.2 ha] at hle; exact_mod_cast hle
  have hR2 : ∑ pr ∈ P.offDiag, (if G.Adj pr.1 pr.2 then (1 : ℤ) else 2) = 60 - eP := by
    have e1 : ∀ pr : V × V, (if G.Adj pr.1 pr.2 then (1 : ℤ) else 2)
        = 2 - (if G.Adj pr.1 pr.2 then 1 else 0) := by intro pr; split_ifs <;> norm_num
    simp_rw [e1]
    rw [Finset.sum_sub_distrib, sum_const, nsmul_eq_mul, offDiag_card, Finset.sum_boole]
    have hf : P.offDiag.filter (fun pr => G.Adj pr.1 pr.2) = (P ×ˢ P).filter (fun pr => G.Adj pr.1 pr.2) := by
      ext pr; simp only [mem_filter, mem_offDiag, mem_product]
      constructor
      · rintro ⟨⟨h1, h2, _⟩, h4⟩; exact ⟨⟨h1, h2⟩, h4⟩
      · rintro ⟨⟨h1, h2⟩, h4⟩; exact ⟨⟨h1, h2, G.ne_of_adj h4⟩, h4⟩
    rw [hf, card_adj_pairs, heP]
    have hPn : P.card = 6 := by exact_mod_cast hPc
    rw [hPn]; push_cast; norm_num
  have hdcZ : ∑ q ∈ B, (((G.neighborFinset q ∩ P).offDiag).card : ℤ)
      = ∑ pr ∈ P.offDiag, ((cn G pr.1 pr.2 ∩ B).card : ℤ) := by exact_mod_cast hdc
  have h5 : 5 * eB ≤ 28 := by linarith
  have hev : Even eB := by
    have h := inner_even hG B
    have e : eB = ((∑ q ∈ B, (G.neighborFinset q ∩ B).card : ℕ) : ℤ) := by rw [heB]; push_cast; rfl
    rw [e]; exact h.natCast
  obtain ⟨k, hk⟩ := hev
  have : eB ≤ 4 := by omega
  have hfin : ((∑ q ∈ B, (G.neighborFinset q ∩ B).card : ℕ) : ℤ) ≤ 4 := by push_cast; exact this
  exact_mod_cast hfin

end SRG

end Conway99
