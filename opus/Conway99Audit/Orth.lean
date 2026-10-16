import Conway99Audit.Roots

/-!
# Part B, step 3: two roots are orthogonal or opposite (§5.2), hence `Φ = A₁^ρ`
-/

open Finset SimpleGraph Matrix

namespace Conway99

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Biplane.neg' {b : V → ℤ} (h : Biplane G b) : Biplane G (-b) := by
  have hp : pos (-b) = neg b := pos_neg_neg b
  have hn : neg (-b) = pos b := neg_neg_pos b
  refine ⟨fun u => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases h.vals u with h | h | h <;> simp [h]
  · rw [hp]; exact h.card_neg
  · rw [hn]; exact h.card_pos
  · rw [hp]; exact h.cocl_neg
  · rw [hn]; exact h.cocl_pos
  · rw [hp, hn]; exact h.four_neg
  · rw [hp, hn]; exact h.four_pos
  · rw [hp, hn]; exact h.cn_neg
  · rw [hp, hn]; exact h.cn_pos
  · simpa using h.norm

/-- The cell `X = {b = 1, c = 0}` and its opposite `X' = {b = -1, c = 0}`. -/
def cellX (b c : V → ℤ) : Finset V := univ.filter (fun u => b u = 1 ∧ c u = 0)
def cellX' (b c : V → ℤ) : Finset V := univ.filter (fun u => b u = -1 ∧ c u = 0)

section SRG

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

lemma no_same_sign {b c : V → ℤ} (hd : Biplane G (b + c)) (u : V) :
    ¬ (b u = 1 ∧ c u = 1) ∧ ¬ (b u = -1 ∧ c u = -1) := by
  have := hd.vals u
  simp only [Pi.add_apply] at this
  constructor <;> rintro ⟨h1, h2⟩ <;> omega

/-- `|X| + |X'| = 7`. -/
lemma cell_card {b c : V → ℤ} (hb : Biplane G b) (hc : Biplane G c) (hd : Biplane G (b + c)) :
    (cellX b c).card + (cellX' b c).card = 7 := by
  have hns := no_same_sign hG hd
  -- pos b = X ∪ Y', neg b = X' ∪ Y, pos c = Y ∪ Z', pos (b+c) = X ∪ Z'
  set Y := univ.filter (fun u => b u = -1 ∧ c u = 1)
  set Y' := univ.filter (fun u => b u = 1 ∧ c u = -1)
  set Z' := univ.filter (fun u => b u = 0 ∧ c u = 1)
  have e1 : (cellX b c).card + Y'.card = 7 := by
    rw [← hb.card_pos, ← card_union_of_disjoint]
    · congr 1; ext u
      simp only [cellX, Y', pos, mem_union, mem_filter, mem_univ, true_and]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        rcases hc.vals u with h0 | h1 | h2
        · exact Or.inl ⟨h, h0⟩
        · exact absurd ⟨h, h1⟩ (hns u).1
        · exact Or.inr ⟨h, h2⟩
    · rw [Finset.disjoint_left]; intro u hu hu'
      simp only [cellX, Y', mem_filter] at hu hu'; omega
  have e2 : (cellX' b c).card + Y.card = 7 := by
    rw [← hb.card_neg, ← card_union_of_disjoint]
    · congr 1; ext u
      simp only [cellX', Y, neg, mem_union, mem_filter, mem_univ, true_and]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        rcases hc.vals u with h0 | h1 | h2
        · exact Or.inl ⟨h, h0⟩
        · exact Or.inr ⟨h, h1⟩
        · exact absurd ⟨h, h2⟩ (hns u).2
    · rw [Finset.disjoint_left]; intro u hu hu'
      simp only [cellX', Y, mem_filter] at hu hu'; omega
  have e3 : Y.card + Z'.card = 7 := by
    rw [← hc.card_pos, ← card_union_of_disjoint]
    · congr 1; ext u
      simp only [Y, Z', pos, mem_union, mem_filter, mem_univ, true_and]
      constructor
      · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
      · intro h
        rcases hb.vals u with h0 | h1 | h2
        · exact Or.inr ⟨h0, h⟩
        · exact absurd ⟨h1, h⟩ (hns u).1
        · exact Or.inl ⟨h2, h⟩
    · rw [Finset.disjoint_left]; intro u hu hu'
      simp only [Y, Z', mem_filter] at hu hu'; omega
  have e4 : (cellX b c).card + Z'.card = 7 := by
    rw [← hd.card_pos, ← card_union_of_disjoint]
    · congr 1; ext u
      simp only [cellX, Z', pos, mem_union, mem_filter, mem_univ, true_and, Pi.add_apply]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
      · intro h
        rcases hb.vals u with h0 | h1 | h2 <;> rcases hc.vals u with k0 | k1 | k2 <;> omega
    · rw [Finset.disjoint_left]; intro u hu hu'
      simp only [cellX, Z', mem_filter] at hu hu'; omega
  omega

/-- Every point of `X` has at least three neighbours in `X'`. -/
lemma cell_three {b c : V → ℤ} (hb : Biplane G b) (hc : Biplane G c) (hd : Biplane G (b + c))
    {u : V} (hu : u ∈ cellX b c) : 3 ≤ (G.neighborFinset u ∩ cellX' b c).card := by
  have hns := no_same_sign hG hd
  simp only [cellX, mem_filter, mem_univ, true_and] at hu
  have h4 := hb.four_pos u (mem_pos.2 hu.1)
  set Y := univ.filter (fun w => b w = -1 ∧ c w = 1)
  have hsplit : G.neighborFinset u ∩ neg b
      = (G.neighborFinset u ∩ cellX' b c) ∪ (G.neighborFinset u ∩ Y) := by
    rw [← Finset.inter_union_distrib_left]; congr 1; ext w
    simp only [neg, cellX', Y, mem_union, mem_filter, mem_univ, true_and]
    constructor
    · intro h
      rcases hc.vals w with h0 | h1 | h2
      · exact Or.inl ⟨h, h0⟩
      · exact Or.inr ⟨h, h1⟩
      · exact absurd ⟨h, h2⟩ (hns w).2
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint (G.neighborFinset u ∩ cellX' b c) (G.neighborFinset u ∩ Y) := by
    rw [Finset.disjoint_left]; intro w hw hw'
    simp only [cellX', Y, mem_inter, mem_filter] at hw hw'; omega
  have hY : (G.neighborFinset u ∩ Y).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro v hv v' hv'
    by_contra hne
    simp only [Y, mem_inter, mem_filter, mem_univ, true_and, mem_neighborFinset] at hv hv'
    have hcn : u ∈ cn G v v' := (mem_cn G).2 ⟨hv.1.symm, hv'.1.symm⟩
    have := hc.cn_pos v (mem_pos.2 hv.2.2) v' (mem_pos.2 hv'.2.2) hne hcn
    rw [mem_neg] at this; omega
  rw [hsplit, card_union_of_disjoint hdisj] at h4
  omega

/-- §5.2: three biplane vectors `b`, `c`, `b + c` cannot coexist. -/
theorem no_sum_triple {b c : V → ℤ} (hb : Biplane G b) (hc : Biplane G c)
    (hd : Biplane G (b + c)) : False := by
  -- reduce to a cell of size ≥ 4 with all its points having ≥ 3 neighbours in the opposite cell
  have key : ∀ b c : V → ℤ, Biplane G b → Biplane G c → Biplane G (b + c) →
      4 ≤ (cellX b c).card → False := by
    intro b c hb hc hd h4
    have hcard := cell_card hG hb hc hd
    obtain ⟨u, hu⟩ : (cellX b c).Nonempty := by rw [← card_pos]; omega
    have h3 := cell_three hG hb hc hd hu
    have hle : (G.neighborFinset u ∩ cellX' b c).card ≤ (cellX' b c).card :=
      card_le_card inter_subset_right
    -- |X| = 4 and |X'| = 3: two points of X share the three points of X'
    have hX4 : (cellX b c).card = 4 := by omega
    obtain ⟨u', hu', hne⟩ : ∃ u' ∈ cellX b c, u' ≠ u := by
      by_contra hcon
      push_neg at hcon
      have : cellX b c ⊆ {u} := fun w hw => mem_singleton.2 (hcon w hw)
      have := card_le_card this; rw [card_singleton] at this; omega
    have h3' := cell_three hG hb hc hd hu'
    have hfull : ∀ w ∈ cellX' b c, w ∈ G.neighborFinset u ∧ w ∈ G.neighborFinset u' := by
      intro w hw
      have e1 : G.neighborFinset u ∩ cellX' b c = cellX' b c :=
        eq_of_subset_of_card_le inter_subset_right (by omega)
      have e2 : G.neighborFinset u' ∩ cellX' b c = cellX' b c :=
        eq_of_subset_of_card_le inter_subset_right (by omega)
      have hw1 : w ∈ G.neighborFinset u ∩ cellX' b c := by rw [e1]; exact hw
      have hw2 : w ∈ G.neighborFinset u' ∩ cellX' b c := by rw [e2]; exact hw
      exact ⟨(mem_inter.1 hw1).1, (mem_inter.1 hw2).1⟩
    have hsub : cellX' b c ⊆ cn G u u' := by
      intro w hw
      have := hfull w hw
      exact (mem_cn G).2 ⟨(G.mem_neighborFinset u w).1 this.1, (G.mem_neighborFinset u' w).1 this.2⟩
    simp only [cellX, mem_filter, mem_univ, true_and] at hu hu'
    have hnadj : ¬ G.Adj u u' := hb.cocl_pos u (mem_pos.2 hu.1) u' (mem_pos.2 hu'.1)
    have h2 := cn_nadj hG (Ne.symm hne) hnadj
    have := card_le_card hsub
    omega
  have hcard := cell_card hG hb hc hd
  by_cases h4 : 4 ≤ (cellX b c).card
  · exact key b c hb hc hd h4
  · -- use (-b, -c): its X-cell is X'
    have hb' := hb.neg'
    have hc' := hc.neg'
    have hd' : Biplane G (-b + -c) := by rw [← neg_add]; exact hd.neg'
    have hX : cellX (-b) (-c) = cellX' b c := by
      ext u
      simp only [cellX, cellX', mem_filter, mem_univ, true_and, Pi.neg_apply]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega
    apply key (-b) (-c) hb' hc' hd'
    rw [hX]; omega

/-- §5.2 and (22): two roots of an even integral overlattice are orthogonal unless equal or
opposite; hence the root system is `A₁^ρ`. -/
theorem roots_orth (L : EvenOverlattice G) {z z' : V → ℤ} (hz : z ∈ L.L) (hz' : z' ∈ L.L)
    (n : z ⬝ᵥ z = 126) (n' : z' ⬝ᵥ z' = 126) (h1 : z' ≠ z) (h2 : z' ≠ -z) : z ⬝ᵥ z' = 0 := by
  obtain ⟨b, rfl, hbM, hb⟩ := root_struct hG L hz n
  obtain ⟨c, rfl, hcM, hc⟩ := root_struct hG L hz' n'
  have hint := L.integral _ hz _ hz'
  have hbc : ((3 : ℤ) • b) ⬝ᵥ ((3 : ℤ) • c) = 9 * (b ⬝ᵥ c) := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
  rw [hbc] at hint ⊢
  have h7 : 7 ∣ b ⬝ᵥ c := by omega
  have hbb := hb.norm
  have hcc := hc.norm
  -- Cauchy–Schwarz bounds
  have hp : 0 ≤ (b + c) ⬝ᵥ (b + c) := by
    simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hm : 0 ≤ (b - c) ⬝ᵥ (b - c) := by
    simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have ep : (b + c) ⬝ᵥ (b + c) = 28 + 2 * (b ⬝ᵥ c) := by
    rw [add_dotProduct, dotProduct_add, dotProduct_add, hbb, hcc, dotProduct_comm c b]; ring
  have em : (b - c) ⬝ᵥ (b - c) = 28 - 2 * (b ⬝ᵥ c) := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hbb, hcc, dotProduct_comm c b]; ring
  have hsq0 : ∀ x : V → ℤ, x ⬝ᵥ x = 0 → x = 0 := by
    intro x hx; funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (x j))).1 hx i
      (mem_univ i)
    simpa using this
  obtain ⟨k, hk⟩ := h7
  have hk2 : -2 ≤ k ∧ k ≤ 2 := by constructor <;> nlinarith
  rcases (by omega : k = -2 ∨ k = -1 ∨ k = 0 ∨ k = 1 ∨ k = 2) with hk' | hk' | hk' | hk' | hk'
  · -- b·c = -14 : c = -b
    exfalso; apply h2
    have := hsq0 (b + c) (by rw [ep, hk, hk']; norm_num)
    have hcb : c = -b := by rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact this
    rw [hcb]; simp
  · -- b·c = -7 : b + c is a root
    exfalso
    have hsum : (3 : ℤ) • b + (3 : ℤ) • c ∈ L.L := L.L.add_mem hz hz'
    have hn : ((3 : ℤ) • b + (3 : ℤ) • c) ⬝ᵥ ((3 : ℤ) • b + (3 : ℤ) • c) = 126 := by
      rw [← smul_add, smul_dotProduct, dotProduct_smul, ep, hk, hk']; simp
    obtain ⟨d, hdz, -, hd⟩ := root_struct hG L hsum hn
    have : d = b + c := by
      funext u; have := congrFun hdz u
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢; linarith
    rw [this] at hd
    exact no_sum_triple hG hb hc hd
  · rw [hk, hk']; ring
  · -- b·c = 7 : b - c is a root, apply the triple lemma to b and -c
    exfalso
    have hdiff : (3 : ℤ) • b - (3 : ℤ) • c ∈ L.L := L.L.sub_mem hz hz'
    have hn : ((3 : ℤ) • b - (3 : ℤ) • c) ⬝ᵥ ((3 : ℤ) • b - (3 : ℤ) • c) = 126 := by
      rw [← smul_sub, smul_dotProduct, dotProduct_smul, em, hk, hk']; simp
    obtain ⟨d, hdz, -, hd⟩ := root_struct hG L hdiff hn
    have : d = b + -c := by
      funext u; have := congrFun hdz u
      simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this ⊢
      linarith
    rw [this] at hd
    exact no_sum_triple hG hb hc.neg' hd
  · -- b·c = 14 : c = b
    exfalso; apply h1
    have := hsq0 (b - c) (by rw [em, hk, hk']; norm_num)
    have hcb : b = c := sub_eq_zero.1 this
    rw [hcb]

end SRG

end Conway99
