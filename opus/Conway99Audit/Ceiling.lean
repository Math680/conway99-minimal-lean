import Conway99Audit.Hoff

/-!
# Part B, step 6: relations (31) between two orthogonal roots, and `ρ ≤ 4` (§6.4)
-/

open Finset SimpleGraph Matrix

namespace Conway99

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma neg_disj_Hp (b : V → ℤ) : Disjoint (neg b) (Hp G b) := by
  rw [Hp, Finset.disjoint_union_right]
  exact ⟨(pos_neg_disj b).symm,
    Finset.disjoint_of_subset_left (neg_sub_C b) (I_disj_C (G := G) b).symm⟩

lemma Hp_neg (b : V → ℤ) (hC : ∀ u, u ∉ Cset b →
    (G.neighborFinset u ∩ pos b).card = (G.neighborFinset u ∩ neg b).card) :
    Hp G (-b) = Hm G b := by
  have hCC : Cset (-b) = Cset b := by rw [Cset, Cset, pos_neg_neg, neg_neg_pos, union_comm]
  have hI : Iset G (-b) = Iset G b := by
    ext u; simp only [Iset, mem_filter, mem_univ, true_and, hCC, pos_neg_neg]
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩
    · rw [hC u h1]; exact h2
    · rw [← hC u h1]; exact h2
  rw [Hp, Hm, pos_neg_neg, hI]

section SRG

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

/-- `H⁺_r` is balanced on every root orthogonal to `r` (consequence of §6.3 and (29)). -/
lemma Hp_balanced {r s : V → ℤ} (hrM : IsM4 G r) (hr : Biplane G r) (hsM : IsM4 G s)
    (hs : Biplane G s) (horth : r ⬝ᵥ s = 0) :
    (Hp G r ∩ pos s).card = (Hp G r ∩ neg s).card := by
  obtain ⟨hH, hcocl, hnex⟩ := Hp_props hG hrM hr
  have hsum := sum_Hp hG hrM hr hsM horth
  rw [sum_over_set hs] at hsum
  have hle1 : (Hp G r ∩ pos s).card ≤ 7 := hs.card_pos ▸ card_le_card inter_subset_right
  have hle2 : (Hp G r ∩ neg s).card ≤ 7 := hs.card_neg ▸ card_le_card inter_subset_right
  set t := ∑ u ∈ pos r, s u
  have ht : t = -1 ∨ t = 0 ∨ t = 1 := by omega
  have hPr : pos r ⊆ Hp G r := subset_union_left
  rcases ht with ht | ht | ht
  · -- active with negative sign: use -s
    exfalso
    have hN7 : (Hp G r ∩ neg s).card = 7 := by omega
    have hP0 : (Hp G r ∩ pos s).card = 0 := by omega
    have hsub : neg s ⊆ Hp G r := by
      have := eq_of_subset_of_card_le (inter_subset_right : Hp G r ∩ neg s ⊆ neg s)
        (by rw [hN7, hs.card_neg])
      rw [← this]; exact inter_subset_left
    have hdisj : Disjoint (pos s) (Hp G r) := by
      rw [card_eq_zero] at hP0
      rw [Finset.disjoint_iff_inter_eq_empty, inter_comm]; exact hP0
    apply two_active hG hH hcocl hnex hr hs.neg' (by rw [dotProduct_neg, horth, neg_zero])
      hPr (neg_disj_Hp r)
    · rw [pos_neg_neg]; exact hsub
    · rw [neg_neg_pos]; exact hdisj
  · omega
  · exfalso
    have hP7 : (Hp G r ∩ pos s).card = 7 := by omega
    have hN0 : (Hp G r ∩ neg s).card = 0 := by omega
    have hsub : pos s ⊆ Hp G r := by
      have := eq_of_subset_of_card_le (inter_subset_right : Hp G r ∩ pos s ⊆ pos s)
        (by rw [hP7, hs.card_pos])
      rw [← this]; exact inter_subset_left
    have hdisj : Disjoint (neg s) (Hp G r) := by
      rw [card_eq_zero] at hN0
      rw [Finset.disjoint_iff_inter_eq_empty, inter_comm]; exact hN0
    exact two_active hG hH hcocl hnex hr hs horth hPr (neg_disj_Hp r) hsub hdisj

/-- (30) applied to `H⁺_r` and `H⁻_r`. -/
lemma Hpm_meet {r s : V → ℤ} (hrM : IsM4 G r) (hr : Biplane G r) (hsM : IsM4 G s)
    (hs : Biplane G s) (horth : r ⬝ᵥ s = 0) :
    (Hp G r ∩ pos s).card = 1 ∧ (Hp G r ∩ neg s).card = 1 ∧ Disjoint (Hp G r) (Iset G s) ∧
    (Hm G r ∩ pos s).card = 1 ∧ (Hm G r ∩ neg s).card = 1 ∧ Disjoint (Hm G r) (Iset G s) := by
  obtain ⟨hH, hcocl, hnex⟩ := Hp_props hG hrM hr
  obtain ⟨a1, a2, a3⟩ := inactive hG hH hcocl hnex hsM hs (Hp_balanced hG hrM hr hsM hs horth)
  have hHm : Hm G r = Hp G (-r) := (Hp_neg r (fun u hu => out_eq hG hrM hr hu)).symm
  have hr' := hr.neg'
  have hrM' := hrM.neg
  have horth' : (-r) ⬝ᵥ s = 0 := by rw [neg_dotProduct, horth, neg_zero]
  obtain ⟨hH', hcocl', hnex'⟩ := Hp_props hG hrM' hr'
  obtain ⟨b1, b2, b3⟩ := inactive hG hH' hcocl' hnex' hsM hs
    (Hp_balanced hG hrM' hr' hsM hs horth')
  rw [← hHm] at b1 b2 b3
  exact ⟨a1, a2, a3, b1, b2, b3⟩

/-- Relations (31) for two orthogonal roots. -/
theorem rel31 {r s : V → ℤ} (hrM : IsM4 G r) (hr : Biplane G r) (hsM : IsM4 G s)
    (hs : Biplane G s) (horth : r ⬝ᵥ s = 0) :
    Disjoint (Cset r) (Iset G s) ∧ Disjoint (Iset G r) (Iset G s) ∧
    (pos r ∩ pos s).card = 1 ∧ (pos r ∩ neg s).card = 1 ∧
    (neg r ∩ pos s).card = 1 ∧ (neg r ∩ neg s).card = 1 ∧ (Cset r ∩ Cset s).card = 4 := by
  obtain ⟨p1, p2, p3, m1, m2, m3⟩ := Hpm_meet hG hrM hr hsM hs horth
  have horth' : s ⬝ᵥ r = 0 := by rw [dotProduct_comm]; exact horth
  obtain ⟨q1, q2, q3, n1, n2, n3⟩ := Hpm_meet hG hsM hs hrM hr horth'
  have hCI : Disjoint (Cset r) (Iset G s) := by
    rw [Cset, Finset.disjoint_union_left]
    exact ⟨Finset.disjoint_of_subset_left subset_union_left p3,
      Finset.disjoint_of_subset_left subset_union_left m3⟩
  have hCI' : Disjoint (Cset s) (Iset G r) := by
    rw [Cset, Finset.disjoint_union_left]
    exact ⟨Finset.disjoint_of_subset_left subset_union_left q3,
      Finset.disjoint_of_subset_left subset_union_left n3⟩
  have hII : Disjoint (Iset G r) (Iset G s) := Finset.disjoint_of_subset_left subset_union_right p3
  -- I_r ∩ pos s = I_r ∩ neg s = ∅
  have e1 : Iset G r ∩ pos s = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.1
      (Finset.disjoint_of_subset_right (pos_sub_C s) hCI'.symm)
  have e2 : Iset G r ∩ neg s = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.1
      (Finset.disjoint_of_subset_right (neg_sub_C s) hCI'.symm)
  have split : ∀ X : Finset V, (Hp G r ∩ X).card = (pos r ∩ X).card + (Iset G r ∩ X).card := by
    intro X
    rw [Hp, Finset.union_inter_distrib_right, card_union_of_disjoint
      (Finset.disjoint_of_subset_left inter_subset_left
        (Finset.disjoint_of_subset_right inter_subset_left
          (Finset.disjoint_of_subset_left (pos_sub_C r) (I_disj_C (G := G) r).symm)))]
  have split' : ∀ X : Finset V, (Hm G r ∩ X).card = (neg r ∩ X).card + (Iset G r ∩ X).card := by
    intro X
    rw [Hm, Finset.union_inter_distrib_right, card_union_of_disjoint
      (Finset.disjoint_of_subset_left inter_subset_left
        (Finset.disjoint_of_subset_right inter_subset_left
          (Finset.disjoint_of_subset_left (neg_sub_C r) (I_disj_C (G := G) r).symm)))]
  have f1 : (pos r ∩ pos s).card = 1 := by have := split (pos s); rw [e1, card_empty] at this; omega
  have f2 : (pos r ∩ neg s).card = 1 := by have := split (neg s); rw [e2, card_empty] at this; omega
  have f3 : (neg r ∩ pos s).card = 1 := by have := split' (pos s); rw [e1, card_empty] at this; omega
  have f4 : (neg r ∩ neg s).card = 1 := by have := split' (neg s); rw [e2, card_empty] at this; omega
  refine ⟨hCI, hII, f1, f2, f3, f4, ?_⟩
  have hd := pos_neg_disj r
  have hd' := pos_neg_disj s
  rw [Cset, Cset, Finset.union_inter_distrib_right, Finset.inter_union_distrib_left,
    Finset.inter_union_distrib_left]
  rw [card_union_of_disjoint, card_union_of_disjoint, card_union_of_disjoint, f1, f2, f3, f4]
  · exact Finset.disjoint_of_subset_left inter_subset_right
      (Finset.disjoint_of_subset_right inter_subset_right hd')
  · exact Finset.disjoint_of_subset_left inter_subset_right
      (Finset.disjoint_of_subset_right inter_subset_right hd')
  · rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨Finset.disjoint_of_subset_left inter_subset_left
        (Finset.disjoint_of_subset_right inter_subset_left hd),
      Finset.disjoint_of_subset_left inter_subset_left
        (Finset.disjoint_of_subset_right inter_subset_left hd)⟩,
      ⟨Finset.disjoint_of_subset_left inter_subset_left
        (Finset.disjoint_of_subset_right inter_subset_left hd),
      Finset.disjoint_of_subset_left inter_subset_left
        (Finset.disjoint_of_subset_right inter_subset_left hd)⟩⟩

/-- Edges from `C_r` to `C_s`: `36` for orthogonal roots. -/
lemma edges_CC {r s : V → ℤ} (hrM : IsM4 G r) (hr : Biplane G r) (hsM : IsM4 G s)
    (hs : Biplane G s) (horth : r ⬝ᵥ s = 0) :
    ∑ u ∈ Cset r, (G.neighborFinset u ∩ Cset s).card = 36 := by
  obtain ⟨hCI, -, -, -, -, -, h4⟩ := rel31 hG hrM hr hsM hs horth
  have : ∀ u ∈ Cset r, (G.neighborFinset u ∩ Cset s).card = if u ∈ Cset s then 4 else 2 := by
    intro u hu
    rw [nbC_card hG hsM hs u]
    split_ifs with h
    · rfl
    · have hnI : u ∉ Iset G s := Finset.disjoint_left.1 hCI hu
      rcases mem_S_or_I hG hs h with ⟨hS, _⟩ | ⟨hI, _⟩
      · simp only [Sset, mem_filter] at hS; rw [hS.2.2]
      · exact absurd hI hnI
  rw [Finset.sum_congr rfl this, Finset.sum_ite, sum_const, sum_const, smul_eq_mul, smul_eq_mul,
    Finset.filter_mem_eq_inter, h4]
  have hf : (Cset r).filter (fun u => u ∉ Cset s) = Cset r \ (Cset r ∩ Cset s) := by
    ext u; simp [mem_sdiff]
  rw [hf, card_sdiff_of_subset inter_subset_left, card_C hG hr, h4]

lemma edges_CC_self {r : V → ℤ} (hrM : IsM4 G r) (hr : Biplane G r) :
    ∑ u ∈ Cset r, (G.neighborFinset u ∩ Cset r).card = 56 := by
  rw [Finset.sum_congr rfl (fun u hu => by rw [nbC_card hG hrM hr u, if_pos hu]), sum_const,
    card_C hG hr, smul_eq_mul]

/-- **First root ceiling (32): there are no five pairwise orthogonal roots.** -/
theorem no_five (b : Fin 5 → V → ℤ) (hM : ∀ i, IsM4 G (b i)) (hb : ∀ i, Biplane G (b i))
    (horth : ∀ i j, i ≠ j → b i ⬝ᵥ b j = 0) : False := by
  set v : V → ℤ := fun u => ∑ i, (if u ∈ Cset (b i) then 1 else 0) with hv
  have hpsd := G0_psd hG v
  rw [G0_quad] at hpsd
  -- double sums over Fin 5 with constant diagonal / off-diagonal values
  have dsum : ∀ (f : Fin 5 → Fin 5 → ℤ) (a c : ℤ), (∀ i, f i i = a) →
      (∀ i j, i ≠ j → f i j = c) → ∑ i, ∑ j, f i j = 5 * a + 20 * c := by
    intro f a c hd ho
    simp only [Fin.sum_univ_five]
    rw [hd 0, hd 1, hd 2, hd 3, hd 4]
    rw [ho 0 1 (by decide), ho 0 2 (by decide), ho 0 3 (by decide), ho 0 4 (by decide),
      ho 1 0 (by decide), ho 1 2 (by decide), ho 1 3 (by decide), ho 1 4 (by decide),
      ho 2 0 (by decide), ho 2 1 (by decide), ho 2 3 (by decide), ho 2 4 (by decide),
      ho 3 0 (by decide), ho 3 1 (by decide), ho 3 2 (by decide), ho 3 4 (by decide),
      ho 4 0 (by decide), ho 4 1 (by decide), ho 4 2 (by decide), ho 4 3 (by decide)]
    ring
  have hvv : v ⬝ᵥ v = 150 := by
    have : v ⬝ᵥ v = ∑ i, ∑ j, (((Cset (b i)) ∩ (Cset (b j))).card : ℤ) := by
      simp only [dotProduct, hv, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      simp only [boole_mul]
      rw [← Finset.sum_filter, Finset.sum_boole]
      congr 2; ext u; simp only [mem_filter, mem_univ, true_and, mem_inter]; tauto
    rw [this, dsum _ 14 4 (fun i => by rw [inter_self, card_C hG (hb i)]; rfl)
      (fun i j hij => by rw [(rel31 hG (hM i) (hb i) (hM j) (hb j) (horth i j hij)).2.2.2.2.2.2]; rfl)]
    norm_num
  have hsv : ∑ u, v u = 70 := by
    simp only [hv]
    rw [Finset.sum_comm]
    simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, univ_inter]
    simp [card_C hG (hb _)]
  have hvAv : v ⬝ᵥ (A G *ᵥ v) = 1000 := by
    have hrow : ∀ u, (A G *ᵥ v) u = ∑ j, ((G.neighborFinset u ∩ Cset (b j)).card : ℤ) := by
      intro u
      rw [Av_apply]
      simp only [hv]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter]
    have : v ⬝ᵥ (A G *ᵥ v)
        = ∑ i, ∑ j, ((∑ u ∈ Cset (b j), (G.neighborFinset u ∩ Cset (b i)).card : ℕ) : ℤ) := by
      rw [dotProduct]
      simp_rw [hrow]
      simp only [hv, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      push_cast
      simp only [boole_mul]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, univ_inter]
    rw [this, dsum _ 56 36 (fun i => by rw [edges_CC_self hG (hM i) (hb i)]; rfl)
      (fun i j hij => by
        rw [edges_CC hG (hM j) (hb j) (hM i) (hb i) (horth j i (Ne.symm hij))]; rfl)]
    norm_num
  rw [hvv, hsv, hvAv] at hpsd
  norm_num at hpsd

end SRG

end Conway99
