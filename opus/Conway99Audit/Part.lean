import Conway99Audit.Orth

/-!
# Part B, step 4: the equitable partition of a root (§5.3) and its Hoffman cocliques (§6.2)

For a biplane vector `b` (a root): `C = P ∪ N`, `S` = outside points with one neighbour on each
side, `I` = outside points with no neighbour in `C`.  Then `|S| = 70`, `|I| = 15`, points of `S`
have three neighbours in `I`, `I` is a coclique, and `H± = P ∪ I`, `N ∪ I` are cocliques of size
22 with exactly four neighbours from every outside vertex.  For every `-4` eigenvector `x`,
`Σ_I x = 3 Σ_C x`.
-/

open Finset SimpleGraph Matrix

namespace Conway99

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def Cset (b : V → ℤ) : Finset V := pos b ∪ neg b

variable (G) in
def Sset (b : V → ℤ) : Finset V :=
  univ.filter (fun u => u ∉ Cset b ∧ (G.neighborFinset u ∩ pos b).card = 1)

variable (G) in
def Iset (b : V → ℤ) : Finset V :=
  univ.filter (fun u => u ∉ Cset b ∧ (G.neighborFinset u ∩ pos b).card = 0)

variable (G) in
def Hp (b : V → ℤ) : Finset V := pos b ∪ Iset G b

variable (G) in
def Hm (b : V → ℤ) : Finset V := neg b ∪ Iset G b

/-- Double counting of the edges leaving a finset `X` into a finset `Y` (unordered version). -/
lemma cross_nat (X Y : Finset V) :
    ∑ u ∈ X, (G.neighborFinset u ∩ Y).card = ∑ v ∈ Y, (G.neighborFinset v ∩ X).card := by
  have := cross_symm (G := G) X Y
  exact_mod_cast this

lemma pos_sub_C (b : V → ℤ) : pos b ⊆ Cset b := subset_union_left
lemma neg_sub_C (b : V → ℤ) : neg b ⊆ Cset b := subset_union_right

lemma I_disj_C (b : V → ℤ) : Disjoint (Iset G b) (Cset b) := by
  rw [Finset.disjoint_left]; intro u hu hC; simp only [Iset, mem_filter] at hu; exact hu.2.1 hC

section SRG

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

lemma card_C {b : V → ℤ} (hb : Biplane G b) : (Cset b).card = 14 := by
  rw [Cset, card_union_of_disjoint (pos_neg_disj b), hb.card_pos, hb.card_neg]

/-- An outside point sees at most one point of each side, and as many of each. -/
lemma out_le_one {b : V → ℤ} (hb : Biplane G b) {u : V} (hu : u ∉ Cset b) :
    (G.neighborFinset u ∩ pos b).card ≤ 1 ∧ (G.neighborFinset u ∩ neg b).card ≤ 1 := by
  constructor
  · rw [Finset.card_le_one]; intro v hv v' hv'; by_contra hne
    simp only [mem_inter, mem_neighborFinset] at hv hv'
    have := hb.cn_pos v hv.2 v' hv'.2 hne ((mem_cn G).2 ⟨hv.1.symm, hv'.1.symm⟩)
    exact hu (mem_union.2 (Or.inr this))
  · rw [Finset.card_le_one]; intro v hv v' hv'; by_contra hne
    simp only [mem_inter, mem_neighborFinset] at hv hv'
    have := hb.cn_neg v hv.2 v' hv'.2 hne ((mem_cn G).2 ⟨hv.1.symm, hv'.1.symm⟩)
    exact hu (mem_union.2 (Or.inl this))

lemma out_eq {b : V → ℤ} (hbM : IsM4 G b) (hb : Biplane G b) {u : V} (hu : u ∉ Cset b) :
    (G.neighborFinset u ∩ pos b).card = (G.neighborFinset u ∩ neg b).card := by
  have h := hbM.apply u
  rw [sum_over hb.vals] at h
  have hb0 : b u = 0 := by
    rcases hb.vals u with h0 | h1 | h2
    · exact h0
    · exact absurd (mem_union.2 (Or.inl (mem_pos.2 h1))) hu
    · exact absurd (mem_union.2 (Or.inr (mem_neg.2 h2))) hu
  rw [hb0] at h
  have : ((G.neighborFinset u ∩ pos b).card : ℤ) = (G.neighborFinset u ∩ neg b).card := by linarith
  exact_mod_cast this

/-- Number of neighbours in `C`. -/
lemma nbC_card {b : V → ℤ} (hbM : IsM4 G b) (hb : Biplane G b) (u : V) :
    (G.neighborFinset u ∩ Cset b).card =
      if u ∈ Cset b then 4 else 2 * (G.neighborFinset u ∩ pos b).card := by
  have hsplit : (G.neighborFinset u ∩ Cset b).card
      = (G.neighborFinset u ∩ pos b).card + (G.neighborFinset u ∩ neg b).card := by
    rw [Cset, Finset.inter_union_distrib_left, card_union_of_disjoint
      (Finset.disjoint_of_subset_left inter_subset_right
        (Finset.disjoint_of_subset_right inter_subset_right (pos_neg_disj b)))]
  rw [hsplit]
  split_ifs with hu
  · rcases mem_union.1 hu with hp | hn
    · have h0 : (G.neighborFinset u ∩ pos b).card = 0 := by
        rw [card_eq_zero, eq_empty_iff_forall_notMem]; intro v hv
        rw [mem_inter, mem_neighborFinset] at hv; exact hb.cocl_pos u hp v hv.2 hv.1
      rw [h0, hb.four_pos u hp]
    · have h0 : (G.neighborFinset u ∩ neg b).card = 0 := by
        rw [card_eq_zero, eq_empty_iff_forall_notMem]; intro v hv
        rw [mem_inter, mem_neighborFinset] at hv; exact hb.cocl_neg u hn v hv.2 hv.1
      rw [h0, hb.four_neg u hn]
  · rw [← out_eq hG hbM hb hu]; ring

lemma mem_S_or_I {b : V → ℤ} (hb : Biplane G b) {u : V} (hu : u ∉ Cset b) :
    (u ∈ Sset G b ∧ u ∉ Iset G b) ∨ (u ∈ Iset G b ∧ u ∉ Sset G b) := by
  have := (out_le_one hG hb hu).1
  simp only [Sset, Iset, mem_filter, mem_univ, true_and, hu, not_false_eq_true]
  omega

lemma card_S {b : V → ℤ} (hbM : IsM4 G b) (hb : Biplane G b) : (Sset G b).card = 70 := by
  have hcross := cross_nat (G := G) (Cset b) (Cset b)ᶜ
  have h1 : ∀ c ∈ Cset b, (G.neighborFinset c ∩ (Cset b)ᶜ).card = 10 := by
    intro c hc
    have h := nbC_card hG hbM hb c
    rw [if_pos hc] at h
    have hsum := Finset.card_inter_add_card_sdiff (G.neighborFinset c) (Cset b)
    rw [Finset.sdiff_eq_inter_compl, h, card_neighborFinset_eq_degree, hG.regular c] at hsum
    omega
  rw [Finset.sum_congr rfl h1, sum_const, card_C hG hb] at hcross
  have h2 : ∀ u ∈ (Cset b)ᶜ, (G.neighborFinset u ∩ Cset b).card
      = if u ∈ Sset G b then 2 else 0 := by
    intro u hu
    rw [mem_compl] at hu
    rw [nbC_card hG hbM hb u, if_neg hu]
    rcases mem_S_or_I hG hb hu with ⟨hS, _⟩ | ⟨hI, hS⟩
    · rw [if_pos hS]; simp only [Sset, mem_filter] at hS; rw [hS.2.2]
    · rw [if_neg hS]; simp only [Iset, mem_filter] at hI; rw [hI.2.2]
  rw [Finset.sum_congr rfl h2, Finset.sum_ite, sum_const_zero, add_zero, sum_const] at hcross
  have hSsub : (Cset b)ᶜ.filter (fun u => u ∈ Sset G b) = Sset G b := by
    ext u; simp only [mem_filter, mem_compl, Sset, mem_univ, true_and]; tauto
  rw [hSsub, smul_eq_mul, smul_eq_mul] at hcross
  omega

lemma card_I {b : V → ℤ} (hbM : IsM4 G b) (hb : Biplane G b) : (Iset G b).card = 15 := by
  have hpart : (Cset b) ∪ (Sset G b) ∪ (Iset G b) = univ := by
    ext u; simp only [mem_union, mem_univ, iff_true]
    by_cases hu : u ∈ Cset b
    · exact Or.inl (Or.inl hu)
    · rcases mem_S_or_I hG hb hu with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  have hd1 : Disjoint (Cset b) (Sset G b) := by
    rw [Finset.disjoint_left]; intro u hC hS; simp only [Sset, mem_filter] at hS; exact hS.2.1 hC
  have hd2 : Disjoint (Cset b ∪ Sset G b) (Iset G b) := by
    rw [Finset.disjoint_left]; intro u h hI
    simp only [Iset, mem_filter] at hI
    rcases mem_union.1 h with hC | hS
    · exact hI.2.1 hC
    · simp only [Sset, mem_filter] at hS; omega
  have := congrArg Finset.card hpart
  rw [card_union_of_disjoint hd2, card_union_of_disjoint hd1, card_C hG hb, card_S hG hbM hb,
    card_univ, card_V hG] at this
  omega

lemma I_no_C {b : V → ℤ} (hbM : IsM4 G b) (hb : Biplane G b) {i : V} (hi : i ∈ Iset G b) :
    (G.neighborFinset i ∩ Cset b).card = 0 := by
  have h := nbC_card hG hbM hb i
  simp only [Iset, mem_filter] at hi
  rw [if_neg hi.2.1, hi.2.2] at h; exact h

lemma C_not_adj_I {b : V → ℤ} (hbM : IsM4 G b) (hb : Biplane G b) {c i : V} (hc : c ∈ Cset b)
    (hi : i ∈ Iset G b) : ¬ G.Adj c i := by
  intro h
  have h0 := I_no_C hG hbM hb hi
  rw [card_eq_zero] at h0
  have : c ∈ G.neighborFinset i ∩ Cset b := mem_inter.2 ⟨(G.mem_neighborFinset i c).2 h.symm, hc⟩
  rw [h0] at this; simp at this

/-- `Σ_{w ∈ N(u)} |N(w) ∩ X| = Σ_{x ∈ X} |cn(u,x)|`. -/
lemma two_step (u : V) (X : Finset V) :
    ∑ w ∈ G.neighborFinset u, (G.neighborFinset w ∩ X).card = ∑ x ∈ X, (cn G u x).card := by
  have e1 : ∀ w, (G.neighborFinset w ∩ X).card = ∑ x ∈ X, (if G.Adj w x then 1 else 0) := by
    intro w; rw [Finset.sum_boole]; congr 1; ext x; simp [mem_neighborFinset, and_comm]
  have e2 : ∀ x, (cn G u x).card = ∑ w ∈ G.neighborFinset u, (if G.Adj w x then 1 else 0) := by
    intro x; rw [Finset.sum_boole]; congr 1; ext w
    simp [cn, mem_neighborFinset, G.adj_comm x w]
  simp_rw [e1, e2]
  exact Finset.sum_comm

lemma partCSI {b : V → ℤ} (hb : Biplane G b) (w : V) :
    (w ∈ Cset b ∧ w ∉ Sset G b ∧ w ∉ Iset G b) ∨ (w ∉ Cset b ∧ w ∈ Sset G b ∧ w ∉ Iset G b) ∨
      (w ∉ Cset b ∧ w ∉ Sset G b ∧ w ∈ Iset G b) := by
  by_cases hw : w ∈ Cset b
  · left; refine ⟨hw, ?_, ?_⟩ <;> simp [Sset, Iset, hw]
  · rcases mem_S_or_I hG hb hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨hw, h1, h2⟩)
    · exact Or.inr (Or.inr ⟨hw, h2, h1⟩)

lemma card_split {b : V → ℤ} (hb : Biplane G b) (X : Finset V) :
    X.card = (X ∩ Cset b).card + (X ∩ Sset G b).card + (X ∩ Iset G b).card := by
  have hd1 : Disjoint (X ∩ Cset b) (X ∩ Sset G b) := by
    rw [Finset.disjoint_left]; intro w h1 h2
    rcases partCSI hG hb w with h | h | h <;> simp_all
  have hd2 : Disjoint (X ∩ Cset b ∪ X ∩ Sset G b) (X ∩ Iset G b) := by
    rw [Finset.disjoint_left]; intro w h1 h2
    rcases partCSI hG hb w with h | h | h <;> simp_all
  rw [← card_union_of_disjoint hd1, ← card_union_of_disjoint hd2]
  congr 1; ext w
  simp only [mem_union, mem_inter]
  rcases partCSI hG hb w with h | h | h <;> tauto

/-- Neighbours in `I`: three for points of `S`, none for points of `I`. -/
lemma nbI {b : V → ℤ} (hbM : IsM4 G b) (hb : Biplane G b) {u : V} (hu : u ∉ Cset b) :
    (G.neighborFinset u ∩ Iset G b).card = if u ∈ Sset G b then 3 else 0 := by
  have hts := two_step hG u (Cset b)
  set k := (G.neighborFinset u ∩ Cset b).card with hk
  have hR : ∑ x ∈ Cset b, (cn G u x).card + k = 28 := by
    have hk' : k = ∑ x ∈ Cset b, (if G.Adj u x then 1 else 0) := by
      rw [hk, Finset.sum_boole]; congr 1; ext x; simp [mem_neighborFinset, and_comm]
    rw [hk', ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun x hx => (show (cn G u x).card + (if G.Adj u x then 1 else 0) = 2 by
      have hne : u ≠ x := fun h => hu (h ▸ hx)
      by_cases ha : G.Adj u x
      · rw [cn_adj hG ha, if_pos ha]
      · rw [cn_nadj hG hne ha, if_neg ha]))]
    rw [sum_const, card_C hG hb, smul_eq_mul]
  have hL : ∑ w ∈ G.neighborFinset u, (G.neighborFinset w ∩ Cset b).card
      = 4 * k + 2 * (G.neighborFinset u ∩ Sset G b).card := by
    have : ∀ w, (G.neighborFinset w ∩ Cset b).card
        = (if w ∈ Cset b then 4 else 0) + (if w ∈ Sset G b then 2 else 0) := by
      intro w
      rw [nbC_card hG hbM hb w]
      rcases partCSI hG hb w with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, h3⟩
      · simp [h1, h2]
      · simp only [Sset, mem_filter] at h2; simp [h1, Sset, h2.2.1, h2.2.2]
      · simp only [Iset, mem_filter] at h3; simp [h1, h2, h3.2.2]
    rw [Finset.sum_congr rfl (fun w _ => this w), Finset.sum_add_distrib, Finset.sum_ite_mem,
      Finset.sum_ite_mem, sum_const, sum_const, smul_eq_mul, smul_eq_mul, hk]
    ring
  have hdeg := card_split hG hb (G.neighborFinset u)
  rw [card_neighborFinset_eq_degree, hG.regular u] at hdeg
  have hkval := nbC_card hG hbM hb u
  rw [if_neg hu] at hkval
  have hp := (out_le_one hG hb hu).1
  split_ifs with hS
  · simp only [Sset, mem_filter] at hS
    rw [hS.2.2] at hkval
    omega
  · have hI : (G.neighborFinset u ∩ pos b).card = 0 := by
      simp only [Sset, mem_filter, mem_univ, true_and, not_and] at hS
      have := hS hu; omega
    rw [hI] at hkval
    omega

/-- `Σ_u |N(u) ∩ X| x_u = -4 Σ_X x` for a `-4` eigenvector `x`. -/
lemma sum_nb_weight {x : V → ℤ} (hx : IsM4 G x) (X : Finset V) :
    ∑ u, ((G.neighborFinset u ∩ X).card : ℤ) * x u = -4 * ∑ v ∈ X, x v := by
  have e1 : ∀ u, ((G.neighborFinset u ∩ X).card : ℤ) * x u
      = ∑ v ∈ X, (if G.Adj v u then x u else 0) := by
    intro u
    rw [card_inter_eq_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro v _
    by_cases h : G.Adj u v
    · rw [if_pos h, if_pos h.symm, one_mul]
    · rw [if_neg h, if_neg (fun h' => h h'.symm), zero_mul]
  simp_rw [e1]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro v _
  rw [← hx.apply v, ← Finset.sum_filter]
  congr 1; ext u; simp [mem_neighborFinset]

/-- `Σ_I x = 3 Σ_C x` for every `-4` eigenvector `x` (from (23)). -/
lemma sum_I_eq {b x : V → ℤ} (hbM : IsM4 G b) (hb : Biplane G b) (hx : IsM4 G x) :
    ∑ u ∈ Iset G b, x u = 3 * ∑ u ∈ Cset b, x u := by
  have hC := sum_nb_weight hG hx (Cset b)
  have hI := sum_nb_weight hG hx (Iset G b)
  have eC : ∀ u, ((G.neighborFinset u ∩ Cset b).card : ℤ) * x u
      = (if u ∈ Cset b then 4 * x u else 0) + (if u ∈ Sset G b then 2 * x u else 0) := by
    intro u
    rw [nbC_card hG hbM hb u]
    rcases partCSI hG hb u with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, h3⟩
    · simp [h1, h2]
    · simp only [Sset, mem_filter] at h2; simp [h1, Sset, h2.2.2]
    · simp only [Iset, mem_filter] at h3; simp [h1, h2, h3.2.2]
  have eI : ∀ u, ((G.neighborFinset u ∩ Iset G b).card : ℤ) * x u
      = if u ∈ Sset G b then 3 * x u else 0 := by
    intro u
    rcases partCSI hG hb u with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
    · have : (G.neighborFinset u ∩ Iset G b).card = 0 := by
        rw [card_eq_zero, eq_empty_iff_forall_notMem]; intro i hi
        rw [mem_inter, mem_neighborFinset] at hi
        exact C_not_adj_I hG hbM hb h1 hi.2 hi.1
      simp [this, h2]
    · rw [nbI hG hbM hb h1, if_pos h2, if_pos h2]; push_cast; ring
    · rw [nbI hG hbM hb h1, if_neg h2, if_neg h2]; simp
  simp_rw [eC] at hC
  simp_rw [eI] at hI
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem, univ_inter, univ_inter,
    ← Finset.mul_sum, ← Finset.mul_sum] at hC
  rw [Finset.sum_ite_mem, univ_inter, ← Finset.mul_sum] at hI
  linarith

/-- The canonical Hoffman coclique `H⁺ = P ∪ I`: size 22, coclique, nexus four. -/
lemma Hp_props {b : V → ℤ} (hbM : IsM4 G b) (hb : Biplane G b) :
    (Hp G b).card = 22 ∧ (∀ u ∈ Hp G b, ∀ v ∈ Hp G b, ¬ G.Adj u v) ∧
      (∀ u ∉ Hp G b, (G.neighborFinset u ∩ Hp G b).card = 4) := by
  have hd : Disjoint (pos b) (Iset G b) :=
    Finset.disjoint_of_subset_left (pos_sub_C b) (I_disj_C (G := G) b).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [Hp, card_union_of_disjoint hd, hb.card_pos, card_I hG hbM hb]
  · intro u hu v hv hadj
    rcases mem_union.1 hu with hu | hu <;> rcases mem_union.1 hv with hv | hv
    · exact hb.cocl_pos u hu v hv hadj
    · exact C_not_adj_I hG hbM hb (pos_sub_C b hu) hv hadj
    · exact C_not_adj_I hG hbM hb (pos_sub_C b hv) hu hadj.symm
    · have h0 := nbI hG hbM hb (Finset.disjoint_left.1 (I_disj_C b) hu)
      have hnS : u ∉ Sset G b := by
        simp only [Iset, mem_filter] at hu; simp only [Sset, mem_filter]; omega
      rw [if_neg hnS, card_eq_zero] at h0
      have : v ∈ G.neighborFinset u ∩ Iset G b :=
        mem_inter.2 ⟨(G.mem_neighborFinset u v).2 hadj, hv⟩
      rw [h0] at this; simp at this
  · intro u hu
    have hsplit : G.neighborFinset u ∩ Hp G b
        = (G.neighborFinset u ∩ pos b) ∪ (G.neighborFinset u ∩ Iset G b) := by
      rw [Hp, Finset.inter_union_distrib_left]
    rw [hsplit, card_union_of_disjoint (Finset.disjoint_of_subset_left inter_subset_right
      (Finset.disjoint_of_subset_right inter_subset_right hd))]
    rcases partCSI hG hb u with ⟨h1, _, _⟩ | ⟨h1, h2, _⟩ | ⟨_, _, h3⟩
    · have hn : u ∈ neg b := by
        rcases mem_union.1 h1 with h | h
        · exact absurd (mem_union.2 (Or.inl h)) hu
        · exact h
      rw [hb.four_neg u hn]
      have : (G.neighborFinset u ∩ Iset G b).card = 0 := by
        rw [card_eq_zero, eq_empty_iff_forall_notMem]; intro i hi
        rw [mem_inter, mem_neighborFinset] at hi
        exact C_not_adj_I hG hbM hb h1 hi.2 hi.1
      rw [this]
    · rw [nbI hG hbM hb h1, if_pos h2]
      simp only [Sset, mem_filter] at h2; rw [h2.2.2]
    · exact absurd (mem_union.2 (Or.inr h3)) hu

/-- The canonical Hoffman coclique `H⁻ = N ∪ I`. -/
lemma Hm_props {b : V → ℤ} (hbM : IsM4 G b) (hb : Biplane G b) :
    (Hm G b).card = 22 ∧ (∀ u ∈ Hm G b, ∀ v ∈ Hm G b, ¬ G.Adj u v) ∧
      (∀ u ∉ Hm G b, (G.neighborFinset u ∩ Hm G b).card = 4) := by
  have hb' := hb.neg'
  have hbM' := hbM.neg
  have hC : Cset (-b) = Cset b := by rw [Cset, Cset, pos_neg_neg, neg_neg_pos, union_comm]
  have hI : Iset G (-b) = Iset G b := by
    ext u; simp only [Iset, mem_filter, mem_univ, true_and, hC, pos_neg_neg]
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩
    · rw [out_eq hG hbM hb h1]; exact h2
    · rw [← out_eq hG hbM hb h1]; exact h2
  have : Hm G b = Hp G (-b) := by rw [Hm, Hp, pos_neg_neg, hI]
  rw [this]
  exact Hp_props hG hbM' hb'

end SRG

end Conway99
