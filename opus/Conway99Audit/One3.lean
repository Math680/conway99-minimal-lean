import Conway99Audit.One2

/-!
# Part B, step 9c: the graph of the twelve arcs and the final contradiction (§§9.3–9.4)

* (Rgraph): `N_R(R_ij) = {R_ki, R_jk : k ∉ {i,j}}`, and `R_ij ≁ R_ji`;
* two arcs with the same origin, the same destination, or two consecutive arcs `R_ij, R_jk`
  have no common neighbour outside `W`;
* a neighbour `t ∈ I_a` of `o` sees exactly two arcs, which are opposite (`R_ij, R_ji`);
* the two common neighbours of `R_01` and `o` would then have the three common neighbours
  `o, R_01, R_10`.  Contradiction: `z = 1` is impossible (37).
-/

open Finset SimpleGraph Matrix

namespace Conway99

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma fin4_cover (a i j k l : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) (hkl : k ≠ l) : a = i ∨ a = j ∨ a = k ∨ a = l := by
  revert a i j k l; decide

section SRG

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

/-- Card of a three-element set of common neighbours. -/
lemma cn_three {x y p q r : V} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp : G.Adj x p ∧ G.Adj y p) (hq : G.Adj x q ∧ G.Adj y q) (hr : G.Adj x r ∧ G.Adj y r) :
    x = y := by
  by_contra hxy
  have hsub : ({p, q, r} : Finset V) ⊆ cn G x y := by
    intro z hz; rw [mem_insert, mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> rw [mem_cn] <;> assumption
  have hc := card_le_card hsub
  rw [card_insert_of_notMem (by simp [hpq, hpr]), card_pair hqr] at hc
  by_cases ha : G.Adj x y
  · rw [cn_adj hG ha] at hc; omega
  · rw [cn_nadj hG hxy ha] at hc; omega

lemma cn_two_adj {x y p q : V} (hxy : G.Adj x y) (hpq : p ≠ q)
    (hp : G.Adj x p ∧ G.Adj y p) (hq : G.Adj x q ∧ G.Adj y q) : False :=
  hpq (cn_unique hG hxy hp hq)

lemma Iset_neg {b : V → ℤ} (hbM : IsM4 G b) (hb : Biplane G b) : Iset G (-b) = Iset G b := by
  have hCC : Cset (-b) = Cset b := by rw [Cset, Cset, pos_neg_neg, neg_neg_pos, union_comm]
  ext u; simp only [Iset, mem_filter, mem_univ, true_and, hCC, pos_neg_neg]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩
  · rw [out_eq hG hbM hb h1]; exact h2
  · rw [← out_eq hG hbM hb h1]; exact h2

namespace OneCfg

variable {b : Fin 4 → V → ℤ} {o v w : V} {R : Fin 4 → Fin 4 → V}

lemma nbV_sub (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) :
    G.neighborFinset (R i j) ∩ Vs G o v w ⊆ Vs G o v w ∩ neg (b i) := by
  intro x hx
  rw [mem_inter, mem_neighborFinset] at hx
  obtain ⟨a, ha, _⟩ := C.Vs_label hG hx.2
  have := C.r2 hG hx.2 ha hij hx.1.symm
  subst this
  exact mem_inter.2 ⟨hx.2, mem_neg.2 ha⟩

lemma nbW_sub (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) :
    G.neighborFinset (R i j) ∩ Ws G o v w ⊆ Ws G o v w ∩ pos (b j) := by
  intro x hx
  rw [mem_inter, mem_neighborFinset] at hx
  obtain ⟨a, ha, _⟩ := C.Ws_label hG hx.2
  have := C.r3 hG hx.2 ha hij hx.1.symm
  subst this
  exact mem_inter.2 ⟨hx.2, mem_pos.2 ha⟩

lemma Rin_nb (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) :
    (G.neighborFinset (R i j) ∩ Rin R i).card = 2 := by
  have h4 := (C.Q.bip i).four_pos (R i j) (mem_pos.2 (C.R1 i j hij).1)
  rw [C.neg_eq hG i, Finset.inter_insert_of_notMem
    (fun h => C.R_nadj_w hG hij ((mem_neighborFinset _ _ _).1 h)),
    Finset.inter_union_distrib_left, card_union_of_disjoint] at h4
  · have e : G.neighborFinset (R i j) ∩ (Vs G o v w ∩ neg (b i))
        = G.neighborFinset (R i j) ∩ Vs G o v w := by
      ext x; constructor
      · intro hx; exact mem_inter.2 ⟨(mem_inter.1 hx).1, (mem_inter.1 (mem_inter.1 hx).2).1⟩
      · intro hx; exact mem_inter.2 ⟨(mem_inter.1 hx).1, C.nbV_sub hG hij hx⟩
    rw [e, C.R_Vs hG hij] at h4; omega
  · exact Finset.disjoint_of_subset_left inter_subset_right
      (Finset.disjoint_of_subset_right inter_subset_right
        (by
          rw [Finset.disjoint_left]; intro x hx hR
          obtain ⟨k, hk, rfl⟩ := mem_Rin.1 hR
          exact C.R_not_Vs hG hk (mem_inter.1 hx).1))

lemma Rout_nb (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) :
    (G.neighborFinset (R i j) ∩ Rout R j).card = 2 := by
  have h4 := (C.Q.bip j).four_neg (R i j) (mem_neg.2 (C.R1 i j hij).2)
  rw [C.pos_eq hG j, Finset.inter_insert_of_notMem
    (fun h => C.R_nadj_v hG hij ((mem_neighborFinset _ _ _).1 h)),
    Finset.inter_union_distrib_left, card_union_of_disjoint] at h4
  · have e : G.neighborFinset (R i j) ∩ (Ws G o v w ∩ pos (b j))
        = G.neighborFinset (R i j) ∩ Ws G o v w := by
      ext x; constructor
      · intro hx; exact mem_inter.2 ⟨(mem_inter.1 hx).1, (mem_inter.1 (mem_inter.1 hx).2).1⟩
      · intro hx; exact mem_inter.2 ⟨(mem_inter.1 hx).1, C.nbW_sub hG hij hx⟩
    rw [e, C.R_Ws hG hij] at h4; omega
  · exact Finset.disjoint_of_subset_left inter_subset_right
      (Finset.disjoint_of_subset_right inter_subset_right
        (by
          rw [Finset.disjoint_left]; intro x hx hR
          obtain ⟨k, hk, rfl⟩ := mem_Rout.1 hR
          exact C.R_not_Ws hG (Ne.symm hk) (mem_inter.1 hx).1))

lemma rest_card (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) :
    ((G.neighborFinset (R i j) ∩ Wset G b) \ (Vs G o v w ∪ Ws G o v w)).card = 4 := by
  have h8 := C.R_deg_W hG hij
  have hsplit := card_sdiff_add_card_inter (G.neighborFinset (R i j) ∩ Wset G b)
    (Vs G o v w ∪ Ws G o v w)
  have e : (G.neighborFinset (R i j) ∩ Wset G b) ∩ (Vs G o v w ∪ Ws G o v w)
      = (G.neighborFinset (R i j) ∩ Vs G o v w) ∪ (G.neighborFinset (R i j) ∩ Ws G o v w) := by
    ext x; simp only [mem_inter, mem_union]
    constructor
    · rintro ⟨⟨h1, _⟩, h3 | h3⟩
      · exact Or.inl ⟨h1, h3⟩
      · exact Or.inr ⟨h1, h3⟩
    · rintro (⟨h1, h3⟩ | ⟨h1, h3⟩)
      · exact ⟨⟨h1, (C.Vs_props hG h3).1⟩, Or.inl h3⟩
      · exact ⟨⟨h1, (C.Ws_props hG h3).1⟩, Or.inr h3⟩
  rw [e, card_union_of_disjoint (Finset.disjoint_of_subset_left inter_subset_right
    (Finset.disjoint_of_subset_right inter_subset_right (C.Vs_Ws_disj hG))),
    C.R_Vs hG hij, C.R_Ws hG hij, h8] at hsplit
  omega

lemma rest_sub (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) :
    (G.neighborFinset (R i j) ∩ Wset G b) \ (Vs G o v w ∪ Ws G o v w)
      ⊆ G.neighborFinset (R i j) ∩ (Rin R i ∪ Rout R j) := by
  intro z hz
  simp only [mem_sdiff, mem_inter, mem_union, not_or] at hz
  obtain ⟨⟨hzN, hzW⟩, hzV, hzWs⟩ := hz
  have hadj := (mem_neighborFinset _ _ _).1 hzN
  refine mem_inter.2 ⟨hzN, ?_⟩
  rcases C.classify hG hzW with rfl | rfl | rfl | h | h | ⟨k, l, hkl, rfl⟩
  · exact absurd hadj (C.R_nadj_o hG hij)
  · exact absurd hadj (C.R_nadj_v hG hij)
  · exact absurd hadj (C.R_nadj_w hG hij)
  · exact absurd h hzV
  · exact absurd h hzWs
  · rcases C.r4 hG hij hkl hadj with h | h
    · subst h; exact mem_union_right _ (mem_Rout.2 ⟨l, Ne.symm hkl, rfl⟩)
    · subst h; exact mem_union_left _ (mem_Rin.2 ⟨k, hkl, rfl⟩)

/-- `R_ij` and `R_ji` are not adjacent. -/
lemma rev_nadj (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) :
    ¬ G.Adj (R i j) (R j i) := by
  intro hadj
  have h1 := card_le_card (C.rest_sub hG hij)
  rw [C.rest_card hG hij, Finset.inter_union_distrib_left] at h1
  have hu := card_union_add_card_inter (G.neighborFinset (R i j) ∩ Rin R i)
    (G.neighborFinset (R i j) ∩ Rout R j)
  rw [C.Rin_nb hG hij, C.Rout_nb hG hij] at hu
  have hm : R j i ∈ (G.neighborFinset (R i j) ∩ Rin R i) ∩ (G.neighborFinset (R i j) ∩ Rout R j) := by
    refine mem_inter.2 ⟨mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 hadj, mem_Rin.2 ⟨j, Ne.symm hij, rfl⟩⟩,
      mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 hadj, mem_Rout.2 ⟨i, hij, rfl⟩⟩⟩
  have := card_pos.2 ⟨_, hm⟩
  omega

/-- (Rgraph), first half: `R_ki ∈ N(R_ij)` for `k ∉ {i,j}`. -/
lemma Rg1 (C : OneCfg G b o v w R) {i j k : Fin 4} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    G.Adj (R i j) (R k i) := by
  have hsub : G.neighborFinset (R i j) ∩ Rin R i ⊆ (Rin R i).erase (R j i) := by
    intro x hx
    rw [mem_inter] at hx
    refine mem_erase.2 ⟨?_, hx.2⟩
    rintro rfl; exact C.rev_nadj hG hij ((mem_neighborFinset _ _ _).1 hx.1)
  have hmem : R j i ∈ Rin R i := mem_Rin.2 ⟨j, Ne.symm hij, rfl⟩
  have heq := eq_of_subset_of_card_le hsub
    (by rw [card_erase_of_mem hmem, C.card_Rin hG, C.Rin_nb hG hij])
  have hk : R k i ∈ (Rin R i).erase (R j i) := by
    refine mem_erase.2 ⟨fun h => hkj (C.R_inj hG hki (Ne.symm hij) h).1, mem_Rin.2 ⟨k, hki, rfl⟩⟩
  rw [← heq] at hk
  exact (mem_neighborFinset _ _ _).1 (mem_inter.1 hk).1

/-- (Rgraph), second half: `R_jk ∈ N(R_ij)` for `k ∉ {i,j}`. -/
lemma Rg2 (C : OneCfg G b o v w R) {i j k : Fin 4} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    G.Adj (R i j) (R j k) := by
  have hsub : G.neighborFinset (R i j) ∩ Rout R j ⊆ (Rout R j).erase (R j i) := by
    intro x hx
    rw [mem_inter] at hx
    refine mem_erase.2 ⟨?_, hx.2⟩
    rintro rfl; exact C.rev_nadj hG hij ((mem_neighborFinset _ _ _).1 hx.1)
  have hmem : R j i ∈ Rout R j := mem_Rout.2 ⟨i, hij, rfl⟩
  have heq := eq_of_subset_of_card_le hsub
    (by rw [card_erase_of_mem hmem, C.card_Rout hG, C.Rout_nb hG hij])
  have hk : R j k ∈ (Rout R j).erase (R j i) := by
    refine mem_erase.2 ⟨fun h => hki (C.R_inj hG (Ne.symm hkj) (Ne.symm hij) h).2,
      mem_Rout.2 ⟨k, hkj, rfl⟩⟩
  rw [← heq] at hk
  exact (mem_neighborFinset _ _ _).1 (mem_inter.1 hk).1

lemma notW_ne (C : OneCfg G b o v w R) {t x : V} (ht : t ∉ Wset G b) (hx : x ∈ Wset G b) :
    x ≠ t := fun h => ht (h ▸ hx)

/-- Two arcs with the same origin have no common neighbour outside `W`. -/
lemma same_origin (C : OneCfg G b o v w R) {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) {t : V} (ht : t ∉ Wset G b) (h1 : G.Adj t (R i j)) (h2 : G.Adj t (R i k)) :
    False := by
  obtain ⟨m, hmi, hmj, hmk⟩ := exists_fourth i j k
  have hA := C.nbV_sub hG hij
  have hB := C.nbV_sub hG hik
  have hU := card_union_add_card_inter (G.neighborFinset (R i j) ∩ Vs G o v w)
    (G.neighborFinset (R i k) ∩ Vs G o v w)
  rw [C.R_Vs hG hij, C.R_Vs hG hik] at hU
  have hle := card_le_card (union_subset hA hB)
  rw [C.Vs_neg_card hG i] at hle
  obtain ⟨x, hx⟩ : ((G.neighborFinset (R i j) ∩ Vs G o v w) ∩
      (G.neighborFinset (R i k) ∩ Vs G o v w)).Nonempty := by
    rw [← card_pos]; omega
  simp only [mem_inter, mem_neighborFinset] at hx
  have hxVs := hx.1.2
  have hR : R m i ∈ Wset G b := C.R_W hG hmi
  have hne1 : x ≠ R m i := fun h => C.R_not_Vs hG hmi (h ▸ hxVs)
  have hne2 : x ≠ t := C.notW_ne hG ht (C.Vs_props hG hxVs).1
  have hne3 : R m i ≠ t := C.notW_ne hG ht hR
  have hRR : R i j = R i k := cn_three hG hne1 hne2 hne3 ⟨hx.1.1, hx.2.1⟩
    ⟨C.Rg1 hG hij hmi hmj, C.Rg1 hG hik hmi hmk⟩ ⟨h1.symm, h2.symm⟩
  exact hjk (C.R_inj hG hij hik hRR).2

/-- Two arcs with the same destination have no common neighbour outside `W`. -/
lemma same_dest (C : OneCfg G b o v w R) {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) {t : V} (ht : t ∉ Wset G b) (h1 : G.Adj t (R j i)) (h2 : G.Adj t (R k i)) :
    False := by
  obtain ⟨m, hmi, hmj, hmk⟩ := exists_fourth i j k
  have hA := C.nbW_sub hG (Ne.symm hij)
  have hB := C.nbW_sub hG (Ne.symm hik)
  have hU := card_union_add_card_inter (G.neighborFinset (R j i) ∩ Ws G o v w)
    (G.neighborFinset (R k i) ∩ Ws G o v w)
  rw [C.R_Ws hG (Ne.symm hij), C.R_Ws hG (Ne.symm hik)] at hU
  have hle := card_le_card (union_subset hA hB)
  rw [C.Ws_pos_card hG i] at hle
  obtain ⟨x, hx⟩ : ((G.neighborFinset (R j i) ∩ Ws G o v w) ∩
      (G.neighborFinset (R k i) ∩ Ws G o v w)).Nonempty := by
    rw [← card_pos]; omega
  simp only [mem_inter, mem_neighborFinset] at hx
  have hxWs := hx.1.2
  have hR : R i m ∈ Wset G b := C.R_W hG (Ne.symm hmi)
  have hne1 : x ≠ R i m := fun h => C.R_not_Ws hG (Ne.symm hmi) (h ▸ hxWs)
  have hne2 : x ≠ t := C.notW_ne hG ht (C.Ws_props hG hxWs).1
  have hne3 : R i m ≠ t := C.notW_ne hG ht hR
  have hRR : R j i = R k i := cn_three hG hne1 hne2 hne3 ⟨hx.1.1, hx.2.1⟩
    ⟨C.Rg2 hG (Ne.symm hij) hmj hmi, C.Rg2 hG (Ne.symm hik) hmk hmi⟩ ⟨h1.symm, h2.symm⟩
  exact hjk (C.R_inj hG (Ne.symm hij) (Ne.symm hik) hRR).1

/-- Two consecutive arcs `R_ij, R_jk` have no common neighbour outside `W` (λ = 1). -/
lemma consec (C : OneCfg G b o v w R) {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) {t : V} (ht : t ∉ Wset G b) (h1 : G.Adj t (R i j)) (h2 : G.Adj t (R j k)) :
    False :=
  cn_two_adj hG (C.Rg2 hG hij (Ne.symm hik) (Ne.symm hjk))
    (C.notW_ne hG ht (C.R_W hG (Ne.symm hik)))
    ⟨C.Rg1 hG hij (Ne.symm hik) (Ne.symm hjk), C.Rg2 hG hjk hij hik⟩
    ⟨h1.symm, h2.symm⟩

/-! ### Neighbours of `o` in the `I_a` -/

lemma I_notW (C : OneCfg G b o v w R) {a : Fin 4} {t : V} (ht : t ∈ Iset G (b a)) :
    t ∉ Wset G b := by
  intro h; exact Quad.not_I_of_W hG h a ht

lemma I_nadj_C (C : OneCfg G b o v w R) {a : Fin 4} {t x : V} (ht : t ∈ Iset G (b a))
    (hx : x ∈ Cset (b a)) : ¬ G.Adj t x :=
  fun h => C_not_adj_I hG (C.Q.m4 a) (C.Q.bip a) hx ht h.symm

lemma I_nadj_R (C : OneCfg G b o v w R) {a : Fin 4} {t : V} (ht : t ∈ Iset G (b a))
    {x y : Fin 4} (hxy : x ≠ y) (h : a = x ∨ a = y) : ¬ G.Adj t (R x y) := by
  apply C.I_nadj_C hG ht
  rw [mem_C_iff (C.Q.bip a)]
  rcases h with rfl | rfl
  · rw [(C.R1 a y hxy).1]; norm_num
  · rw [(C.R1 x a hxy).2]; norm_num

lemma I_degW (C : OneCfg G b o v w R) {a : Fin 4} {t : V} (ht : t ∈ Iset G (b a)) :
    (G.neighborFinset t ∩ Wset G b).card = 5 := by
  have hsplit := Quad.card_nb_split hG (b := b) t
  have hcoc := (Hp_props hG (C.Q.m4 a) (C.Q.bip a)).2.1
  have hI : ∀ c, (G.neighborFinset t ∩ Iset G (b c)).card = if c = a then 0 else 3 := by
    intro c
    split_ifs with hca
    · subst hca
      rw [card_eq_zero, eq_empty_iff_forall_notMem]
      intro x hx; rw [mem_inter, mem_neighborFinset] at hx
      exact hcoc t (mem_union_right _ ht) x (mem_union_right _ hx.2) hx.1
    · have hnC : t ∉ Cset (b c) := fun h => Finset.disjoint_left.1 (C.Q.C_disj_I hG c a) h ht
      have hnI : t ∉ Iset G (b c) := fun h => Finset.disjoint_left.1 (C.Q.I_disj hG hca) h ht
      rw [nbI hG (C.Q.m4 c) (C.Q.bip c) hnC]
      rcases mem_S_or_I hG (C.Q.bip c) hnC with ⟨h, _⟩ | ⟨h, _⟩
      · rw [if_pos h]
      · exact absurd h hnI
  rw [C.Q.nbIall hG t, Finset.sum_congr rfl (fun c _ => hI c)] at hsplit
  have : ∑ c : Fin 4, (if c = a then 0 else 3) = 9 := by fin_cases a <;> simp [Fin.sum_univ_four]
  omega

lemma I_Vs (C : OneCfg G b o v w R) {a : Fin 4} {t : V} (ht : t ∈ Iset G (b a))
    (hto : G.Adj t o) : (G.neighborFinset t ∩ Vs G o v w).card = 1 := by
  have htv : ¬ G.Adj t v := C.I_nadj_C hG ht (C.vC hG a)
  have htw : ¬ G.Adj t w := C.I_nadj_C hG ht (C.wC hG a)
  have hne : t ≠ v := fun h => C.I_notW hG ht (h ▸ C.vW hG)
  have h2 := cn_nadj hG hne htv
  have he : cn G t v = insert o (G.neighborFinset t ∩ Vs G o v w) := by
    ext y; simp only [mem_cn, mem_insert, mem_inter, mem_neighborFinset, mem_Vs]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hyo : y = o
      · exact Or.inl hyo
      · refine Or.inr ⟨h1, h2, hyo, ?_⟩
        rintro rfl; exact htw h1
    · rintro (rfl | ⟨h1, h2, _, _⟩)
      · exact ⟨hto, (C.ov_adj hG).symm⟩
      · exact ⟨h1, h2⟩
  rw [he, card_insert_of_notMem (fun h => (mem_Vs.1 (mem_inter.1 h).2).2.1 rfl)] at h2
  omega

lemma I_Ws (C : OneCfg G b o v w R) {a : Fin 4} {t : V} (ht : t ∈ Iset G (b a))
    (hto : G.Adj t o) : (G.neighborFinset t ∩ Ws G o v w).card = 1 := by
  have htv : ¬ G.Adj t v := C.I_nadj_C hG ht (C.vC hG a)
  have htw : ¬ G.Adj t w := C.I_nadj_C hG ht (C.wC hG a)
  have hne : t ≠ w := fun h => C.I_notW hG ht (h ▸ C.wW hG)
  have h2 := cn_nadj hG hne htw
  have he : cn G t w = insert o (G.neighborFinset t ∩ Ws G o v w) := by
    ext y; simp only [mem_cn, mem_insert, mem_inter, mem_neighborFinset, mem_Ws]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hyo : y = o
      · exact Or.inl hyo
      · refine Or.inr ⟨h1, h2, hyo, ?_⟩
        rintro rfl; exact htv h1
    · rintro (rfl | ⟨h1, h2, _, _⟩)
      · exact ⟨hto, (C.ow_adj hG).symm⟩
      · exact ⟨h1, h2⟩
  rw [he, card_insert_of_notMem (fun h => (mem_Ws.1 (mem_inter.1 h).2).2.1 rfl)] at h2
  omega

/-- A neighbour `t ∈ I_a` of `o` adjacent to `R_ij` is adjacent to `R_ji`. -/
lemma I_rev (C : OneCfg G b o v w R) {a : Fin 4} {t : V} (ht : t ∈ Iset G (b a))
    (hto : G.Adj t o) {i j : Fin 4} (hij : i ≠ j) (hadj : G.Adj t (R i j)) :
    G.Adj t (R j i) := by
  have htW := C.I_notW hG ht
  set X := ((G.neighborFinset t ∩ Wset G b) \ (Vs G o v w ∪ Ws G o v w)).erase o with hX
  have hsplit := card_sdiff_add_card_inter (G.neighborFinset t ∩ Wset G b)
    (Vs G o v w ∪ Ws G o v w)
  have e : (G.neighborFinset t ∩ Wset G b) ∩ (Vs G o v w ∪ Ws G o v w)
      = (G.neighborFinset t ∩ Vs G o v w) ∪ (G.neighborFinset t ∩ Ws G o v w) := by
    ext x; simp only [mem_inter, mem_union]
    constructor
    · rintro ⟨⟨h1, _⟩, h3 | h3⟩
      · exact Or.inl ⟨h1, h3⟩
      · exact Or.inr ⟨h1, h3⟩
    · rintro (⟨h1, h3⟩ | ⟨h1, h3⟩)
      · exact ⟨⟨h1, (C.Vs_props hG h3).1⟩, Or.inl h3⟩
      · exact ⟨⟨h1, (C.Ws_props hG h3).1⟩, Or.inr h3⟩
  rw [e, card_union_of_disjoint (Finset.disjoint_of_subset_left inter_subset_right
    (Finset.disjoint_of_subset_right inter_subset_right (C.Vs_Ws_disj hG))),
    C.I_Vs hG ht hto, C.I_Ws hG ht hto, C.I_degW hG ht] at hsplit
  have hoX : o ∈ (G.neighborFinset t ∩ Wset G b) \ (Vs G o v w ∪ Ws G o v w) := by
    simp only [mem_sdiff, mem_inter, mem_union, mem_neighborFinset, not_or]
    exact ⟨⟨hto, C.oW⟩, fun h => (mem_Vs.1 h).2.1 rfl, fun h => (mem_Ws.1 h).2.1 rfl⟩
  have hXc : X.card = 2 := by rw [hX, card_erase_of_mem hoX]; omega
  have hRX : R i j ∈ X := by
    rw [hX, mem_erase]
    refine ⟨C.R_ne_o hG hij, ?_⟩
    simp only [mem_sdiff, mem_inter, mem_union, mem_neighborFinset, not_or]
    exact ⟨⟨hadj, C.R_W hG hij⟩, C.R_not_Vs hG hij, C.R_not_Ws hG hij⟩
  obtain ⟨z, hzX, hzne⟩ : ∃ z ∈ X, z ≠ R i j := by
    obtain ⟨p, q, hpq, hpqX⟩ := card_eq_two.1 hXc
    rw [hpqX, mem_insert, mem_singleton] at hRX
    rcases hRX with h | h
    · exact ⟨q, by rw [hpqX]; simp, fun hq => hpq (h.symm.trans hq.symm)⟩
    · exact ⟨p, by rw [hpqX]; simp, fun hp => hpq (hp.trans h)⟩
  rw [hX, mem_erase] at hzX
  obtain ⟨hzo, hz⟩ := hzX
  simp only [mem_sdiff, mem_inter, mem_union, mem_neighborFinset, not_or] at hz
  obtain ⟨⟨hzadj, hzW⟩, hzV, hzWs⟩ := hz
  have hai : a ≠ i := fun h => C.I_nadj_R hG ht hij (Or.inl h) hadj
  have haj : a ≠ j := fun h => C.I_nadj_R hG ht hij (Or.inr h) hadj
  rcases C.classify hG hzW with h | h | h | h | h | ⟨k, l, hkl, rfl⟩
  · exact absurd h hzo
  · subst h; exact absurd hzadj (C.I_nadj_C hG ht (C.vC hG a))
  · subst h; exact absurd hzadj (C.I_nadj_C hG ht (C.wC hG a))
  · exact absurd h hzV
  · exact absurd h hzWs
  · have hak : a ≠ k := fun h => C.I_nadj_R hG ht hkl (Or.inl h) hzadj
    have hal : a ≠ l := fun h => C.I_nadj_R hG ht hkl (Or.inr h) hzadj
    by_cases hki : k = i
    · subst hki
      have hjl : j ≠ l := fun h => hzne (by rw [h])
      exact (C.same_origin hG hij hkl hjl htW hadj hzadj).elim
    by_cases hlj : l = j
    · subst hlj
      exact (C.same_dest hG (Ne.symm hij) (Ne.symm hkl) (Ne.symm hki) htW hadj hzadj).elim
    by_cases hkj : k = j
    · subst hkj
      by_cases hli : l = i
      · subst hli; exact hzadj
      · exact (C.consec hG hij (Ne.symm hli) (hkl) htW hadj hzadj).elim
    by_cases hli : l = i
    · subst hli
      exact (C.consec hG hkl hkj hij htW hzadj hadj).elim
    exfalso
    rcases fin4_cover a i j k l hij (Ne.symm hki) (Ne.symm hli) (Ne.symm hkj) (Ne.symm hlj) hkl
      with h | h | h | h
    · exact hai h
    · exact haj h
    · exact hak h
    · exact hal h

/-- **(37): the configuration `z = 1` is impossible.** -/
theorem contra (C : OneCfg G b o v w R) : False := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h2 := cn_nadj hG (C.R_ne_o hG h01) (C.R_nadj_o hG h01)
  obtain ⟨t, t', htt, hset⟩ := card_eq_two.1 h2
  have hmem : ∀ s ∈ cn G (R 0 1) o, G.Adj s o ∧ G.Adj s (R 0 1) ∧ G.Adj s (R 1 0) := by
    intro s hs
    rw [mem_cn] at hs
    have hsW : s ∉ Wset G b := by
      intro hW
      have : s ∈ G.neighborFinset o ∩ Wset G b := mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 hs.2, hW⟩
      rw [C.onb, mem_insert, mem_singleton] at this
      rcases this with rfl | rfl
      · exact C.R_nadj_v hG h01 hs.1
      · exact C.R_nadj_w hG h01 hs.1
    have hsI : s ∈ Iall G b := by
      by_contra h; exact hsW (by rw [Wset, mem_sdiff]; exact ⟨mem_univ _, h⟩)
    rw [Iall, mem_biUnion] at hsI
    obtain ⟨a, _, ha⟩ := hsI
    exact ⟨hs.2.symm, hs.1.symm, C.I_rev hG ha hs.2.symm h01 hs.1.symm⟩
  have ht := hmem t (by rw [hset]; simp)
  have ht' := hmem t' (by rw [hset]; simp)
  have hne1 : o ≠ R 0 1 := (C.R_ne_o hG h01).symm
  have hne2 : o ≠ R 1 0 := (C.R_ne_o hG (Ne.symm h01)).symm
  have hne3 : R 0 1 ≠ R 1 0 := fun h => h01 (C.R_inj hG h01 (Ne.symm h01) h).1
  exact htt (cn_three hG hne1 hne2 hne3 ⟨ht.1, ht'.1⟩ ⟨ht.2.1, ht'.2.1⟩ ⟨ht.2.2, ht'.2.2⟩)

end OneCfg

end SRG

end Conway99
