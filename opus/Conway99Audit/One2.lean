import Conway99Audit.One1

/-!
# Part B, step 9b: the six profiles `s_D` and the restrictions (Rrestrictions) (§9.2)

For an ordered pair `k ≠ l` (each 2-set `D` is counted twice) put
`ℓ_{kl}(u) = 3[u = v] - [u ~ v] - b_k u - b_l u`.
Then `A ℓ = -4 ℓ - 2`, `Σ ℓ² = 23`, `ℓ ∈ {-1,0,1}`, so the profile budget applies:
at most two edges inside `B_{kl} = {ℓ = -1}`.  The `V`- and `W`-matchings already use
the whole budget, hence no other edge has both ends in some `B_{kl}`; this gives the
restrictions `V_i – R_jk ⇒ i = j`, `W_i – R_jk ⇒ i = k`, `R_ij – R_kl ⇒ j = k ∨ l = i`.
-/

open Finset SimpleGraph Matrix

namespace Conway99

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
def prof (b : Fin 4 → V → ℤ) (v : V) (k l : Fin 4) (u : V) : ℤ :=
  (if u = v then 3 else 0) - (if G.Adj u v then 1 else 0) - b k u - b l u

lemma exists_fourth (a j k : Fin 4) : ∃ m, m ≠ a ∧ m ≠ j ∧ m ≠ k := by
  revert a j k; decide

lemma count_V (a a' : Fin 4) (h : a ≠ a') :
    ((univ : Finset (Fin 4 × Fin 4)).filter (fun d => d.1 ≠ d.2 ∧
      ((d.1 ≠ a ∧ d.2 ≠ a) ∧ (d.1 ≠ a' ∧ d.2 ≠ a')))).card = 2 := by
  revert a a'; decide

lemma count_W (a a' : Fin 4) (h : a ≠ a') :
    ((univ : Finset (Fin 4 × Fin 4)).filter (fun d => d.1 ≠ d.2 ∧
      ((d.1 = a ∨ d.2 = a) ∧ (d.1 = a' ∨ d.2 = a')))).card = 2 := by
  revert a a'; decide

section SRG

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

namespace OneCfg

variable {b : Fin 4 → V → ℤ} {o v w : V} {R : Fin 4 → Fin 4 → V}

lemma prof_eig (C : OneCfg G b o v w R) (k l : Fin 4) (u : V) :
    ∑ x ∈ G.neighborFinset u, prof G b v k l x = -4 * prof G b v k l u - 2 := by
  have e1 : ∑ x ∈ G.neighborFinset u, (if x = v then (3 : ℤ) else 0)
      = if G.Adj u v then 3 else 0 := by
    rw [Finset.sum_ite_eq']; simp [mem_neighborFinset]
  have e2 : ∑ x ∈ G.neighborFinset u, (if G.Adj x v then (1 : ℤ) else 0) = (cn G u v).card := by
    rw [Finset.sum_boole]; congr 2; ext x; simp [cn, mem_neighborFinset, G.adj_comm]
  have e3 := (C.Q.m4 k).apply u
  have e4 := (C.Q.m4 l).apply u
  simp only [prof, Finset.sum_sub_distrib, e1, e2, e3, e4]
  by_cases huv : u = v
  · subst huv
    rw [show cn G u u = G.neighborFinset u by simp [cn], degree_eq hG]; simp; ring
  · by_cases ha : G.Adj u v
    · rw [cn_adj hG ha]; simp [huv, ha]; ring
    · rw [cn_nadj hG huv ha]; simp [huv, ha]; ring

lemma prof_sq (C : OneCfg G b o v w R) {k l : Fin 4} (hkl : k ≠ l) :
    ∑ u, prof G b v k l u * prof G b v k l u = 23 := by
  set e : V → ℤ := fun u => if u = v then 1 else 0 with he
  set a : V → ℤ := fun u => if G.Adj u v then 1 else 0 with ha
  have hp : ∀ u, prof G b v k l u = 3 * e u - a u - b k u - b l u := by
    intro u; simp only [prof, he, ha]; split_ifs <;> ring
  have hexp : ∀ u, prof G b v k l u * prof G b v k l u
      = 9 * (e u * e u) + a u * a u + b k u * b k u + b l u * b l u - 6 * (e u * a u)
        - 6 * (e u * b k u) - 6 * (e u * b l u) + 2 * (a u * b k u) + 2 * (a u * b l u)
        + 2 * (b k u * b l u) := by
    intro u; rw [hp]; ring
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have s1 : ∑ u, e u * e u = 1 := by simp [he]
  have s2 : ∑ u, a u * a u = 14 := by
    have : ∀ u, a u * a u = if G.Adj v u then 1 else 0 := by
      intro u; simp only [ha, G.adj_comm u v]; split_ifs <;> norm_num
    simp only [this]
    rw [Finset.sum_boole, ← neighborFinset_eq_filter, degree_eq hG]; rfl
  have s3 : ∑ u, b k u * b k u = 14 := (C.Q.bip k).norm
  have s4 : ∑ u, b l u * b l u = 14 := (C.Q.bip l).norm
  have s5 : ∑ u, e u * a u = 0 := by
    apply Finset.sum_eq_zero; intro x _
    by_cases h : x = v
    · subst h; simp [he, ha]
    · simp [he, h]
  have s6 : ∑ u, e u * b k u = 1 := by simp [he, C.v1 k]
  have s7 : ∑ u, e u * b l u = 1 := by simp [he, C.v1 l]
  have hnb : ∀ c : V → ℤ, ∑ u, a u * c u = ∑ u ∈ G.neighborFinset v, c u := by
    intro c
    simp only [ha, boole_mul]
    rw [← Finset.sum_filter]
    congr 1; ext u; simp [mem_neighborFinset, G.adj_comm]
  have s8 : ∑ u, a u * b k u = -4 := by rw [hnb, (C.Q.m4 k).apply v, C.v1 k]; norm_num
  have s9 : ∑ u, a u * b l u = -4 := by rw [hnb, (C.Q.m4 l).apply v, C.v1 l]; norm_num
  have s10 : ∑ u, b k u * b l u = 0 := C.Q.orth k l hkl
  rw [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10]; norm_num

lemma prof_Vs (C : OneCfg G b o v w R) (k l : Fin 4) {x : V} (hx : x ∈ Vs G o v w) :
    prof G b v k l x = -1 - b k x - b l x := by
  obtain ⟨-, -, hxv, -, hvx, -⟩ := C.Vs_props hG hx
  simp [prof, hxv, hvx.symm]

lemma prof_Ws (C : OneCfg G b o v w R) (k l : Fin 4) {x : V} (hx : x ∈ Ws G o v w) :
    prof G b v k l x = - b k x - b l x := by
  obtain ⟨-, -, hxv, -, -, -⟩ := C.Ws_props hG hx
  simp [prof, hxv, C.Ws_nadj_v hG hx]

lemma prof_R (C : OneCfg G b o v w R) (k l : Fin 4) {i j : Fin 4} (hij : i ≠ j) :
    prof G b v k l (R i j) = - b k (R i j) - b l (R i j) := by
  simp [prof, C.R_ne_v hG hij, C.R_nadj_v hG hij]

/-- Values of a coordinate of `R i j`. -/
lemma R_val (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) (k : Fin 4) :
    b k (R i j) = if k = i then 1 else if k = j then -1 else 0 := by
  split_ifs with h1 h2
  · subst h1; exact (C.R1 k j hij).1
  · subst h2; exact (C.R1 i k hij).2
  · exact C.R_zero hG hij h1 h2

lemma R_eq_one (C : OneCfg G b o v w R) {i j k : Fin 4} (hij : i ≠ j) (h : b k (R i j) = 1) :
    k = i := by
  by_contra hki
  by_cases hkj : k = j
  · subst hkj; rw [(C.R1 i k hij).2] at h; norm_num at h
  · rw [C.R_zero hG hij hki hkj] at h; norm_num at h

lemma R_eq_neg_one (C : OneCfg G b o v w R) {i j k : Fin 4} (hij : i ≠ j) (h : b k (R i j) = -1) :
    k = j := by
  by_contra hkj
  by_cases hki : k = i
  · subst hki; rw [(C.R1 k j hij).1] at h; norm_num at h
  · rw [C.R_zero hG hij hki hkj] at h; norm_num at h

lemma prof_vals (C : OneCfg G b o v w R) {k l : Fin 4} (hkl : k ≠ l) (u : V) :
    prof G b v k l u = 0 ∨ prof G b v k l u = 1 ∨ prof G b v k l u = -1 := by
  by_cases huW : u ∈ Wset G b
  · rcases C.classify hG huW with rfl | rfl | rfl | hV | hW | ⟨i, j, hij, rfl⟩
    · right; right; simp [prof, C.ov hG, C.ov_adj hG, C.oz]
    · right; left; simp [prof, C.v1]; try norm_num
    · right; left
      simp [prof, C.vw.symm, (C.vw_adj hG).symm, C.w1]; try norm_num
    · rw [C.prof_Vs hG k l hV]
      obtain ⟨a, ha, h0⟩ := C.Vs_label hG hV
      by_cases hka : k = a
      · subst hka; rw [ha, h0 l (Ne.symm hkl)]; norm_num
      · rw [h0 k hka]
        by_cases hla : l = a
        · subst hla; rw [ha]; norm_num
        · rw [h0 l hla]; norm_num
    · rw [C.prof_Ws hG k l hW]
      obtain ⟨a, ha, h0⟩ := C.Ws_label hG hW
      by_cases hka : k = a
      · subst hka; rw [ha, h0 l (Ne.symm hkl)]; norm_num
      · rw [h0 k hka]
        by_cases hla : l = a
        · subst hla; rw [ha]; norm_num
        · rw [h0 l hla]; norm_num
    · rw [C.prof_R hG k l hij]
      have hk := (C.Q.bip k).vals (R i j)
      have hl := (C.Q.bip l).vals (R i j)
      have h11 : ¬ (b k (R i j) = 1 ∧ b l (R i j) = 1) := by
        rintro ⟨h1, h2⟩
        exact hkl ((C.R_eq_one hG hij h1).trans (C.R_eq_one hG hij h2).symm)
      have h22 : ¬ (b k (R i j) = -1 ∧ b l (R i j) = -1) := by
        rintro ⟨h1, h2⟩
        exact hkl ((C.R_eq_neg_one hG hij h1).trans (C.R_eq_neg_one hG hij h2).symm)
      omega
  · -- `u` lies in some `I_i`: all coordinates vanish and `u` is not adjacent to `v`
    have h0 : ∀ i, b i u = 0 := by
      intro i
      by_contra h
      exact huW (C.Q.mem_W_of_C hG ((mem_C_iff (C.Q.bip i) u).2 h))
    have huv : u ≠ v := fun h => huW (h ▸ C.vW hG)
    have hna : ¬ G.Adj u v := fun h =>
      huW (C.nb_W_of_allC hG (C.vC hG) ((mem_neighborFinset _ _ _).2 h.symm))
    left; simp [prof, huv, hna, h0]

/-- The profile budget, for each of the twelve ordered pairs. -/
lemma prof_budget (C : OneCfg G b o v w R) {k l : Fin 4} (hkl : k ≠ l) :
    ((neg (prof G b v k l) ×ˢ neg (prof G b v k l)).filter (fun p => G.Adj p.1 p.2)).card ≤ 4 := by
  rw [card_adj_pairs]
  exact profile_budget hG _ (C.prof_vals hG hkl) (C.prof_eig hG k l) (C.prof_sq hG hkl)

lemma VV_card (C : OneCfg G b o v w R) :
    ((Vs G o v w ×ˢ Vs G o v w).filter (fun p => G.Adj p.1 p.2)).card = 12 := by
  rw [card_adj_pairs, Finset.sum_congr rfl (fun x hx => C.Vs_match hG hx), sum_const,
    C.card_Vs hG]; rfl

lemma WW_card (C : OneCfg G b o v w R) :
    ((Ws G o v w ×ˢ Ws G o v w).filter (fun p => G.Adj p.1 p.2)).card = 12 := by
  rw [card_adj_pairs, Finset.sum_congr rfl (fun x hx => C.Ws_match hG hx), sum_const,
    C.card_Ws hG]; rfl

lemma Vs_memB (C : OneCfg G b o v w R) {x : V} (hx : x ∈ Vs G o v w) {a : Fin 4}
    (ha : b a x = -1) (k l : Fin 4) (hkl : k ≠ l) :
    x ∈ neg (prof G b v k l) ↔ (k ≠ a ∧ l ≠ a) := by
  obtain ⟨a', ha', h0⟩ := C.Vs_label hG hx
  have haa : a = a' := by
    by_contra h; rw [h0 a h] at ha; norm_num at ha
  subst haa
  rw [mem_neg, C.prof_Vs hG k l hx]
  by_cases hka : k = a
  · subst hka; rw [ha, h0 l (Ne.symm hkl)]; simp
  · rw [h0 k hka]
    by_cases hla : l = a
    · subst hla; rw [ha]; simp
    · rw [h0 l hla]; simp [hka, hla]

lemma Ws_memB (C : OneCfg G b o v w R) {x : V} (hx : x ∈ Ws G o v w) {a : Fin 4}
    (ha : b a x = 1) (k l : Fin 4) (hkl : k ≠ l) :
    x ∈ neg (prof G b v k l) ↔ (k = a ∨ l = a) := by
  obtain ⟨a', ha', h0⟩ := C.Ws_label hG hx
  have haa : a = a' := by
    by_contra h; rw [h0 a h] at ha; norm_num at ha
  subst haa
  rw [mem_neg, C.prof_Ws hG k l hx]
  by_cases hka : k = a
  · subst hka; rw [ha, h0 l (Ne.symm hkl)]; simp
  · rw [h0 k hka]
    by_cases hla : l = a
    · subst hla; rw [ha]; simp
    · rw [h0 l hla]; simp [hka, hla]

/-- **Budget**: inside each `B_{kl}`, the only edges are matching edges. -/
theorem budget (C : OneCfg G b o v w R) {k l : Fin 4} (hkl : k ≠ l) {x y : V}
    (hx : x ∈ neg (prof G b v k l)) (hy : y ∈ neg (prof G b v k l)) (hxy : G.Adj x y) :
    (x ∈ Vs G o v w ∧ y ∈ Vs G o v w) ∨ (x ∈ Ws G o v w ∧ y ∈ Ws G o v w) := by
  by_contra hno
  set Dset : Finset (Fin 4 × Fin 4) := univ.filter (fun d => d.1 ≠ d.2) with hD
  set E : Fin 4 × Fin 4 → Finset (V × V) := fun d =>
    (neg (prof G b v d.1 d.2) ×ˢ neg (prof G b v d.1 d.2)).filter (fun p => G.Adj p.1 p.2) with hE
  set KK : Finset (V × V) := (Vs G o v w ×ˢ Vs G o v w).filter (fun p => G.Adj p.1 p.2) ∪
    (Ws G o v w ×ˢ Ws G o v w).filter (fun p => G.Adj p.1 p.2) with hKK
  set Pd : Fin 4 × Fin 4 → V × V → Prop := fun d p =>
    p.1 ∈ neg (prof G b v d.1 d.2) ∧ p.2 ∈ neg (prof G b v d.1 d.2) with hPd
  set K : Fin 4 × Fin 4 → Finset (V × V) := fun d => KK.filter (Pd d) with hK
  have hKKc : KK.card = 24 := by
    rw [hKK, card_union_of_disjoint, C.VV_card hG, C.WW_card hG]
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [mem_filter, mem_product] at h1 h2
    exact Finset.disjoint_left.1 (C.Vs_Ws_disj hG) h1.1.1 h2.1.1
  -- every known pair is counted twice
  have hcount : ∀ p ∈ KK, (Dset.filter (fun d => Pd d p)).card = 2 := by
    intro p hp
    rw [hKK, mem_union, mem_filter, mem_filter, mem_product, mem_product] at hp
    rcases hp with ⟨⟨h1, h2⟩, hadj⟩ | ⟨⟨h1, h2⟩, hadj⟩
    · obtain ⟨a, ha, _⟩ := C.Vs_label hG h1
      obtain ⟨a', ha', _⟩ := C.Vs_label hG h2
      have haa : a ≠ a' := by
        rintro rfl; exact (C.Q.bip a).nadj_neg ha ha' hadj
      rw [← count_V a a' haa, hD, filter_filter]
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro d _
      simp only [hPd]
      constructor
      · rintro ⟨hd, hp1, hp2⟩
        exact ⟨hd, (C.Vs_memB hG h1 ha d.1 d.2 hd).1 hp1, (C.Vs_memB hG h2 ha' d.1 d.2 hd).1 hp2⟩
      · rintro ⟨hd, hp1, hp2⟩
        exact ⟨hd, (C.Vs_memB hG h1 ha d.1 d.2 hd).2 hp1, (C.Vs_memB hG h2 ha' d.1 d.2 hd).2 hp2⟩
    · obtain ⟨a, ha, _⟩ := C.Ws_label hG h1
      obtain ⟨a', ha', _⟩ := C.Ws_label hG h2
      have haa : a ≠ a' := by
        rintro rfl; exact (C.Q.bip a).nadj_pos ha ha' hadj
      rw [← count_W a a' haa, hD, filter_filter]
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro d _
      simp only [hPd]
      constructor
      · rintro ⟨hd, hp1, hp2⟩
        exact ⟨hd, (C.Ws_memB hG h1 ha d.1 d.2 hd).1 hp1, (C.Ws_memB hG h2 ha' d.1 d.2 hd).1 hp2⟩
      · rintro ⟨hd, hp1, hp2⟩
        exact ⟨hd, (C.Ws_memB hG h1 ha d.1 d.2 hd).2 hp1, (C.Ws_memB hG h2 ha' d.1 d.2 hd).2 hp2⟩
  have hsumK : ∑ d ∈ Dset, (K d).card = 48 := by
    have : ∑ d ∈ Dset, (K d).card = ∑ p ∈ KK, (Dset.filter (fun d => Pd d p)).card := by
      simp only [hK, card_filter]
      exact Finset.sum_comm
    rw [this, Finset.sum_congr rfl hcount, sum_const, hKKc]; rfl
  have hKE : ∀ d ∈ Dset, K d ⊆ E d := by
    intro d _ p hp
    simp only [hK, hKK, hPd, mem_filter, mem_union, mem_product] at hp
    simp only [hE, mem_filter, mem_product]
    rcases hp.1 with h | h
    · exact ⟨⟨hp.2.1, hp.2.2⟩, h.2⟩
    · exact ⟨⟨hp.2.1, hp.2.2⟩, h.2⟩
  have hd0 : (k, l) ∈ Dset := by simp [hD, hkl]
  have hxyK : (x, y) ∉ KK := by
    intro h; simp only [hKK, mem_union, mem_filter, mem_product] at h
    rcases h with h | h
    · exact hno (Or.inl h.1)
    · exact hno (Or.inr h.1)
  have hyxK : (y, x) ∉ KK := by
    intro h; simp only [hKK, mem_union, mem_filter, mem_product] at h
    rcases h with h | h
    · exact hno (Or.inl ⟨h.1.2, h.1.1⟩)
    · exact hno (Or.inr ⟨h.1.2, h.1.1⟩)
  have hxy' : (x, y) ≠ (y, x) := by
    intro h; simp only [Prod.mk.injEq] at h; exact G.ne_of_adj hxy h.1
  have hsub0 : insert (x, y) (insert (y, x) (K (k, l))) ⊆ E (k, l) := by
    intro p hp
    rw [mem_insert, mem_insert] at hp
    rcases hp with rfl | rfl | hp
    · simp only [hE, mem_filter, mem_product]; exact ⟨⟨hx, hy⟩, hxy⟩
    · simp only [hE, mem_filter, mem_product]; exact ⟨⟨hy, hx⟩, hxy.symm⟩
    · exact hKE _ hd0 hp
  have hc0 : (K (k, l)).card + 2 ≤ (E (k, l)).card := by
    have := card_le_card hsub0
    rw [card_insert_of_notMem, card_insert_of_notMem] at this
    · omega
    · intro h; exact hyxK (mem_filter.1 h).1
    · rw [mem_insert]; push Not
      exact ⟨hxy', fun h => hxyK (mem_filter.1 h).1⟩
  have hsumE : ∑ d ∈ Dset, (E d).card ≤ 48 := by
    have : ∑ d ∈ Dset, (E d).card ≤ ∑ d ∈ Dset, 4 := by
      apply Finset.sum_le_sum; intro d hd
      have hd' : d.1 ≠ d.2 := (mem_filter.1 hd).2
      exact C.prof_budget hG hd'
    rw [sum_const] at this
    have hc : Dset.card = 12 := by rw [hD]; decide
    rw [hc] at this; simpa using this
  have hge : ∑ d ∈ Dset, (K d).card + 2 ≤ ∑ d ∈ Dset, (E d).card := by
    rw [← Finset.add_sum_erase _ _ hd0, ← Finset.add_sum_erase _ _ hd0]
    have : ∑ d ∈ Dset.erase (k, l), (K d).card ≤ ∑ d ∈ Dset.erase (k, l), (E d).card :=
      Finset.sum_le_sum (fun d hd => card_le_card (hKE d (mem_of_mem_erase hd)))
    omega
  omega

/-- `V_a – R_jk ⇒ j = a`. -/
lemma r2 (C : OneCfg G b o v w R) {x : V} (hx : x ∈ Vs G o v w) {a : Fin 4} (ha : b a x = -1)
    {j k : Fin 4} (hjk : j ≠ k) (hadj : G.Adj x (R j k)) : j = a := by
  by_contra hja
  have hka : k ≠ a := by
    rintro rfl; exact (C.Q.bip k).nadj_neg ha (C.R1 j k hjk).2 hadj
  obtain ⟨m, hma, hmj, hmk⟩ := exists_fourth a j k
  have hjm : j ≠ m := Ne.symm hmj
  have h1 : x ∈ neg (prof G b v j m) := (C.Vs_memB hG hx ha j m hjm).2 ⟨hja, hma⟩
  have h2 : R j k ∈ neg (prof G b v j m) := by
    rw [mem_neg, C.prof_R hG j m hjk, (C.R1 j k hjk).1, C.R_zero hG hjk hmj hmk]; norm_num
  rcases C.budget hG hjm h1 h2 hadj with h | h
  · exact C.R_not_Vs hG hjk h.2
  · exact C.R_not_Ws hG hjk h.2

/-- `W_a – R_jk ⇒ k = a`. -/
lemma r3 (C : OneCfg G b o v w R) {y : V} (hy : y ∈ Ws G o v w) {a : Fin 4} (ha : b a y = 1)
    {j k : Fin 4} (hjk : j ≠ k) (hadj : G.Adj y (R j k)) : k = a := by
  by_contra hka
  have hja : j ≠ a := by
    rintro rfl; exact (C.Q.bip j).nadj_pos ha (C.R1 j k hjk).1 hadj
  have haj : a ≠ j := Ne.symm hja
  have h1 : y ∈ neg (prof G b v a j) := (C.Ws_memB hG hy ha a j haj).2 (Or.inl rfl)
  have h2 : R j k ∈ neg (prof G b v a j) := by
    rw [mem_neg, C.prof_R hG a j hjk, (C.R1 j k hjk).1,
      C.R_zero hG hjk haj (Ne.symm hka)]; norm_num
  rcases C.budget hG haj h1 h2 hadj with h | h
  · exact C.R_not_Vs hG hjk h.2
  · exact C.R_not_Ws hG hjk h.2

/-- `R_ij – R_kl ⇒ j = k ∨ l = i`. -/
lemma r4 (C : OneCfg G b o v w R) {i j k l : Fin 4} (hij : i ≠ j) (hkl : k ≠ l)
    (hadj : G.Adj (R i j) (R k l)) : j = k ∨ l = i := by
  by_contra hno
  push Not at hno
  have hik : i ≠ k := by
    rintro rfl; exact (C.Q.bip i).nadj_pos (C.R1 i j hij).1 (C.R1 i l hkl).1 hadj
  have h1 : R i j ∈ neg (prof G b v i k) := by
    rw [mem_neg, C.prof_R hG i k hij, (C.R1 i j hij).1,
      C.R_zero hG hij (Ne.symm hik) (Ne.symm hno.1)]; norm_num
  have h2 : R k l ∈ neg (prof G b v i k) := by
    rw [mem_neg, C.prof_R hG i k hkl, (C.R1 k l hkl).1,
      C.R_zero hG hkl hik (Ne.symm hno.2)]; norm_num
  rcases C.budget hG hik h1 h2 hadj with h | h
  · exact C.R_not_Vs hG hij h.1
  · exact C.R_not_Ws hG hij h.1

end OneCfg

end SRG

end Conway99
