import Conway99Audit.Profile

/-!
# Part B, step 9a: the configuration around the zero point (§9.1)

`OneCfg G b o v w R`: four orthogonal roots, the zero point `o ∈ W`, its two `W`-neighbours
`v` (all signs `+`) and `w` (all signs `-`), every other point of `W` of weight 1 or 2, and
`R i j` a point with `b_i = 1`, `b_j = -1` (the cell of the ordered pair `(i,j)`).

We derive: `v ~ w`; `Vs = N(v) \ {o,w}` consists of 12 points of weight 1 and negative sign,
`Ws = N(w) \ {o,v}` of 12 points of weight 1 and positive sign; `R i j` has weight 2;
`P_i = {v} ∪ W_i ∪ {R_ij}`, `N_i = {w} ∪ V_i ∪ {R_ji}`; every point of `W` is
`o, v, w`, in `Vs`, in `Ws` or some `R i j`; perfect matchings `V–V`, `W–W`, `V–W`;
each `R i j` has two neighbours in `Vs` and two in `Ws`.
-/

open Finset SimpleGraph Matrix

namespace Conway99

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- The configuration of §9.1 (roots oriented so that `v` has all signs `+`). -/
structure OneCfg (b : Fin 4 → V → ℤ) (o v w : V) (R : Fin 4 → Fin 4 → V) : Prop where
  Q : Quad G b
  oW : o ∈ Wset G b
  oz : ∀ i, b i o = 0
  vw : v ≠ w
  onb : G.neighborFinset o ∩ Wset G b = {v, w}
  v1 : ∀ i, b i v = 1
  w1 : ∀ i, b i w = -1
  cov : ∀ u ∈ Wset G b, u ≠ o → u ≠ v → u ≠ w → wt b u = 1 ∨ wt b u = 2
  R1 : ∀ i j, i ≠ j → b i (R i j) = 1 ∧ b j (R i j) = -1

variable (G) in
def Vs (o v w : V) : Finset V := G.neighborFinset v \ {o, w}

variable (G) in
def Ws (o v w : V) : Finset V := G.neighborFinset w \ {o, v}

def Rin (R : Fin 4 → Fin 4 → V) (i : Fin 4) : Finset V := (univ.erase i).image (fun k => R k i)

def Rout (R : Fin 4 → Fin 4 → V) (i : Fin 4) : Finset V := (univ.erase i).image (fun k => R i k)

lemma wt_ge {b : Fin 4 → V → ℤ} {x : V} (s : Finset (Fin 4)) (h : ∀ i ∈ s, x ∈ Cset (b i)) :
    (s.card : ℤ) ≤ wt b x := by
  rw [wt]
  calc (s.card : ℤ) = ∑ i ∈ s, (if x ∈ Cset (b i) then (1 : ℤ) else 0) := by
        rw [Finset.sum_congr rfl (fun i hi => if_pos (h i hi))]; simp
    _ ≤ ∑ i, (if x ∈ Cset (b i) then (1 : ℤ) else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
          (fun i _ _ => by split_ifs <;> norm_num)

lemma Biplane.nadj_pos {b : V → ℤ} (hb : Biplane G b) {x y : V} (hx : b x = 1) (hy : b y = 1) :
    ¬ G.Adj x y := hb.cocl_pos x (mem_pos.2 hx) y (mem_pos.2 hy)

lemma Biplane.nadj_neg {b : V → ℤ} (hb : Biplane G b) {x y : V} (hx : b x = -1) (hy : b y = -1) :
    ¬ G.Adj x y := hb.cocl_neg x (mem_neg.2 hx) y (mem_neg.2 hy)

lemma mem_Vs {o v w x : V} : x ∈ Vs G o v w ↔ G.Adj v x ∧ x ≠ o ∧ x ≠ w := by
  simp [Vs, mem_sdiff, mem_neighborFinset, not_or]

lemma mem_Ws {o v w x : V} : x ∈ Ws G o v w ↔ G.Adj w x ∧ x ≠ o ∧ x ≠ v := by
  simp [Ws, mem_sdiff, mem_neighborFinset, not_or]

lemma mem_Rin {R : Fin 4 → Fin 4 → V} {i : Fin 4} {x : V} : x ∈ Rin R i ↔ ∃ k, k ≠ i ∧ R k i = x := by
  simp [Rin]

lemma mem_Rout {R : Fin 4 → Fin 4 → V} {i : Fin 4} {x : V} : x ∈ Rout R i ↔ ∃ k, k ≠ i ∧ R i k = x := by
  simp [Rout]

section SRG

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

namespace OneCfg

variable {b : Fin 4 → V → ℤ} {o v w : V} {R : Fin 4 → Fin 4 → V}

lemma vC (C : OneCfg G b o v w R) (i : Fin 4) : v ∈ Cset (b i) :=
  (mem_C_iff (C.Q.bip i) v).2 (by rw [C.v1 i]; norm_num)

lemma wC (C : OneCfg G b o v w R) (i : Fin 4) : w ∈ Cset (b i) :=
  (mem_C_iff (C.Q.bip i) w).2 (by rw [C.w1 i]; norm_num)

lemma oC (C : OneCfg G b o v w R) (i : Fin 4) : o ∉ Cset (b i) :=
  fun h => (mem_C_iff (C.Q.bip i) o).1 h (C.oz i)

lemma vW (C : OneCfg G b o v w R) : v ∈ Wset G b := C.Q.mem_W_of_C hG (C.vC hG 0)

lemma wW (C : OneCfg G b o v w R) : w ∈ Wset G b := C.Q.mem_W_of_C hG (C.wC hG 0)

lemma ov (C : OneCfg G b o v w R) : o ≠ v := by
  intro h; have := C.oz 0; rw [h, C.v1 0] at this; norm_num at this

lemma ow (C : OneCfg G b o v w R) : o ≠ w := by
  intro h; have := C.oz 0; rw [h, C.w1 0] at this; norm_num at this

lemma nb_W_of_allC (C : OneCfg G b o v w R) {x : V} (hx : ∀ k, x ∈ Cset (b k)) :
    G.neighborFinset x ⊆ Wset G b := by
  intro y hy
  rw [Wset, mem_sdiff, Iall, mem_biUnion]
  refine ⟨mem_univ _, ?_⟩
  rintro ⟨k, _, hk⟩
  exact C_not_adj_I hG (C.Q.m4 k) (C.Q.bip k) (hx k) hk ((mem_neighborFinset _ _ _).1 hy)

lemma o_nadj (C : OneCfg G b o v w R) {x : V} (hx : x ∈ Wset G b) (hxv : x ≠ v) (hxw : x ≠ w) :
    ¬ G.Adj o x := by
  intro h
  have : x ∈ G.neighborFinset o ∩ Wset G b := mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 h, hx⟩
  rw [C.onb, mem_insert, mem_singleton] at this
  rcases this with h1 | h1
  · exact hxv h1
  · exact hxw h1

lemma ov_adj (C : OneCfg G b o v w R) : G.Adj o v := by
  have : v ∈ G.neighborFinset o ∩ Wset G b := by rw [C.onb]; simp
  exact (mem_neighborFinset _ _ _).1 (mem_inter.1 this).1

lemma ow_adj (C : OneCfg G b o v w R) : G.Adj o w := by
  have : w ∈ G.neighborFinset o ∩ Wset G b := by rw [C.onb]; simp
  exact (mem_neighborFinset _ _ _).1 (mem_inter.1 this).1

lemma zero_eq (C : OneCfg G b o v w R) {x : V} (hx : x ∈ Wset G b) (h0 : ∀ i, b i x = 0) :
    x = o := by
  by_contra hxo
  have hxv : x ≠ v := by intro h; have := h0 0; rw [h, C.v1 0] at this; norm_num at this
  have hxw : x ≠ w := by intro h; have := h0 0; rw [h, C.w1 0] at this; norm_num at this
  have hC : ∀ i, x ∉ Cset (b i) := fun i h => (mem_C_iff (C.Q.bip i) x).1 h (h0 i)
  rcases C.cov x hx hxo hxv hxw with h | h <;> rw [wt_eq_zero hC] at h <;> norm_num at h

/-- `v` and `w` are adjacent: their only possible common neighbour is `o`. -/
lemma vw_adj (C : OneCfg G b o v w R) : G.Adj v w := by
  by_contra hna
  have h2 := cn_nadj hG C.vw hna
  have hsub : cn G v w ⊆ {o} := by
    intro x hx
    rw [mem_cn] at hx
    have hxW : x ∈ Wset G b :=
      C.nb_W_of_allC hG (C.vC hG) ((mem_neighborFinset _ _ _).2 hx.1)
    have h0 : ∀ i, b i x = 0 := by
      intro i
      rcases (C.Q.bip i).vals x with h | h | h
      · exact h
      · exact absurd hx.1 ((C.Q.bip i).nadj_pos (C.v1 i) h)
      · exact absurd hx.2 ((C.Q.bip i).nadj_neg (C.w1 i) h)
    rw [mem_singleton]; exact C.zero_eq hG hxW h0
  have := card_le_card hsub
  rw [h2, card_singleton] at this
  norm_num at this

lemma Vs_props (C : OneCfg G b o v w R) {x : V} (hx : x ∈ Vs G o v w) :
    x ∈ Wset G b ∧ x ≠ o ∧ x ≠ v ∧ x ≠ w ∧ G.Adj v x ∧ ∀ i, b i x = 0 ∨ b i x = -1 := by
  rw [mem_Vs] at hx
  refine ⟨C.nb_W_of_allC hG (C.vC hG) ((mem_neighborFinset _ _ _).2 hx.1), hx.2.1,
    fun h => by rw [h] at hx; exact G.irrefl hx.1, hx.2.2, hx.1, fun i => ?_⟩
  rcases (C.Q.bip i).vals x with h | h | h
  · exact Or.inl h
  · exact absurd hx.1 ((C.Q.bip i).nadj_pos (C.v1 i) h)
  · exact Or.inr h

lemma Ws_props (C : OneCfg G b o v w R) {x : V} (hx : x ∈ Ws G o v w) :
    x ∈ Wset G b ∧ x ≠ o ∧ x ≠ v ∧ x ≠ w ∧ G.Adj w x ∧ ∀ i, b i x = 0 ∨ b i x = 1 := by
  rw [mem_Ws] at hx
  refine ⟨C.nb_W_of_allC hG (C.wC hG) ((mem_neighborFinset _ _ _).2 hx.1), hx.2.1, hx.2.2,
    fun h => by rw [h] at hx; exact G.irrefl hx.1, hx.1, fun i => ?_⟩
  rcases (C.Q.bip i).vals x with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd hx.1 ((C.Q.bip i).nadj_neg (C.w1 i) h)

lemma card_Vs (C : OneCfg G b o v w R) : (Vs G o v w).card = 12 := by
  rw [Vs, card_sdiff_of_subset, degree_eq hG, card_pair (C.ow hG)]
  intro x hx
  rw [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact (mem_neighborFinset _ _ _).2 (C.ov_adj hG).symm
  · exact (mem_neighborFinset _ _ _).2 (C.vw_adj hG)

lemma card_Ws (C : OneCfg G b o v w R) : (Ws G o v w).card = 12 := by
  rw [Ws, card_sdiff_of_subset, degree_eq hG, card_pair (C.ov hG)]
  intro x hx
  rw [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact (mem_neighborFinset _ _ _).2 (C.ow_adj hG).symm
  · exact (mem_neighborFinset _ _ _).2 (C.vw_adj hG).symm

lemma Vs_neg_card (C : OneCfg G b o v w R) (i : Fin 4) : (Vs G o v w ∩ neg (b i)).card = 3 := by
  have h4 := (C.Q.bip i).four_pos v (mem_pos.2 (C.v1 i))
  have he : Vs G o v w ∩ neg (b i) = (G.neighborFinset v ∩ neg (b i)).erase w := by
    ext x; simp only [mem_inter, mem_erase, mem_Vs, mem_neighborFinset, mem_neg]
    constructor
    · rintro ⟨⟨h1, _, h3⟩, h4⟩; exact ⟨h3, h1, h4⟩
    · rintro ⟨h3, h1, h4⟩
      refine ⟨⟨h1, ?_, h3⟩, h4⟩
      rintro rfl; rw [C.oz i] at h4; norm_num at h4
  rw [he, card_erase_of_mem, h4]
  exact mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 (C.vw_adj hG), mem_neg.2 (C.w1 i)⟩

lemma Ws_pos_card (C : OneCfg G b o v w R) (i : Fin 4) : (Ws G o v w ∩ pos (b i)).card = 3 := by
  have h4 := (C.Q.bip i).four_neg w (mem_neg.2 (C.w1 i))
  have he : Ws G o v w ∩ pos (b i) = (G.neighborFinset w ∩ pos (b i)).erase v := by
    ext x; simp only [mem_inter, mem_erase, mem_Ws, mem_neighborFinset, mem_pos]
    constructor
    · rintro ⟨⟨h1, _, h3⟩, h4⟩; exact ⟨h3, h1, h4⟩
    · rintro ⟨h3, h1, h4⟩
      refine ⟨⟨h1, ?_, h3⟩, h4⟩
      rintro rfl; rw [C.oz i] at h4; norm_num at h4
  rw [he, card_erase_of_mem, h4]
  exact mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 (C.vw_adj hG).symm, mem_pos.2 (C.v1 i)⟩

/-- Points of `Vs` have weight one. -/
lemma Vs_wt (C : OneCfg G b o v w R) {x : V} (hx : x ∈ Vs G o v w) : wt b x = 1 := by
  have hind : ∀ y ∈ Vs G o v w, wt b y = ∑ i, (if y ∈ neg (b i) then (1 : ℤ) else 0) := by
    intro y hy
    rw [wt]; apply Finset.sum_congr rfl; intro i _
    have hv := (C.Vs_props hG hy).2.2.2.2.2 i
    rcases hv with h | h
    · have h1 : y ∉ Cset (b i) := fun hc => (mem_C_iff (C.Q.bip i) y).1 hc h
      have h2 : y ∉ neg (b i) := by rw [mem_neg, h]; norm_num
      simp [h1, h2]
    · have h1 : y ∈ Cset (b i) := (mem_C_iff (C.Q.bip i) y).2 (by rw [h]; norm_num)
      have h2 : y ∈ neg (b i) := mem_neg.2 h
      simp [h1, h2]
  have hsum : ∑ y ∈ Vs G o v w, wt b y = 12 := by
    rw [Finset.sum_congr rfl hind, Finset.sum_comm]
    simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, C.Vs_neg_card hG]
    simp
  have hge : ∀ y ∈ Vs G o v w, 1 ≤ wt b y := by
    intro y hy
    obtain ⟨h1, h2, h3, h4, -, -⟩ := C.Vs_props hG hy
    rcases C.cov y h1 h2 h3 h4 with h | h <;> rw [h] <;> norm_num
  have hz : ∑ y ∈ Vs G o v w, (wt b y - 1) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, sum_const, C.card_Vs hG]; norm_num
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun y hy => by have := hge y hy; linarith)).1 hz x hx
  linarith

lemma Ws_wt (C : OneCfg G b o v w R) {x : V} (hx : x ∈ Ws G o v w) : wt b x = 1 := by
  have hind : ∀ y ∈ Ws G o v w, wt b y = ∑ i, (if y ∈ pos (b i) then (1 : ℤ) else 0) := by
    intro y hy
    rw [wt]; apply Finset.sum_congr rfl; intro i _
    have hv := (C.Ws_props hG hy).2.2.2.2.2 i
    rcases hv with h | h
    · have h1 : y ∉ Cset (b i) := fun hc => (mem_C_iff (C.Q.bip i) y).1 hc h
      have h2 : y ∉ pos (b i) := by rw [mem_pos, h]; norm_num
      simp [h1, h2]
    · have h1 : y ∈ Cset (b i) := (mem_C_iff (C.Q.bip i) y).2 (by rw [h]; norm_num)
      have h2 : y ∈ pos (b i) := mem_pos.2 h
      simp [h1, h2]
  have hsum : ∑ y ∈ Ws G o v w, wt b y = 12 := by
    rw [Finset.sum_congr rfl hind, Finset.sum_comm]
    simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, C.Ws_pos_card hG]
    simp
  have hge : ∀ y ∈ Ws G o v w, 1 ≤ wt b y := by
    intro y hy
    obtain ⟨h1, h2, h3, h4, -, -⟩ := C.Ws_props hG hy
    rcases C.cov y h1 h2 h3 h4 with h | h <;> rw [h] <;> norm_num
  have hz : ∑ y ∈ Ws G o v w, (wt b y - 1) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, sum_const, C.card_Ws hG]; norm_num
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun y hy => by have := hge y hy; linarith)).1 hz x hx
  linarith

/-- Two nonzero coordinates force weight at least two. -/
lemma wt_two_le {x : V} {i j : Fin 4} (hij : i ≠ j) (C : OneCfg G b o v w R)
    (hi : b i x ≠ 0) (hj : b j x ≠ 0) : 2 ≤ wt b x := by
  have := wt_ge (b := b) (x := x) {i, j} (by
    intro k hk; rw [mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact (mem_C_iff (C.Q.bip _) x).2 hi
    · exact (mem_C_iff (C.Q.bip _) x).2 hj)
  rw [card_pair hij] at this; exact_mod_cast this

lemma wt_three_le {x : V} {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (C : OneCfg G b o v w R) (hi : b i x ≠ 0) (hj : b j x ≠ 0) (hk : b k x ≠ 0) : 3 ≤ wt b x := by
  have := wt_ge (b := b) (x := x) {i, j, k} (by
    intro l hl; rw [mem_insert, mem_insert, mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact (mem_C_iff (C.Q.bip _) x).2 hi
    · exact (mem_C_iff (C.Q.bip _) x).2 hj
    · exact (mem_C_iff (C.Q.bip _) x).2 hk)
  rw [card_insert_of_notMem (by simp [hij, hik]), card_pair hjk] at this
  exact_mod_cast this

/-- A point of `Vs` has a label `a` (its only nonzero coordinate, equal to `-1`). -/
lemma Vs_label (C : OneCfg G b o v w R) {x : V} (hx : x ∈ Vs G o v w) :
    ∃ a, b a x = -1 ∧ ∀ i, i ≠ a → b i x = 0 := by
  have hw := C.Vs_wt hG hx
  have hv := (C.Vs_props hG hx).2.2.2.2.2
  obtain ⟨a, ha⟩ : ∃ a, b a x ≠ 0 := by
    by_contra h; push_neg at h
    rw [wt_eq_zero (fun i hc => (mem_C_iff (C.Q.bip i) x).1 hc (h i))] at hw; norm_num at hw
  refine ⟨a, ?_, fun i hia => ?_⟩
  · rcases hv a with h | h
    · exact absurd h ha
    · exact h
  · by_contra hi
    have := C.wt_two_le hG hia hi ha
    rw [hw] at this; norm_num at this

lemma Ws_label (C : OneCfg G b o v w R) {x : V} (hx : x ∈ Ws G o v w) :
    ∃ a, b a x = 1 ∧ ∀ i, i ≠ a → b i x = 0 := by
  have hw := C.Ws_wt hG hx
  have hv := (C.Ws_props hG hx).2.2.2.2.2
  obtain ⟨a, ha⟩ : ∃ a, b a x ≠ 0 := by
    by_contra h; push_neg at h
    rw [wt_eq_zero (fun i hc => (mem_C_iff (C.Q.bip i) x).1 hc (h i))] at hw; norm_num at hw
  refine ⟨a, ?_, fun i hia => ?_⟩
  · rcases hv a with h | h
    · exact absurd h ha
    · exact h
  · by_contra hi
    have := C.wt_two_le hG hia hi ha
    rw [hw] at this; norm_num at this

lemma Vs_Ws_disj (C : OneCfg G b o v w R) : Disjoint (Vs G o v w) (Ws G o v w) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨a, ha, _⟩ := C.Vs_label hG hx
  rcases (C.Ws_props hG hy).2.2.2.2.2 a with h | h <;> rw [h] at ha <;> norm_num at ha

/-! ### The cell points `R i j` -/

lemma R_W (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) : R i j ∈ Wset G b :=
  C.Q.mem_W_of_C hG ((mem_C_iff (C.Q.bip i) _).2 (by rw [(C.R1 i j hij).1]; norm_num))

lemma R_ne_o (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) : R i j ≠ o := by
  intro h; have := (C.R1 i j hij).1; rw [h, C.oz i] at this; norm_num at this

lemma R_ne_v (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) : R i j ≠ v := by
  intro h; have := (C.R1 i j hij).2; rw [h, C.v1 j] at this; norm_num at this

lemma R_ne_w (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) : R i j ≠ w := by
  intro h; have := (C.R1 i j hij).1; rw [h, C.w1 i] at this; norm_num at this

lemma R_zero (C : OneCfg G b o v w R) {i j k : Fin 4} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    b k (R i j) = 0 := by
  by_contra hk
  have h3 := C.wt_three_le hG hij (Ne.symm hki) (Ne.symm hkj)
    (by rw [(C.R1 i j hij).1]; norm_num) (by rw [(C.R1 i j hij).2]; norm_num) hk
  rcases C.cov _ (C.R_W hG hij) (C.R_ne_o hG hij) (C.R_ne_v hG hij) (C.R_ne_w hG hij) with h | h <;>
    rw [h] at h3 <;> norm_num at h3

lemma R_unique (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) {x : V}
    (h1 : b i x = 1) (h2 : b j x = -1) : x = R i j := by
  have hc := (rel31 hG (C.Q.m4 i) (C.Q.bip i) (C.Q.m4 j) (C.Q.bip j) (C.Q.orth i j hij)).2.2.2.1
  exact card_le_one.1 hc.le x (mem_inter.2 ⟨mem_pos.2 h1, mem_neg.2 h2⟩) (R i j)
    (mem_inter.2 ⟨mem_pos.2 (C.R1 i j hij).1, mem_neg.2 (C.R1 i j hij).2⟩)

lemma pp_unique (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) {x : V}
    (h1 : b i x = 1) (h2 : b j x = 1) : x = v := by
  have hc := (rel31 hG (C.Q.m4 i) (C.Q.bip i) (C.Q.m4 j) (C.Q.bip j) (C.Q.orth i j hij)).2.2.1
  exact card_le_one.1 hc.le x (mem_inter.2 ⟨mem_pos.2 h1, mem_pos.2 h2⟩) v
    (mem_inter.2 ⟨mem_pos.2 (C.v1 i), mem_pos.2 (C.v1 j)⟩)

lemma nn_unique (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) {x : V}
    (h1 : b i x = -1) (h2 : b j x = -1) : x = w := by
  have hc := (rel31 hG (C.Q.m4 i) (C.Q.bip i) (C.Q.m4 j) (C.Q.bip j) (C.Q.orth i j hij)).2.2.2.2.2.1
  exact card_le_one.1 hc.le x (mem_inter.2 ⟨mem_neg.2 h1, mem_neg.2 h2⟩) w
    (mem_inter.2 ⟨mem_neg.2 (C.w1 i), mem_neg.2 (C.w1 j)⟩)

lemma R_not_Vs (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) : R i j ∉ Vs G o v w := by
  intro h
  rcases (C.Vs_props hG h).2.2.2.2.2 i with h' | h' <;> rw [(C.R1 i j hij).1] at h' <;>
    norm_num at h'

lemma R_not_Ws (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) : R i j ∉ Ws G o v w := by
  intro h
  rcases (C.Ws_props hG h).2.2.2.2.2 j with h' | h' <;> rw [(C.R1 i j hij).2] at h' <;>
    norm_num at h'

lemma R_inj (C : OneCfg G b o v w R) {i j k l : Fin 4} (hij : i ≠ j) (hkl : k ≠ l)
    (h : R i j = R k l) : i = k ∧ j = l := by
  have e1 := (C.R1 i j hij).1
  have e2 := (C.R1 i j hij).2
  rw [h] at e1 e2
  constructor
  · by_contra hik
    by_cases hil : i = l
    · subst hil; rw [(C.R1 k i hkl).2] at e1; norm_num at e1
    · rw [C.R_zero hG hkl hik hil] at e1; norm_num at e1
  · by_contra hjl
    by_cases hjk : j = k
    · subst hjk; rw [(C.R1 j l hkl).1] at e2; norm_num at e2
    · rw [C.R_zero hG hkl hjk hjl] at e2; norm_num at e2

lemma card_Rin (C : OneCfg G b o v w R) (i : Fin 4) : (Rin R i).card = 3 := by
  rw [Rin, card_image_of_injOn]
  · simp
  · intro k hk k' hk' h
    simp only [coe_erase, coe_univ, Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff,
      true_and] at hk hk'
    exact (C.R_inj hG hk hk' h).1

lemma card_Rout (C : OneCfg G b o v w R) (i : Fin 4) : (Rout R i).card = 3 := by
  rw [Rout, card_image_of_injOn]
  · simp
  · intro k hk k' hk' h
    simp only [coe_erase, coe_univ, Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff,
      true_and] at hk hk'
    exact (C.R_inj hG (Ne.symm hk) (Ne.symm hk') h).2

/-- `N_i = {w} ∪ V_i ∪ {R_ki}`. -/
lemma neg_eq (C : OneCfg G b o v w R) (i : Fin 4) :
    neg (b i) = insert w ((Vs G o v w ∩ neg (b i)) ∪ Rin R i) := by
  have hsub : insert w ((Vs G o v w ∩ neg (b i)) ∪ Rin R i) ⊆ neg (b i) := by
    intro x hx
    rw [mem_insert, mem_union, mem_Rin] at hx
    rcases hx with rfl | hx | ⟨k, hk, rfl⟩
    · exact mem_neg.2 (C.w1 i)
    · exact (mem_inter.1 hx).2
    · exact mem_neg.2 (C.R1 k i hk).2
  have hwn : w ∉ (Vs G o v w ∩ neg (b i)) ∪ Rin R i := by
    rw [mem_union, mem_Rin, not_or]
    refine ⟨fun h => (mem_Vs.1 (mem_inter.1 h).1).2.2 rfl, ?_⟩
    rintro ⟨k, hk, h⟩
    have := (C.R1 k i hk).1; rw [h, C.w1 k] at this; norm_num at this
  have hd : Disjoint (Vs G o v w ∩ neg (b i)) (Rin R i) := by
    rw [Finset.disjoint_left]
    intro x hx hR
    obtain ⟨k, hk, rfl⟩ := mem_Rin.1 hR
    exact C.R_not_Vs hG hk (mem_inter.1 hx).1
  have hc : (insert w ((Vs G o v w ∩ neg (b i)) ∪ Rin R i)).card = 7 := by
    rw [card_insert_of_notMem hwn, card_union_of_disjoint hd, C.Vs_neg_card hG, C.card_Rin hG]
  exact (eq_of_subset_of_card_le hsub (by rw [hc, (C.Q.bip i).card_neg])).symm

/-- `P_i = {v} ∪ W_i ∪ {R_ik}`. -/
lemma pos_eq (C : OneCfg G b o v w R) (i : Fin 4) :
    pos (b i) = insert v ((Ws G o v w ∩ pos (b i)) ∪ Rout R i) := by
  have hsub : insert v ((Ws G o v w ∩ pos (b i)) ∪ Rout R i) ⊆ pos (b i) := by
    intro x hx
    rw [mem_insert, mem_union, mem_Rout] at hx
    rcases hx with rfl | hx | ⟨k, hk, rfl⟩
    · exact mem_pos.2 (C.v1 i)
    · exact (mem_inter.1 hx).2
    · exact mem_pos.2 (C.R1 i k (Ne.symm hk)).1
  have hvn : v ∉ (Ws G o v w ∩ pos (b i)) ∪ Rout R i := by
    rw [mem_union, mem_Rout, not_or]
    refine ⟨fun h => (mem_Ws.1 (mem_inter.1 h).1).2.2 rfl, ?_⟩
    rintro ⟨k, hk, h⟩
    have := (C.R1 i k (Ne.symm hk)).2; rw [h, C.v1 k] at this; norm_num at this
  have hd : Disjoint (Ws G o v w ∩ pos (b i)) (Rout R i) := by
    rw [Finset.disjoint_left]
    intro x hx hR
    obtain ⟨k, hk, rfl⟩ := mem_Rout.1 hR
    exact C.R_not_Ws hG (Ne.symm hk) (mem_inter.1 hx).1
  have hc : (insert v ((Ws G o v w ∩ pos (b i)) ∪ Rout R i)).card = 7 := by
    rw [card_insert_of_notMem hvn, card_union_of_disjoint hd, C.Ws_pos_card hG, C.card_Rout hG]
  exact (eq_of_subset_of_card_le hsub (by rw [hc, (C.Q.bip i).card_pos])).symm

/-- Every point of `W` is `o`, `v`, `w`, in `Vs`, in `Ws`, or a cell point `R i j`. -/
lemma classify (C : OneCfg G b o v w R) {x : V} (hx : x ∈ Wset G b) :
    x = o ∨ x = v ∨ x = w ∨ x ∈ Vs G o v w ∨ x ∈ Ws G o v w ∨ ∃ i j, i ≠ j ∧ x = R i j := by
  by_cases h0 : ∀ i, b i x = 0
  · exact Or.inl (C.zero_eq hG hx h0)
  push_neg at h0
  obtain ⟨i, hi⟩ := h0
  rcases (C.Q.bip i).vals x with h | h | h
  · exact absurd h hi
  · have hm : x ∈ pos (b i) := mem_pos.2 h
    rw [C.pos_eq hG i, mem_insert, mem_union, mem_Rout] at hm
    rcases hm with h1 | h1 | ⟨k, hk, h1⟩
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mem_inter.1 h1).1))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, k, Ne.symm hk, h1.symm⟩))))
  · have hm : x ∈ neg (b i) := mem_neg.2 h
    rw [C.neg_eq hG i, mem_insert, mem_union, mem_Rin] at hm
    rcases hm with h1 | h1 | ⟨k, hk, h1⟩
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_inter.1 h1).1)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, i, hk, h1.symm⟩))))

/-! ### Matchings -/

lemma Vs_nadj_w (C : OneCfg G b o v w R) {x : V} (hx : x ∈ Vs G o v w) : ¬ G.Adj x w := by
  obtain ⟨a, ha, _⟩ := C.Vs_label hG hx
  exact (C.Q.bip a).nadj_neg ha (C.w1 a)

lemma Ws_nadj_v (C : OneCfg G b o v w R) {x : V} (hx : x ∈ Ws G o v w) : ¬ G.Adj x v := by
  obtain ⟨a, ha, _⟩ := C.Ws_label hG hx
  exact (C.Q.bip a).nadj_pos ha (C.v1 a)

lemma Vs_nadj_o (C : OneCfg G b o v w R) {x : V} (hx : x ∈ Vs G o v w) : ¬ G.Adj x o := by
  obtain ⟨h1, -, h3, h4, -, -⟩ := C.Vs_props hG hx
  exact fun h => C.o_nadj hG h1 h3 h4 h.symm

lemma Ws_nadj_o (C : OneCfg G b o v w R) {x : V} (hx : x ∈ Ws G o v w) : ¬ G.Adj x o := by
  obtain ⟨h1, -, h3, h4, -, -⟩ := C.Ws_props hG hx
  exact fun h => C.o_nadj hG h1 h3 h4 h.symm

lemma Vs_match (C : OneCfg G b o v w R) {x : V} (hx : x ∈ Vs G o v w) :
    (G.neighborFinset x ∩ Vs G o v w).card = 1 := by
  have hvx := (C.Vs_props hG hx).2.2.2.2.1
  have he : G.neighborFinset x ∩ Vs G o v w = cn G v x := by
    ext y; simp only [mem_inter, mem_neighborFinset, mem_Vs, mem_cn]
    constructor
    · rintro ⟨h1, h2, _, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩
      refine ⟨h1, h2, ?_, ?_⟩
      · rintro rfl; exact C.Vs_nadj_o hG hx h1
      · rintro rfl; exact C.Vs_nadj_w hG hx h1
  rw [he, cn_adj hG hvx]

lemma Ws_match (C : OneCfg G b o v w R) {x : V} (hx : x ∈ Ws G o v w) :
    (G.neighborFinset x ∩ Ws G o v w).card = 1 := by
  have hwx := (C.Ws_props hG hx).2.2.2.2.1
  have he : G.neighborFinset x ∩ Ws G o v w = cn G w x := by
    ext y; simp only [mem_inter, mem_neighborFinset, mem_Ws, mem_cn]
    constructor
    · rintro ⟨h1, h2, _, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩
      refine ⟨h1, h2, ?_, ?_⟩
      · rintro rfl; exact C.Ws_nadj_o hG hx h1
      · rintro rfl; exact C.Ws_nadj_v hG hx h1
  rw [he, cn_adj hG hwx]

lemma Vs_Ws_one (C : OneCfg G b o v w R) {x : V} (hx : x ∈ Vs G o v w) :
    (G.neighborFinset x ∩ Ws G o v w).card = 1 := by
  obtain ⟨-, -, -, hxw, hvx, -⟩ := C.Vs_props hG hx
  have h2 := cn_nadj hG hxw (C.Vs_nadj_w hG hx)
  have he : cn G x w = insert v (G.neighborFinset x ∩ Ws G o v w) := by
    ext y; simp only [mem_cn, mem_insert, mem_inter, mem_neighborFinset, mem_Ws]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hyv : y = v
      · exact Or.inl hyv
      · refine Or.inr ⟨h1, h2, ?_, hyv⟩
        rintro rfl; exact C.Vs_nadj_o hG hx h1
    · rintro (rfl | ⟨h1, h2, _, _⟩)
      · exact ⟨hvx.symm, (C.vw_adj hG).symm⟩
      · exact ⟨h1, h2⟩
  rw [he, card_insert_of_notMem (fun h => (mem_Ws.1 (mem_inter.1 h).2).2.2 rfl)] at h2
  omega

lemma Ws_Vs_one (C : OneCfg G b o v w R) {x : V} (hx : x ∈ Ws G o v w) :
    (G.neighborFinset x ∩ Vs G o v w).card = 1 := by
  obtain ⟨-, -, hxv, -, hwx, -⟩ := C.Ws_props hG hx
  have h2 := cn_nadj hG hxv (C.Ws_nadj_v hG hx)
  have he : cn G x v = insert w (G.neighborFinset x ∩ Vs G o v w) := by
    ext y; simp only [mem_cn, mem_insert, mem_inter, mem_neighborFinset, mem_Vs]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hyw : y = w
      · exact Or.inl hyw
      · refine Or.inr ⟨h1, h2, ?_, hyw⟩
        rintro rfl; exact C.Ws_nadj_o hG hx h1
    · rintro (rfl | ⟨h1, h2, _, _⟩)
      · exact ⟨hwx.symm, C.vw_adj hG⟩
      · exact ⟨h1, h2⟩
  rw [he, card_insert_of_notMem (fun h => (mem_Vs.1 (mem_inter.1 h).2).2.2 rfl)] at h2
  omega

/-! ### Neighbours of the cell points -/

lemma R_nadj_v (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) : ¬ G.Adj (R i j) v :=
  (C.Q.bip i).nadj_pos (C.R1 i j hij).1 (C.v1 i)

lemma R_nadj_w (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) : ¬ G.Adj (R i j) w :=
  (C.Q.bip j).nadj_neg (C.R1 i j hij).2 (C.w1 j)

lemma R_nadj_o (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) : ¬ G.Adj (R i j) o :=
  fun h => C.o_nadj hG (C.R_W hG hij) (C.R_ne_v hG hij) (C.R_ne_w hG hij) h.symm

lemma R_Vs (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) :
    (G.neighborFinset (R i j) ∩ Vs G o v w).card = 2 := by
  have he : G.neighborFinset (R i j) ∩ Vs G o v w = cn G (R i j) v := by
    ext y; simp only [mem_inter, mem_neighborFinset, mem_Vs, mem_cn]
    constructor
    · rintro ⟨h1, h2, _, _⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, h2, ?_, ?_⟩
      · rintro rfl; exact C.R_nadj_o hG hij h1
      · rintro rfl; exact C.R_nadj_w hG hij h1
  rw [he, cn_nadj hG (C.R_ne_v hG hij) (C.R_nadj_v hG hij)]

lemma R_Ws (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) :
    (G.neighborFinset (R i j) ∩ Ws G o v w).card = 2 := by
  have he : G.neighborFinset (R i j) ∩ Ws G o v w = cn G (R i j) w := by
    ext y; simp only [mem_inter, mem_neighborFinset, mem_Ws, mem_cn]
    constructor
    · rintro ⟨h1, h2, _, _⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, h2, ?_, ?_⟩
      · rintro rfl; exact C.R_nadj_o hG hij h1
      · rintro rfl; exact C.R_nadj_v hG hij h1
  rw [he, cn_nadj hG (C.R_ne_w hG hij) (C.R_nadj_w hG hij)]

lemma R_wt (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) : wt b (R i j) = 2 := by
  have h2 := C.wt_two_le hG hij (by rw [(C.R1 i j hij).1]; norm_num)
    (by rw [(C.R1 i j hij).2]; norm_num)
  rcases C.cov _ (C.R_W hG hij) (C.R_ne_o hG hij) (C.R_ne_v hG hij) (C.R_ne_w hG hij) with h | h
  · rw [h] at h2; norm_num at h2
  · exact h

lemma R_deg_W (C : OneCfg G b o v w R) {i j : Fin 4} (hij : i ≠ j) :
    (G.neighborFinset (R i j) ∩ Wset G b).card = 8 := by
  have := C.Q.deg_W hG (C.R_W hG hij)
  rw [C.R_wt hG hij] at this
  omega

end OneCfg

end SRG

end Conway99
