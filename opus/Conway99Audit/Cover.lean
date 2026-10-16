import Conway99Audit.Ceiling

/-!
# Part B, step 7: four orthogonal roots leave only `z ∈ {0, 1}` (§7)

`b : Fin 4 → V → ℤ` are four pairwise orthogonal root vectors (`Quad`).  `W` is the complement
of the four (disjoint) sets `I_i`; it has `39` points and contains every support `C_i`.
The weight `wt u` is the number of directions with `b_i u ≠ 0`.

Main facts:
* `Σ_{u ∈ W} (wt u - 1)(wt u - 2) = 14`  (equivalent to `z = 7 - n₃ - 3 n₄` of (34));
* a zero-signature point `o ∈ W` has exactly two neighbours in `W`, of weight 4 and of
  opposite signs in every direction;
* hence there is at most one zero point, and if there is one, every other point of `W`
  apart from its two neighbours has weight 1 or 2 (this is (35)–(36)).

The direct incidence argument used here (12 neighbours of `o` in the `I_i`) replaces the
case analysis on the vector `ℓ` of §7; both are correct.
-/

open Finset SimpleGraph Matrix

namespace Conway99

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- Four pairwise orthogonal root vectors. -/
structure Quad (b : Fin 4 → V → ℤ) : Prop where
  m4 : ∀ i, IsM4 G (b i)
  bip : ∀ i, Biplane G (b i)
  orth : ∀ i j, i ≠ j → b i ⬝ᵥ b j = 0

variable (G) in
def Iall (b : Fin 4 → V → ℤ) : Finset V := univ.biUnion (fun i => Iset G (b i))

variable (G) in
def Wset (b : Fin 4 → V → ℤ) : Finset V := univ \ Iall G b

/-- Weight of the signature `(b_1 u, …, b_4 u)`. -/
def wt (b : Fin 4 → V → ℤ) (u : V) : ℤ := ∑ i, if u ∈ Cset (b i) then 1 else 0

lemma mem_C_iff {b : V → ℤ} (hb : Biplane G b) (u : V) : u ∈ Cset b ↔ b u ≠ 0 := by
  rw [Cset, mem_union, mem_pos, mem_neg]
  rcases hb.vals u with h | h | h <;> simp [h]

lemma wt_eq_zero {b : Fin 4 → V → ℤ} {u : V} (h : ∀ i, u ∉ Cset (b i)) : wt b u = 0 := by
  simp [wt, h]

lemma wt_eq_four {b : Fin 4 → V → ℤ} {u : V} (h : ∀ i, u ∈ Cset (b i)) : wt b u = 4 := by
  simp [wt, h]

section SRG

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

namespace Quad

variable {b : Fin 4 → V → ℤ}

lemma I_disj (hQ : Quad G b) {i j : Fin 4} (hij : i ≠ j) :
    Disjoint (Iset G (b i)) (Iset G (b j)) :=
  (rel31 hG (hQ.m4 i) (hQ.bip i) (hQ.m4 j) (hQ.bip j) (hQ.orth i j hij)).2.1

lemma C_disj_I (hQ : Quad G b) (i j : Fin 4) : Disjoint (Cset (b i)) (Iset G (b j)) := by
  by_cases hij : i = j
  · subst hij; exact (I_disj_C (b i)).symm
  · exact (rel31 hG (hQ.m4 i) (hQ.bip i) (hQ.m4 j) (hQ.bip j) (hQ.orth i j hij)).1

lemma card_Iall (hQ : Quad G b) : (Iall G b).card = 60 := by
  rw [Iall, card_biUnion]
  · simp [card_I hG (hQ.m4 _) (hQ.bip _)]
  · intro i _ j _ hij; exact hQ.I_disj hG hij

lemma mem_W_of_C (hQ : Quad G b) {i : Fin 4} {u : V} (hu : u ∈ Cset (b i)) : u ∈ Wset G b := by
  rw [Wset, mem_sdiff, Iall, mem_biUnion]
  refine ⟨mem_univ _, ?_⟩
  rintro ⟨j, _, hj⟩
  exact Finset.disjoint_left.1 (hQ.C_disj_I hG i j) hu hj

lemma card_W (hQ : Quad G b) : (Wset G b).card = 39 := by
  rw [Wset, card_sdiff_of_subset (subset_univ _), card_univ, card_V hG, hQ.card_Iall hG]

lemma not_I_of_W {u : V} (hu : u ∈ Wset G b) (i : Fin 4) : u ∉ Iset G (b i) := by
  intro h; rw [Wset, mem_sdiff, Iall, mem_biUnion] at hu; exact hu.2 ⟨i, mem_univ _, h⟩

/-- A point of `W` outside `C_i` lies in `S_i`. -/
lemma mem_S_of_W (hQ : Quad G b) {u : V} (hu : u ∈ Wset G b) {i : Fin 4} (hC : u ∉ Cset (b i)) :
    u ∈ Sset G (b i) := by
  rcases mem_S_or_I hG (hQ.bip i) hC with ⟨h, _⟩ | ⟨h, _⟩
  · exact h
  · exact absurd h (not_I_of_W hG hu i)

/-- Neighbours of a point of `W` in `I_k`: three if `b_k u = 0`, none otherwise. -/
lemma nbI_W (hQ : Quad G b) {u : V} (hu : u ∈ Wset G b) (k : Fin 4) :
    (G.neighborFinset u ∩ Iset G (b k)).card = if u ∈ Cset (b k) then 0 else 3 := by
  split_ifs with hC
  · rw [card_eq_zero, eq_empty_iff_forall_notMem]
    intro x hx; rw [mem_inter, mem_neighborFinset] at hx
    exact C_not_adj_I hG (hQ.m4 k) (hQ.bip k) hC hx.2 hx.1
  · rw [nbI hG (hQ.m4 k) (hQ.bip k) hC, if_pos (hQ.mem_S_of_W hG hu hC)]

lemma nbIall (hQ : Quad G b) (u : V) :
    (G.neighborFinset u ∩ Iall G b).card = ∑ k, (G.neighborFinset u ∩ Iset G (b k)).card := by
  rw [Iall, Finset.inter_biUnion, card_biUnion]
  intro i _ j _ hij
  exact Finset.disjoint_of_subset_left inter_subset_right
    (Finset.disjoint_of_subset_right inter_subset_right (hQ.I_disj hG hij))

lemma card_nb_split (u : V) :
    (G.neighborFinset u ∩ Wset G b).card + (G.neighborFinset u ∩ Iall G b).card = 14 := by
  rw [← degree_eq hG u, Wset, ← Finset.inter_sdiff_assoc, inter_univ]
  exact card_sdiff_add_card_inter _ _

/-- Degree inside `W` of a point of `W`: `2 + 3 wt`. -/
lemma deg_W (hQ : Quad G b) {u : V} (hu : u ∈ Wset G b) :
    ((G.neighborFinset u ∩ Wset G b).card : ℤ) = 2 + 3 * wt b u := by
  have h1 := card_nb_split hG (b := b) u
  rw [hQ.nbIall hG u, Finset.sum_congr rfl (fun k _ => hQ.nbI_W hG hu k)] at h1
  have h2 : ((∑ k : Fin 4, (if u ∈ Cset (b k) then 0 else 3 : ℕ)) : ℤ) = 12 - 3 * wt b u := by
    rw [wt]
    push_cast
    simp only [Fin.sum_univ_four]
    split_ifs <;> norm_num
  have h3 : ((G.neighborFinset u ∩ Wset G b).card : ℤ)
      + ((∑ k : Fin 4, (if u ∈ Cset (b k) then 0 else 3 : ℕ)) : ℤ) = 14 := by exact_mod_cast h1
  linarith

lemma sum_ind_W (hQ : Quad G b) (i : Fin 4) :
    ∑ u ∈ Wset G b, (if u ∈ Cset (b i) then (1 : ℤ) else 0) = 14 := by
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, inter_eq_right.2
    (fun u hu => hQ.mem_W_of_C hG hu), card_C hG (hQ.bip i)]
  rfl

lemma sum_ind2_W (hQ : Quad G b) (i j : Fin 4) :
    ∑ u ∈ Wset G b, ((if u ∈ Cset (b i) then (1 : ℤ) else 0) * (if u ∈ Cset (b j) then 1 else 0))
      = if i = j then 14 else 4 := by
  simp only [boole_mul]
  rw [← Finset.sum_filter, Finset.sum_boole]
  have : ((Wset G b).filter (fun u => u ∈ Cset (b i))).filter (fun u => u ∈ Cset (b j))
      = Cset (b i) ∩ Cset (b j) := by
    ext u; simp only [mem_filter, mem_inter]
    constructor
    · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨hQ.mem_W_of_C hG h1, h1⟩, h2⟩
  rw [this]
  split_ifs with hij
  · subst hij; rw [inter_self, card_C hG (hQ.bip i)]; rfl
  · rw [(rel31 hG (hQ.m4 i) (hQ.bip i) (hQ.m4 j) (hQ.bip j) (hQ.orth i j hij)).2.2.2.2.2.2]; rfl

lemma sum_wt (hQ : Quad G b) : ∑ u ∈ Wset G b, wt b u = 56 := by
  simp only [wt]
  rw [Finset.sum_comm]
  simp only [hQ.sum_ind_W hG, sum_const, card_univ, Fintype.card_fin]
  norm_num

lemma sum_wt_sq (hQ : Quad G b) : ∑ u ∈ Wset G b, wt b u * wt b u = 104 := by
  have e : ∀ u, wt b u * wt b u = ∑ i, ∑ j, ((if u ∈ Cset (b i) then (1 : ℤ) else 0) *
      (if u ∈ Cset (b j) then 1 else 0)) := by
    intro u; rw [wt, Finset.sum_mul_sum]
  simp only [e]
  rw [Finset.sum_comm]
  have h : ∀ i : Fin 4, ∑ u ∈ Wset G b, ∑ j, ((if u ∈ Cset (b i) then (1 : ℤ) else 0) *
      (if u ∈ Cset (b j) then 1 else 0)) = ∑ j, (if i = j then (14 : ℤ) else 4) := by
    intro i; rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun j _ => hQ.sum_ind2_W hG i j)
  simp only [h]
  simp [Fin.sum_univ_four]

/-- `Σ_{u ∈ W} (wt u - 1)(wt u - 2) = 14`, i.e. `z + n₃ + 3 n₄ = 7` (34). -/
theorem sum_f (hQ : Quad G b) :
    ∑ u ∈ Wset G b, (wt b u - 1) * (wt b u - 2) = 14 := by
  have e : ∀ u, (wt b u - 1) * (wt b u - 2) = wt b u * wt b u - 3 * wt b u + 2 := fun u => by ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_const,
    hQ.sum_wt_sq hG, hQ.sum_wt hG, hQ.card_W hG]
  norm_num

/-- A zero-signature point of `W` has exactly two neighbours in `W`, of opposite signs
in every direction (in particular both of weight four). -/
theorem zero_nbrs (hQ : Quad G b) {o : V} (ho : o ∈ Wset G b) (hz : ∀ i, b i o = 0) :
    ∃ x y : V, x ≠ y ∧ G.neighborFinset o ∩ Wset G b = {x, y} ∧
      ∀ i, (b i x = 1 ∧ b i y = -1) ∨ (b i x = -1 ∧ b i y = 1) := by
  have hC : ∀ i, o ∉ Cset (b i) := fun i h => (mem_C_iff (hQ.bip i) o).1 h (hz i)
  have hdeg := hQ.deg_W hG ho
  rw [wt_eq_zero hC] at hdeg
  have h2 : (G.neighborFinset o ∩ Wset G b).card = 2 := by omega
  obtain ⟨x, y, hxy, hset⟩ := card_eq_two.1 h2
  refine ⟨x, y, hxy, hset, fun i => ?_⟩
  have hS := hQ.mem_S_of_W hG ho (hC i)
  have hP : (G.neighborFinset o ∩ pos (b i)).card = 1 := by
    simp only [Sset, mem_filter] at hS; exact hS.2.2
  have hN : (G.neighborFinset o ∩ neg (b i)).card = 1 := by
    rw [← out_eq hG (hQ.m4 i) (hQ.bip i) (hC i)]; exact hP
  obtain ⟨p, hp⟩ := card_eq_one.1 hP
  obtain ⟨n, hn⟩ := card_eq_one.1 hN
  have hp' : p ∈ G.neighborFinset o ∩ pos (b i) := by rw [hp]; exact mem_singleton_self p
  have hn' : n ∈ G.neighborFinset o ∩ neg (b i) := by rw [hn]; exact mem_singleton_self n
  rw [mem_inter, mem_pos] at hp'
  rw [mem_inter, mem_neg] at hn'
  have hpW : p ∈ G.neighborFinset o ∩ Wset G b :=
    mem_inter.2 ⟨hp'.1, hQ.mem_W_of_C hG ((mem_C_iff (hQ.bip i) p).2 (by rw [hp'.2]; norm_num))⟩
  have hnW : n ∈ G.neighborFinset o ∩ Wset G b :=
    mem_inter.2 ⟨hn'.1, hQ.mem_W_of_C hG ((mem_C_iff (hQ.bip i) n).2 (by rw [hn'.2]; norm_num))⟩
  rw [hset, mem_insert, mem_singleton] at hpW hnW
  have hpn : p ≠ n := by intro h; rw [h] at hp'; rw [hp'.2] at hn'; norm_num at hn'
  rcases hpW with rfl | rfl <;> rcases hnW with rfl | rfl
  · exact absurd rfl hpn
  · exact Or.inl ⟨hp'.2, hn'.2⟩
  · exact Or.inr ⟨hn'.2, hp'.2⟩
  · exact absurd rfl hpn

/-- (35)–(36): if `o ∈ W` has zero signature, with `W`-neighbours `x, y`, then every other point
of `W` has weight 1 or 2.  In particular `o` is the only zero point. -/
theorem cover (hQ : Quad G b) {o x y : V} (ho : o ∈ Wset G b) (hz : ∀ i, b i o = 0)
    (hxy : x ≠ y) (hset : G.neighborFinset o ∩ Wset G b = {x, y})
    (hsig : ∀ i, (b i x = 1 ∧ b i y = -1) ∨ (b i x = -1 ∧ b i y = 1)) :
    ∀ u ∈ Wset G b, u ≠ o → u ≠ x → u ≠ y → wt b u = 1 ∨ wt b u = 2 := by
  have hxW : x ∈ Wset G b := by
    have : x ∈ G.neighborFinset o ∩ Wset G b := by rw [hset]; simp
    exact (mem_inter.1 this).2
  have hyW : y ∈ Wset G b := by
    have : y ∈ G.neighborFinset o ∩ Wset G b := by rw [hset]; simp
    exact (mem_inter.1 this).2
  have hCo : ∀ i, o ∉ Cset (b i) := fun i h => (mem_C_iff (hQ.bip i) o).1 h (hz i)
  have hCx : ∀ i, x ∈ Cset (b i) := fun i =>
    (mem_C_iff (hQ.bip i) x).2 (by rcases hsig i with h | h <;> rw [h.1] <;> norm_num)
  have hCy : ∀ i, y ∈ Cset (b i) := fun i =>
    (mem_C_iff (hQ.bip i) y).2 (by rcases hsig i with h | h <;> rw [h.2] <;> norm_num)
  have hox : o ≠ x := fun h => hCo 0 (h ▸ hCx 0)
  have hoy : o ≠ y := fun h => hCo 0 (h ▸ hCy 0)
  have hs := hQ.sum_f hG
  set f : V → ℤ := fun u => (wt b u - 1) * (wt b u - 2) with hf
  have hfnn : ∀ u, 0 ≤ f u := by
    intro u; simp only [hf]
    rcases le_or_gt (wt b u) 1 with h | h
    · nlinarith
    · nlinarith
  have e1 := Finset.add_sum_erase _ f ho
  have hxo : x ∈ (Wset G b).erase o := mem_erase.2 ⟨hox.symm, hxW⟩
  have e2 := Finset.add_sum_erase _ f hxo
  have hyo : y ∈ ((Wset G b).erase o).erase x := mem_erase.2 ⟨hxy.symm, mem_erase.2 ⟨hoy.symm, hyW⟩⟩
  have e3 := Finset.add_sum_erase _ f hyo
  have fo : f o = 2 := by simp only [hf, wt_eq_zero hCo]; norm_num
  have fx : f x = 6 := by simp only [hf, wt_eq_four hCx]; norm_num
  have fy : f y = 6 := by simp only [hf, wt_eq_four hCy]; norm_num
  have hrest : ∑ u ∈ (((Wset G b).erase o).erase x).erase y, f u = 0 := by
    have : ∑ u ∈ Wset G b, f u = 14 := hs
    linarith
  intro u hu huo hux huy
  have hmem : u ∈ (((Wset G b).erase o).erase x).erase y :=
    mem_erase.2 ⟨huy, mem_erase.2 ⟨hux, mem_erase.2 ⟨huo, hu⟩⟩⟩
  have hfu := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => hfnn u)).1 hrest u hmem
  simp only [hf] at hfu
  rcases mul_eq_zero.1 hfu with h | h
  · left; linarith
  · right; linarith

end Quad

end SRG

end Conway99
