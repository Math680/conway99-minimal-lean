import Mathlib

/-!
# Conway 99-graph audit — combinatorial foundations (Part A)

Hypothesis: `G.IsSRGWith 99 14 1 2`.  We derive the triangle structure used by the
minimal proof (§2.1): every edge lies in exactly one triangle, an outside vertex sees at
most one vertex of a triangle, every vertex lies in seven triangles, there are 231
triangles, and the incidence matrix satisfies `B Bᵀ = 7 I + A`.
-/

open Finset SimpleGraph

namespace Conway99

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Common neighbours as a finset. -/
def cn (u v : V) : Finset V := G.neighborFinset u ∩ G.neighborFinset v

lemma mem_cn {u v w : V} : w ∈ cn G u v ↔ G.Adj u w ∧ G.Adj v w := by
  simp [cn, mem_neighborFinset]

lemma card_cn (u v : V) : (cn G u v).card = Fintype.card (G.commonNeighbors u v) := by
  rw [← Set.toFinset_card]
  congr 1
  ext w
  simp only [cn, Finset.mem_inter, mem_neighborFinset, Set.mem_toFinset, mem_commonNeighbors]

variable {G}

section SRG

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

lemma card_V : Fintype.card V = 99 := hG.card

lemma degree_eq (u : V) : (G.neighborFinset u).card = 14 := by
  rw [card_neighborFinset_eq_degree]; exact hG.regular u

lemma cn_adj {u v : V} (h : G.Adj u v) : (cn G u v).card = 1 := by
  rw [card_cn]; exact hG.of_adj u v h

lemma cn_nadj {u v : V} (hne : u ≠ v) (h : ¬ G.Adj u v) : (cn G u v).card = 2 := by
  rw [card_cn]; exact hG.of_not_adj hne h

/-- λ = 1: two common neighbours of adjacent vertices coincide. -/
lemma cn_unique {u v w w' : V} (h : G.Adj u v) (hw : G.Adj u w ∧ G.Adj v w)
    (hw' : G.Adj u w' ∧ G.Adj v w') : w = w' := by
  have h1 := cn_adj hG h
  rw [Finset.card_eq_one] at h1
  obtain ⟨a, ha⟩ := h1
  have : w ∈ cn G u v := (mem_cn G).2 hw
  have : w' ∈ cn G u v := (mem_cn G).2 hw'
  simp_all

lemma cn_exists {u v : V} (h : G.Adj u v) : ∃ w, G.Adj u w ∧ G.Adj v w := by
  have h1 := cn_adj hG h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h1
  have : a ∈ cn G u v := by rw [ha]; exact mem_singleton_self a
  exact ⟨a, (mem_cn G).1 this⟩

end SRG

/-! ## Triangles -/

/-- The finset of triangles. -/
abbrev T : Finset (Finset V) := G.cliqueFinset 3

lemma mem_T {t : Finset V} : t ∈ T (G := G) ↔ G.IsNClique 3 t := mem_cliqueFinset_iff

lemma T_card3 {t : Finset V} (ht : t ∈ T (G := G)) : t.card = 3 :=
  ((mem_T).1 ht).card_eq

lemma T_adj {t : Finset V} (ht : t ∈ T (G := G)) {a b : V} (ha : a ∈ t) (hb : b ∈ t)
    (hab : a ≠ b) : G.Adj a b :=
  ((mem_T).1 ht).isClique ha hb hab

/-- In a triangle, the two other vertices are exactly the neighbours inside it. -/
lemma T_filter_adj {t : Finset V} (ht : t ∈ T (G := G)) {u : V} (hu : u ∈ t) :
    (t.filter (G.Adj u)) = t.erase u := by
  ext x
  simp only [mem_filter, mem_erase]
  constructor
  · rintro ⟨hx, hux⟩; exact ⟨(G.ne_of_adj hux).symm, hx⟩
  · rintro ⟨hne, hx⟩; exact ⟨hx, T_adj ht hu hx (Ne.symm hne)⟩

lemma T_card_filter_adj_mem {t : Finset V} (ht : t ∈ T (G := G)) {u : V} (hu : u ∈ t) :
    (t.filter (G.Adj u)).card = 2 := by
  rw [T_filter_adj ht hu, card_erase_of_mem hu, T_card3 ht]

section SRG2

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

/-- (C2) An outside vertex is adjacent to at most one vertex of a triangle. -/
lemma T_card_filter_adj_out {t : Finset V} (ht : t ∈ T (G := G)) {u : V} (hu : u ∉ t) :
    (t.filter (G.Adj u)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hab
  simp only [mem_filter] at ha hb
  -- third vertex c of t
  have hc : ((t.erase a).erase b).Nonempty := by
    rw [← card_pos, card_erase_of_mem (mem_erase.2 ⟨Ne.symm hab, hb.1⟩),
      card_erase_of_mem ha.1, T_card3 ht]; norm_num
  obtain ⟨c, hcm⟩ := hc
  simp only [mem_erase] at hcm
  have hab' : G.Adj a b := T_adj ht ha.1 hb.1 hab
  have hac : G.Adj a c := T_adj ht ha.1 hcm.2.2 (Ne.symm hcm.2.1)
  have hbc : G.Adj b c := T_adj ht hb.1 hcm.2.2 (Ne.symm hcm.1)
  have huc : u = c := cn_unique hG hab' ⟨ha.2.symm, hb.2.symm⟩ ⟨hac, hbc⟩
  exact hu (huc ▸ hcm.2.2)

/-- Number of neighbours of `u` inside a triangle `t`: 2 if `u ∈ t`, at most 1 otherwise. -/
lemma n_le_one_or_two {t : Finset V} (ht : t ∈ T (G := G)) (u : V) :
    (u ∈ t ∧ (t.filter (G.Adj u)).card = 2) ∨ (u ∉ t ∧ (t.filter (G.Adj u)).card ≤ 1) := by
  by_cases hu : u ∈ t
  · exact Or.inl ⟨hu, T_card_filter_adj_mem ht hu⟩
  · exact Or.inr ⟨hu, T_card_filter_adj_out hG ht hu⟩

/-- Triangles through an edge: exactly one. -/
lemma T_through_edge {u v : V} (h : G.Adj u v) :
    ((T (G := G)).filter (fun t => u ∈ t ∧ v ∈ t)).card = 1 := by
  obtain ⟨w, huw, hvw⟩ := cn_exists hG h
  rw [Finset.card_eq_one]
  refine ⟨{u, v, w}, ?_⟩
  ext t
  simp only [mem_filter, mem_singleton]
  constructor
  · rintro ⟨ht, hu, hv⟩
    have huv : u ≠ v := G.ne_of_adj h
    have hc : ((t.erase u).erase v).Nonempty := by
      rw [← card_pos, card_erase_of_mem (mem_erase.2 ⟨Ne.symm huv, hv⟩),
        card_erase_of_mem hu, T_card3 ht]; norm_num
    obtain ⟨c, hcm⟩ := hc
    simp only [mem_erase] at hcm
    have huc : G.Adj u c := T_adj ht hu hcm.2.2 (Ne.symm hcm.2.1)
    have hvc : G.Adj v c := T_adj ht hv hcm.2.2 (Ne.symm hcm.1)
    have hcw : c = w := cn_unique hG h ⟨huc, hvc⟩ ⟨huw, hvw⟩
    have hsub : ({u, v, c} : Finset V) ⊆ t := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with hx | hx | hx
      · exact hx ▸ hu
      · exact hx ▸ hv
      · exact hx ▸ hcm.2.2
    have hcard : ({u, v, c} : Finset V).card = 3 := by
      rw [card_insert_of_notMem, card_pair (Ne.symm hcm.1)]
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨huv, Ne.symm hcm.2.1⟩
    rw [← hcw]
    exact (eq_of_subset_of_card_le hsub (by rw [hcard, T_card3 ht])).symm
  · rintro rfl
    refine ⟨?_, by simp, by simp⟩
    rw [mem_T, is3Clique_triple_iff]
    exact ⟨h, huw, hvw⟩

end SRG2

lemma T_through_nonedge {u v : V} (hne : u ≠ v) (h : ¬ G.Adj u v) :
    ((T (G := G)).filter (fun t => u ∈ t ∧ v ∈ t)).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro t ht ⟨hu, hv⟩
  exact h (T_adj ht hu hv hne)

section SRG3

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

/-- (C5) Every vertex lies in exactly seven triangles. -/
lemma T_through_vertex (u : V) : ((T (G := G)).filter (fun t => u ∈ t)).card = 7 := by
  set Tu := (T (G := G)).filter (fun t => u ∈ t) with hTu
  have h1 : ∀ t ∈ Tu, (t.filter (G.Adj u)).card
      = ∑ v ∈ G.neighborFinset u, (if v ∈ t then 1 else 0) := by
    intro t _
    rw [← card_filter]
    congr 1
    ext v; simp [mem_neighborFinset, and_comm]
  have h2 : ∑ t ∈ Tu, (t.filter (G.Adj u)).card = 2 * Tu.card := by
    rw [card_eq_sum_ones Tu, mul_sum]
    apply sum_congr rfl
    intro t ht
    simp only [hTu, mem_filter] at ht
    rw [T_card_filter_adj_mem ht.1 ht.2]; ring
  have h3 : ∑ t ∈ Tu, (t.filter (G.Adj u)).card = 14 := by
    rw [sum_congr rfl h1, sum_comm]
    have : ∀ v ∈ G.neighborFinset u, (∑ t ∈ Tu, (if v ∈ t then 1 else 0)) = 1 := by
      intro v hv
      rw [← card_filter, hTu, filter_filter]
      exact T_through_edge hG ((G.mem_neighborFinset u v).1 hv)
    rw [sum_congr rfl this, sum_const, smul_eq_mul, mul_one, degree_eq hG]
  omega

/-- (C6) There are 231 triangles. -/
lemma card_T : (T (G := G)).card = 231 := by
  have h : ∑ u : V, ((T (G := G)).filter (fun t => u ∈ t)).card
      = ∑ t ∈ T (G := G), t.card := by
    simp only [card_eq_sum_ones, sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro t _
    rw [← card_eq_sum_ones]
    simp [univ_inter]
  have h7 : ∑ u : V, ((T (G := G)).filter (fun t => u ∈ t)).card = 99 * 7 := by
    rw [sum_congr rfl (fun u _ => T_through_vertex hG u), sum_const, card_univ, card_V hG]
    rfl
  have h3 : ∑ t ∈ T (G := G), t.card = 3 * (T (G := G)).card := by
    rw [card_eq_sum_ones (T (G := G)), mul_sum]
    exact sum_congr rfl (fun t ht => by rw [T_card3 ht]; ring)
  omega

end SRG3

end Conway99
