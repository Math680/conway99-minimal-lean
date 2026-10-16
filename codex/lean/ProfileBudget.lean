import RootPartition
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! The six-positive/seventeen-negative profile bound, using actual finite
graph incidence counts rather than a postulated common-neighbour budget. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def profileDegree (T : Finset V) (u : V) : ℕ := (T.filter (G.Adj u)).card
def profileDegreeSum (T : Finset V) : ℕ := ∑ u ∈ T, profileDegree G T u

theorem profile_degree_sum_swap (P B : Finset V) :
    (∑ p ∈ P, profileDegree G B p) = ∑ b ∈ B, profileDegree G P b := by
  simpa only [profileDegree, Finset.bipartiteAbove, Finset.bipartiteBelow,
    SimpleGraph.adj_comm] using
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj (s := P) (t := B)

def profileRestrictedGraph (P : Finset V) : SimpleGraph V where
  Adj u v := u ∈ P ∧ v ∈ P ∧ G.Adj u v
  symm := by intro u v hh; exact ⟨hh.2.1, hh.1, hh.2.2.symm⟩
  loopless := by intro u hh; exact G.loopless u hh.2.2

instance (P : Finset V) : DecidableRel (profileRestrictedGraph G P).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem profileRestrictedGraph_degree (P : Finset V) (u : V) :
    (profileRestrictedGraph G P).degree u = if u ∈ P then profileDegree G P u else 0 := by
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  by_cases hu : u ∈ P
  · rw [if_pos hu]
    congr 1
    ext v
    simp [profileRestrictedGraph, profileDegree, hu]
  · simp [profileRestrictedGraph, hu]

theorem profile_degree_sum_even (P : Finset V) :
    ∃ e : ℕ, profileDegreeSum G P = 2 * e := by
  refine ⟨(profileRestrictedGraph G P).edgeFinset.card, ?_⟩
  have hh := (profileRestrictedGraph G P).sum_degrees_eq_twice_card_edges
  simp_rw [profileRestrictedGraph_degree] at hh
  simpa [profileDegreeSum, Finset.sum_ite] using hh

theorem profile_ordered_wedges (P B : Finset V) :
    (∑ a ∈ P.offDiag, (B.filter (fun b => G.Adj a.1 b ∧ G.Adj a.2 b)).card) =
      ∑ b ∈ B, profileDegree G P b * (profileDegree G P b - 1) := by
  have hh := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun a : V × V => fun b => G.Adj a.1 b ∧ G.Adj a.2 b) (s := P.offDiag) (t := B)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro b _
  have heq : P.offDiag.filter (fun a => G.Adj a.1 b ∧ G.Adj a.2 b) =
      (P.filter (G.Adj b)).offDiag := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_offDiag]
    simp only [SimpleGraph.adj_comm]
    tauto
  rw [heq, Finset.offDiag_card]
  unfold profileDegree
  rw [Nat.mul_sub_left_distrib, Nat.mul_one]

theorem profile_ordered_internal_edges (P : Finset V) :
    (∑ a ∈ P.offDiag, if G.Adj a.1 a.2 then (1 : ℕ) else 0) = profileDegreeSum G P := by
  have hh : (∑ a ∈ P.offDiag, if G.Adj a.1 a.2 then (1 : ℕ) else 0) =
      ∑ a ∈ P ×ˢ P, if G.Adj a.1 a.2 then 1 else 0 := by
    apply Finset.sum_subset
    · intro a ha
      exact Finset.mem_product.mpr ⟨(Finset.mem_offDiag.mp ha).1, (Finset.mem_offDiag.mp ha).2.1⟩
    · intro a ha hnot
      have heq : a.1 = a.2 := by
        have hp := Finset.mem_product.mp ha
        by_contra hn
        exact hnot (Finset.mem_offDiag.mpr ⟨hp.1, hp.2, hn⟩)
      simp [heq]
  rw [hh, Finset.sum_product]
  unfold profileDegreeSum profileDegree
  apply Finset.sum_congr rfl
  intro p _
  simp [Finset.sum_ite]

theorem profile_common_neighbors_bound (h : G.IsSRGWith 99 14 1 2)
    (B : Finset V) (p q : V) (hne : p ≠ q) :
    (B.filter (fun b => G.Adj p b ∧ G.Adj q b)).card +
      (if G.Adj p q then 1 else 0) ≤ 2 := by
  have hh : (B.filter (fun b => G.Adj p b ∧ G.Adj q b)).card ≤
      Fintype.card (G.commonNeighbors p q) := by
    simpa using
      Finset.card_le_card (show B.filter (fun b => G.Adj p b ∧ G.Adj q b) ⊆
        (G.commonNeighbors p q).toFinset by
        intro b hb
        exact Set.mem_toFinset.mpr (Finset.mem_filter.mp hb).2)
  by_cases ha : G.Adj p q
  · rw [h.of_adj p q ha] at hh
    simp only [if_pos ha]
    omega
  · rw [h.of_not_adj hne ha] at hh
    simpa [ha] using hh

theorem profile_srg_wedge_budget (h : G.IsSRGWith 99 14 1 2)
    (P B : Finset V) (hP : P.card = 6) :
    (∑ b ∈ B, profileDegree G P b * (profileDegree G P b - 1)) +
      profileDegreeSum G P ≤ 60 := by
  have hh := Finset.sum_le_sum (s := P.offDiag) (fun a ha =>
    profile_common_neighbors_bound G h B a.1 a.2 (Finset.mem_offDiag.mp ha).2.2)
  rw [Finset.sum_add_distrib, profile_ordered_wedges, profile_ordered_internal_edges] at hh
  simpa [Finset.sum_const, Finset.offDiag_card, hP] using hh

theorem profile_six_seventeen_edge_bound (h : G.IsSRGWith 99 14 1 2)
    (P B : Finset V) (hP : P.card = 6) (hB : B.card = 17)
    (hp : ∀ p ∈ P, profileDegree G B p = profileDegree G P p + 6)
    (hb : ∀ b ∈ B, profileDegree G P b = profileDegree G B b + 2) :
    profileDegreeSum G P ≤ 2 := by
  have hc := profile_degree_sum_swap G P B
  rw [Finset.sum_congr rfl hp, Finset.sum_congr rfl hb] at hc
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hP, hB] at hc
  change profileDegreeSum G P + 6 * 6 = profileDegreeSum G B + 17 * 2 at hc
  have hw := profile_srg_wedge_budget G h P B hP
  have hl : 34 + 4 * profileDegreeSum G B ≤
      ∑ b ∈ B, profileDegree G P b * (profileDegree G P b - 1) := by
    have hh := Finset.sum_le_sum (s := B) (fun b hmem =>
      show 2 + 4 * profileDegree G B b ≤ profileDegree G P b * (profileDegree G P b - 1) from by
        rw [hb b hmem]
        have hn := Nat.zero_le (profileDegree G B b)
        have hs : profileDegree G B b + 2 - 1 = profileDegree G B b + 1 := by omega
        rw [hs]
        by_cases hz : profileDegree G B b = 0
        · simp [hz]
        · have : 1 ≤ profileDegree G B b := by omega
          nlinarith)
    simpa only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
      hB, profileDegreeSum] using hh
  obtain ⟨e, he⟩ := profile_degree_sum_even G P
  omega

def profileEdgeCount (T : Finset V) : ℕ := (profileRestrictedGraph G T).edgeFinset.card

theorem profile_degree_sum_eq_twice_edges (P : Finset V) :
    profileDegreeSum G P = 2 * profileEdgeCount G P := by
  have hh := (profileRestrictedGraph G P).sum_degrees_eq_twice_card_edges
  simp_rw [profileRestrictedGraph_degree] at hh
  simpa [profileDegreeSum, profileEdgeCount, Finset.sum_ite] using hh

theorem profile_six_seventeen_edges (h : G.IsSRGWith 99 14 1 2)
    (P B : Finset V) (hP : P.card = 6) (hB : B.card = 17)
    (hp : ∀ p ∈ P, profileDegree G B p = profileDegree G P p + 6)
    (hb : ∀ b ∈ B, profileDegree G P b = profileDegree G B b + 2) :
    profileEdgeCount G P ≤ 1 ∧ profileEdgeCount G B = profileEdgeCount G P + 1 := by
  have hbound := profile_six_seventeen_edge_bound G h P B hP hB hp hb
  have hc := profile_degree_sum_swap G P B
  rw [Finset.sum_congr rfl hp, Finset.sum_congr rfl hb] at hc
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hP, hB] at hc
  change profileDegreeSum G P + 6 * 6 = profileDegreeSum G B + 17 * 2 at hc
  rw [profile_degree_sum_eq_twice_edges, profile_degree_sum_eq_twice_edges] at hc
  rw [profile_degree_sum_eq_twice_edges] at hbound
  omega

theorem profile_six_seventeen_saturated_of_edge (h : G.IsSRGWith 99 14 1 2)
    (P B : Finset V) (hP : P.card = 6) (hB : B.card = 17)
    (hp : ∀ p ∈ P, profileDegree G B p = profileDegree G P p + 6)
    (hb : ∀ b ∈ B, profileDegree G P b = profileDegree G B b + 2)
    (u v : V) (hu : u ∈ P) (hv : v ∈ P) (ha : G.Adj u v) :
    profileEdgeCount G P = 1 ∧ profileEdgeCount G B = 2 := by
  have hh := profile_six_seventeen_edges G h P B hP hB hp hb
  have hpos : 0 < profileEdgeCount G P := by
    apply Finset.card_pos.mpr
    exact ⟨s(u, v), SimpleGraph.mem_edgeFinset.mpr ⟨hu, hv, ha⟩⟩
  omega

#print axioms profile_degree_sum_even
#print axioms profile_ordered_wedges
#print axioms profile_srg_wedge_budget
#print axioms profile_six_seventeen_edge_bound
#print axioms profile_six_seventeen_edges
#print axioms profile_six_seventeen_saturated_of_edge

end Conway99
