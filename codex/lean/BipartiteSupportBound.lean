import SRG
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! A local length-two path count in a graph with at most two common neighbours. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem filtered_common_neighbors_le_two (h : G.IsSRGWith 99 14 1 2)
    (T : Finset V) (u w : V) (huw : u ≠ w) :
    (T.filter (fun v => G.Adj u v ∧ G.Adj w v)).card ≤ 2 := by
  have hs : T.filter (fun v => G.Adj u v ∧ G.Adj w v) ⊆
      (G.commonNeighbors u w).toFinset := by
    intro v hv
    exact Set.mem_toFinset.mpr (Finset.mem_filter.mp hv).2
  have hb := common_neighbors_at_most_two G h u w huw
  exact (Finset.card_le_card hs).trans (by simpa using hb)

theorem bipartite_four_neighbors_degree_bound (h : G.IsSRGWith 99 14 1 2)
    (P N : Finset V) (u : V) (hu : u ∈ P)
    (hn : ∀ v ∈ N, 4 ≤ (P.filter (G.Adj v)).card) :
    3 * (N.filter (G.Adj u)).card ≤ 2 * (P.card - 1) := by
  classical
  let T := N.filter (G.Adj u)
  have hlow (v : V) (hv : v ∈ T) : 3 ≤ ((P.erase u).filter (G.Adj v)).card := by
    have hvN := (Finset.mem_filter.mp hv).1
    have huv := (Finset.mem_filter.mp hv).2
    have hum : u ∈ P.filter (G.Adj v) := Finset.mem_filter.mpr ⟨hu, huv.symm⟩
    have heq : (P.erase u).filter (G.Adj v) = (P.filter (G.Adj v)).erase u := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_erase]
      tauto
    rw [heq, Finset.card_erase_of_mem hum]
    have hh := hn v hvN
    omega
  have hupp (w : V) (hw : w ∈ P.erase u) : (T.filter (G.Adj w)).card ≤ 2 := by
    have huw : u ≠ w := (Finset.mem_erase.mp hw).1.symm
    have heq : T.filter (G.Adj w) = N.filter (fun v => G.Adj u v ∧ G.Adj w v) := by
      ext v
      simp [T, and_assoc]
    rw [heq]
    exact filtered_common_neighbors_le_two G h N u w huw
  have hdouble : (∑ v ∈ T, ((P.erase u).filter (G.Adj v)).card) =
      ∑ w ∈ P.erase u, (T.filter (G.Adj w)).card := by
    simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow, SimpleGraph.adj_comm] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj
        (s := T) (t := P.erase u))
  have hlo : 3 * T.card ≤ ∑ v ∈ T, ((P.erase u).filter (G.Adj v)).card := by
    calc
      _ = ∑ _v ∈ T, 3 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum hlow
  have hhi : (∑ w ∈ P.erase u, (T.filter (G.Adj w)).card) ≤ 2 * (P.erase u).card := by
    calc
      _ ≤ ∑ _w ∈ P.erase u, 2 := Finset.sum_le_sum hupp
      _ = _ := by simp [Nat.mul_comm]
  rw [hdouble] at hlo
  rw [Finset.card_erase_of_mem hu] at hhi
  exact hlo.trans hhi

theorem bipartite_four_neighbors_support_bound (h : G.IsSRGWith 99 14 1 2)
    (P N : Finset V) (hP : P.Nonempty)
    (hp : ∀ u ∈ P, 4 ≤ (N.filter (G.Adj u)).card)
    (hn : ∀ v ∈ N, 4 ≤ (P.filter (G.Adj v)).card) : 7 ≤ P.card := by
  obtain ⟨u, hu⟩ := hP
  have hlo := hp u hu
  have hhi := bipartite_four_neighbors_degree_bound G h P N u hu hn
  omega

#print axioms bipartite_four_neighbors_support_bound

end Conway99
