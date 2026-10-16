import IntegerEigenMinimum

/-! Equality in the integral eigenvector minimum gives a (7,4,2) biplane. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem bipartite_seven_degree_four (h : G.IsSRGWith 99 14 1 2)
    (P N : Finset V) (hP : P.card = 7)
    (hp : ∀ u ∈ P, 4 ≤ (N.filter (G.Adj u)).card)
    (hn : ∀ v ∈ N, 4 ≤ (P.filter (G.Adj v)).card) :
    ∀ u ∈ P, (N.filter (G.Adj u)).card = 4 := by
  intro u hu
  have hlo := hp u hu
  have hhi := bipartite_four_neighbors_degree_bound G h P N u hu hn
  rw [hP] at hhi
  omega

theorem bipartite_seven_common_two (h : G.IsSRGWith 99 14 1 2)
    (P N : Finset V) (hP : P.card = 7)
    (hp : ∀ u ∈ P, (N.filter (G.Adj u)).card = 4)
    (hn : ∀ v ∈ N, (P.filter (G.Adj v)).card = 4)
    (u w : V) (hu : u ∈ P) (hw : w ∈ P) (huw : u ≠ w) :
    (N.filter (fun v => G.Adj u v ∧ G.Adj w v)).card = 2 := by
  classical
  let T := N.filter (G.Adj u)
  have hT : T.card = 4 := hp u hu
  have hcount (v : V) (hv : v ∈ T) : ((P.erase u).filter (G.Adj v)).card = 3 := by
    have hvN := (Finset.mem_filter.mp hv).1
    have huv := (Finset.mem_filter.mp hv).2
    have hum : u ∈ P.filter (G.Adj v) := Finset.mem_filter.mpr ⟨hu, huv.symm⟩
    have heq : (P.erase u).filter (G.Adj v) = (P.filter (G.Adj v)).erase u := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_erase]
      tauto
    rw [heq, Finset.card_erase_of_mem hum, hn v hvN]
  have hupp (t : V) (ht : t ∈ P.erase u) : (T.filter (G.Adj t)).card ≤ 2 := by
    have hut : u ≠ t := (Finset.mem_erase.mp ht).1.symm
    have heq : T.filter (G.Adj t) = N.filter (fun v => G.Adj u v ∧ G.Adj t v) := by
      ext v
      simp [T, and_assoc]
    rw [heq]
    exact filtered_common_neighbors_le_two G h N u t hut
  have hdouble : (∑ v ∈ T, ((P.erase u).filter (G.Adj v)).card) =
      ∑ t ∈ P.erase u, (T.filter (G.Adj t)).card := by
    simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow, SimpleGraph.adj_comm] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj
        (s := T) (t := P.erase u))
  have hequal : (∑ t ∈ P.erase u, (T.filter (G.Adj t)).card) =
      ∑ _t ∈ P.erase u, 2 := by
    rw [← hdouble, Finset.sum_congr rfl hcount]
    simp [hT, Finset.card_erase_of_mem hu, hP]
  have hall := (Finset.sum_eq_sum_iff_of_le hupp).mp hequal
  have hw' : w ∈ P.erase u := Finset.mem_erase.mpr ⟨huw.symm, hw⟩
  have heq : T.filter (G.Adj w) = N.filter (fun v => G.Adj u v ∧ G.Adj w v) := by
    ext v
    simp [T, and_assoc]
  rw [← heq]
  exact hall w hw'

structure SignedBiplaneCode (b : V → ℤ) : Prop where
  signs : ∀ u, b u = -1 ∨ b u = 0 ∨ b u = 1
  positive_card : (positiveCodeSupport b).card = 7
  negative_card : (negativeCodeSupport b).card = 7
  positive_internal : ∀ u ∈ positiveCodeSupport b,
    ((positiveCodeSupport b).filter (G.Adj u)).card = 0
  negative_internal : ∀ u ∈ negativeCodeSupport b,
    ((negativeCodeSupport b).filter (G.Adj u)).card = 0
  positive_cross : ∀ u ∈ positiveCodeSupport b,
    ((negativeCodeSupport b).filter (G.Adj u)).card = 4
  negative_cross : ∀ u ∈ negativeCodeSupport b,
    ((positiveCodeSupport b).filter (G.Adj u)).card = 4
  positive_pairs : ∀ u ∈ positiveCodeSupport b, ∀ w ∈ positiveCodeSupport b, u ≠ w →
    ((negativeCodeSupport b).filter (fun v => G.Adj u v ∧ G.Adj w v)).card = 2
  negative_pairs : ∀ u ∈ negativeCodeSupport b, ∀ w ∈ negativeCodeSupport b, u ≠ w →
    ((positiveCodeSupport b).filter (fun v => G.Adj u v ∧ G.Adj w v)).card = 2

theorem integer_eigen_norm_fourteen_biplane (h : G.IsSRGWith 99 14 1 2)
    (b : V → ℤ) (hs : ∑ u, b u = 0)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u)
    (hn : ∑ u, b u ^ 2 = 14) : SignedBiplaneCode G b := by
  have hsign := integer_eigen_small_coordinates G b hs he hn.le
  have hsum := sign_code_sum b hsign
  have hnorm := sign_code_norm b hsign
  have hP : (positiveCodeSupport b).card = 7 := by omega
  have hN : (negativeCodeSupport b).card = 7 := by omega
  have hpdeg : ∀ u ∈ positiveCodeSupport b,
      4 ≤ ((negativeCodeSupport b).filter (G.Adj u)).card := by
    intro u hu
    have hv : b u = 1 := (Finset.mem_filter.mp hu).2
    have hh := sign_code_neighbor_sum G b hsign u
    rw [he, hv] at hh
    omega
  have hndeg : ∀ u ∈ negativeCodeSupport b,
      4 ≤ ((positiveCodeSupport b).filter (G.Adj u)).card := by
    intro u hu
    have hv : b u = -1 := (Finset.mem_filter.mp hu).2
    have hh := sign_code_neighbor_sum G b hsign u
    rw [he, hv] at hh
    omega
  have hp4 := bipartite_seven_degree_four G h _ _ hP hpdeg hndeg
  have hn4 := bipartite_seven_degree_four G h _ _ hN hndeg hpdeg
  refine ⟨hsign, hP, hN, ?_, ?_, hp4, hn4, ?_, ?_⟩
  · intro u hu
    have hv : b u = 1 := (Finset.mem_filter.mp hu).2
    have hh := sign_code_neighbor_sum G b hsign u
    rw [he, hv, hp4 u hu] at hh
    omega
  · intro u hu
    have hv : b u = -1 := (Finset.mem_filter.mp hu).2
    have hh := sign_code_neighbor_sum G b hsign u
    rw [he, hv, hn4 u hu] at hh
    omega
  · intro u hu w hw huw
    exact bipartite_seven_common_two G h _ _ hP hp4 hn4 u w hu hw huw
  · intro u hu w hw huw
    exact bipartite_seven_common_two G h _ _ hN hn4 hp4 u w hu hw huw

#print axioms integer_eigen_norm_fourteen_biplane

end Conway99
