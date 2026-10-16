import RootBiplane

/-! The 14/70/15 vertex partition of a signed root biplane. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem biplane_external_degree_le_one (h : G.IsSRGWith 99 14 1 2)
    (P N : Finset V)
    (hpairs : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      (N.filter (fun v => G.Adj p v ∧ G.Adj q v)).card = 2)
    (u : V) (hu : u ∉ N) : (P.filter (G.Adj u)).card ≤ 1 := by
  by_contra hnot
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < (P.filter (G.Adj u)).card)
  have hpP := (Finset.mem_filter.mp hp).1
  have hqP := (Finset.mem_filter.mp hq).1
  have hup := (Finset.mem_filter.mp hp).2
  have huq := (Finset.mem_filter.mp hq).2
  let T := N.filter (fun v => G.Adj p v ∧ G.Adj q v)
  have hT : T.card = 2 := hpairs p hpP q hqP hpq
  have huT : u ∉ T := fun hh => hu (Finset.mem_filter.mp hh).1
  have hsub : insert u T ⊆ Finset.univ.filter (fun v => G.Adj p v ∧ G.Adj q v) := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hup.symm, huq.symm⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
  have hcard := Finset.card_le_card hsub
  have hbound := filtered_common_neighbors_le_two G h Finset.univ p q hpq
  rw [Finset.card_insert_of_notMem huT, hT] at hcard
  omega

def rootShell (b : V → ℤ) : Finset V :=
  Finset.univ.filter (fun u => b u = 0 ∧ ((positiveCodeSupport b).filter (G.Adj u)).card = 1)

def rootIsolated (b : V → ℤ) : Finset V :=
  Finset.univ.filter (fun u => b u = 0 ∧ ((positiveCodeSupport b).filter (G.Adj u)).card = 0)

theorem signed_biplane_zero_degrees (h : G.IsSRGWith 99 14 1 2)
    (b : V → ℤ) (hb : SignedBiplaneCode G b)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u)
    (u : V) (hu : b u = 0) :
    (((positiveCodeSupport b).filter (G.Adj u)).card = 0 ∧
      ((negativeCodeSupport b).filter (G.Adj u)).card = 0) ∨
    (((positiveCodeSupport b).filter (G.Adj u)).card = 1 ∧
      ((negativeCodeSupport b).filter (G.Adj u)).card = 1) := by
  have huN : u ∉ negativeCodeSupport b := by simp [negativeCodeSupport, hu]
  have hp := biplane_external_degree_le_one G h _ _ hb.positive_pairs u huN
  have hh := sign_code_neighbor_sum G b hb.signs u
  rw [he, hu] at hh
  omega

theorem signed_biplane_shell_card (h : G.IsSRGWith 99 14 1 2)
    (b : V → ℤ) (hb : SignedBiplaneCode G b)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u) :
    (rootShell G b).card = 70 := by
  classical
  have hpoint (u : V) : (((positiveCodeSupport b).filter (G.Adj u)).card : ℕ) =
      (if b u = -1 then 4 else 0) + (if u ∈ rootShell G b then 1 else 0) := by
    rcases hb.signs u with hu | hu | hu
    · have hm : u ∈ negativeCodeSupport b := by simp [negativeCodeSupport, hu]
      rw [hb.negative_cross u hm]
      simp [rootShell, hu]
    · have hh := signed_biplane_zero_degrees G h b hb he u hu
      rcases hh with hh | hh <;> simp [rootShell, hu, hh.1]
    · have hm : u ∈ positiveCodeSupport b := by simp [positiveCodeSupport, hu]
      rw [hb.positive_internal u hm]
      simp [rootShell, hu]
  have hdouble : (∑ u, ((positiveCodeSupport b).filter (G.Adj u)).card) =
      ∑ v ∈ positiveCodeSupport b, (Finset.univ.filter (G.Adj v)).card := by
    simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow, SimpleGraph.adj_comm] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj
        (s := Finset.univ) (t := positiveCodeSupport b))
  have hdeg (v : V) : (Finset.univ.filter (G.Adj v)).card = 14 := by
    simpa [SimpleGraph.degree, SimpleGraph.neighborFinset_def] using h.regular.degree_eq v
  have hsum : (∑ u, ((positiveCodeSupport b).filter (G.Adj u)).card) = 98 := by
    rw [hdouble, Finset.sum_congr rfl (fun v _ => hdeg v)]
    simp [hb.positive_card]
  rw [Finset.sum_congr rfl (fun u _ => hpoint u), Finset.sum_add_distrib] at hsum
  have hneg : (∑ u : V, if b u = -1 then 4 else 0) = 28 := by
    simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul]
    change (negativeCodeSupport b).card * 4 = 28
    rw [hb.negative_card]
  rw [hneg] at hsum
  have hshell : (∑ u : V, if u ∈ rootShell G b then 1 else 0) = (rootShell G b).card := by
    simp
  rw [hshell] at hsum
  omega

theorem signed_biplane_isolated_card (h : G.IsSRGWith 99 14 1 2)
    (b : V → ℤ) (hb : SignedBiplaneCode G b)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u) :
    (rootIsolated G b).card = 15 := by
  have hpoint (u : V) : (1 : ℕ) =
      (if b u = 1 then 1 else 0) + (if b u = -1 then 1 else 0) +
      (if u ∈ rootShell G b then 1 else 0) + (if u ∈ rootIsolated G b then 1 else 0) := by
    rcases hb.signs u with hu | hu | hu
    · simp [hu, rootShell, rootIsolated]
    · rcases signed_biplane_zero_degrees G h b hb he u hu with hh | hh <;>
        simp only [rootShell, rootIsolated, Finset.mem_filter, Finset.mem_univ, hu, hh.1] <;> norm_num
    · simp [hu, rootShell, rootIsolated]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun u _ => hpoint u)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, h.card,
    nsmul_eq_mul, mul_one] at hsum
  have hpos : (∑ u : V, if b u = 1 then 1 else 0) = (positiveCodeSupport b).card := by
    simp [positiveCodeSupport]
  have hneg : (∑ u : V, if b u = -1 then 1 else 0) = (negativeCodeSupport b).card := by
    simp [negativeCodeSupport]
  have hshell : (∑ u : V, if u ∈ rootShell G b then 1 else 0) = (rootShell G b).card := by simp
  have hisol : (∑ u : V, if u ∈ rootIsolated G b then 1 else 0) = (rootIsolated G b).card := by simp
  rw [hpos, hneg, hshell, hisol, hb.positive_card, hb.negative_card,
    signed_biplane_shell_card G h b hb he] at hsum
  omega

#print axioms signed_biplane_zero_degrees
#print axioms signed_biplane_shell_card
#print axioms signed_biplane_isolated_card

end Conway99
