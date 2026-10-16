import RootEquitable

/-! The two canonical cocliques of size 22 associated with a root code. -/

namespace Conway99

open scoped BigOperators Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def rootPositiveHoffman (b : V → ℤ) : Finset V := positiveCodeSupport b ∪ rootIsolated G b
def rootNegativeHoffman (b : V → ℤ) : Finset V := negativeCodeSupport b ∪ rootIsolated G b

theorem not_adj_of_filter_card_zero (T : Finset V) (u : V)
    (hz : (T.filter (G.Adj u)).card = 0) {v : V} (hv : v ∈ T) : ¬G.Adj u v := by
  intro huv
  have hm := Finset.mem_filter.mpr ⟨hv, huv⟩
  rw [Finset.card_eq_zero.mp hz] at hm
  exact Finset.not_mem_empty v hm

theorem signed_biplane_isolated_degree_zero (h : G.IsSRGWith 99 14 1 2)
    (b : V → ℤ) (hb : SignedBiplaneCode G b)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u)
    (u : V) (hu : u ∉ rootShell G b) :
    ((rootIsolated G b).filter (G.Adj u)).card = 0 := by
  have hh := congrFun (signed_biplane_isolated_adjacency G h b hb he) u
  rw [finiteIndicator_adjacency] at hh
  simp only [Pi.smul_apply, smul_eq_mul, finiteIndicator, if_neg hu, mul_zero] at hh
  exact_mod_cast hh

theorem signed_biplane_canonical_hoffman (h : G.IsSRGWith 99 14 1 2)
    (b : V → ℤ) (hb : SignedBiplaneCode G b)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u) :
    (rootPositiveHoffman G b).card = 22 ∧ G.IsIndepSet (rootPositiveHoffman G b : Set V) ∧
    (rootNegativeHoffman G b).card = 22 ∧ G.IsIndepSet (rootNegativeHoffman G b : Set V) := by
  have hIc := signed_biplane_isolated_card G h b hb he
  have hdisP : Disjoint (positiveCodeSupport b) (rootIsolated G b) := by
    apply Finset.disjoint_left.mpr
    intro u hp hi
    have hp' := (Finset.mem_filter.mp hp).2
    have hi' := (Finset.mem_filter.mp hi).2.1
    omega
  have hdisN : Disjoint (negativeCodeSupport b) (rootIsolated G b) := by
    apply Finset.disjoint_left.mpr
    intro u hn hi
    have hn' := (Finset.mem_filter.mp hn).2
    have hi' := (Finset.mem_filter.mp hi).2.1
    omega
  have hPcard : (rootPositiveHoffman G b).card = 22 := by
    rw [rootPositiveHoffman, Finset.card_union_of_disjoint hdisP, hb.positive_card, hIc]
  have hNcard : (rootNegativeHoffman G b).card = 22 := by
    rw [rootNegativeHoffman, Finset.card_union_of_disjoint hdisN, hb.negative_card, hIc]
  have hPI (u : V) (hu : u ∈ positiveCodeSupport b) : u ∉ rootShell G b := by
    have hv := (Finset.mem_filter.mp hu).2
    simp [rootShell, hv]
  have hNI (u : V) (hu : u ∈ negativeCodeSupport b) : u ∉ rootShell G b := by
    have hv := (Finset.mem_filter.mp hu).2
    simp [rootShell, hv]
  have hII (u : V) (hu : u ∈ rootIsolated G b) : u ∉ rootShell G b := by
    have hv := (Finset.mem_filter.mp hu).2
    simp only [rootShell, Finset.mem_filter, Finset.mem_univ, true_and, hv.1, hv.2]
    norm_num
  have hPind : G.IsIndepSet (rootPositiveHoffman G b : Set V) := by
    rw [SimpleGraph.isIndepSet_iff]
    intro u hu v hv _hne
    change u ∈ positiveCodeSupport b ∪ rootIsolated G b at hu
    change v ∈ positiveCodeSupport b ∪ rootIsolated G b at hv
    rcases Finset.mem_union.mp hu with hu | hu <;> rcases Finset.mem_union.mp hv with hv | hv
    · exact not_adj_of_filter_card_zero G _ u (hb.positive_internal u hu) hv
    · exact not_adj_of_filter_card_zero G _ u
        (signed_biplane_isolated_degree_zero G h b hb he u (hPI u hu)) hv
    · intro huv
      exact not_adj_of_filter_card_zero G _ v
        (signed_biplane_isolated_degree_zero G h b hb he v (hPI v hv)) hu huv.symm
    · exact not_adj_of_filter_card_zero G _ u
        (signed_biplane_isolated_degree_zero G h b hb he u (hII u hu)) hv
  have hNind : G.IsIndepSet (rootNegativeHoffman G b : Set V) := by
    rw [SimpleGraph.isIndepSet_iff]
    intro u hu v hv _hne
    change u ∈ negativeCodeSupport b ∪ rootIsolated G b at hu
    change v ∈ negativeCodeSupport b ∪ rootIsolated G b at hv
    rcases Finset.mem_union.mp hu with hu | hu <;> rcases Finset.mem_union.mp hv with hv | hv
    · exact not_adj_of_filter_card_zero G _ u (hb.negative_internal u hu) hv
    · exact not_adj_of_filter_card_zero G _ u
        (signed_biplane_isolated_degree_zero G h b hb he u (hNI u hu)) hv
    · intro huv
      exact not_adj_of_filter_card_zero G _ v
        (signed_biplane_isolated_degree_zero G h b hb he v (hNI v hv)) hu huv.symm
    · exact not_adj_of_filter_card_zero G _ u
        (signed_biplane_isolated_degree_zero G h b hb he u (hII u hu)) hv
  exact ⟨hPcard, hPind, hNcard, hNind⟩

#print axioms signed_biplane_canonical_hoffman

end Conway99
