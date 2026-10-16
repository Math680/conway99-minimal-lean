import RootPartition

/-! The quotient equations for the 14/70/15 partition. -/

namespace Conway99

open scoped BigOperators Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def finiteIndicator (T : Finset V) : V → ℚ := fun u => if u ∈ T then 1 else 0
def rootSupport (b : V → ℤ) : Finset V := positiveCodeSupport b ∪ negativeCodeSupport b

theorem finiteIndicator_adjacency (T : Finset V) (u : V) :
    (G.adjMatrix ℚ *ᵥ finiteIndicator T) u = ((T.filter (G.Adj u)).card : ℚ) := by
  classical
  simp only [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply, finiteIndicator]
  have hp (v : V) : (if G.Adj u v then (1 : ℚ) else 0) * (if v ∈ T then 1 else 0) =
      if v ∈ T ∧ G.Adj u v then 1 else 0 := by
    by_cases ha : G.Adj u v <;> by_cases hv : v ∈ T <;> simp [ha, hv]
  simp_rw [hp]
  simp only [Finset.sum_boole, Finset.filter_filter]
  congr 2
  ext v
  simp

theorem finiteIndicator_sum (T : Finset V) : ∑ u, finiteIndicator T u = (T.card : ℚ) := by
  simp [finiteIndicator]

theorem signed_biplane_support_card (b : V → ℤ) (hb : SignedBiplaneCode G b) :
    (rootSupport b).card = 14 := by
  have hd : Disjoint (positiveCodeSupport b) (negativeCodeSupport b) := by
    apply Finset.disjoint_left.mpr
    intro u hp hn
    have hp' := (Finset.mem_filter.mp hp).2
    have hn' := (Finset.mem_filter.mp hn).2
    omega
  rw [rootSupport, Finset.card_union_of_disjoint hd, hb.positive_card, hb.negative_card]

theorem signed_biplane_indicator_partition (h : G.IsSRGWith 99 14 1 2)
    (b : V → ℤ) (hb : SignedBiplaneCode G b)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u) :
    finiteIndicator (rootSupport b) + finiteIndicator (rootShell G b) +
      finiteIndicator (rootIsolated G b) = (fun _ => (1 : ℚ)) := by
  ext u
  rcases hb.signs u with hu | hu | hu
  · simp [finiteIndicator, rootSupport, positiveCodeSupport, negativeCodeSupport,
      rootShell, rootIsolated, hu]
  · rcases signed_biplane_zero_degrees G h b hb he u hu with hh | hh <;>
      simp only [Pi.add_apply, finiteIndicator, rootSupport,
        rootShell, rootIsolated, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, hu, hh.1] <;>
      simp [positiveCodeSupport, negativeCodeSupport, hu] <;> norm_num
  · simp [finiteIndicator, rootSupport, positiveCodeSupport, negativeCodeSupport,
      rootShell, rootIsolated, hu]

theorem signed_biplane_support_adjacency (h : G.IsSRGWith 99 14 1 2)
    (b : V → ℤ) (hb : SignedBiplaneCode G b)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u) :
    G.adjMatrix ℚ *ᵥ finiteIndicator (rootSupport b) =
      (4 : ℚ) • finiteIndicator (rootSupport b) +
      (2 : ℚ) • finiteIndicator (rootShell G b) := by
  have hd : Disjoint (positiveCodeSupport b) (negativeCodeSupport b) := by
    apply Finset.disjoint_left.mpr
    intro u hp hn
    have hp' := (Finset.mem_filter.mp hp).2
    have hn' := (Finset.mem_filter.mp hn).2
    omega
  have hcount (u : V) : ((rootSupport b).filter (G.Adj u)).card =
      ((positiveCodeSupport b).filter (G.Adj u)).card +
      ((negativeCodeSupport b).filter (G.Adj u)).card := by
    rw [rootSupport, Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hd)]
  ext u
  rw [finiteIndicator_adjacency, hcount, Nat.cast_add]
  rcases hb.signs u with hu | hu | hu
  · have hm : u ∈ negativeCodeSupport b := by simp [negativeCodeSupport, hu]
    rw [hb.negative_internal u hm, hb.negative_cross u hm]
    simp [finiteIndicator, rootSupport, positiveCodeSupport, negativeCodeSupport, rootShell, hu]
  · rcases signed_biplane_zero_degrees G h b hb he u hu with hh | hh <;>
      rw [hh.1, hh.2] <;>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, finiteIndicator,
        rootSupport, rootShell,
        Finset.mem_union, Finset.mem_filter, Finset.mem_univ, hu, hh.1] <;>
      simp [positiveCodeSupport, negativeCodeSupport, hu] <;> norm_num
  · have hm : u ∈ positiveCodeSupport b := by simp [positiveCodeSupport, hu]
    rw [hb.positive_internal u hm, hb.positive_cross u hm]
    simp [finiteIndicator, rootSupport, positiveCodeSupport, negativeCodeSupport, rootShell, hu]

theorem signed_biplane_shell_adjacency (h : G.IsSRGWith 99 14 1 2)
    (b : V → ℤ) (hb : SignedBiplaneCode G b)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u) :
    G.adjMatrix ℚ *ᵥ finiteIndicator (rootShell G b) =
      (10 : ℚ) • finiteIndicator (rootSupport b) +
      (9 : ℚ) • finiteIndicator (rootShell G b) +
      (14 : ℚ) • finiteIndicator (rootIsolated G b) := by
  have hAC := signed_biplane_support_adjacency G h b hb he
  have hJ : allOnes *ᵥ finiteIndicator (rootSupport b) = (fun _ => (14 : ℚ)) := by
    ext u
    simp [Matrix.mulVec, dotProduct, allOnes, finiteIndicator_sum,
      signed_biplane_support_card G b hb]
  have hAA := congrArg (fun v => G.adjMatrix ℚ *ᵥ v) hAC
  dsimp only at hAA
  rw [Matrix.mulVec_mulVec, adjacency_square G h] at hAA
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul] at hAA
  rw [hAC, hJ] at hAA
  have hpart := signed_biplane_indicator_partition G h b hb he
  ext u
  have h₁ := congrFun hAA u
  have h₂ := congrFun hpart u
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] at h₁ h₂ ⊢
  change 12 * finiteIndicator (rootSupport b) u -
      (4 * finiteIndicator (rootSupport b) u + 2 * finiteIndicator (rootShell G b) u) + 2 * 14 =
      4 * (4 * finiteIndicator (rootSupport b) u + 2 * finiteIndicator (rootShell G b) u) +
      2 * (G.adjMatrix ℚ *ᵥ finiteIndicator (rootShell G b)) u at h₁
  linarith

theorem signed_biplane_isolated_adjacency (h : G.IsSRGWith 99 14 1 2)
    (b : V → ℤ) (hb : SignedBiplaneCode G b)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u) :
    G.adjMatrix ℚ *ᵥ finiteIndicator (rootIsolated G b) =
      (3 : ℚ) • finiteIndicator (rootShell G b) := by
  have hpart := signed_biplane_indicator_partition G h b hb he
  have hA := congrArg (fun v => G.adjMatrix ℚ *ᵥ v) hpart
  dsimp only at hA
  rw [Matrix.mulVec_add, Matrix.mulVec_add,
    signed_biplane_support_adjacency G h b hb he,
    signed_biplane_shell_adjacency G h b hb he] at hA
  have hconst : G.adjMatrix ℚ *ᵥ (fun _ => (1 : ℚ)) = (fun _ => (14 : ℚ)) := by
    ext u
    simpa [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply] using
      (show ((Finset.univ.filter (G.Adj u)).card : ℚ) = 14 by
        exact_mod_cast (show (Finset.univ.filter (G.Adj u)).card = 14 by
          simpa [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter] using h.regular.degree_eq u))
  rw [hconst] at hA
  ext u
  have h₁ := congrFun hA u
  have h₂ := congrFun hpart u
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h₁ h₂ ⊢
  linarith

#print axioms signed_biplane_support_adjacency
#print axioms signed_biplane_shell_adjacency
#print axioms signed_biplane_isolated_adjacency

end Conway99
