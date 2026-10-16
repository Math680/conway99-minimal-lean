import FourDirectionOneTriangle

/-! The twelve nontriangle neighbors of either full-signature vertex are simple. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace FourDirectionSystem

variable (F : FourDirectionSystem G)

theorem full_weight_support_neighbor_count {v : V} (hv : F.weight v = 4)
    (i : Fin 4) : ((rootSupport (F.code i)).filter (G.Adj v)).card = 4 := by
  have hc := (F.weight_four_iff v).mp hv i
  have hd : Disjoint (positiveCodeSupport (F.code i)) (negativeCodeSupport (F.code i)) := by
    apply Finset.disjoint_left.mpr
    intro x hp hn
    have hp' := (Finset.mem_filter.mp hp).2
    have hn' := (Finset.mem_filter.mp hn).2
    omega
  have heq : ((rootSupport (F.code i)).filter (G.Adj v)).card =
      ((positiveCodeSupport (F.code i)).filter (G.Adj v)).card +
      ((negativeCodeSupport (F.code i)).filter (G.Adj v)).card := by
    rw [rootSupport, Finset.filter_union,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hd)]
  rw [heq]
  rcases (F.biplane i).signs v with hn | hz | hp
  · have hvN : v ∈ negativeCodeSupport (F.code i) := by simp [negativeCodeSupport, hn]
    rw [(F.biplane i).negative_cross v hvN, (F.biplane i).negative_internal v hvN]
  · exact (hc hz).elim
  · have hvP : v ∈ positiveCodeSupport (F.code i) := by simp [positiveCodeSupport, hp]
    rw [(F.biplane i).positive_cross v hvP, (F.biplane i).positive_internal v hvP]

theorem full_weight_neighbor_weight_sum {v : V} (hv : F.weight v = 4) :
    (∑ u ∈ Finset.univ.filter (G.Adj v), F.weight u) = 16 := by
  unfold weight
  rw [Finset.sum_comm]
  have hh (i : Fin 4) :
      (∑ u ∈ Finset.univ.filter (G.Adj v),
        if u ∈ rootSupport (F.code i) then (1 : ℤ) else 0) = 4 := by
    have heq : (Finset.univ.filter (G.Adj v)).filter
        (fun u => u ∈ rootSupport (F.code i)) = (rootSupport (F.code i)).filter (G.Adj v) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one,
      mul_zero, add_zero]
    rw [heq, F.full_weight_support_neighbor_count hv i]
    norm_num
  simp only [hh, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

def outsideTriangleNeighbors (_F : FourDirectionSystem G) (o v w : V) : Finset V :=
  ((Finset.univ.filter (G.Adj v)).erase o).erase w

theorem outsideTriangleNeighbors_card (h : G.IsSRGWith 99 14 1 2)
    {o v w : V} (hvo : G.Adj v o) (hvw : G.Adj v w) (how : o ≠ w) :
    (F.outsideTriangleNeighbors o v w).card = 12 := by
  have hdeg : (Finset.univ.filter (G.Adj v)).card = 14 := by
    simpa [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter] using h.regular.degree_eq v
  have ho : o ∈ Finset.univ.filter (G.Adj v) := by simp [hvo]
  have hw : w ∈ (Finset.univ.filter (G.Adj v)).erase o := by simp [hvw, how.symm]
  rw [outsideTriangleNeighbors, Finset.card_erase_of_mem hw,
    Finset.card_erase_of_mem ho, hdeg]

theorem outsideTriangleNeighbors_weight_sum {o v w : V}
    (hzo : F.weight o = 0) (hfv : F.weight v = 4) (hfw : F.weight w = 4)
    (hvo : G.Adj v o) (hvw : G.Adj v w) (how : o ≠ w) :
    (∑ u ∈ F.outsideTriangleNeighbors o v w, F.weight u) = 12 := by
  have ho : o ∈ Finset.univ.filter (G.Adj v) := by simp [hvo]
  have hw : w ∈ (Finset.univ.filter (G.Adj v)).erase o := by simp [hvw, how.symm]
  have h1 := Finset.sum_erase_add (Finset.univ.filter (G.Adj v)) F.weight ho
  have h2 := Finset.sum_erase_add ((Finset.univ.filter (G.Adj v)).erase o) F.weight hw
  rw [F.full_weight_neighbor_weight_sum hfv, hzo] at h1
  rw [hfw] at h2
  change (∑ u ∈ ((Finset.univ.filter (G.Adj v)).erase o).erase w, F.weight u) = 12
  omega

theorem outsideTriangleNeighbors_simple (h : G.IsSRGWith 99 14 1 2)
    (hz : F.weightCount 0 = 1) {o v w : V}
    (ho : o ∈ F.W) (hzo : F.weight o = 0)
    (hfv : F.weight v = 4) (hfw : F.weight w = 4)
    (hvo : G.Adj v o) (hvw : G.Adj v w) (how : o ≠ w) :
    ∀ u ∈ F.outsideTriangleNeighbors o v w, F.weight u = 1 := by
  have hle (u : V) (hu : u ∈ F.outsideTriangleNeighbors o v w) : (1 : ℤ) ≤ F.weight u := by
    have hu' := Finset.mem_erase.mp hu
    have hu'' := Finset.mem_erase.mp hu'.2
    have hvu := (Finset.mem_filter.mp hu''.2).2
    have huW : u ∈ F.W := by
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro huI
      exact F.full_weight_not_adj_isolated h hfv huI hvu
    have hne : F.weight u ≠ 0 := by
      intro hzero
      exact hu''.1 (F.one_zero_unique hz ho hzo huW hzero)
    have hnon := F.weight_nonneg u
    omega
  have heq : (∑ u ∈ F.outsideTriangleNeighbors o v w, (1 : ℤ)) =
      ∑ u ∈ F.outsideTriangleNeighbors o v w, F.weight u := by
    rw [F.outsideTriangleNeighbors_weight_sum hzo hfv hfw hvo hvw how]
    simp [F.outsideTriangleNeighbors_card h hvo hvw how]
  have hh := (Finset.sum_eq_sum_iff_of_le hle).mp heq
  intro u hu
  exact (hh u hu).symm

#print axioms outsideTriangleNeighbors_simple

end FourDirectionSystem
end Conway99
