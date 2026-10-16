import FourDirectionOneRDegree
import SignaturePacking

/-! Necessary neighbourhood constraints for the finite zero-point certificate.
The equations and common-neighbour budgets concern the actual graph. -/

namespace Conway99

open scoped BigOperators

def signatureEdgeAllowed (a b : RootSignature) : Prop :=
  ∀ i, a i ≠ 1 → b i ≠ 1 → a i ≠ b i

namespace FourDirectionSystem

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (F : FourDirectionSystem G)

theorem adjacent_signatures_allowed {u v : V} (ha : G.Adj u v) :
    signatureEdgeAllowed (F.signature u) (F.signature v) := by
  intro i hi hj heq
  have hcode : F.code i u = F.code i v := by
    have hh := congrArg (fun a : Fin 3 => (a.val : ℤ)) heq
    change ((F.signature u i).val : ℤ) = ((F.signature v i).val : ℤ) at hh
    rw [F.signature_val, F.signature_val] at hh
    omega
  exact F.same_nonzero_coordinate_not_adj i ((F.signature_nonzero_iff u i).mp hi) hcode ha

theorem isolated_union_code_zero {u : V} (hu : u ∈ F.isolatedUnion) (i : Fin 4) :
    F.code i u = 0 := by
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hu
  by_contra hne
  exact Finset.disjoint_left.mp (F.support_avoids_isolated i j)
    ((F.mem_support_iff_code_ne_zero i u).mpr hne) hj

theorem W_neighbor_code_moment (v : V) (i : Fin 4) :
    (∑ u ∈ F.W.filter (G.Adj v), F.code i u) = -4 * F.code i v := by
  rw [Finset.sum_filter]
  calc
    _ = ∑ u, if G.Adj v u then F.code i u else 0 := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro u hu hnu
      have hI : u ∈ F.isolatedUnion := by
        simpa only [W, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] using hnu
      rw [F.isolated_union_code_zero hI i]
      simp
    _ = _ := F.eigen i v

theorem nonzero_coordinate_not_adj_isolated (h : G.IsSRGWith 99 14 1 2)
    (i : Fin 4) {v u : V} (hv : F.code i v ≠ 0) (hu : u ∈ rootIsolated G (F.code i)) :
    ¬ G.Adj v u := by
  have hs : v ∉ rootShell G (F.code i) := by simp [rootShell, hv]
  exact not_adj_of_filter_card_zero G _ v
    (signed_biplane_isolated_degree_zero G h _ (F.biplane i) (F.eigen i) v hs) hu

theorem common_neighbors_mem_W_of_no_shared_zero
    (h : G.IsSRGWith 99 14 1 2) {v w u : V}
    (hz : ∀ i, F.code i v ≠ 0 ∨ F.code i w ≠ 0)
    (hv : G.Adj v u) (hw : G.Adj w u) : u ∈ F.W := by
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hu
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hu
  rcases hz i with hi' | hi'
  · exact F.nonzero_coordinate_not_adj_isolated h i hi' hi hv
  · exact F.nonzero_coordinate_not_adj_isolated h i hi' hi hw

theorem W_common_neighbors_exact_of_no_shared_zero
    (h : G.IsSRGWith 99 14 1 2) {v w : V} (hne : v ≠ w)
    (hz : ∀ i, F.code i v ≠ 0 ∨ F.code i w ≠ 0) :
    (F.W.filter (fun u => G.Adj v u ∧ G.Adj w u)).card =
      if G.Adj v w then 1 else 2 := by
  have heq : F.W.filter (fun u => G.Adj v u ∧ G.Adj w u) =
      (G.commonNeighbors v w).toFinset := by
    ext u
    simp only [Finset.mem_filter, Set.mem_toFinset]
    constructor
    · exact fun hu => hu.2
    · intro hu
      exact ⟨F.common_neighbors_mem_W_of_no_shared_zero h hz hu.1 hu.2, hu⟩
  rw [heq, Set.toFinset_card]
  by_cases ha : G.Adj v w
  · rw [if_pos ha, h.of_adj v w ha]
  · rw [if_neg ha, h.of_not_adj hne ha]

#print axioms adjacent_signatures_allowed
#print axioms W_neighbor_code_moment
#print axioms W_common_neighbors_exact_of_no_shared_zero

end FourDirectionSystem
end Conway99
