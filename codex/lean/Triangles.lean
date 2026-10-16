import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

/-! Graph-level triangle consequences of `G.IsSRGWith 99 14 1 2`.

The declarations below do not use the open `SimpleGraph.conway_99`
declaration. A triangle is specified by its three adjacency relations.
-/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Each edge belongs to a unique triangle. -/
theorem edge_unique_common_neighbor (h : G.IsSRGWith 99 14 1 2)
    {u v : V} (huv : G.Adj u v) :
    ∃! w : V, G.Adj u w ∧ G.Adj v w := by
  obtain ⟨w, hw⟩ := Fintype.card_eq_one_iff.mp (h.of_adj u v huv)
  refine ⟨w.val, w.property, ?_⟩
  intro z hz
  exact congrArg Subtype.val (hw ⟨z, hz⟩)

/-- Two common neighbors of an adjacent pair must coincide. -/
theorem edge_common_neighbor_eq (h : G.IsSRGWith 99 14 1 2)
    {u v x y : V} (huv : G.Adj u v)
    (hux : G.Adj u x) (hvx : G.Adj v x)
    (huy : G.Adj u y) (hvy : G.Adj v y) : x = y := by
  obtain ⟨w, _, hw⟩ := edge_unique_common_neighbor G h huv
  exact (hw x ⟨hux, hvx⟩).trans (hw y ⟨huy, hvy⟩).symm

/-- A point different from the third vertex of a triangle cannot touch
    both endpoints of its opposite edge. -/
theorem triangle_exterior_not_two (h : G.IsSRGWith 99 14 1 2)
    {a b c x : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hca : G.Adj c a) (hxc : x ≠ c) :
    ¬ (G.Adj x a ∧ G.Adj x b) := by
  rintro ⟨hxa, hxb⟩
  exact hxc (edge_common_neighbor_eq G h hab hxa.symm hxb.symm hca.symm hbc)

/-- A vertex outside a triangle has at most one neighbor on it. -/
theorem triangle_exterior_neighbor_card [DecidableEq V] (h : G.IsSRGWith 99 14 1 2)
    {a b c x : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hca : G.Adj c a) (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) :
    ((G.neighborFinset x) ∩ ({a, b, c} : Finset V)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
    Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with ⟨hxu, hu | hu | hu⟩ <;>
    rcases hv with ⟨hxv, hv | hv | hv⟩ <;> subst u <;> subst v
  · rfl
  · exact False.elim (triangle_exterior_not_two G h hab hbc hca hxc ⟨hxu, hxv⟩)
  · exact False.elim
      (triangle_exterior_not_two G h hca hab hbc hxb ⟨hxv, hxu⟩)
  · exact False.elim (triangle_exterior_not_two G h hab hbc hca hxc ⟨hxv, hxu⟩)
  · rfl
  · exact False.elim
      (triangle_exterior_not_two G h hbc hca hab hxa ⟨hxu, hxv⟩)
  · exact False.elim
      (triangle_exterior_not_two G h hca hab hbc hxb ⟨hxu, hxv⟩)
  · exact False.elim
      (triangle_exterior_not_two G h hbc hca hab hxa ⟨hxv, hxu⟩)
  · rfl

/-- The graph induced on a vertex's neighbors is regular of degree one. -/
theorem neighborhood_regular_one (h : G.IsSRGWith 99 14 1 2) (u : V) :
    (G.induce (G.neighborSet u)).IsRegularOfDegree 1 := by
  intro v
  let e : (G.induce (G.neighborSet u)).neighborSet v ≃ G.commonNeighbors u v :=
    { toFun := fun w => ⟨w.val.val, ⟨w.val.property, w.property⟩⟩
      invFun := fun w => ⟨⟨w.val, w.property.1⟩, w.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact (Fintype.card_congr e).trans (h.of_adj u v v.property)

/-- There are fourteen vertices in each induced neighborhood. -/
theorem neighborhood_card_fourteen (h : G.IsSRGWith 99 14 1 2) (u : V) :
    Fintype.card (G.neighborSet u) = 14 := by
  rw [SimpleGraph.card_neighborSet_eq_degree]
  exact h.regular u

/-- The fourteen neighbors form seven disjoint edges: degree one above,
    and exactly seven edges here. Each such edge gives a triangle at `u`. -/
theorem neighborhood_seven_edges (h : G.IsSRGWith 99 14 1 2) (u : V) :
    (G.induce (G.neighborSet u)).edgeFinset.card = 7 := by
  have hs := (G.induce (G.neighborSet u)).sum_degrees_eq_twice_card_edges
  have hr := neighborhood_regular_one G h u
  simp only [hr.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hs
  rw [neighborhood_card_fourteen G h u] at hs
  omega

/-- The graph has exactly 693 edges. -/
theorem graph_edges_693 (h : G.IsSRGWith 99 14 1 2) : G.edgeFinset.card = 693 := by
  have hs := G.sum_degrees_eq_twice_card_edges
  simp only [h.regular.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hs
  rw [h.card] at hs
  omega

#print axioms edge_unique_common_neighbor
#print axioms edge_common_neighbor_eq
#print axioms triangle_exterior_not_two
#print axioms triangle_exterior_neighbor_card
#print axioms neighborhood_regular_one
#print axioms neighborhood_card_fourteen
#print axioms neighborhood_seven_edges
#print axioms graph_edges_693

end Conway99
