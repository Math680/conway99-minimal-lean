import FourDirectionOneCells
import ProfileBudget

/-! The three perfect matchings on the simple vertices in the one-point case. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace OnePointConfiguration

variable {F : FourDirectionSystem G} (C : OnePointConfiguration F)

def swap : OnePointConfiguration F where
  srg := C.srg
  signedCells := C.signedCells
  zero_count := C.zero_count
  o := C.o
  v := C.w
  w := C.v
  o_mem := C.o_mem
  o_weight := C.o_weight
  v_mem := C.w_mem
  w_mem := C.v_mem
  vw_ne := C.vw_ne.symm
  ov_adj := C.ow_adj
  ow_adj := C.ov_adj
  vw_adj := C.vw_adj.symm
  v_weight := C.w_weight
  w_weight := C.v_weight
  opposite := fun i => by have hh := C.opposite i; omega
  common_unique := fun x hx hy => C.common_unique x hy hx

theorem mem_Vset (u : V) :
    u ∈ C.Vset ↔ u ≠ C.w ∧ u ≠ C.o ∧ G.Adj C.v u := by
  simp [Vset, FourDirectionSystem.outsideTriangleNeighbors]

theorem mem_Wset (u : V) :
    u ∈ C.Wset ↔ u ≠ C.v ∧ u ≠ C.o ∧ G.Adj C.w u := by
  simp [Wset, FourDirectionSystem.outsideTriangleNeighbors]

theorem simple_not_adj_o {u : V} (hu : u ∈ F.W) (hs : F.weight u = 1) : ¬G.Adj C.o u := by
  intro ha
  have hw := F.zero_neighbors_weight_four C.srg C.o C.o_mem C.o_weight u
    (Finset.mem_filter.mpr ⟨hu,ha⟩)
  omega

theorem Vset_not_adj_o {u : V} (hu : u ∈ C.Vset) : ¬G.Adj C.o u :=
  C.simple_not_adj_o (C.Vset_mem_W hu) (C.Vset_simple hu)

theorem Wset_not_adj_o {u : V} (hu : u ∈ C.Wset) : ¬G.Adj C.o u :=
  C.simple_not_adj_o (C.Wset_mem_W hu) (C.Wset_simple hu)

theorem Vset_not_adj_w {u : V} (hu : u ∈ C.Vset) : ¬G.Adj C.w u := by
  intro ha
  have hm := (C.mem_Vset u).mp hu
  exact hm.2.1 (C.common_unique u hm.2.2 ha)

theorem Wset_not_adj_v {u : V} (hu : u ∈ C.Wset) : ¬G.Adj C.v u := by
  intro ha
  have hm := (C.mem_Wset u).mp hu
  exact hm.2.1 (C.common_unique u ha hm.2.2)

theorem Vset_internal_common_eq {u : V} (hu : u ∈ C.Vset) :
    C.Vset.filter (G.Adj u) = (G.commonNeighbors C.v u).toFinset := by
  ext x
  simp only [Finset.mem_filter, Set.mem_toFinset, SimpleGraph.mem_commonNeighbors]
  constructor
  · intro hx
    exact ⟨((C.mem_Vset x).mp hx.1).2.2,hx.2⟩
  · intro hx
    refine ⟨(C.mem_Vset x).mpr ⟨?_,?_,hx.1⟩,hx.2⟩
    · intro he
      subst x
      exact C.Vset_not_adj_w hu hx.2.symm
    · intro he
      subst x
      exact C.Vset_not_adj_o hu hx.2.symm

theorem Vset_internal_degree {u : V} (hu : u ∈ C.Vset) :
    (C.Vset.filter (G.Adj u)).card = 1 := by
  rw [C.Vset_internal_common_eq hu, Set.toFinset_card]
  exact C.srg.of_adj C.v u ((C.mem_Vset u).mp hu).2.2

theorem Wset_internal_degree {u : V} (hu : u ∈ C.Wset) :
    (C.Wset.filter (G.Adj u)).card = 1 :=
  C.swap.Vset_internal_degree hu

theorem Vset_cross_common_eq {u : V} (hu : u ∈ C.Vset) :
    (G.commonNeighbors u C.w).toFinset = insert C.v (C.Wset.filter (G.Adj u)) := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_filter, Set.mem_toFinset,
    SimpleGraph.mem_commonNeighbors]
  constructor
  · intro hx
    by_cases he : x = C.v
    · exact Or.inl he
    · apply Or.inr
      refine ⟨(C.mem_Wset x).mpr ⟨he,?_,hx.2⟩,hx.1⟩
      intro heo
      subst x
      exact C.Vset_not_adj_o hu hx.1.symm
  · intro hx
    rcases hx with rfl | hx
    · exact ⟨((C.mem_Vset u).mp hu).2.2.symm,C.vw_adj.symm⟩
    · exact ⟨hx.2,((C.mem_Wset x).mp hx.1).2.2⟩

theorem Vset_cross_degree {u : V} (hu : u ∈ C.Vset) :
    (C.Wset.filter (G.Adj u)).card = 1 := by
  have hm := (C.mem_Vset u).mp hu
  have hc := C.srg.of_not_adj hm.1 (fun ha => C.Vset_not_adj_w hu ha.symm)
  have hn : C.v ∉ C.Wset.filter (G.Adj u) := by
    intro hh
    exact ((C.mem_Wset C.v).mp (Finset.mem_filter.mp hh).1).1 rfl
  have hcard : ((G.commonNeighbors u C.w).toFinset).card = 2 := by simpa using hc
  rw [C.Vset_cross_common_eq hu, Finset.card_insert_of_notMem hn] at hcard
  omega

theorem Wset_cross_degree {u : V} (hu : u ∈ C.Wset) :
    (C.Vset.filter (G.Adj u)).card = 1 :=
  C.swap.Vset_cross_degree hu

theorem Vi_same_label_not_adj (i : Fin 4) {u x : V}
    (hu : u ∈ C.Vi i) (hx : x ∈ C.Vi i) : ¬G.Adj u x := by
  apply F.same_nonzero_coordinate_not_adj i (Finset.mem_filter.mp hu).2
  rw [C.Vi_code hu,C.Vi_code hx]

theorem Wi_same_label_not_adj (i : Fin 4) {u x : V}
    (hu : u ∈ C.Wi i) (hx : x ∈ C.Wi i) : ¬G.Adj u x := by
  apply F.same_nonzero_coordinate_not_adj i (Finset.mem_filter.mp hu).2
  rw [C.Wi_code hu,C.Wi_code hx]

theorem Vset_internal_edges : profileEdgeCount G C.Vset = 6 := by
  have hh := profile_degree_sum_eq_twice_edges G C.Vset
  have hs : profileDegreeSum G C.Vset = 12 := by
    unfold profileDegreeSum profileDegree
    simp only [Finset.sum_congr rfl (fun u hu => C.Vset_internal_degree hu),
      Finset.sum_const, C.Vset_card]
    norm_num
  omega

theorem Wset_internal_edges : profileEdgeCount G C.Wset = 6 :=
  C.swap.Vset_internal_edges

#print axioms Vset_internal_degree
#print axioms Vset_cross_degree
#print axioms Vset_internal_edges

end OnePointConfiguration
end Conway99
