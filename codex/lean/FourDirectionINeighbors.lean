import FourDirectionOneRDegree

/-! The five outside-I neighbours of an isolated-cell vertex adjacent to o:
o itself, one simple vertex on each side, and two double vertices. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace OnePointConfiguration

variable {F : FourDirectionSystem G} (C : OnePointConfiguration F)
include C

theorem isolated_cell_not_adj_full {a : Fin 4} {t : V}
    (ht : t ∈ rootIsolated G (F.code a)) : ¬ G.Adj C.v t ∧ ¬ G.Adj C.w t := by
  have hI : t ∈ F.isolatedUnion := Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, ht⟩
  exact ⟨F.full_weight_not_adj_isolated C.srg C.v_weight hI,
    F.full_weight_not_adj_isolated C.srg C.w_weight hI⟩

theorem isolated_cell_ne_full {a : Fin 4} {t : V}
    (ht : t ∈ rootIsolated G (F.code a)) : t ≠ C.v ∧ t ≠ C.w := by
  have hz := (Finset.mem_filter.mp ht).2.1
  constructor
  · intro he
    exact C.v_code_ne a (he ▸ hz)
  · intro he
    exact C.w_code_ne a (he ▸ hz)

theorem isolated_cell_not_adj_support {a : Fin 4} {t u : V}
    (ht : t ∈ rootIsolated G (F.code a)) (hu : u ∈ rootSupport (F.code a)) : ¬ G.Adj t u := by
  have hnotC : t ∉ rootSupport (F.code a) := fun hh =>
    Finset.disjoint_left.mp (F.support_avoids_isolated a a) hh ht
  have hnotS : t ∉ rootShell G (F.code a) := by
    intro hs
    have h0 := (Finset.mem_filter.mp ht).2.2
    have h1 := (Finset.mem_filter.mp hs).2.2
    omega
  have hh := congrFun (signed_biplane_support_adjacency G C.srg _ (F.biplane a) (F.eigen a)) t
  rw [finiteIndicator_adjacency] at hh
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, finiteIndicator, if_neg hnotC,
    if_neg hnotS, mul_zero, add_zero] at hh
  exact not_adj_of_filter_card_zero G _ t (by exact_mod_cast hh) hu

theorem isolated_cell_isolated_degree {a : Fin 4} {t : V}
    (ht : t ∈ rootIsolated G (F.code a)) (j : Fin 4) :
    ((rootIsolated G (F.code j)).filter (G.Adj t)).card = if j = a then 0 else 3 := by
  have hnotC : t ∉ rootSupport (F.code j) := fun hc =>
    Finset.disjoint_left.mp (F.support_avoids_isolated j a) hc ht
  by_cases hja : j = a
  · subst j
    rw [if_pos rfl]
    apply signed_biplane_isolated_degree_zero G C.srg _ (F.biplane a) (F.eigen a) t
    intro hs
    have hzero := (Finset.mem_filter.mp ht).2.2
    have hone := (Finset.mem_filter.mp hs).2.2
    omega
  · rw [if_neg hja]
    have hnotI : t ∉ rootIsolated G (F.code j) := by
      intro hh
      exact Finset.disjoint_left.mp (F.isolated_disjoint hja) hh ht
    have hp := congrFun (signed_biplane_indicator_partition G C.srg _ (F.biplane j) (F.eigen j)) t
    have hS : t ∈ rootShell G (F.code j) := by
      by_contra hs
      simp [Pi.add_apply, finiteIndicator, hnotC, hnotI, hs] at hp
    have hh := congrFun (signed_biplane_isolated_adjacency G C.srg _ (F.biplane j) (F.eigen j)) t
    rw [finiteIndicator_adjacency] at hh
    simp only [Pi.smul_apply, smul_eq_mul, finiteIndicator, if_pos hS, mul_one] at hh
    exact_mod_cast hh

theorem isolated_cell_isolated_union_degree {a : Fin 4} {t : V}
    (ht : t ∈ rootIsolated G (F.code a)) : (F.isolatedUnion.filter (G.Adj t)).card = 9 := by
  have heq : F.isolatedUnion.filter (G.Adj t) =
      Finset.univ.biUnion (fun i => (rootIsolated G (F.code i)).filter (G.Adj t)) := by
    ext x
    simp only [FourDirectionSystem.isolatedUnion, Finset.mem_filter, Finset.mem_biUnion]
    aesop
  rw [heq, Finset.card_biUnion (by
    intro i _ j _ hij
    exact Finset.disjoint_filter_filter (F.isolated_disjoint hij))]
  simp only [C.isolated_cell_isolated_degree ht]
  have hsum : ∀ a : Fin 4, (∑ j : Fin 4, if j = a then (0 : ℕ) else 3) = 9 := by decide
  exact hsum a

theorem isolated_cell_W_degree {a : Fin 4} {t : V}
    (ht : t ∈ rootIsolated G (F.code a)) : (F.W.filter (G.Adj t)).card = 5 := by
  have hdeg : (Finset.univ.filter (G.Adj t)).card = 14 := by
    simpa [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter] using C.srg.regular.degree_eq t
  have hi := C.isolated_cell_isolated_union_degree ht
  have hd : Disjoint (F.W.filter (G.Adj t)) (F.isolatedUnion.filter (G.Adj t)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).2 (Finset.mem_filter.mp hy).1
  have heq : F.W.filter (G.Adj t) ∪ F.isolatedUnion.filter (G.Adj t) =
      Finset.univ.filter (G.Adj t) := by
    ext x
    simp only [FourDirectionSystem.W, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
    tauto
  have hh := Finset.card_union_of_disjoint hd
  rw [heq, hdeg, hi] at hh
  omega

theorem isolated_o_Vset_degree {a : Fin 4} {t : V}
    (ht : t ∈ rootIsolated G (F.code a)) (ho : G.Adj C.o t) :
    (C.Vset.filter (G.Adj t)).card = 1 := by
  have hno := C.isolated_cell_not_adj_full ht
  have hne := C.isolated_cell_ne_full ht
  have hoV : C.o ∉ C.Vset := by
    intro hh
    exact ((C.mem_Vset C.o).mp hh).2.1 rfl
  have heq : (G.commonNeighbors C.v t).toFinset = insert C.o (C.Vset.filter (G.Adj t)) := by
    ext x
    simp only [Set.mem_toFinset, SimpleGraph.mem_commonNeighbors, Finset.mem_insert,
      Finset.mem_filter]
    constructor
    · intro hx
      by_cases hxo : x = C.o
      · exact Or.inl hxo
      · exact Or.inr ⟨(C.mem_Vset x).mpr ⟨by intro he; subst x; exact hno.2 hx.2.symm,
          hxo, hx.1⟩, hx.2⟩
    · rintro (rfl | hx)
      · exact ⟨C.ov_adj.symm, ho.symm⟩
      · exact ⟨((C.mem_Vset x).mp hx.1).2.2, hx.2⟩
  have hc : (G.commonNeighbors C.v t).toFinset.card = 2 := by
    rw [Set.toFinset_card]
    exact C.srg.of_not_adj hne.1.symm hno.1
  rw [heq, Finset.card_insert_of_notMem (by
    intro hh
    exact hoV (Finset.mem_filter.mp hh).1)] at hc
  omega

theorem isolated_o_Wset_degree {a : Fin 4} {t : V}
    (ht : t ∈ rootIsolated G (F.code a)) (ho : G.Adj C.o t) :
    (C.Wset.filter (G.Adj t)).card = 1 := C.swap.isolated_o_Vset_degree ht ho

theorem isolated_o_Rset_degree {a : Fin 4} {t : V}
    (ht : t ∈ rootIsolated G (F.code a)) (ho : G.Adj C.o t) :
    (C.Rset.filter (G.Adj t)).card = 2 := by
  have hno := C.isolated_cell_not_adj_full ht
  have hWV : Disjoint (C.Vset ∪ C.Wset) C.Rset := C.Rset_simple_disjoint
  have hoR : C.o ∉ (C.Vset ∪ C.Wset) ∪ C.Rset := by
    intro hh
    rcases Finset.mem_union.mp hh with hs | hr
    · rcases Finset.mem_union.mp hs with hv | hw
      · exact ((C.mem_Vset C.o).mp hv).2.1 rfl
      · exact ((C.mem_Wset C.o).mp hw).2.1 rfl
    · have hw := (Finset.mem_filter.mp hr).2
      rw [C.o_weight] at hw
      omega
  have heq : F.W.filter (G.Adj t) =
      insert C.o (((C.Vset ∪ C.Wset) ∪ C.Rset).filter (G.Adj t)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
    constructor
    · intro hx
      rcases C.W_cases hx.1 with rfl | rfl | rfl | hv | hw | hr
      · exact Or.inl rfl
      · exact (hno.1 hx.2.symm).elim
      · exact (hno.2 hx.2.symm).elim
      · exact Or.inr ⟨Or.inl (Or.inl hv), hx.2⟩
      · exact Or.inr ⟨Or.inl (Or.inr hw), hx.2⟩
      · exact Or.inr ⟨Or.inr hr, hx.2⟩
    · rintro (rfl | hx)
      · exact ⟨C.o_mem, ho.symm⟩
      · refine ⟨?_, hx.2⟩
        rcases hx.1 with (hv | hw) | hr
        · exact C.Vset_mem_W hv
        · exact C.Wset_mem_W hw
        · exact (Finset.mem_filter.mp hr).1
  have hh := C.isolated_cell_W_degree ht
  rw [heq, Finset.card_insert_of_notMem (by
      intro hm; exact hoR (Finset.mem_filter.mp hm).1),
    Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hWV),
    Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter C.Vset_Wset_disjoint),
    C.isolated_o_Vset_degree ht ho, C.isolated_o_Wset_degree ht ho] at hh
  omega

#print axioms isolated_cell_W_degree
#print axioms isolated_o_Rset_degree

end OnePointConfiguration
end Conway99
