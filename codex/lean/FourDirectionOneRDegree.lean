import FourDirectionOneMatchings

/-! Each double-signature vertex has two neighbors on each simple side
and four neighbors among the twelve double-signature vertices. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace FourDirectionSystem

variable (F : FourDirectionSystem G)

theorem W_isolated_neighbors (h : G.IsSRGWith 99 14 1 2) {u : V}
    (hu : u ∈ F.W) (i : Fin 4) :
    ((rootIsolated G (F.code i)).filter (G.Adj u)).card =
      if u ∈ rootSupport (F.code i) then 0 else 3 := by
  by_cases ha : u ∈ rootSupport (F.code i)
  · rw [if_pos ha]
    apply signed_biplane_isolated_degree_zero G h _ (F.biplane i) (F.eigen i)
    have hn := (F.mem_support_iff_code_ne_zero i u).mp ha
    simp [rootShell,hn]
  · rw [if_neg ha]
    have hi : u ∉ rootIsolated G (F.code i) := by
      intro hm
      exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hm⟩)
    have hp := congrFun (signed_biplane_indicator_partition G h _ (F.biplane i) (F.eigen i)) u
    have hs : u ∈ rootShell G (F.code i) := by
      by_contra hh
      simp [Pi.add_apply, finiteIndicator,ha,hi,hh] at hp
    have hh := congrFun (signed_biplane_isolated_adjacency G h _ (F.biplane i) (F.eigen i)) u
    rw [finiteIndicator_adjacency] at hh
    simp only [Pi.smul_apply,smul_eq_mul,finiteIndicator,if_pos hs,mul_one] at hh
    exact_mod_cast hh

theorem W_isolated_union_degree (h : G.IsSRGWith 99 14 1 2) {u : V}
    (hu : u ∈ F.W) :
    ((F.isolatedUnion.filter (G.Adj u)).card : ℤ) = 12 - 3 * F.weight u := by
  have heq : F.isolatedUnion.filter (G.Adj u) =
      Finset.univ.biUnion (fun i => (rootIsolated G (F.code i)).filter (G.Adj u)) := by
    ext x
    simp only [isolatedUnion,Finset.mem_filter,Finset.mem_biUnion]
    aesop
  rw [heq,Finset.card_biUnion (by
    intro i _ j _ hij
    exact Finset.disjoint_filter_filter (F.isolated_disjoint hij)),Nat.cast_sum]
  simp only [F.W_isolated_neighbors h hu,Nat.cast_ite,Nat.cast_zero,Nat.cast_ofNat]
  have hp (i : Fin 4) : (if u ∈ rootSupport (F.code i) then (0 : ℤ) else 3) =
      3 - 3 * (if u ∈ rootSupport (F.code i) then 1 else 0) := by
    split_ifs <;> norm_num
  simp_rw [hp]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum]
  simp [weight]

theorem W_neighbor_degree (h : G.IsSRGWith 99 14 1 2) {u : V} (hu : u ∈ F.W) :
    ((F.W.filter (G.Adj u)).card : ℤ) = 2 + 3 * F.weight u := by
  have hdeg : (Finset.univ.filter (G.Adj u)).card = 14 := by
    simpa [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter] using h.regular.degree_eq u
  have hd : Disjoint (F.W.filter (G.Adj u)) (F.isolatedUnion.filter (G.Adj u)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).2 (Finset.mem_filter.mp hy).1
  have heq : F.W.filter (G.Adj u) ∪ F.isolatedUnion.filter (G.Adj u) =
      Finset.univ.filter (G.Adj u) := by
    ext x
    simp only [W,Finset.mem_union,Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and]
    tauto
  have hc := Finset.card_union_of_disjoint hd
  rw [heq,hdeg] at hc
  have hi := F.W_isolated_union_degree h hu
  omega

end FourDirectionSystem

namespace OnePointConfiguration

variable {F : FourDirectionSystem G} (C : OnePointConfiguration F)

theorem W_cases {u : V} (hu : u ∈ F.W) :
    u = C.o ∨ u = C.v ∨ u = C.w ∨ u ∈ C.Vset ∨ u ∈ C.Wset ∨ u ∈ C.Rset := by
  have hlo := F.weight_nonneg u
  have hhi := F.weight_le_four u
  have hz3 : F.weight u ≠ 3 := by
    intro he
    have hc := (F.one_zero_weight_profile C.srg C.zero_count).2.2.1
    have hm : u ∈ F.W.filter (fun x => F.weight x = 3) := Finset.mem_filter.mpr ⟨hu,he⟩
    rw [Finset.card_eq_zero.mp hc] at hm
    exact Finset.notMem_empty _ hm
  have hchoices : F.weight u = 0 ∨ F.weight u = 1 ∨ F.weight u = 2 ∨ F.weight u = 4 := by omega
  rcases hchoices with h0 | h1 | h2 | h4
  · exact Or.inl (F.one_zero_unique C.zero_count C.o_mem C.o_weight hu h0)
  · have hm : u ∈ F.W.filter (fun x => F.weight x = 1) := Finset.mem_filter.mpr ⟨hu,h1⟩
    rw [C.simple_points_eq,Finset.mem_union] at hm
    tauto
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Finset.mem_filter.mpr ⟨hu,h2⟩)))))
  · have hm : u ∈ F.W.filter (fun x => F.weight x = 4) := Finset.mem_filter.mpr ⟨hu,h4⟩
    rw [C.full_points_eq] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    tauto

theorem Rset_not_adj_o {u : V} (hu : u ∈ C.Rset) : ¬G.Adj C.o u := by
  intro ha
  have hh := F.zero_neighbors_weight_four C.srg C.o C.o_mem C.o_weight u
    (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1,ha⟩)
  have hw := (Finset.mem_filter.mp hu).2
  omega

theorem Rset_not_adj_v {u : V} (hu : u ∈ C.Rset) : ¬G.Adj C.v u := by
  intro ha
  have hw := (Finset.mem_filter.mp hu).2
  have hno : u ≠ C.o := by intro he; rw [he,C.o_weight] at hw; omega
  have hnw : u ≠ C.w := by intro he; rw [he,C.w_weight] at hw; omega
  have hv : u ∈ C.Vset := (C.mem_Vset u).mpr ⟨hnw,hno,ha⟩
  have hs := C.Vset_simple hv
  omega

theorem Rset_not_adj_w {u : V} (hu : u ∈ C.Rset) : ¬G.Adj C.w u :=
  C.swap.Rset_not_adj_v hu

theorem Rset_Vset_common_eq {u : V} (hu : u ∈ C.Rset) :
    C.Vset.filter (G.Adj u) = (G.commonNeighbors C.v u).toFinset := by
  ext x
  simp only [Finset.mem_filter,Set.mem_toFinset,SimpleGraph.mem_commonNeighbors]
  constructor
  · intro hx
    exact ⟨((C.mem_Vset x).mp hx.1).2.2,hx.2⟩
  · intro hx
    refine ⟨(C.mem_Vset x).mpr ⟨?_,?_,hx.1⟩,hx.2⟩
    · intro he
      subst x
      exact C.Rset_not_adj_w hu hx.2.symm
    · intro he
      subst x
      exact C.Rset_not_adj_o hu hx.2.symm

theorem Rset_Vset_degree {u : V} (hu : u ∈ C.Rset) :
    (C.Vset.filter (G.Adj u)).card = 2 := by
  rw [C.Rset_Vset_common_eq hu,Set.toFinset_card]
  have hne : C.v ≠ u := by
    intro he
    have hw := (Finset.mem_filter.mp hu).2
    rw [← he,C.v_weight] at hw
    omega
  exact C.srg.of_not_adj hne (C.Rset_not_adj_v hu)

theorem Rset_Wset_degree {u : V} (hu : u ∈ C.Rset) :
    (C.Wset.filter (G.Adj u)).card = 2 :=
  C.swap.Rset_Vset_degree hu

theorem Rset_simple_disjoint : Disjoint (C.Vset ∪ C.Wset) C.Rset := by
  apply Finset.disjoint_left.mpr
  intro u hs hr
  have hw := (Finset.mem_filter.mp hr).2
  rcases Finset.mem_union.mp hs with hv | hw'
  · have hh := C.Vset_simple hv; omega
  · have hh := C.Wset_simple hw'; omega

theorem Rset_neighbor_union {u : V} (hu : u ∈ C.Rset) :
    F.W.filter (G.Adj u) =
      ((C.Vset ∪ C.Wset) ∪ C.Rset).filter (G.Adj u) := by
  ext x
  simp only [Finset.mem_filter,Finset.mem_union]
  constructor
  · intro hx
    refine ⟨?_,hx.2⟩
    rcases C.W_cases hx.1 with rfl | rfl | rfl | hv | hw | hr
    · exact (C.Rset_not_adj_o hu hx.2.symm).elim
    · exact (C.Rset_not_adj_v hu hx.2.symm).elim
    · exact (C.Rset_not_adj_w hu hx.2.symm).elim
    · tauto
    · tauto
    · tauto
  · intro hx
    refine ⟨?_,hx.2⟩
    rcases hx.1 with (hv | hw) | hr
    · exact C.Vset_mem_W hv
    · exact C.Wset_mem_W hw
    · exact (Finset.mem_filter.mp hr).1

theorem Rset_internal_degree {u : V} (hu : u ∈ C.Rset) :
    (C.Rset.filter (G.Adj u)).card = 4 := by
  have hdeg := F.W_neighbor_degree C.srg (Finset.mem_filter.mp hu).1
  rw [(Finset.mem_filter.mp hu).2] at hdeg
  have heq := congrArg Finset.card (C.Rset_neighbor_union hu)
  rw [Finset.filter_union,Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter C.Rset_simple_disjoint),
    Finset.filter_union,Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter C.Vset_Wset_disjoint),
    C.Rset_Vset_degree hu,C.Rset_Wset_degree hu] at heq
  omega

#print axioms W_cases
#print axioms Rset_internal_degree

end OnePointConfiguration
end Conway99
