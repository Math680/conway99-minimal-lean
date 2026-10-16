import ZeroCaseNeighbors

/-! The actual core and eight singleton-signature classes of the zero case. -/

namespace Conway99
namespace FourDirectionSystem

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (F : FourDirectionSystem G)

def coreVertices : Finset V := F.W.filter (fun u => 2 ≤ F.weight u)

def singleClass (a : Fin 4 × Bool) : Finset V :=
  (F.W.filter (fun u => F.weight u = 1)) ∩ signedCodeSupport (F.code a.1) a.2

def singleUnion : Finset V := Finset.univ.biUnion F.singleClass

theorem singleClass_mem {a : Fin 4 × Bool} {u : V} (hu : u ∈ F.singleClass a) :
    u ∈ F.W ∧ F.weight u = 1 ∧ F.code a.1 u = if a.2 then 1 else -1 := by
  have hs := Finset.mem_inter.mp hu
  exact ⟨(Finset.mem_filter.mp hs.1).1, (Finset.mem_filter.mp hs.1).2,
    (signedCodeSupport_mem _ _ _).mp hs.2⟩

theorem singleClass_code_ne {a : Fin 4 × Bool} {u : V} (hu : u ∈ F.singleClass a) :
    F.code a.1 u ≠ 0 := by
  have hs := (F.singleClass_mem hu).2.2
  cases h : a.2 <;> simp_all

theorem singleClass_pairwise_disjoint :
    Pairwise (fun a b : Fin 4 × Bool => Disjoint (F.singleClass a) (F.singleClass b)) := by
  intro a b hab
  apply Finset.disjoint_left.mpr
  intro u hua hub
  obtain ⟨i, hi⟩ := F.simple_active_unique (F.singleClass_mem hua).2.1
  have hai := (hi a.1).mp (F.singleClass_code_ne hua)
  have hbi := (hi b.1).mp (F.singleClass_code_ne hub)
  have hiab : a.1 = b.1 := hai.trans hbi.symm
  have hsa := (F.singleClass_mem hua).2.2
  have hsb := (F.singleClass_mem hub).2.2
  rw [hiab] at hsa
  have hsab : a.2 = b.2 := by
    cases h1 : a.2 <;> cases h2 : b.2 <;> simp_all
  exact hab (Prod.ext hiab hsab)

theorem weight_one_mem_singleUnion {u : V} (hu : u ∈ F.W) (hw : F.weight u = 1) :
    u ∈ F.singleUnion := by
  obtain ⟨i, hi⟩ := F.simple_active_unique hw
  have hn := (hi i).mpr rfl
  rcases (F.biplane i).signs u with hm | hz | hp
  · apply Finset.mem_biUnion.mpr
    refine ⟨(i,false), Finset.mem_univ _, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨hu, hw⟩
    · exact (signedCodeSupport_mem _ _ _).mpr hm
  · exact (hn hz).elim
  · apply Finset.mem_biUnion.mpr
    refine ⟨(i,true), Finset.mem_univ _, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨hu, hw⟩
    · exact (signedCodeSupport_mem _ _ _).mpr hp

theorem core_single_disjoint : Disjoint F.coreVertices F.singleUnion := by
  apply Finset.disjoint_left.mpr
  intro u hcore hsingle
  obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hsingle
  have hw := (F.singleClass_mem ha).2.1
  have hc := (Finset.mem_filter.mp hcore).2
  omega

theorem zero_case_W_partition (hz : F.weightCount 0 = 0) :
    F.W = F.coreVertices ∪ F.singleUnion := by
  ext u
  constructor
  · intro hu
    have hn : F.weight u ≠ 0 := by
      intro h0
      have he : F.W.filter (fun u => F.weight u = 0) = ∅ := Finset.card_eq_zero.mp hz
      have hm : u ∈ F.W.filter (fun u => F.weight u = 0) := Finset.mem_filter.mpr ⟨hu, h0⟩
      rw [he] at hm
      exact Finset.notMem_empty _ hm
    have hlo := F.weight_nonneg u
    by_cases hw : F.weight u = 1
    · exact Finset.mem_union_right _ (F.weight_one_mem_singleUnion hu hw)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hu, by omega⟩)
  · intro hu
    rcases Finset.mem_union.mp hu with hc | hs
    · exact (Finset.mem_filter.mp hc).1
    · obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hs
      exact (F.singleClass_mem ha).1

theorem zero_case_neighbor_partition (hz : F.weightCount 0 = 0) (v : V) :
    (F.W.filter (G.Adj v)).card = (F.coreVertices.filter (G.Adj v)).card +
      ∑ a : Fin 4 × Bool, ((F.singleClass a).filter (G.Adj v)).card := by
  rw [F.zero_case_W_partition hz, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter F.core_single_disjoint)]
  congr 1
  rw [singleUnion, Finset.filter_biUnion, Finset.card_biUnion]
  intro a ha b hb hab
  exact Finset.disjoint_filter_filter (F.singleClass_pairwise_disjoint hab)

#print axioms singleClass_pairwise_disjoint
#print axioms zero_case_W_partition
#print axioms zero_case_neighbor_partition

end FourDirectionSystem
end Conway99
