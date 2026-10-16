import FourDirectionOneGlobalBudget
import FourDirectionOneArcPoint

/-! The two incoming and two outgoing neighbors forced by each signed biplane. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace OnePointConfiguration

variable {F : FourDirectionSystem G} (C : OnePointConfiguration F)

theorem Rij_mem_Rset {i j : Fin 4} (hij : i ≠ j) {u : V} (hu : u ∈ C.Rij i j) :
    u ∈ C.Rset := by
  rw [← C.Rall_eq_Rset]
  exact Finset.mem_biUnion.mpr ⟨(i,j),Finset.mem_offDiag.mpr
    ⟨Finset.mem_univ _,Finset.mem_univ _,hij⟩,hu⟩

theorem Rij_Vi_neighbor_eq {i j : Fin 4} (hij : i ≠ j) {u : V} (hu : u ∈ C.Rij i j) :
    C.Vset.filter (G.Adj u) = (C.Vi i).filter (G.Adj u) := by
  ext x
  simp only [Finset.mem_filter]
  constructor
  · intro hx
    have hV := hx.1
    rw [← C.Vi_cover] at hV
    obtain ⟨k,_,hk⟩ := Finset.mem_biUnion.mp hV
    have he := C.Vi_Rij_restriction hij hk hu hx.2.symm
    subst k
    exact ⟨hk,hx.2⟩
  · intro hx
    exact ⟨(Finset.mem_filter.mp hx.1).1,hx.2⟩

theorem Rij_Wi_neighbor_eq {i j : Fin 4} (hij : i ≠ j) {u : V} (hu : u ∈ C.Rij i j) :
    C.Wset.filter (G.Adj u) = (C.Wi j).filter (G.Adj u) := by
  ext x
  simp only [Finset.mem_filter]
  constructor
  · intro hx
    have hW := hx.1
    rw [← C.Wi_cover] at hW
    obtain ⟨k,_,hk⟩ := Finset.mem_biUnion.mp hW
    have he := C.Wi_Rij_restriction hij hk hu hx.2.symm
    subst k
    exact ⟨hk,hx.2⟩
  · intro hx
    exact ⟨(Finset.mem_filter.mp hx.1).1,hx.2⟩

theorem arcPoint_Vi_degree (a : FourDirections.Arc) :
    ((C.Vi (FourDirections.src a)).filter (G.Adj (C.arcPoint a))).card = 2 := by
  change ((C.Vi a.val.1).filter (G.Adj (C.arcPoint a))).card = 2
  rw [← C.Rij_Vi_neighbor_eq a.property (C.arcPoint_mem_cell a)]
  exact C.Rset_Vset_degree (C.arcPoint_mem_Rset a)

theorem arcPoint_Wi_degree (a : FourDirections.Arc) :
    ((C.Wi (FourDirections.dst a)).filter (G.Adj (C.arcPoint a))).card = 2 := by
  change ((C.Wi a.val.2).filter (G.Adj (C.arcPoint a))).card = 2
  rw [← C.Rij_Wi_neighbor_eq a.property (C.arcPoint_mem_cell a)]
  exact C.Rset_Wset_degree (C.arcPoint_mem_Rset a)

theorem Rij_opposite_side_degree {i j : Fin 4} (hij : i ≠ j) {u : V}
    (hu : u ∈ C.Rij i j) :
    ((Finset.univ.filter (fun x => F.code i x = -F.code i C.v)).filter (G.Adj u)).card = 4 := by
  have hs := (Finset.mem_filter.mp hu).2.1
  rcases (F.biplane i).signs C.v with hn | hz | hp
  · have heq : Finset.univ.filter (fun x => F.code i x = -F.code i C.v) =
        positiveCodeSupport (F.code i) := by simp [hn,positiveCodeSupport]
    rw [heq]
    exact (F.biplane i).negative_cross u (by simp [negativeCodeSupport,hs,hn])
  · exact (C.v_code_ne i hz).elim
  · have heq : Finset.univ.filter (fun x => F.code i x = -F.code i C.v) =
        negativeCodeSupport (F.code i) := by simp [hp,negativeCodeSupport]
    rw [heq]
    exact (F.biplane i).positive_cross u (by simp [positiveCodeSupport,hs,hp])

theorem Rij_opposite_side_neighbor_eq {i j : Fin 4} (hij : i ≠ j) {u : V}
    (hu : u ∈ C.Rij i j) :
    ((Finset.univ.filter (fun x => F.code i x = -F.code i C.v)).filter (G.Adj u)) =
      (C.Vi i).filter (G.Adj u) ∪
        C.Rset.filter (fun x => G.Adj u x ∧ F.code i x = -F.code i C.v) := by
  have huR := C.Rij_mem_Rset hij hu
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
  constructor
  · intro hx
    have hxcode : F.code i x ≠ 0 := by rw [hx.1]; exact neg_ne_zero.mpr (C.v_code_ne i)
    have hxW := F.support_subset_W i ((F.mem_support_iff_code_ne_zero i x).mpr hxcode)
    rcases C.W_cases hxW with rfl | rfl | rfl | hV | hW | hR
    · exact (C.Rset_not_adj_o huR hx.2.symm).elim
    · exact (C.Rset_not_adj_v huR hx.2.symm).elim
    · exact (C.Rset_not_adj_w huR hx.2.symm).elim
    · exact Or.inl ⟨Finset.mem_filter.mpr ⟨hV,hxcode⟩,hx.2⟩
    · have hiW : x ∈ C.Wi i := Finset.mem_filter.mpr ⟨hW,hxcode⟩
      have hsame := C.Wi_code hiW
      have hn := C.v_code_ne i
      exfalso
      omega
    · exact Or.inr ⟨hR,hx.2,hx.1⟩
  · intro hx
    rcases hx with hV | hR
    · exact ⟨C.Vi_code hV.1,hV.2⟩
    · exact ⟨hR.2.2,hR.2.1⟩

theorem Rij_incoming_degree {i j : Fin 4} (hij : i ≠ j) {u : V}
    (hu : u ∈ C.Rij i j) :
    (C.Rset.filter (fun x => G.Adj u x ∧ F.code i x = -F.code i C.v)).card = 2 := by
  have hc := C.Rij_opposite_side_degree hij hu
  rw [C.Rij_opposite_side_neighbor_eq hij hu] at hc
  have hd : Disjoint ((C.Vi i).filter (G.Adj u))
      (C.Rset.filter (fun x => G.Adj u x ∧ F.code i x = -F.code i C.v)) := by
    apply Finset.disjoint_left.mpr
    intro x hV hR
    have hs := C.Vset_simple (Finset.mem_filter.mp (Finset.mem_filter.mp hV).1).1
    have hr := (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).2
    omega
  rw [Finset.card_union_of_disjoint hd,← C.Rij_Vi_neighbor_eq hij hu,
    C.Rset_Vset_degree (C.Rij_mem_Rset hij hu)] at hc
  omega

theorem Rij_outgoing_degree {i j : Fin 4} (hij : i ≠ j) {u : V}
    (hu : u ∈ C.Rij i j) :
    (C.Rset.filter (fun x => G.Adj u x ∧ F.code j x = F.code j C.v)).card = 2 := by
  have hs := (Finset.mem_filter.mp hu).2
  have hm : u ∈ C.swap.Rij j i := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_⟩
    · change F.code j u = F.code j C.w
      have hh := C.opposite j
      omega
    · change F.code i u = -F.code i C.w
      exact hs.1.trans (C.opposite i)
  have hc := C.swap.Rij_incoming_degree hij.symm hm
  change (C.Rset.filter (fun x => G.Adj u x ∧ F.code j x = -F.code j C.w)).card = 2 at hc
  rwa [← C.opposite j] at hc

#print axioms arcPoint_Vi_degree
#print axioms Rij_incoming_degree
#print axioms Rij_outgoing_degree

end OnePointConfiguration
end Conway99
