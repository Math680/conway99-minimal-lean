import FourDirectionOneCells
import FourDirections

/-! The canonical bijection between the twelve directed label arcs and the double points. -/

namespace Conway99

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace OnePointConfiguration

variable {F : FourDirectionSystem G} (C : OnePointConfiguration F)

noncomputable def arcPoint (a : FourDirections.Arc) : V := C.Rpoint a.val.1 a.val.2 a.property

theorem arcPoint_mem_cell (a : FourDirections.Arc) :
    C.arcPoint a ∈ C.Rij a.val.1 a.val.2 := C.Rpoint_mem _ _ a.property

theorem arcPoint_mem_Rset (a : FourDirections.Arc) : C.arcPoint a ∈ C.Rset := by
  rw [← C.Rall_eq_Rset]
  exact Finset.mem_biUnion.mpr ⟨a.val,Finset.mem_offDiag.mpr
    ⟨Finset.mem_univ _,Finset.mem_univ _,a.property⟩,C.arcPoint_mem_cell a⟩

theorem arcPoint_injective : Function.Injective C.arcPoint := by
  intro a b he
  by_contra hn
  have hp : a.val ≠ b.val := by intro hh; exact hn (Subtype.ext hh)
  have hd := C.Rij_disjoint a.val b.val a.property b.property hp
  exact Finset.disjoint_left.mp hd (C.arcPoint_mem_cell a) (he ▸ C.arcPoint_mem_cell b)

theorem Rset_arcPoint_exists {u : V} (hu : u ∈ C.Rset) :
    ∃ a : FourDirections.Arc, C.arcPoint a = u := by
  obtain ⟨i,j,hij,hm⟩ := C.double_cell_exists hu
  rw [C.Rij_eq_singleton i j hij,Finset.mem_singleton] at hm
  exact ⟨⟨(i,j),hij⟩,hm.symm⟩

theorem arcPoint_signature (a : FourDirections.Arc) (k : Fin 4) :
    F.code k (C.arcPoint a) =
      if k = FourDirections.src a then F.code k C.v else
        if k = FourDirections.dst a then -F.code k C.v else 0 := by
  have hs := C.Rpoint_signature a.val.1 a.val.2 a.property k
  change F.code k (C.Rpoint a.val.1 a.val.2 a.property) = _
  rw [hs]
  dsimp only [FourDirections.src,FourDirections.dst]
  split_ifs <;> simp_all

#print axioms arcPoint_injective

end OnePointConfiguration
end Conway99
