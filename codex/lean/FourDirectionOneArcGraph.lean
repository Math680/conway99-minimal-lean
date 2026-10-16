import FourDirectionOneArcDegrees

/-! The graph on the twelve double-signature points is exactly the
nonbacktracking directed-arc graph on four labels. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace OnePointConfiguration

variable {F : FourDirectionSystem G} (C : OnePointConfiguration F)

theorem Rij_inout_union {i j : Fin 4} (hij : i ≠ j) {u : V} (hu : u ∈ C.Rij i j) :
    C.Rset.filter (fun x => G.Adj u x ∧ F.code i x = -F.code i C.v) ∪
      C.Rset.filter (fun x => G.Adj u x ∧ F.code j x = F.code j C.v) =
        C.Rset.filter (G.Adj u) := by
  ext x
  simp only [Finset.mem_union,Finset.mem_filter]
  constructor
  · tauto
  · intro hx
    obtain ⟨k,l,hkl,hxl⟩ := C.double_cell_exists hx.1
    have hr := C.Rij_Rij_restriction hij hkl hu hxl hx.2
    have hs := (Finset.mem_filter.mp hxl).2
    rcases hr with rfl | rfl
    · exact Or.inr ⟨hx.1,hx.2,hs.1⟩
    · exact Or.inl ⟨hx.1,hx.2,hs.2⟩

theorem Rij_inout_disjoint {i j : Fin 4} (hij : i ≠ j) {u : V} (hu : u ∈ C.Rij i j) :
    Disjoint (C.Rset.filter (fun x => G.Adj u x ∧ F.code i x = -F.code i C.v))
      (C.Rset.filter (fun x => G.Adj u x ∧ F.code j x = F.code j C.v)) := by
  have hc := Finset.card_union_add_card_inter
    (C.Rset.filter (fun x => G.Adj u x ∧ F.code i x = -F.code i C.v))
    (C.Rset.filter (fun x => G.Adj u x ∧ F.code j x = F.code j C.v))
  rw [C.Rij_inout_union hij hu,C.Rset_internal_degree (C.Rij_mem_Rset hij hu),
    C.Rij_incoming_degree hij hu,C.Rij_outgoing_degree hij hu] at hc
  apply Finset.disjoint_iff_inter_eq_empty.mpr
  apply Finset.card_eq_zero.mp
  omega

theorem arcPoint_adj_implies (a b : FourDirections.Arc)
    (ha : G.Adj (C.arcPoint a) (C.arcPoint b)) : FourDirections.arcAdj a b := by
  have hr := C.Rij_Rij_restriction a.property b.property
    (C.arcPoint_mem_cell a) (C.arcPoint_mem_cell b) ha
  have hs := (Finset.mem_filter.mp (C.arcPoint_mem_cell b)).2
  have hinv : ¬ (a.val.2 = b.val.1 ∧ b.val.2 = a.val.1) := by
    rintro ⟨h1,h2⟩
    have hR := C.arcPoint_mem_Rset b
    have hd := C.Rij_inout_disjoint a.property (C.arcPoint_mem_cell a)
    have hi : C.arcPoint b ∈ C.Rset.filter
        (fun x => G.Adj (C.arcPoint a) x ∧ F.code a.val.1 x = -F.code a.val.1 C.v) := by
      apply Finset.mem_filter.mpr
      refine ⟨hR,ha,?_⟩
      simpa only [h2] using hs.2
    have ho : C.arcPoint b ∈ C.Rset.filter
        (fun x => G.Adj (C.arcPoint a) x ∧ F.code a.val.2 x = F.code a.val.2 C.v) := by
      apply Finset.mem_filter.mpr
      refine ⟨hR,ha,?_⟩
      simpa only [h1] using hs.1
    exact Finset.disjoint_left.mp hd hi ho
  change (a.val.2 = b.val.1 ∧ b.val.2 ≠ a.val.1) ∨
    (b.val.2 = a.val.1 ∧ b.val.1 ≠ a.val.2)
  tauto

noncomputable def arcNeighbors (a : FourDirections.Arc) : Finset FourDirections.Arc :=
  Finset.univ.filter (fun b => G.Adj (C.arcPoint a) (C.arcPoint b))

theorem arcNeighbors_image (a : FourDirections.Arc) :
    (C.arcNeighbors a).image C.arcPoint = C.Rset.filter (G.Adj (C.arcPoint a)) := by
  ext x
  simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,arcNeighbors]
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact ⟨C.arcPoint_mem_Rset b,hb⟩
  · intro hx
    obtain ⟨b,rfl⟩ := C.Rset_arcPoint_exists hx.1
    exact ⟨b,hx.2,rfl⟩

theorem arcNeighbors_card (a : FourDirections.Arc) : (C.arcNeighbors a).card = 4 := by
  have hc := C.Rset_internal_degree (C.arcPoint_mem_Rset a)
  rw [← C.arcNeighbors_image a,Finset.card_image_of_injective _ C.arcPoint_injective] at hc
  exact hc

theorem arc_allowed_degree : ∀ a : FourDirections.Arc,
    (Finset.univ.filter (FourDirections.arcAdj a)).card = 4 := by decide

theorem arcNeighbors_eq (a : FourDirections.Arc) :
    C.arcNeighbors a = Finset.univ.filter (FourDirections.arcAdj a) := by
  apply Finset.eq_of_subset_of_card_le
  · intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,C.arcPoint_adj_implies a b (Finset.mem_filter.mp hb).2⟩
  · rw [C.arcNeighbors_card,arc_allowed_degree]

theorem arcPoint_adj_iff (a b : FourDirections.Arc) :
    G.Adj (C.arcPoint a) (C.arcPoint b) ↔ FourDirections.arcAdj a b := by
  have hm := congrArg (fun S => b ∈ S) (C.arcNeighbors_eq a)
  simpa only [arcNeighbors,Finset.mem_filter,Finset.mem_univ,true_and] using (Iff.of_eq hm)

#print axioms arcPoint_adj_iff

end OnePointConfiguration
end Conway99
