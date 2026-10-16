import FourDirectionOnePartition

/-! The twelve one-point mixed-sign cells partition the double-signature points. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace OnePointConfiguration

variable {F : FourDirectionSystem G} (C : OnePointConfiguration F)

theorem Rij_active_indices {i j : Fin 4} (hij : i ≠ j) {u : V}
    (hu : u ∈ C.Rij i j) :
    (Finset.univ.filter (fun k : Fin 4 => F.code k u ≠ 0)) = {i,j} := by
  have ha := C.Rij_simple_coordinates hu
  have hs : {i,j} ⊆ Finset.univ.filter (fun k : Fin 4 => F.code k u ≠ 0) := by
    intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> simp [ha.1,ha.2]
  symm
  apply Finset.eq_of_subset_of_card_le hs
  have hw := C.Rij_weight hij hu
  have hc := F.active_count_eq_weight u
  rw [Finset.card_pair hij]
  omega

theorem Rij_code_else_zero {i j k : Fin 4} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    {u : V} (hu : u ∈ C.Rij i j) : F.code k u = 0 := by
  have he := C.Rij_active_indices hij hu
  have hk : k ∉ Finset.univ.filter (fun l : Fin 4 => F.code l u ≠ 0) := by
    rw [he]
    simp [hki,hkj]
  simpa using hk

theorem Rij_disjoint (p q : Fin 4 × Fin 4) (hp : p.1 ≠ p.2) (hq : q.1 ≠ q.2)
    (hpq : p ≠ q) : Disjoint (C.Rij p.1 p.2) (C.Rij q.1 q.2) := by
  apply Finset.disjoint_left.mpr
  intro u hpu hqu
  have he := C.Rij_active_indices hp hpu
  have ha := C.Rij_simple_coordinates hqu
  have hi : q.1 = p.1 ∨ q.1 = p.2 := by
    have hm : q.1 ∈ Finset.univ.filter (fun l : Fin 4 => F.code l u ≠ 0) := by simp [ha.1]
    rw [he] at hm
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
  have hj : q.2 = p.1 ∨ q.2 = p.2 := by
    have hm : q.2 ∈ Finset.univ.filter (fun l : Fin 4 => F.code l u ≠ 0) := by simp [ha.2]
    rw [he] at hm
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
  have hps := (Finset.mem_filter.mp hpu).2
  have hqs := (Finset.mem_filter.mp hqu).2
  have hi' : q.1 = p.1 := by
    rcases hi with hh | hh
    · exact hh
    · have hv := C.v_code_ne p.2
      rw [hh] at hqs
      omega
  have hj' : q.2 = p.2 := by
    rcases hj with hh | hh
    · have hv := C.v_code_ne p.1
      rw [hh] at hqs
      omega
    · exact hh
  exact hpq (Prod.ext hi'.symm hj'.symm)

def Rset (_C : OnePointConfiguration F) : Finset V := F.W.filter (fun u => F.weight u = 2)
def Rall : Finset V := (Finset.univ : Finset (Fin 4)).offDiag.biUnion
  (fun p => C.Rij p.1 p.2)

theorem Rall_card : C.Rall.card = 12 := by
  rw [Rall, Finset.card_biUnion (by
    intro p hp q hq hpq
    exact C.Rij_disjoint p q (Finset.mem_offDiag.mp hp).2.2
      (Finset.mem_offDiag.mp hq).2.2 hpq)]
  have hh : (∑ p ∈ (Finset.univ : Finset (Fin 4)).offDiag, (C.Rij p.1 p.2).card) =
      ∑ _p ∈ (Finset.univ : Finset (Fin 4)).offDiag, (1 : ℕ) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact C.Rij_card p.1 p.2 (Finset.mem_offDiag.mp hp).2.2
  rw [hh]
  norm_num [Finset.offDiag_card]

theorem Rset_card : C.Rset.card = 12 := (F.one_zero_weight_profile C.srg C.zero_count).2.1

theorem Rall_eq_Rset : C.Rall = C.Rset := by
  apply Finset.eq_of_subset_of_card_le
  · intro u hu
    obtain ⟨p,hp,hpu⟩ := Finset.mem_biUnion.mp hu
    have hij := (Finset.mem_offDiag.mp hp).2.2
    have ha := C.Rij_simple_coordinates hpu
    exact Finset.mem_filter.mpr ⟨F.support_subset_W p.1
      ((F.mem_support_iff_code_ne_zero p.1 u).mpr ha.1), C.Rij_weight hij hpu⟩
  · rw [C.Rset_card,C.Rall_card]

theorem double_cell_exists {u : V} (hu : u ∈ C.Rset) :
    ∃ i j : Fin 4, i ≠ j ∧ u ∈ C.Rij i j := by
  rw [← C.Rall_eq_Rset] at hu
  obtain ⟨p,hp,hpu⟩ := Finset.mem_biUnion.mp hu
  exact ⟨p.1,p.2,(Finset.mem_offDiag.mp hp).2.2,hpu⟩

noncomputable def Rpoint (i j : Fin 4) (hij : i ≠ j) : V :=
  Classical.choose (Finset.card_eq_one.mp (C.Rij_card i j hij))

theorem Rij_eq_singleton (i j : Fin 4) (hij : i ≠ j) :
    C.Rij i j = {C.Rpoint i j hij} :=
  Classical.choose_spec (Finset.card_eq_one.mp (C.Rij_card i j hij))

theorem Rpoint_mem (i j : Fin 4) (hij : i ≠ j) : C.Rpoint i j hij ∈ C.Rij i j := by
  rw [C.Rij_eq_singleton i j hij]
  simp

theorem Rpoint_signature (i j : Fin 4) (hij : i ≠ j) (k : Fin 4) :
    F.code k (C.Rpoint i j hij) =
      if k = i then F.code i C.v else if k = j then -F.code j C.v else 0 := by
  have hm := C.Rpoint_mem i j hij
  have hs := (Finset.mem_filter.mp hm).2
  by_cases hki : k = i
  · subst k
    simp [hs.1]
  · by_cases hkj : k = j
    · subst k
      simp [hki,hs.2]
    · simp [hki,hkj,C.Rij_code_else_zero hij hki hkj hm]

#print axioms Rall_eq_Rset
#print axioms Rpoint_signature

end OnePointConfiguration
end Conway99
