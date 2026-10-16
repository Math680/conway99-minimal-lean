import FourDirectionOneNeighbors

/-! The relative-sign partition in the unique-zero case. No roots are reoriented. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

structure OnePointConfiguration (F : FourDirectionSystem G) where
  srg : G.IsSRGWith 99 14 1 2
  signedCells : F.HasSignedCells
  zero_count : F.weightCount 0 = 1
  o : V
  v : V
  w : V
  o_mem : o ∈ F.W
  o_weight : F.weight o = 0
  v_mem : v ∈ F.W
  w_mem : w ∈ F.W
  vw_ne : v ≠ w
  ov_adj : G.Adj o v
  ow_adj : G.Adj o w
  vw_adj : G.Adj v w
  v_weight : F.weight v = 4
  w_weight : F.weight w = 4
  opposite : ∀ i, F.code i v = -F.code i w
  common_unique : ∀ x, G.Adj v x → G.Adj w x → x = o

theorem onePointConfiguration_exists (F : FourDirectionSystem G)
    (h : G.IsSRGWith 99 14 1 2) (hc : F.HasSignedCells) (hz : F.weightCount 0 = 1) :
    Nonempty (OnePointConfiguration F) := by
  obtain ⟨o,v,w,ho,hzo,hv,hw,hne,hov,how,hvw,hfv,hfw,hop,huniq⟩ := F.one_zero_triangle h hz
  exact ⟨⟨h,hc,hz,o,v,w,ho,hzo,hv,hw,hne,hov,how,hvw,hfv,hfw,hop,huniq⟩⟩

namespace FourDirectionSystem

variable (F : FourDirectionSystem G)

theorem active_count_eq_weight (u : V) :
    (((Finset.univ : Finset (Fin 4)).filter (fun i => F.code i u ≠ 0)).card : ℤ) =
      F.weight u := by
  simp [weight, ← F.mem_support_iff_code_ne_zero, Finset.sum_ite, Finset.sum_const,
    nsmul_eq_mul]

theorem simple_active_unique {u : V} (hu : F.weight u = 1) :
    ∃ i : Fin 4, ∀ j, F.code j u ≠ 0 ↔ j = i := by
  have hc : ((Finset.univ : Finset (Fin 4)).filter (fun i => F.code i u ≠ 0)).card = 1 := by
    have hh := F.active_count_eq_weight u
    omega
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
  refine ⟨i, ?_⟩
  intro j
  have hm : j ∈ (Finset.univ : Finset (Fin 4)).filter (fun i => F.code i u ≠ 0) ↔ j = i := by
    rw [hi, Finset.mem_singleton]
  simpa using hm

theorem adjacent_nonzero_coordinate_opposite (i : Fin 4) {u v : V}
    (hu : F.code i u ≠ 0) (hv : F.code i v ≠ 0) (ha : G.Adj u v) :
    F.code i u = -F.code i v := by
  have hne : F.code i u ≠ F.code i v := fun he => F.same_nonzero_coordinate_not_adj i hu he ha
  rcases (F.biplane i).signs u with hm | hz | hp <;>
    rcases (F.biplane i).signs v with hm' | hz' | hp' <;> omega

end FourDirectionSystem

namespace OnePointConfiguration

variable {F : FourDirectionSystem G} (C : OnePointConfiguration F)

def Vset : Finset V := F.outsideTriangleNeighbors C.o C.v C.w
def Wset : Finset V := F.outsideTriangleNeighbors C.o C.w C.v
def Vi (i : Fin 4) : Finset V := C.Vset.filter (fun u => F.code i u ≠ 0)
def Wi (i : Fin 4) : Finset V := C.Wset.filter (fun u => F.code i u ≠ 0)
def Rij (i j : Fin 4) : Finset V := Finset.univ.filter
  (fun u => F.code i u = F.code i C.v ∧ F.code j u = -F.code j C.v)

theorem o_ne_v : C.o ≠ C.v := C.ov_adj.ne
theorem o_ne_w : C.o ≠ C.w := C.ow_adj.ne
theorem v_code_ne (i : Fin 4) : F.code i C.v ≠ 0 :=
  (F.weight_four_iff C.v).mp C.v_weight i
theorem w_code_ne (i : Fin 4) : F.code i C.w ≠ 0 :=
  (F.weight_four_iff C.w).mp C.w_weight i

theorem Vset_card : C.Vset.card = 12 :=
  F.outsideTriangleNeighbors_card C.srg C.ov_adj.symm C.vw_adj C.o_ne_w
theorem Wset_card : C.Wset.card = 12 :=
  F.outsideTriangleNeighbors_card C.srg C.ow_adj.symm C.vw_adj.symm C.o_ne_v

theorem Vset_simple {u : V} (hu : u ∈ C.Vset) : F.weight u = 1 :=
  F.outsideTriangleNeighbors_simple C.srg C.zero_count C.o_mem C.o_weight C.v_weight
    C.w_weight C.ov_adj.symm C.vw_adj C.o_ne_w u hu
theorem Wset_simple {u : V} (hu : u ∈ C.Wset) : F.weight u = 1 :=
  F.outsideTriangleNeighbors_simple C.srg C.zero_count C.o_mem C.o_weight C.w_weight
    C.v_weight C.ow_adj.symm C.vw_adj.symm C.o_ne_v u hu

theorem Vset_mem_W {u : V} (hu : u ∈ C.Vset) : u ∈ F.W := by
  have ha := (Finset.mem_filter.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hu).2).2).2
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hi =>
    F.full_weight_not_adj_isolated C.srg C.v_weight hi ha⟩
theorem Wset_mem_W {u : V} (hu : u ∈ C.Wset) : u ∈ F.W := by
  have ha := (Finset.mem_filter.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hu).2).2).2
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hi =>
    F.full_weight_not_adj_isolated C.srg C.w_weight hi ha⟩

theorem Vset_Wset_disjoint : Disjoint C.Vset C.Wset := by
  apply Finset.disjoint_left.mpr
  intro u hv hw
  have hvo := Finset.mem_erase.mp (Finset.mem_erase.mp hv).2
  have hwo := Finset.mem_erase.mp (Finset.mem_erase.mp hw).2
  have he := C.common_unique u (Finset.mem_filter.mp hvo.2).2 (Finset.mem_filter.mp hwo.2).2
  exact hvo.1 he

theorem simple_points_eq : F.W.filter (fun u => F.weight u = 1) = C.Vset ∪ C.Wset := by
  have hsub : C.Vset ∪ C.Wset ⊆ F.W.filter (fun u => F.weight u = 1) := by
    intro u hu
    rcases Finset.mem_union.mp hu with hv | hw
    · exact Finset.mem_filter.mpr ⟨C.Vset_mem_W hv, C.Vset_simple hv⟩
    · exact Finset.mem_filter.mpr ⟨C.Wset_mem_W hw, C.Wset_simple hw⟩
  symm
  apply Finset.eq_of_subset_of_card_le hsub
  have hc := C.srg
  have hp := F.one_zero_weight_profile C.srg C.zero_count
  rw [Finset.card_union_of_disjoint C.Vset_Wset_disjoint, C.Vset_card, C.Wset_card]
  exact hp.1.le

theorem Vi_code {i : Fin 4} {u : V} (hu : u ∈ C.Vi i) : F.code i u = -F.code i C.v := by
  have ha := (Finset.mem_filter.mp (Finset.mem_erase.mp
    (Finset.mem_erase.mp (Finset.mem_filter.mp hu).1).2).2).2
  exact F.adjacent_nonzero_coordinate_opposite i (Finset.mem_filter.mp hu).2 (C.v_code_ne i) ha.symm

theorem Wi_code {i : Fin 4} {u : V} (hu : u ∈ C.Wi i) : F.code i u = F.code i C.v := by
  have ha := (Finset.mem_filter.mp (Finset.mem_erase.mp
    (Finset.mem_erase.mp (Finset.mem_filter.mp hu).1).2).2).2
  have hh := F.adjacent_nonzero_coordinate_opposite i (Finset.mem_filter.mp hu).2
    (C.w_code_ne i) ha.symm
  rw [hh, C.opposite i]

theorem Vi_cover : Finset.univ.biUnion C.Vi = C.Vset := by
  ext u
  constructor
  · intro hu
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hu
    exact (Finset.mem_filter.mp hi).1
  · intro hu
    obtain ⟨i,hi⟩ := F.simple_active_unique (C.Vset_simple hu)
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hu,(hi i).mpr rfl⟩⟩

theorem Wi_cover : Finset.univ.biUnion C.Wi = C.Wset := by
  ext u
  constructor
  · intro hu
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hu
    exact (Finset.mem_filter.mp hi).1
  · intro hu
    obtain ⟨i,hi⟩ := F.simple_active_unique (C.Wset_simple hu)
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hu,(hi i).mpr rfl⟩⟩

theorem Vi_pairwise_disjoint : Pairwise (fun i j => Disjoint (C.Vi i) (C.Vi j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro u hi hj
  obtain ⟨k,hk⟩ := F.simple_active_unique (C.Vset_simple (Finset.mem_filter.mp hi).1)
  exact hij (((hk i).mp (Finset.mem_filter.mp hi).2).trans
    ((hk j).mp (Finset.mem_filter.mp hj).2).symm)

theorem Wi_pairwise_disjoint : Pairwise (fun i j => Disjoint (C.Wi i) (C.Wi j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro u hi hj
  obtain ⟨k,hk⟩ := F.simple_active_unique (C.Wset_simple (Finset.mem_filter.mp hi).1)
  exact hij (((hk i).mp (Finset.mem_filter.mp hi).2).trans
    ((hk j).mp (Finset.mem_filter.mp hj).2).symm)

theorem Vi_support_neighbors (i : Fin 4) :
    (rootSupport (F.code i)).filter (G.Adj C.v) = insert C.w (C.Vi i) := by
  ext u
  simp only [Vi, Finset.mem_filter, Finset.mem_insert]
  constructor
  · intro hu
    by_cases he : u = C.w
    · exact Or.inl he
    · apply Or.inr
      refine ⟨?_, (F.mem_support_iff_code_ne_zero i u).mp hu.1⟩
      have hno : u ≠ C.o := by
        intro heo
        have hzero := (F.weight_zero_iff C.o).mp C.o_weight i
        exact hzero (heo ▸ hu.1)
      exact Finset.mem_erase.mpr ⟨he, Finset.mem_erase.mpr ⟨hno,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu.2⟩⟩⟩
  · intro hu
    rcases hu with rfl | hu
    · exact ⟨(F.mem_support_iff_code_ne_zero i C.w).mpr (C.w_code_ne i),C.vw_adj⟩
    · exact ⟨(F.mem_support_iff_code_ne_zero i u).mpr hu.2,
        (Finset.mem_filter.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hu.1).2).2).2⟩

theorem Wi_support_neighbors (i : Fin 4) :
    (rootSupport (F.code i)).filter (G.Adj C.w) = insert C.v (C.Wi i) := by
  ext u
  simp only [Wi, Finset.mem_filter, Finset.mem_insert]
  constructor
  · intro hu
    by_cases he : u = C.v
    · exact Or.inl he
    · apply Or.inr
      refine ⟨?_, (F.mem_support_iff_code_ne_zero i u).mp hu.1⟩
      have hno : u ≠ C.o := by
        intro heo
        have hzero := (F.weight_zero_iff C.o).mp C.o_weight i
        exact hzero (heo ▸ hu.1)
      exact Finset.mem_erase.mpr ⟨he, Finset.mem_erase.mpr ⟨hno,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu.2⟩⟩⟩
  · intro hu
    rcases hu with rfl | hu
    · exact ⟨(F.mem_support_iff_code_ne_zero i C.v).mpr (C.v_code_ne i),C.vw_adj.symm⟩
    · exact ⟨(F.mem_support_iff_code_ne_zero i u).mpr hu.2,
        (Finset.mem_filter.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hu.1).2).2).2⟩

theorem Vi_card (i : Fin 4) : (C.Vi i).card = 3 := by
  have hc := F.full_weight_support_neighbor_count C.v_weight i
  rw [C.Vi_support_neighbors] at hc
  have hn : C.w ∉ C.Vi i := by
    intro hh
    exact (Finset.mem_erase.mp (Finset.mem_filter.mp hh).1).1 rfl
  rw [Finset.card_insert_of_notMem hn] at hc
  omega

theorem Wi_card (i : Fin 4) : (C.Wi i).card = 3 := by
  have hc := F.full_weight_support_neighbor_count C.w_weight i
  rw [C.Wi_support_neighbors] at hc
  have hn : C.v ∉ C.Wi i := by
    intro hh
    exact (Finset.mem_erase.mp (Finset.mem_filter.mp hh).1).1 rfl
  rw [Finset.card_insert_of_notMem hn] at hc
  omega

theorem Rij_eq_signed_cell (i j : Fin 4) (s t : Bool)
    (hs : F.code i C.v = if s then 1 else -1)
    (ht : F.code j C.v = if t then 1 else -1) :
    C.Rij i j = signedCodeSupport (F.code i) s ∩ signedCodeSupport (F.code j) (!t) := by
  ext u
  simp only [Rij, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_inter, signedCodeSupport_mem, hs, ht]
  cases s <;> cases t <;> norm_num

theorem Rij_card (i j : Fin 4) (hij : i ≠ j) : (C.Rij i j).card = 1 := by
  have hsign (k : Fin 4) : ∃ s : Bool, F.code k C.v = if s then 1 else -1 := by
    rcases (F.biplane k).signs C.v with hn | hz | hp
    · exact ⟨false,hn⟩
    · exact (C.v_code_ne k hz).elim
    · exact ⟨true,hp⟩
  obtain ⟨s,hs⟩ := hsign i
  obtain ⟨t,ht⟩ := hsign j
  rw [C.Rij_eq_signed_cell i j s t hs ht]
  exact C.signedCells i j hij s (!t)

theorem full_points_eq : F.W.filter (fun u => F.weight u = 4) = {C.v,C.w} := by
  have hp := F.one_zero_weight_profile C.srg C.zero_count
  have hsub : {C.v,C.w} ⊆ F.W.filter (fun u => F.weight u = 4) := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨C.v_mem,C.v_weight⟩
    · exact Finset.mem_filter.mpr ⟨C.w_mem,C.w_weight⟩
  symm
  apply Finset.eq_of_subset_of_card_le hsub
  simp only [Finset.card_pair C.vw_ne]
  exact hp.2.2.2.le

theorem Rij_simple_coordinates {i j : Fin 4} {u : V} (hu : u ∈ C.Rij i j) :
    F.code i u ≠ 0 ∧ F.code j u ≠ 0 := by
  have he := (Finset.mem_filter.mp hu).2
  constructor
  · rw [he.1]
    exact C.v_code_ne i
  · rw [he.2]
    exact neg_ne_zero.mpr (C.v_code_ne j)

theorem Rij_weight {i j : Fin 4} (hij : i ≠ j) {u : V} (hu : u ∈ C.Rij i j) :
    F.weight u = 2 := by
  have hactive := C.Rij_simple_coordinates hu
  have huW := F.support_subset_W i ((F.mem_support_iff_code_ne_zero i u).mpr hactive.1)
  have hlo : 2 ≤ F.weight u := by
    have hsub : {i,j} ⊆ (Finset.univ : Finset (Fin 4)).filter (fun k => F.code k u ≠ 0) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> simp [hactive.1,hactive.2]
    have hc := Finset.card_le_card hsub
    rw [Finset.card_pair hij] at hc
    have hh := F.active_count_eq_weight u
    omega
  have hhi := F.weight_le_four u
  have hn3 : F.weight u ≠ 3 := by
    intro he
    have hp := (F.one_zero_weight_profile C.srg C.zero_count).2.2.1
    have hm : u ∈ F.W.filter (fun x => F.weight x = 3) := Finset.mem_filter.mpr ⟨huW,he⟩
    rw [Finset.card_eq_zero.mp hp] at hm
    exact Finset.not_mem_empty _ hm
  have hn4 : F.weight u ≠ 4 := by
    intro he
    have hm : u ∈ F.W.filter (fun x => F.weight x = 4) := Finset.mem_filter.mpr ⟨huW,he⟩
    rw [C.full_points_eq] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    have hs := (Finset.mem_filter.mp hu).2
    rcases hm with rfl | rfl
    · exact C.v_code_ne j (by omega)
    · have ho := C.opposite i
      exact C.v_code_ne i (by omega)
  omega

#print axioms simple_points_eq
#print axioms Vi_pairwise_disjoint
#print axioms Vi_card
#print axioms Rij_card
#print axioms Rij_weight

end OnePointConfiguration
end Conway99
