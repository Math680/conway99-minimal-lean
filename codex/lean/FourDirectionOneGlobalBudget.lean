import FourDirectionOneProfiles
import FourDirectionOneRDegree
import ProfileGlobalBudget

/-! The twelve actual matching edges exhaust all six negative-profile budgets. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace OnePointConfiguration

variable {F : FourDirectionSystem G} (C : OnePointConfiguration F)

def profileNegative (D : Finset (Fin 4)) : Finset V := negativeCodeSupport (F.profile C.v D)
def matchingEdges : Finset (Sym2 V) :=
  (profileRestrictedGraph G C.Vset).edgeFinset ∪ (profileRestrictedGraph G C.Wset).edgeFinset

theorem Vi_code_else_zero {i k : Fin 4} (hki : k ≠ i) {u : V} (hu : u ∈ C.Vi i) :
    F.code k u = 0 := by
  obtain ⟨a,ha⟩ := F.simple_active_unique (C.Vset_simple (Finset.mem_filter.mp hu).1)
  have hai := (ha i).mp (Finset.mem_filter.mp hu).2
  by_contra hn
  exact hki (((ha k).mp hn).trans hai.symm)

theorem Wi_code_else_zero {i k : Fin 4} (hki : k ≠ i) {u : V} (hu : u ∈ C.Wi i) :
    F.code k u = 0 := by
  obtain ⟨a,ha⟩ := F.simple_active_unique (C.Wset_simple (Finset.mem_filter.mp hu).1)
  have hai := (ha i).mp (Finset.mem_filter.mp hu).2
  by_contra hn
  exact hki (((ha k).mp hn).trans hai.symm)

theorem profile_at_Vi (D : Finset (Fin 4)) {i : Fin 4} {u : V} (hu : u ∈ C.Vi i) :
    F.profile C.v D u = -1 + if i ∈ D then 1 else 0 := by
  have hmem := (C.mem_Vset u).mp (Finset.mem_filter.mp hu).1
  have huv : u ≠ C.v := hmem.2.2.ne.symm
  have hp (k : Fin 4) : F.code k C.v * F.code k u = if k = i then -1 else 0 := by
    by_cases hki : k = i
    · subst k
      rw [C.Vi_code hu]
      have hs := C.profile_code_square i
      simp only [if_true]
      nlinarith
    · simp [C.Vi_code_else_zero hki hu,hki]
  simp [FourDirectionSystem.profile,profileVertexBase,huv,hmem.2.2,hp]
  split_ifs <;> ring

theorem profile_at_Wi (D : Finset (Fin 4)) {i : Fin 4} {u : V} (hu : u ∈ C.Wi i) :
    F.profile C.v D u = -(if i ∈ D then 1 else 0) := by
  have hmem := (C.mem_Wset u).mp (Finset.mem_filter.mp hu).1
  have hnot := C.Wset_not_adj_v (Finset.mem_filter.mp hu).1
  have hp (k : Fin 4) : F.code k C.v * F.code k u = if k = i then 1 else 0 := by
    by_cases hki : k = i
    · subst k
      rw [C.Wi_code hu]
      have hs := C.profile_code_square i
      simp only [if_true]
      nlinarith
    · simp [C.Wi_code_else_zero hki hu,hki]
  simp [FourDirectionSystem.profile,profileVertexBase,hmem.1,hnot,hp]

theorem profile_at_Rij (D : Finset (Fin 4)) {i j : Fin 4} (hij : i ≠ j) {u : V}
    (hu : u ∈ C.Rij i j) :
    F.profile C.v D u = -(if i ∈ D then 1 else 0) + if j ∈ D then 1 else 0 := by
  have hw := C.Rij_weight hij hu
  have ha := C.Rij_simple_coordinates hu
  have hR : u ∈ C.Rset := Finset.mem_filter.mpr ⟨F.support_subset_W i
    ((F.mem_support_iff_code_ne_zero i u).mpr ha.1),hw⟩
  have hnot := C.Rset_not_adj_v hR
  have huv : u ≠ C.v := by intro hh; rw [hh,C.v_weight] at hw; omega
  have hp (k : Fin 4) : F.code k C.v * F.code k u =
      (if k = i then 1 else 0) - (if k = j then 1 else 0) := by
    have hs := (Finset.mem_filter.mp hu).2
    by_cases hki : k = i
    · subst k
      rw [hs.1]
      have hh := C.profile_code_square i
      simp only [if_true,if_neg hij]
      nlinarith
    · by_cases hkj : k = j
      · subst k
        rw [hs.2]
        have hh := C.profile_code_square j
        simp only [if_true,if_neg hki]
        nlinarith
      · simp [C.Rij_code_else_zero hij hki hkj hu,hki,hkj]
  simp only [FourDirectionSystem.profile,profileVertexBase,if_neg huv,if_neg hnot,
    hp,Finset.sum_sub_distrib]
  simp
  ring

theorem Vi_negative_iff (D : Finset (Fin 4)) {i : Fin 4} {u : V} (hu : u ∈ C.Vi i) :
    u ∈ C.profileNegative D ↔ FourDirections.negV D i := by
  simp only [profileNegative,negativeCodeSupport,Finset.mem_filter,Finset.mem_univ,true_and,
    C.profile_at_Vi D hu,FourDirections.negV]
  by_cases hi : i ∈ D <;> simp [hi]

theorem Wi_negative_iff (D : Finset (Fin 4)) {i : Fin 4} {u : V} (hu : u ∈ C.Wi i) :
    u ∈ C.profileNegative D ↔ FourDirections.negW D i := by
  simp only [profileNegative,negativeCodeSupport,Finset.mem_filter,Finset.mem_univ,true_and,
    C.profile_at_Wi D hu,FourDirections.negW]
  by_cases hi : i ∈ D <;> simp [hi]

theorem Rij_negative_iff (D : Finset (Fin 4)) {i j : Fin 4} (hij : i ≠ j) {u : V}
    (hu : u ∈ C.Rij i j) :
    u ∈ C.profileNegative D ↔ FourDirections.negR D ⟨(i,j),hij⟩ := by
  simp only [profileNegative,negativeCodeSupport,Finset.mem_filter,Finset.mem_univ,true_and,
    C.profile_at_Rij D hij hu,FourDirections.negR,FourDirections.src,FourDirections.dst]
  by_cases hi : i ∈ D <;> by_cases hj : j ∈ D <;> simp [hi,hj]

theorem matchingEdges_mem (u x : V) : s(u,x) ∈ C.matchingEdges ↔
    (u ∈ C.Vset ∧ x ∈ C.Vset ∧ G.Adj u x) ∨
    (u ∈ C.Wset ∧ x ∈ C.Wset ∧ G.Adj u x) := by
  simp only [matchingEdges,Finset.mem_union,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
  rfl

theorem matchingEdges_disjoint : Disjoint (profileRestrictedGraph G C.Vset).edgeFinset
    (profileRestrictedGraph G C.Wset).edgeFinset := by
  apply Finset.disjoint_left.mpr
  intro e heV heW
  induction e using Sym2.inductionOn with
  | hf u x =>
    have hv : u ∈ C.Vset ∧ x ∈ C.Vset ∧ G.Adj u x := SimpleGraph.mem_edgeFinset.mp heV
    have hw : u ∈ C.Wset ∧ x ∈ C.Wset ∧ G.Adj u x := SimpleGraph.mem_edgeFinset.mp heW
    exact Finset.disjoint_left.mp C.Vset_Wset_disjoint hv.1 hw.1

theorem matchingEdges_card : C.matchingEdges.card = 12 := by
  rw [matchingEdges,Finset.card_union_of_disjoint C.matchingEdges_disjoint]
  change profileEdgeCount G C.Vset + profileEdgeCount G C.Wset = 12
  rw [C.Vset_internal_edges,C.Wset_internal_edges]

theorem matchingEdges_owner : ∀ e ∈ C.matchingEdges,
    (FourDirections.Profiles.filter (fun D =>
      e ∈ (profileRestrictedGraph G (C.profileNegative D)).edgeFinset)).card = 1 := by
  intro e he
  induction e using Sym2.inductionOn with
  | hf u x =>
    rcases (C.matchingEdges_mem u x).mp he with hv | hw
    · rw [← C.Vi_cover] at hv
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hv.1
      obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hv.2.1
      have hij : i ≠ j := by intro hh; subst j; exact C.Vi_same_label_not_adj i hi hj hv.2.2
      exact FourDirections.profile_V_internal_owner_count G C.profileNegative u x i j hij hv.2.2
        (fun D _ => C.Vi_negative_iff D hi) (fun D _ => C.Vi_negative_iff D hj)
    · rw [← C.Wi_cover] at hw
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hw.1
      obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hw.2.1
      have hij : i ≠ j := by intro hh; subst j; exact C.Wi_same_label_not_adj i hi hj hw.2.2
      exact FourDirections.profile_W_internal_owner_count G C.profileNegative u x i j hij hw.2.2
        (fun D _ => C.Wi_negative_iff D hi) (fun D _ => C.Wi_negative_iff D hj)

theorem profile_negative_edges_exhausted : ∀ D ∈ FourDirections.Profiles,
    (profileRestrictedGraph G (C.profileNegative D)).edgeFinset ⊆ C.matchingEdges :=
  profile_six_budget_saturated G FourDirections.Profiles FourDirections.six_profiles
    C.profileNegative C.six_profile_negative_edge_counts C.matchingEdges C.matchingEdges_card
    C.matchingEdges_owner

theorem Vset_Wset_edge_not_matching {u x : V} (hu : u ∈ C.Vset) (hx : x ∈ C.Wset) :
    s(u,x) ∉ C.matchingEdges := by
  intro he
  rcases (C.matchingEdges_mem u x).mp he with hv | hw
  · exact Finset.disjoint_left.mp C.Vset_Wset_disjoint hv.2.1 hx
  · exact Finset.disjoint_left.mp C.Vset_Wset_disjoint hu hw.1

theorem Rset_edge_not_matching {u x : V} (hu : u ∈ C.Rset) : s(u,x) ∉ C.matchingEdges := by
  intro he
  rcases (C.matchingEdges_mem u x).mp he with hv | hw
  · exact Finset.disjoint_left.mp C.Rset_simple_disjoint (Finset.mem_union_left _ hv.1) hu
  · exact Finset.disjoint_left.mp C.Rset_simple_disjoint (Finset.mem_union_right _ hw.1) hu

theorem Vi_Wi_restriction {i j : Fin 4} {u x : V}
    (hu : u ∈ C.Vi i) (hx : x ∈ C.Wi j) (ha : G.Adj u x) : i = j := by
  exact FourDirections.global_profile_V_W_restriction G C.profileNegative
    C.six_profile_negative_edge_counts C.matchingEdges C.matchingEdges_card C.matchingEdges_owner
    u x i j ha (C.Vset_Wset_edge_not_matching (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hx).1)
    (fun D _ hh => (C.Vi_negative_iff D hu).mpr hh)
    (fun D _ hh => (C.Wi_negative_iff D hx).mpr hh)

theorem Vi_Rij_restriction {i j k : Fin 4} (hjk : j ≠ k) {u x : V}
    (hu : u ∈ C.Vi i) (hx : x ∈ C.Rij j k) (ha : G.Adj u x) : i = j := by
  have hR : x ∈ C.Rset := by
    rw [← C.Rall_eq_Rset]
    exact Finset.mem_biUnion.mpr ⟨(j,k),Finset.mem_offDiag.mpr ⟨Finset.mem_univ _,Finset.mem_univ _,hjk⟩,hx⟩
  have hn : s(u,x) ∉ C.matchingEdges := by simpa only [Sym2.eq_swap] using C.Rset_edge_not_matching (x := u) hR
  exact FourDirections.global_profile_V_R_restriction G C.profileNegative
    C.six_profile_negative_edge_counts C.matchingEdges C.matchingEdges_card C.matchingEdges_owner
    u x i ⟨(j,k),hjk⟩ ha hn (fun D _ hh => (C.Vi_negative_iff D hu).mpr hh)
    (fun D _ hh => (C.Rij_negative_iff D hjk hx).mpr hh)

theorem Wi_Rij_restriction {i j k : Fin 4} (hjk : j ≠ k) {u x : V}
    (hu : u ∈ C.Wi i) (hx : x ∈ C.Rij j k) (ha : G.Adj u x) : i = k := by
  have hR : x ∈ C.Rset := by
    rw [← C.Rall_eq_Rset]
    exact Finset.mem_biUnion.mpr ⟨(j,k),Finset.mem_offDiag.mpr ⟨Finset.mem_univ _,Finset.mem_univ _,hjk⟩,hx⟩
  have hn : s(u,x) ∉ C.matchingEdges := by simpa only [Sym2.eq_swap] using C.Rset_edge_not_matching (x := u) hR
  exact FourDirections.global_profile_W_R_restriction G C.profileNegative
    C.six_profile_negative_edge_counts C.matchingEdges C.matchingEdges_card C.matchingEdges_owner
    u x i ⟨(j,k),hjk⟩ ha hn (fun D _ hh => (C.Wi_negative_iff D hu).mpr hh)
    (fun D _ hh => (C.Rij_negative_iff D hjk hx).mpr hh)

theorem Rij_Rij_restriction {i j k l : Fin 4} (hij : i ≠ j) (hkl : k ≠ l) {u x : V}
    (hu : u ∈ C.Rij i j) (hx : x ∈ C.Rij k l) (ha : G.Adj u x) : j = k ∨ l = i := by
  have hR : u ∈ C.Rset := by
    rw [← C.Rall_eq_Rset]
    exact Finset.mem_biUnion.mpr ⟨(i,j),Finset.mem_offDiag.mpr ⟨Finset.mem_univ _,Finset.mem_univ _,hij⟩,hu⟩
  exact FourDirections.global_profile_R_R_restriction G C.profileNegative
    C.six_profile_negative_edge_counts C.matchingEdges C.matchingEdges_card C.matchingEdges_owner
    u x ⟨(i,j),hij⟩ ⟨(k,l),hkl⟩ ha (C.Rset_edge_not_matching hR)
    (fun D _ hh => (C.Rij_negative_iff D hij hu).mpr hh)
    (fun D _ hh => (C.Rij_negative_iff D hkl hx).mpr hh)

#print axioms matchingEdges_owner
#print axioms profile_negative_edges_exhausted
#print axioms Rij_Rij_restriction

end OnePointConfiguration
end Conway99
