import FourDirectionINeighbors
import FourDirectionOneArcPoint
import FourDirectionOneArcGraph

/-! The final inverse-arc obstruction. The arc graph is an explicit hypothesis
in this module; its independent derivation is supplied by OneArcGraph. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem three_common_neighbors_impossible (h : G.IsSRGWith 99 14 1 2)
    {u v x y z : V} (huv : u ≠ v) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hux : G.Adj u x) (hvx : G.Adj v x) (huy : G.Adj u y) (hvy : G.Adj v y)
    (huz : G.Adj u z) (hvz : G.Adj v z) : False := by
  have hs : insert x {y,z} ⊆ (G.commonNeighbors u v).toFinset := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Set.mem_toFinset.mpr ⟨hux,hvx⟩
    · rcases Finset.mem_insert.mp ha with rfl | ha
      · exact Set.mem_toFinset.mpr ⟨huy,hvy⟩
      · have he := Finset.mem_singleton.mp ha
        subst a
        exact Set.mem_toFinset.mpr ⟨huz,hvz⟩
  have hh := Finset.card_le_card hs
  have hc : (insert x {y,z} : Finset V).card = 3 := by simp [hxy,hxz,hyz]
  rw [hc,Set.toFinset_card] at hh
  have hb := common_neighbors_at_most_two G h u v huv
  omega

theorem two_common_neighbors_adj_impossible (h : G.IsSRGWith 99 14 1 2)
    {u v x y : V} (huv : G.Adj u v) (hxy : x ≠ y)
    (hux : G.Adj u x) (hvx : G.Adj v x) (huy : G.Adj u y) (hvy : G.Adj v y) : False := by
  have hs : {x,y} ⊆ (G.commonNeighbors u v).toFinset := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Set.mem_toFinset.mpr ⟨hux,hvx⟩
    · have he := Finset.mem_singleton.mp ha
      subst a
      exact Set.mem_toFinset.mpr ⟨huy,hvy⟩
  have hh := Finset.card_le_card hs
  have hc : ({x,y} : Finset V).card = 2 := by simp [hxy]
  rw [hc,Set.toFinset_card,h.of_adj u v huv] at hh
  omega

theorem two_in_three_share_neighbor (T : Finset V) (hT : T.card = 3) (u v : V)
    (hu : (T.filter (G.Adj u)).card = 2) (hv : (T.filter (G.Adj v)).card = 2) :
    ∃ x ∈ T, G.Adj u x ∧ G.Adj v x := by
  have hs : T.filter (G.Adj u) ∪ T.filter (G.Adj v) ⊆ T := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx <;> exact (Finset.mem_filter.mp hx).1
  have hb := Finset.card_le_card hs
  have hh := Finset.card_union_add_card_inter (T.filter (G.Adj u)) (T.filter (G.Adj v))
  rw [hT] at hb
  rw [hu,hv] at hh
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0 <
    (T.filter (G.Adj u) ∩ T.filter (G.Adj v)).card)
  exact ⟨x,(Finset.mem_filter.mp (Finset.mem_inter.mp hx).1).1,
    (Finset.mem_filter.mp (Finset.mem_inter.mp hx).1).2,
    (Finset.mem_filter.mp (Finset.mem_inter.mp hx).2).2⟩

namespace FourDirections

def reverseArc (a : Arc) : Arc := ⟨(dst a, src a), Ne.symm a.property⟩

theorem reverseArc_ne (a : Arc) : reverseArc a ≠ a := by
  intro hh
  have he := congrArg (fun b : Arc => src b) hh
  exact a.property he.symm

theorem three_labels_inverse_eq (a b : Arc) (excluded : Label)
    (has : src a ≠ excluded) (had : dst a ≠ excluded)
    (hbs : src b ≠ excluded) (hbd : dst b ≠ excluded)
    (hsrc : src a ≠ src b) (hdst : dst a ≠ dst b) (hna : ¬arcAdj a b) :
    b = reverseArc a := by
  obtain ⟨h₁,h₂⟩ := three_labels_force_inverse a b excluded has had hbs hbd hsrc hdst hna
  apply Subtype.ext
  exact Prod.ext h₂.symm h₁.symm

end FourDirections

namespace OnePointConfiguration

variable {G} {F : FourDirectionSystem G} (C : OnePointConfiguration F)
include C

theorem isolated_not_mem_W {excluded : Fin 4} {t : V}
    (ht : t ∈ rootIsolated G (F.code excluded)) : t ∉ F.W := by
  intro hw
  exact (Finset.mem_sdiff.mp hw).2 (Finset.mem_biUnion.mpr ⟨excluded,Finset.mem_univ _,ht⟩)

theorem arc_common_R_vertex
    (hArc : ∀ a b, G.Adj (C.arcPoint a) (C.arcPoint b) ↔ FourDirections.arcAdj a b)
    (a b : FourDirections.Arc) (hc : (FourDirections.commonArcs a b).card = 1) :
    ∃ x ∈ C.Rset, G.Adj (C.arcPoint a) x ∧ G.Adj (C.arcPoint b) x := by
  obtain ⟨c,hc'⟩ := Finset.card_pos.mp (by omega : 0 < (FourDirections.commonArcs a b).card)
  have ha := (Finset.mem_filter.mp hc').2
  exact ⟨C.arcPoint c,C.arcPoint_mem_Rset c,(hArc a c).mpr ha.1,(hArc b c).mpr ha.2⟩

theorem isolated_arc_distinct_source
    (hArc : ∀ a b, G.Adj (C.arcPoint a) (C.arcPoint b) ↔ FourDirections.arcAdj a b)
    (hVi : ∀ a, ((C.Vi (FourDirections.src a)).filter (G.Adj (C.arcPoint a))).card = 2)
    {excluded : Fin 4} {t : V} (ht : t ∈ rootIsolated G (F.code excluded))
    (a b : FourDirections.Arc) (hab : a ≠ b)
    (hta : G.Adj t (C.arcPoint a)) (htb : G.Adj t (C.arcPoint b)) :
    FourDirections.src a ≠ FourDirections.src b := by
  intro hsrc
  have hbd : ((C.Vi (FourDirections.src a)).filter (G.Adj (C.arcPoint b))).card = 2 := by
    rw [hsrc]
    exact hVi b
  obtain ⟨x,hx,hax,hbx⟩ := two_in_three_share_neighbor G _ (C.Vi_card _) _ _ (hVi a) hbd
  obtain ⟨y,hy,hay,hby⟩ := C.arc_common_R_vertex hArc a b
    (FourDirections.same_source_one_common_arc a b hab hsrc)
  have hxW := C.Vset_mem_W (Finset.mem_filter.mp hx).1
  have hyW := (Finset.mem_filter.mp hy).1
  have htx : t ≠ x := fun hh => C.isolated_not_mem_W ht (hh ▸ hxW)
  have hty : t ≠ y := fun hh => C.isolated_not_mem_W ht (hh ▸ hyW)
  have hxy : x ≠ y := by
    intro hh
    have hw1 := C.Vset_simple (Finset.mem_filter.mp hx).1
    have hw2 := (Finset.mem_filter.mp hy).2
    rw [hh] at hw1
    omega
  exact three_common_neighbors_impossible G C.srg (C.arcPoint_injective.ne hab) htx hty hxy
    hta.symm htb.symm hax hbx hay hby

theorem isolated_arc_distinct_destination
    (hArc : ∀ a b, G.Adj (C.arcPoint a) (C.arcPoint b) ↔ FourDirections.arcAdj a b)
    (hWi : ∀ a, ((C.Wi (FourDirections.dst a)).filter (G.Adj (C.arcPoint a))).card = 2)
    {excluded : Fin 4} {t : V} (ht : t ∈ rootIsolated G (F.code excluded))
    (a b : FourDirections.Arc) (hab : a ≠ b)
    (hta : G.Adj t (C.arcPoint a)) (htb : G.Adj t (C.arcPoint b)) :
    FourDirections.dst a ≠ FourDirections.dst b := by
  intro hdst
  have hbd : ((C.Wi (FourDirections.dst a)).filter (G.Adj (C.arcPoint b))).card = 2 := by
    rw [hdst]
    exact hWi b
  obtain ⟨x,hx,hax,hbx⟩ := two_in_three_share_neighbor G _ (C.Wi_card _) _ _ (hWi a) hbd
  obtain ⟨y,hy,hay,hby⟩ := C.arc_common_R_vertex hArc a b
    (FourDirections.same_destination_one_common_arc a b hab hdst)
  have hxW := C.Wset_mem_W (Finset.mem_filter.mp hx).1
  have hyW := (Finset.mem_filter.mp hy).1
  have htx : t ≠ x := fun hh => C.isolated_not_mem_W ht (hh ▸ hxW)
  have hty : t ≠ y := fun hh => C.isolated_not_mem_W ht (hh ▸ hyW)
  have hxy : x ≠ y := by
    intro hh
    have hw1 := C.Wset_simple (Finset.mem_filter.mp hx).1
    have hw2 := (Finset.mem_filter.mp hy).2
    rw [hh] at hw1
    omega
  exact three_common_neighbors_impossible G C.srg (C.arcPoint_injective.ne hab) htx hty hxy
    hta.symm htb.symm hax hbx hay hby

theorem isolated_arc_nonadjacent
    (hArc : ∀ a b, G.Adj (C.arcPoint a) (C.arcPoint b) ↔ FourDirections.arcAdj a b)
    {excluded : Fin 4} {t : V} (ht : t ∈ rootIsolated G (F.code excluded))
    (a b : FourDirections.Arc)
    (hta : G.Adj t (C.arcPoint a)) (htb : G.Adj t (C.arcPoint b)) :
    ¬FourDirections.arcAdj a b := by
  intro hab
  obtain ⟨y,hy,hay,hby⟩ := C.arc_common_R_vertex hArc a b
    (FourDirections.adjacent_one_common_arc a b hab)
  have hty : t ≠ y := fun hh => C.isolated_not_mem_W ht (hh ▸ (Finset.mem_filter.mp hy).1)
  exact two_common_neighbors_adj_impossible G C.srg ((hArc a b).mpr hab) hty
    hta.symm htb.symm hay hby

theorem isolated_arc_excludes_label {excluded : Fin 4} {t : V}
    (ht : t ∈ rootIsolated G (F.code excluded)) (a : FourDirections.Arc)
    (hta : G.Adj t (C.arcPoint a)) :
    FourDirections.src a ≠ excluded ∧ FourDirections.dst a ≠ excluded := by
  have hs := (Finset.mem_filter.mp (C.arcPoint_mem_cell a)).2
  have hsrc : C.arcPoint a ∈ rootSupport (F.code (FourDirections.src a)) := by
    apply (F.mem_support_iff_code_ne_zero _ _).mpr
    intro hh
    exact C.v_code_ne _ (hs.1.symm.trans hh)
  have hdst : C.arcPoint a ∈ rootSupport (F.code (FourDirections.dst a)) := by
    apply (F.mem_support_iff_code_ne_zero _ _).mpr
    intro hh
    change F.code a.val.2 (C.arcPoint a) = 0 at hh
    have hn := C.v_code_ne a.val.2
    have hsn := hs.2
    rw [hh] at hsn
    omega
  constructor
  · intro he
    rw [he] at hsrc
    exact C.isolated_cell_not_adj_support ht hsrc hta
  · intro he
    rw [he] at hdst
    exact C.isolated_cell_not_adj_support ht hdst hta

theorem isolated_o_arc_inverse_neighbor
    (hArc : ∀ a b, G.Adj (C.arcPoint a) (C.arcPoint b) ↔ FourDirections.arcAdj a b)
    (hVi : ∀ a, ((C.Vi (FourDirections.src a)).filter (G.Adj (C.arcPoint a))).card = 2)
    (hWi : ∀ a, ((C.Wi (FourDirections.dst a)).filter (G.Adj (C.arcPoint a))).card = 2)
    {excluded : Fin 4} {t : V} (ht : t ∈ rootIsolated G (F.code excluded))
    (ho : G.Adj C.o t) (a : FourDirections.Arc) (hta : G.Adj t (C.arcPoint a)) :
    G.Adj t (C.arcPoint (FourDirections.reverseArc a)) := by
  let T := C.Rset.filter (G.Adj t)
  have hc : T.card = 2 := C.isolated_o_Rset_degree ht ho
  have hm : C.arcPoint a ∈ T := Finset.mem_filter.mpr ⟨C.arcPoint_mem_Rset a,hta⟩
  have hp : 0 < (T.erase (C.arcPoint a)).card := by
    rw [Finset.card_erase_of_mem hm,hc]
    decide
  obtain ⟨x,hx⟩ := Finset.card_pos.mp hp
  have hxne := (Finset.mem_erase.mp hx).1
  have hxT := (Finset.mem_erase.mp hx).2
  obtain ⟨b,hbx⟩ := C.Rset_arcPoint_exists (Finset.mem_filter.mp hxT).1
  have htb : G.Adj t (C.arcPoint b) := hbx ▸ (Finset.mem_filter.mp hxT).2
  have hba : b ≠ a := fun hh => hxne (hbx.symm.trans (congrArg C.arcPoint hh))
  have has := C.isolated_arc_excludes_label ht a hta
  have hbs := C.isolated_arc_excludes_label ht b htb
  have hsrc := C.isolated_arc_distinct_source hArc hVi ht a b hba.symm hta htb
  have hdst := C.isolated_arc_distinct_destination hArc hWi ht a b hba.symm hta htb
  have hna := C.isolated_arc_nonadjacent hArc ht a b hta htb
  have he := FourDirections.three_labels_inverse_eq a b excluded has.1 has.2 hbs.1 hbs.2 hsrc hdst hna
  rw [he] at htb
  exact htb

theorem o_arc_common_isolated (a : FourDirections.Arc) {t : V}
    (ho : G.Adj C.o t) (hr : G.Adj (C.arcPoint a) t) : t ∈ F.isolatedUnion := by
  by_contra hn
  have htW : t ∈ F.W := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hn⟩
  have h4 := F.zero_neighbors_weight_four C.srg C.o C.o_mem C.o_weight t
    (Finset.mem_filter.mpr ⟨htW,ho⟩)
  have hfull : t ∈ F.W.filter (fun u => F.weight u = 4) := Finset.mem_filter.mpr ⟨htW,h4⟩
  rw [C.full_points_eq] at hfull
  rcases Finset.mem_insert.mp hfull with rfl | hh
  · exact C.Rset_not_adj_v (C.arcPoint_mem_Rset a) hr.symm
  · have he := Finset.mem_singleton.mp hh
    subst t
    exact C.Rset_not_adj_w (C.arcPoint_mem_Rset a) hr.symm

theorem arc_graph_contradiction
    (hArc : ∀ a b, G.Adj (C.arcPoint a) (C.arcPoint b) ↔ FourDirections.arcAdj a b)
    (hVi : ∀ a, ((C.Vi (FourDirections.src a)).filter (G.Adj (C.arcPoint a))).card = 2)
    (hWi : ∀ a, ((C.Wi (FourDirections.dst a)).filter (G.Adj (C.arcPoint a))).card = 2) : False := by
  let a : FourDirections.Arc := ⟨(0,1),by decide⟩
  have hR := C.arcPoint_mem_Rset a
  have hno := C.Rset_not_adj_o hR
  have hone : C.o ≠ C.arcPoint a := by
    intro he
    have hw := (Finset.mem_filter.mp hR).2
    rw [← he,C.o_weight] at hw
    omega
  have hc : ((G.commonNeighbors C.o (C.arcPoint a)).toFinset).card = 2 := by
    rw [Set.toFinset_card]
    exact C.srg.of_not_adj hone hno
  obtain ⟨t,ht,s,hs,hts⟩ := Finset.one_lt_card.mp (by omega : 1 <
    ((G.commonNeighbors C.o (C.arcPoint a)).toFinset).card)
  have htc := Set.mem_toFinset.mp ht
  have hsc := Set.mem_toFinset.mp hs
  have hti := C.o_arc_common_isolated a htc.1 htc.2
  have hsi := C.o_arc_common_isolated a hsc.1 hsc.2
  obtain ⟨it,_,htI⟩ := Finset.mem_biUnion.mp hti
  obtain ⟨is,_,hsI⟩ := Finset.mem_biUnion.mp hsi
  have htr := C.isolated_o_arc_inverse_neighbor hArc hVi hWi htI htc.1 a htc.2.symm
  have hsr := C.isolated_o_arc_inverse_neighbor hArc hVi hWi hsI hsc.1 a hsc.2.symm
  have hrevR := C.arcPoint_mem_Rset (FourDirections.reverseArc a)
  have horev : C.o ≠ C.arcPoint (FourDirections.reverseArc a) := by
    intro he
    have hw := (Finset.mem_filter.mp hrevR).2
    rw [← he,C.o_weight] at hw
    omega
  have hpoints : C.arcPoint a ≠ C.arcPoint (FourDirections.reverseArc a) :=
    C.arcPoint_injective.ne (Ne.symm (FourDirections.reverseArc_ne a))
  exact three_common_neighbors_impossible G C.srg hts hone horev hpoints
    htc.1.symm hsc.1.symm htc.2.symm hsc.2.symm htr hsr

theorem onePointConfiguration_impossible : False :=
  C.arc_graph_contradiction C.arcPoint_adj_iff C.arcPoint_Vi_degree C.arcPoint_Wi_degree

omit C in
theorem four_directions_one_zero_impossible (F : FourDirectionSystem G)
    (h : G.IsSRGWith 99 14 1 2) (hc : F.HasSignedCells) (hz : F.weightCount 0 = 1) : False := by
  obtain ⟨C⟩ := onePointConfiguration_exists F h hc hz
  exact C.onePointConfiguration_impossible

#print axioms isolated_arc_distinct_source
#print axioms isolated_arc_nonadjacent
#print axioms isolated_o_arc_inverse_neighbor
#print axioms onePointConfiguration_impossible
#print axioms four_directions_one_zero_impossible

end OnePointConfiguration

variable {G}

theorem four_directions_one_zero_impossible (F : FourDirectionSystem G)
    (h : G.IsSRGWith 99 14 1 2) (hc : F.HasSignedCells) (hz : F.weightCount 0 = 1) : False :=
  OnePointConfiguration.four_directions_one_zero_impossible F h hc hz

#check @four_directions_one_zero_impossible
#print axioms four_directions_one_zero_impossible

end Conway99
