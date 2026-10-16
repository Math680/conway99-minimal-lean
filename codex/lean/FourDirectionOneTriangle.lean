import FourDirectionSignatures

/-! The triangle around the unique zero-signature vertex in the one-point case. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace FourDirectionSystem

variable (F : FourDirectionSystem G)

theorem mem_support_iff_code_ne_zero (i : Fin 4) (u : V) :
    u ∈ rootSupport (F.code i) ↔ F.code i u ≠ 0 := by
  rcases (F.biplane i).signs u with he | he | he <;>
    simp [rootSupport, positiveCodeSupport, negativeCodeSupport, he]

theorem weight_four_iff (u : V) : F.weight u = 4 ↔ ∀ i, F.code i u ≠ 0 := by
  constructor
  · intro hu
    have heq : (∑ i : Fin 4, if u ∈ rootSupport (F.code i) then (1 : ℤ) else 0) =
        ∑ _i : Fin 4, (1 : ℤ) := by
      simpa [weight] using hu
    have hh := (Finset.sum_eq_sum_iff_of_le (fun (i : Fin 4) _ =>
      show (if u ∈ rootSupport (F.code i) then (1 : ℤ) else 0) ≤ 1 by
        split_ifs <;> norm_num)).mp heq
    intro i
    apply (F.mem_support_iff_code_ne_zero i u).mp
    by_contra hn
    have hi := hh i (Finset.mem_univ _)
    simp [hn] at hi
  · intro hu
    simp [weight, fun i => (F.mem_support_iff_code_ne_zero i u).mpr (hu i)]

theorem same_nonzero_coordinate_not_adj (i : Fin 4) {u v : V}
    (hu : F.code i u ≠ 0) (he : F.code i u = F.code i v) : ¬G.Adj u v := by
  rcases (F.biplane i).signs u with hm | hz | hp
  · have huN : u ∈ negativeCodeSupport (F.code i) := by
      simp [negativeCodeSupport, hm]
    have hvN : v ∈ negativeCodeSupport (F.code i) := by
      simp [negativeCodeSupport, ← he, hm]
    exact not_adj_of_filter_card_zero G _ u ((F.biplane i).negative_internal u huN) hvN
  · exact (hu hz).elim
  · have huP : u ∈ positiveCodeSupport (F.code i) := by
      simp [positiveCodeSupport, hp]
    have hvP : v ∈ positiveCodeSupport (F.code i) := by
      simp [positiveCodeSupport, ← he, hp]
    exact not_adj_of_filter_card_zero G _ u ((F.biplane i).positive_internal u huP) hvP

theorem full_weight_not_adj_isolated (h : G.IsSRGWith 99 14 1 2)
    {u x : V} (hu : F.weight u = 4) (hx : x ∈ F.isolatedUnion) : ¬G.Adj u x := by
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
  have hcode := (F.weight_four_iff u).mp hu i
  have hs : u ∉ rootShell G (F.code i) := by
    simp [rootShell, hcode]
  exact not_adj_of_filter_card_zero G _ u
    (signed_biplane_isolated_degree_zero G h _ (F.biplane i) (F.eigen i) u hs) hi

theorem zero_W_neighbors_opposite (h : G.IsSRGWith 99 14 1 2)
    {o v w : V} (ho : o ∈ F.W) (hz : F.weight o = 0)
    (hv : v ∈ F.W.filter (G.Adj o)) (hw : w ∈ F.W.filter (G.Adj o))
    (hvw : v ≠ w) : ∀ i, F.code i v = -F.code i w := by
  intro i
  have hfv := F.zero_neighbors_weight_four h o ho hz v hv
  have hfw := F.zero_neighbors_weight_four h o ho hz w hw
  have hcv := (F.weight_four_iff v).mp hfv i
  have hcw := (F.weight_four_iff w).mp hfw i
  have hs := F.zero_mem_shell h o ho hz i
  have hp : ((positiveCodeSupport (F.code i)).filter (G.Adj o)).card = 1 :=
    (Finset.mem_filter.mp hs).2.2
  have hn : ((negativeCodeSupport (F.code i)).filter (G.Adj o)).card = 1 := by
    have hd := signed_biplane_zero_degrees G h _ (F.biplane i) (F.eigen i) o
      (Finset.mem_filter.mp hs).2.1
    omega
  have hneq (T : Finset V) (hc : (T.filter (G.Adj o)).card = 1)
      (hvT : v ∈ T) (hwT : w ∈ T) : False := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    have hv' : v ∈ T.filter (G.Adj o) :=
      Finset.mem_filter.mpr ⟨hvT, (Finset.mem_filter.mp hv).2⟩
    have hw' : w ∈ T.filter (G.Adj o) :=
      Finset.mem_filter.mpr ⟨hwT, (Finset.mem_filter.mp hw).2⟩
    rw [ha, Finset.mem_singleton] at hv' hw'
    exact hvw (hv'.trans hw'.symm)
  rcases (F.biplane i).signs v with hvm | hvz | hvp <;>
    rcases (F.biplane i).signs w with hwm | hwz | hwp
  · exact (hneq _ hn (by simp [negativeCodeSupport, hvm])
      (by simp [negativeCodeSupport, hwm])).elim
  · exact (hcw hwz).elim
  · omega
  · exact (hcv hvz).elim
  · exact (hcv hvz).elim
  · exact (hcv hvz).elim
  · omega
  · exact (hcw hwz).elim
  · exact (hneq _ hp (by simp [positiveCodeSupport, hvp])
      (by simp [positiveCodeSupport, hwp])).elim

theorem one_zero_unique (hz : F.weightCount 0 = 1) {o x : V}
    (ho : o ∈ F.W) (hzo : F.weight o = 0) (hx : x ∈ F.W)
    (hzx : F.weight x = 0) : x = o := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hz
  have hmo : o ∈ F.W.filter (fun u => F.weight u = 0) := Finset.mem_filter.mpr ⟨ho, hzo⟩
  have hmx : x ∈ F.W.filter (fun u => F.weight u = 0) := Finset.mem_filter.mpr ⟨hx, hzx⟩
  rw [ha, Finset.mem_singleton] at hmo hmx
  exact hmx.trans hmo.symm

theorem one_zero_common_neighbor_unique (h : G.IsSRGWith 99 14 1 2)
    (hz : F.weightCount 0 = 1) {o v w x : V}
    (ho : o ∈ F.W) (hzo : F.weight o = 0)
    (hv : v ∈ F.W.filter (G.Adj o)) (hw : w ∈ F.W.filter (G.Adj o))
    (hvw : v ≠ w) (hvx : G.Adj v x) (hwx : G.Adj w x) : x = o := by
  have hfv := F.zero_neighbors_weight_four h o ho hzo v hv
  by_cases hxI : x ∈ F.isolatedUnion
  · exact (F.full_weight_not_adj_isolated h hfv hxI hvx).elim
  have hxW : x ∈ F.W := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxI⟩
  by_cases hzx : F.weight x = 0
  · exact F.one_zero_unique hz ho hzo hxW hzx
  have hop := F.zero_W_neighbors_opposite h ho hzo hv hw hvw
  have hex : ∃ i, F.code i x ≠ 0 := by
    by_contra hh
    push_neg at hh
    apply hzx
    apply (F.weight_zero_iff x).mpr
    intro i
    simpa [F.mem_support_iff_code_ne_zero] using hh i
  obtain ⟨i, hi⟩ := hex
  have hiv := (F.weight_four_iff v).mp hfv i
  have hiw := (F.weight_four_iff w).mp
    (F.zero_neighbors_weight_four h o ho hzo w hw) i
  have hp : F.code i v = -F.code i w := hop i
  have hsame : F.code i x = F.code i v ∨ F.code i x = F.code i w := by
    rcases (F.biplane i).signs x with hm | hh | hp' <;>
      rcases (F.biplane i).signs v with hm' | hh' | hp'' <;>
      rcases (F.biplane i).signs w with hm'' | hh'' | hp''' <;> omega
  rcases hsame with hev | hew
  · exact (F.same_nonzero_coordinate_not_adj i hi hev hvx.symm).elim
  · exact (F.same_nonzero_coordinate_not_adj i hi hew hwx.symm).elim

theorem one_zero_triangle (h : G.IsSRGWith 99 14 1 2)
    (hz : F.weightCount 0 = 1) : ∃ o v w : V,
      o ∈ F.W ∧ F.weight o = 0 ∧
      v ∈ F.W ∧ w ∈ F.W ∧ v ≠ w ∧
      G.Adj o v ∧ G.Adj o w ∧ G.Adj v w ∧
      F.weight v = 4 ∧ F.weight w = 4 ∧
      (∀ i, F.code i v = -F.code i w) ∧
      (∀ x, G.Adj v x → G.Adj w x → x = o) := by
  classical
  have hpos : 0 < F.weightCount 0 := by omega
  obtain ⟨o, ho'⟩ := Finset.card_pos.mp hpos
  have ho := (Finset.mem_filter.mp ho').1
  have hzo := (Finset.mem_filter.mp ho').2
  obtain ⟨v, w, hvw, hp⟩ := Finset.card_eq_two.mp (F.zero_W_neighbors h o ho hzo)
  have hv : v ∈ F.W.filter (G.Adj o) := by rw [hp]; simp
  have hw : w ∈ F.W.filter (G.Adj o) := by rw [hp]; simp
  have huniq : ∀ x, G.Adj v x → G.Adj w x → x = o :=
    fun x => F.one_zero_common_neighbor_unique h hz ho hzo hv hw hvw (x := x)
  have hadj : G.Adj v w := by
    by_contra hno
    have hcard := h.of_not_adj hvw hno
    have hsub : (G.commonNeighbors v w).toFinset ⊆ {o} := by
      intro x hx
      have ha : x ∈ G.commonNeighbors v w := Set.mem_toFinset.mp hx
      exact Finset.mem_singleton.mpr (huniq x ha.1 ha.2)
    have hle := Finset.card_le_card hsub
    simp only [Set.toFinset_card, Finset.card_singleton] at hle
    omega
  exact ⟨o, v, w, ho, hzo, (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hw).1,
    hvw, (Finset.mem_filter.mp hv).2, (Finset.mem_filter.mp hw).2, hadj,
    F.zero_neighbors_weight_four h o ho hzo v hv,
    F.zero_neighbors_weight_four h o ho hzo w hw,
    F.zero_W_neighbors_opposite h ho hzo hv hw hvw, huniq⟩

#print axioms one_zero_triangle

end FourDirectionSystem
end Conway99
