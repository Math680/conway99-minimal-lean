import RootCode

/-! A pair of signed biplane codes cannot have another signed biplane code as its sum.
The argument uses the six nonzero sign cells and exhausted common-neighbour sets.
-/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem common_neighbor_set_exhausted (h : G.IsSRGWith 99 14 1 2)
    (T : Finset V) (u w : V) (huw : u ≠ w)
    (ht : (T.filter (fun v => G.Adj u v ∧ G.Adj w v)).card = 2)
    (v : V) (huv : G.Adj u v) (hwv : G.Adj w v) : v ∈ T := by
  let C := Finset.univ.filter (fun v => G.Adj u v ∧ G.Adj w v)
  have hsub : T.filter (fun v => G.Adj u v ∧ G.Adj w v) ⊆ C := by
    intro t ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ht).2⟩
  have hcard : C.card ≤ 2 := filtered_common_neighbors_le_two G h _ u w huw
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hv : v ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, hwv⟩
  rw [← heq] at hv
  exact (Finset.mem_filter.mp hv).1

theorem signedBiplane_common_neighbor_opposite (h : G.IsSRGWith 99 14 1 2)
    {b : V → ℤ} (hb : SignedBiplaneCode G b)
    (u w v : V) (huw : u ≠ w) (heq : b u = b w) (hne : b u ≠ 0)
    (huv : G.Adj u v) (hwv : G.Adj w v) : b v = -b u := by
  rcases hb.signs u with hu | hu | hu
  · have hwu : b w = -1 := by omega
    have hum : u ∈ negativeCodeSupport b := by simp [negativeCodeSupport, hu]
    have hwm : w ∈ negativeCodeSupport b := by simp [negativeCodeSupport, hwu]
    have hv := common_neighbor_set_exhausted G h (positiveCodeSupport b) u w huw
      (hb.negative_pairs u hum w hwm huw) v huv hwv
    have hv1 : b v = 1 := (Finset.mem_filter.mp hv).2
    omega
  · exact (hne hu).elim
  · have hwu : b w = 1 := by omega
    have hum : u ∈ positiveCodeSupport b := by simp [positiveCodeSupport, hu]
    have hwm : w ∈ positiveCodeSupport b := by simp [positiveCodeSupport, hwu]
    have hv := common_neighbor_set_exhausted G h (negativeCodeSupport b) u w huw
      (hb.positive_pairs u hum w hwm huw) v huv hwv
    have hv1 : b v = -1 := (Finset.mem_filter.mp hv).2
    omega

def rootSignCell (b c : V → ℤ) (a d : ℤ) : Finset V :=
  Finset.univ.filter (fun u => b u = a ∧ c u = d)

@[simp] theorem mem_rootSignCell (b c : V → ℤ) (a d : ℤ) (u : V) :
    u ∈ rootSignCell b c a d ↔ b u = a ∧ c u = d := by simp [rootSignCell]

theorem rootSignCell_disjoint (b c : V → ℤ) (a d a' d' : ℤ)
    (hne : a ≠ a' ∨ d ≠ d') : Disjoint (rootSignCell b c a d) (rootSignCell b c a' d') := by
  apply Finset.disjoint_left.mpr
  intro u hu hu'
  simp only [mem_rootSignCell] at hu hu'
  omega

theorem rootSignCell_common_neighbor (h : G.IsSRGWith 99 14 1 2)
    {b c : V → ℤ} (hb : SignedBiplaneCode G b) (hc : SignedBiplaneCode G c)
    (hs : SignedBiplaneCode G (b + c))
    (a d : ℤ) (hne : a ≠ 0 ∨ d ≠ 0)
    (u w v : V) (hu : u ∈ rootSignCell b c a d) (hw : w ∈ rootSignCell b c a d)
    (huw : u ≠ w) (huv : G.Adj u v) (hwv : G.Adj w v) :
    v ∈ rootSignCell b c (-a) (-d) := by
  simp only [mem_rootSignCell] at hu hw ⊢
  by_cases ha : a = 0
  · have hd : d ≠ 0 := by omega
    have hvc := signedBiplane_common_neighbor_opposite G h hc u w v huw (by omega)
      (by omega) huv hwv
    have hvs := signedBiplane_common_neighbor_opposite G h hs u w v huw
      (by simp only [Pi.add_apply]; omega) (by simp only [Pi.add_apply]; omega) huv hwv
    simp only [Pi.add_apply] at hvs
    constructor <;> omega
  · have hvb := signedBiplane_common_neighbor_opposite G h hb u w v huw (by omega)
      (by omega) huv hwv
    by_cases hd : d = 0
    · have hvs := signedBiplane_common_neighbor_opposite G h hs u w v huw
        (by simp only [Pi.add_apply]; omega) (by simp only [Pi.add_apply]; omega) huv hwv
      simp only [Pi.add_apply] at hvs
      constructor <;> omega
    · have hvc := signedBiplane_common_neighbor_opposite G h hc u w v huw (by omega)
        (by omega) huv hwv
      constructor <;> omega

theorem rootSignCell_partial_matching (h : G.IsSRGWith 99 14 1 2)
    {b c : V → ℤ} (hb : SignedBiplaneCode G b) (hc : SignedBiplaneCode G c)
    (hs : SignedBiplaneCode G (b + c))
    (a d : ℤ) (hne : a ≠ 0 ∨ d ≠ 0) (u : V)
    (hu : u ∉ rootSignCell b c (-a) (-d)) :
    ((rootSignCell b c a d).filter (G.Adj u)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro v hv w hw
  by_contra hvw
  exact hu (rootSignCell_common_neighbor G h hb hc hs a d hne v w u
    (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hw).1 hvw
    (Finset.mem_filter.mp hv).2.symm (Finset.mem_filter.mp hw).2.symm)

theorem signedBiplane_opposite_neighbors_four {b : V → ℤ} (hb : SignedBiplaneCode G b)
    (u : V) (hne : b u ≠ 0) :
    (Finset.univ.filter (fun v => b v = -b u ∧ G.Adj u v)).card = 4 := by
  rcases hb.signs u with hu | hu | hu
  · simpa [positiveCodeSupport, hu, Finset.filter_filter, and_assoc] using
      hb.negative_cross u (by simp [negativeCodeSupport, hu])
  · exact (hne hu).elim
  · simpa [negativeCodeSupport, hu, Finset.filter_filter, and_assoc] using
      hb.positive_cross u (by simp [positiveCodeSupport, hu])

theorem rootSignCell_axis_opposite_degree (h : G.IsSRGWith 99 14 1 2)
    {b c : V → ℤ} (hb : SignedBiplaneCode G b) (hc : SignedBiplaneCode G c)
    (hs : SignedBiplaneCode G (b + c)) (a : ℤ) (ha : a = -1 ∨ a = 1)
    (u : V) (hu : u ∈ rootSignCell b c a 0) :
    3 ≤ ((rootSignCell b c (-a) 0).filter (G.Adj u)).card := by
  have hu' := mem_rootSignCell b c a 0 u |>.mp hu
  have hcross := signedBiplane_opposite_neighbors_four G hb u (by omega)
  have heq : Finset.univ.filter (fun v => b v = -b u ∧ G.Adj u v) =
      ((rootSignCell b c (-a) 0).filter (G.Adj u)) ∪
      ((rootSignCell b c (-a) a).filter (G.Adj u)) := by
    ext v
    have hcv := hc.signs v
    have hsv := hs.signs v
    simp only [Pi.add_apply] at hsv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, mem_rootSignCell]
    by_cases hav : G.Adj u v
    · simp only [hav, and_true]
      omega
    · simp only [hav, and_false, or_self]
  have hdis : Disjoint ((rootSignCell b c (-a) 0).filter (G.Adj u))
      ((rootSignCell b c (-a) a).filter (G.Adj u)) :=
    (rootSignCell_disjoint b c (-a) 0 (-a) a (Or.inr (by omega))).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hm := rootSignCell_partial_matching G h hb hc hs (-a) a (by omega) u (by
    simp only [mem_rootSignCell]
    omega)
  rw [heq, Finset.card_union_of_disjoint hdis] at hcross
  omega

theorem rootSignCell_axis_card_sum {b c : V → ℤ}
    (hb : SignedBiplaneCode G b) (hc : SignedBiplaneCode G c)
    (hs : SignedBiplaneCode G (b + c)) :
    (rootSignCell b c 1 0).card + (rootSignCell b c (-1) 0).card = 7 := by
  have hec : positiveCodeSupport c = rootSignCell b c (-1) 1 ∪ rootSignCell b c 0 1 := by
    ext v
    have hbv := hb.signs v
    have hsv := hs.signs v
    simp only [Pi.add_apply] at hsv
    simp only [positiveCodeSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, mem_rootSignCell]
    omega
  have hes : positiveCodeSupport (b + c) = rootSignCell b c 1 0 ∪ rootSignCell b c 0 1 := by
    ext v
    have hbv := hb.signs v
    have hcv := hc.signs v
    simp only [positiveCodeSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, mem_rootSignCell, Pi.add_apply]
    omega
  have heb : negativeCodeSupport b = rootSignCell b c (-1) 1 ∪ rootSignCell b c (-1) 0 := by
    ext v
    have hcv := hc.signs v
    have hsv := hs.signs v
    simp only [Pi.add_apply] at hsv
    simp only [negativeCodeSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, mem_rootSignCell]
    omega
  have hpc := hc.positive_card
  have hps := hs.positive_card
  have hnb := hb.negative_card
  rw [hec, Finset.card_union_of_disjoint (rootSignCell_disjoint b c (-1) 1 0 1 (by omega))] at hpc
  rw [hes, Finset.card_union_of_disjoint (rootSignCell_disjoint b c 1 0 0 1 (by omega))] at hps
  rw [heb, Finset.card_union_of_disjoint (rootSignCell_disjoint b c (-1) 1 (-1) 0 (by omega))] at hnb
  omega

theorem bipartite_seven_three_impossible (h : G.IsSRGWith 99 14 1 2)
    (P N : Finset V) (hcard : P.card + N.card = 7) (hP : 4 ≤ P.card)
    (hd : ∀ u ∈ P, 3 ≤ (N.filter (G.Adj u)).card) : False := by
  obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp (show 1 < P.card by omega)
  have hN : N.card = 3 := by
    have hdu := hd u hu
    have hle := Finset.card_filter_le N (G.Adj u)
    omega
  have hall (v : V) (hv : v ∈ P) : N.filter (G.Adj v) = N := by
    exact Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by
      have hnv := hd v hv
      omega)
  have heq : N.filter (fun v => G.Adj u v ∧ G.Adj w v) = N := by
    apply Finset.filter_eq_self.mpr
    intro v hv
    have huv : v ∈ N.filter (G.Adj u) := by rw [hall u hu]; exact hv
    have hwv : v ∈ N.filter (G.Adj w) := by rw [hall w hw]; exact hv
    exact ⟨(Finset.mem_filter.mp huv).2, (Finset.mem_filter.mp hwv).2⟩
  have hh := filtered_common_neighbors_le_two G h N u w huw
  rw [heq, hN] at hh
  omega

theorem signed_biplane_sum_impossible (h : G.IsSRGWith 99 14 1 2)
    {b c : V → ℤ} (hb : SignedBiplaneCode G b) (hc : SignedBiplaneCode G c)
    (hs : SignedBiplaneCode G (b + c)) : False := by
  have hcard := rootSignCell_axis_card_sum G hb hc hs
  by_cases hp : 4 ≤ (rootSignCell b c 1 0).card
  · exact bipartite_seven_three_impossible G h (rootSignCell b c 1 0)
      (rootSignCell b c (-1) 0) hcard hp (by
        intro u hu
        exact rootSignCell_axis_opposite_degree G h hb hc hs 1 (Or.inr rfl) u hu)
  · have hn : 4 ≤ (rootSignCell b c (-1) 0).card := by omega
    exact bipartite_seven_three_impossible G h (rootSignCell b c (-1) 0)
      (rootSignCell b c 1 0) (by omega) hn (by
        intro u hu
        simpa only [neg_neg] using
          rootSignCell_axis_opposite_degree G h hb hc hs (-1) (Or.inl rfl) u hu)

theorem codePair_neg_left (x y : V → ℚ) : codePair (-x) y = -codePair x y := by
  simp only [codePair, neg_dotProduct, neg_div]

theorem codePair_neg_right (x y : V → ℚ) : codePair x (-y) = -codePair x y := by
  rw [codePair_symm, codePair_neg_left, codePair_symm]

theorem codePair_neg_norm (x : V → ℚ) : codePair (-x) (-x) = codePair x x := by
  rw [codePair_neg_left, codePair_neg_right, neg_neg]

theorem canonicalDual_root_pair_neg_one_impossible (h : G.IsSRGWith 99 14 1 2)
    {x y : V → ℚ} (hx : IsCanonicalDual G x) (hy : IsCanonicalDual G y)
    (hnx : codePair x x = 2) (hny : codePair y y = 2)
    (hxy : codePair x y = -1) : False := by
  have hsum : IsCanonicalDual G (x + y) := (canonicalDual G).add_mem hx hy
  have hnorm : codePair (x + y) (x + y) = 2 := by
    rw [codePair_norm_add, hnx, hny, hxy]
    norm_num
  obtain ⟨b, hxb, _, _, _, hb⟩ := canonicalDual_root_biplane G h hx hnx
  obtain ⟨c, hyc, _, _, _, hc⟩ := canonicalDual_root_biplane G h hy hny
  obtain ⟨d, hsd, _, _, _, hd⟩ := canonicalDual_root_biplane G h hsum hnorm
  have hdbc : d = b + c := by
    ext u
    have hpoint := congrFun hsd u
    rw [hxb, hyc] at hpoint
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hpoint
    change d u = b u + c u
    apply Int.cast_injective (α := ℚ)
    push_cast
    linarith
  rw [hdbc] at hd
  exact signed_biplane_sum_impossible G h hb hc hd

theorem canonicalDual_root_pair_pos_one_impossible (h : G.IsSRGWith 99 14 1 2)
    {x y : V → ℚ} (hx : IsCanonicalDual G x) (hy : IsCanonicalDual G y)
    (hnx : codePair x x = 2) (hny : codePair y y = 2)
    (hxy : codePair x y = 1) : False := by
  apply canonicalDual_root_pair_neg_one_impossible G h hx ((canonicalDual G).neg_mem hy) hnx
  · rw [codePair_neg_norm, hny]
  · rw [codePair_neg_right, hxy]

theorem canonicalLift_distinct_root_directions_orthogonal (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G))
    (hH : ∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0)
    {x y : V → ℚ} (hx : x ∈ canonicalLift G H) (hy : y ∈ canonicalLift G H)
    (hnx : codePair x x = 2) (hny : codePair y y = 2)
    (hne : x ≠ y) (hnopp : x ≠ -y) : codePair x y = 0 := by
  have hsne : x + y ≠ 0 := by
    intro hz
    exact hnopp (add_eq_zero_iff_eq_neg.mp hz)
  have hdne : x + -y ≠ 0 := by
    intro hz
    have hh := add_eq_zero_iff_eq_neg.mp hz
    exact hne (by simpa only [neg_neg] using hh)
  have hspos := codePair_pos (x + y) hsne
  have hdpos := codePair_pos (x + -y) hdne
  rw [codePair_norm_add, hnx, hny] at hspos
  rw [codePair_norm_add, hnx, codePair_neg_norm, hny, codePair_neg_right] at hdpos
  obtain ⟨a, ha⟩ := canonicalLift_integral G h H hH hx hy
  have hlo : (-2 : ℤ) < a := by
    exact_mod_cast (show (-2 : ℚ) < (a : ℚ) by rw [ha] at hspos; linarith)
  have hhi : a < (2 : ℤ) := by
    exact_mod_cast (show (a : ℚ) < (2 : ℚ) by rw [ha] at hdpos; linarith)
  have hdx := canonicalLift_le_dual G H hx
  have hdy := canonicalLift_le_dual G H hy
  have ha0 : a = 0 := by
    have hneg : a ≠ -1 := by
      intro hz
      apply canonicalDual_root_pair_neg_one_impossible G h hdx hdy hnx hny
      rw [ha, hz]
      norm_num
    have hpos : a ≠ 1 := by
      intro hz
      apply canonicalDual_root_pair_pos_one_impossible G h hdx hdy hnx hny
      rw [ha, hz]
      norm_num
    omega
  rw [ha, ha0]
  norm_num

#print axioms rootSignCell_partial_matching
#print axioms rootSignCell_axis_opposite_degree
#print axioms signed_biplane_sum_impossible
#print axioms canonicalDual_root_pair_neg_one_impossible
#print axioms canonicalDual_root_pair_pos_one_impossible
#print axioms canonicalLift_distinct_root_directions_orthogonal

end Conway99
