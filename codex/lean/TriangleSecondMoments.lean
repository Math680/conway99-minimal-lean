import TriangleMoments
import IntegralGram

/-! Exact second moments from S² = 21S, without a separate enumeration of
four-cycles. All counts concern the actual triangle-disjointness graph. -/

namespace Conway99.TriangleSecondMoments

open scoped BigOperators
open TriangleMoments TrianglePairs

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- N_m counts actual unordered disjoint triangle pairs with m crossing edges. -/
def crossingPairCount (m : ℕ) : ℕ :=
  ((unorderedDisjointTrianglePairs G).filter fun e => unorderedCrossingEdges G e = m).card

theorem integerGram_disjoint (L M : Incidence.TriangleIndex G)
    (hd : Disjoint L.val M.val) :
    integerTriangleGram G L M = 1 - (triangleCrossEdges G L M : ℤ) := by
  simp [integerTriangleGram, Finset.disjoint_iff_inter_eq_empty.mp hd]
  ring

theorem integerGram_meeting (h : G.IsSRGWith 99 14 1 2)
    (L M : Incidence.TriangleIndex G) (hne : L ≠ M)
    (hm : ¬Disjoint L.val M.val) : integerTriangleGram G L M = 0 := by
  have hic : (L.val ∩ M.val).card = 1 := by
    have hle := distinct_triangles_inter_card G h hne
    have hp := Finset.card_pos.mpr (Finset.not_disjoint_iff_nonempty_inter.mp hm)
    omega
  simp [integerTriangleGram, hic, meeting_crossing_edges_four G h L M hne hm]

/-- The squared row norm of the genuine integral Gram matrix is 84. -/
theorem integerGram_row_square (h : G.IsSRGWith 99 14 1 2)
    (L : Incidence.TriangleIndex G) :
    (∑ M, integerTriangleGram G L M ^ 2) = 84 := by
  have hh := congrArg
    (fun S : Matrix (Incidence.TriangleIndex G) (Incidence.TriangleIndex G) ℤ => S L L)
    (integerTriangleGram_square G h)
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, integerTriangleGram_diag] at hh
  have he : (∑ M, integerTriangleGram G L M * integerTriangleGram G M L) =
      ∑ M, integerTriangleGram G L M ^ 2 := by
    apply Finset.sum_congr rfl
    intro M hM
    rw [integerTriangleGram_symmetric G M L, pow_two]
  rw [he] at hh
  norm_num at hh
  exact hh

theorem disjoint_triangle_indicator_sum (h : G.IsSRGWith 99 14 1 2)
    (L : Incidence.TriangleIndex G) :
    (∑ M : Incidence.TriangleIndex G, if Disjoint L.val M.val then 1 else 0) = 212 := by
  rw [Finset.sum_coe_sort (G.cliqueFinset 3)
    (fun s : Finset V => if Disjoint L.val s then (1 : ℕ) else 0)]
  rw [← Finset.sum_filter]
  simpa [disjointTriangles] using disjoint_triangle_count_212 G h
    (G.mem_cliqueFinset_iff.mp L.property)

/-- Removing the diagonal and the zero intersecting entries leaves 68. -/
theorem disjoint_shifted_square_row (h : G.IsSRGWith 99 14 1 2)
    (L : Incidence.TriangleIndex G) :
    (∑ M : Incidence.TriangleIndex G,
      if Disjoint L.val M.val then (1 - (triangleCrossEdges G L M : ℤ)) ^ 2 else 0) = 68 := by
  have hdecomp : ∀ M : Incidence.TriangleIndex G, integerTriangleGram G L M ^ 2 =
      (if Disjoint L.val M.val then (1 - (triangleCrossEdges G L M : ℤ)) ^ 2 else 0) +
      16 * (if M = L then 1 else 0) := by
    intro M
    by_cases he : M = L
    · subst M
      have hnd : ¬Disjoint L.val L.val := by
        obtain ⟨u, hu⟩ := Finset.card_pos.mp (by rw [triangle_card G L]; norm_num)
        intro hd
        exact Finset.disjoint_left.mp hd hu hu
      simp only [hnd, if_false, if_true, integerTriangleGram_diag G L]
      norm_num
    · by_cases hd : Disjoint L.val M.val
      · simp only [hd, if_true, he, if_false, integerGram_disjoint G L M hd, mul_zero,
          add_zero]
      · simp only [hd, if_false, he, integerGram_meeting G h L M (Ne.symm he) hd,
          zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
  have hh := congrArg (fun f : Incidence.TriangleIndex G → ℤ => ∑ M, f M)
    (funext hdecomp)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  rw [integerGram_row_square G h L] at hh
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hh
  omega

/-- Exact second moment of crossing edges in a disjoint row. -/
theorem disjoint_crossing_square_row (h : G.IsSRGWith 99 14 1 2)
    (L : Incidence.TriangleIndex G) :
    (∑ M : Incidence.TriangleIndex G,
      if Disjoint L.val M.val then triangleCrossEdges G L M ^ 2 else 0) = 288 := by
  have h0 : (∑ M : Incidence.TriangleIndex G,
      if Disjoint L.val M.val then (1 : ℤ) else 0) = 212 := by
    exact_mod_cast disjoint_triangle_indicator_sum G h L
  have h1 : (∑ M : Incidence.TriangleIndex G,
      if Disjoint L.val M.val then (triangleCrossEdges G L M : ℤ) else 0) = 216 := by
    exact_mod_cast disjoint_crossing_edges_row_sum G h L
  have h2 := disjoint_shifted_square_row G h L
  have he : ∀ M : Incidence.TriangleIndex G,
      (if Disjoint L.val M.val then (1 - (triangleCrossEdges G L M : ℤ)) ^ 2 else 0) =
      (if Disjoint L.val M.val then (1 : ℤ) else 0) -
      2 * (if Disjoint L.val M.val then (triangleCrossEdges G L M : ℤ) else 0) +
      (if Disjoint L.val M.val then (triangleCrossEdges G L M : ℤ) ^ 2 else 0) := by
    intro M
    by_cases hd : Disjoint L.val M.val <;> simp only [hd, if_true, if_false] <;> ring
  have hh := congrArg (fun f : Incidence.TriangleIndex G → ℤ => ∑ M, f M) (funext he)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hh
  rw [h2, h0, h1] at hh
  have hz : (∑ M : Incidence.TriangleIndex G,
      if Disjoint L.val M.val then (triangleCrossEdges G L M : ℤ) ^ 2 else 0) = 288 := by
    omega
  exact_mod_cast hz

theorem ordered_crossing_square_moment (h : G.IsSRGWith 99 14 1 2) :
    (∑ p ∈ orderedDisjointTrianglePairs G, triangleCrossEdges G p.1 p.2 ^ 2) = 66528 := by
  have he : (∑ p ∈ orderedDisjointTrianglePairs G, triangleCrossEdges G p.1 p.2 ^ 2) =
      ∑ L : Incidence.TriangleIndex G, ∑ M : Incidence.TriangleIndex G,
        if Disjoint L.val M.val then triangleCrossEdges G L M ^ 2 else 0 := by
    rw [orderedDisjointTrianglePairs, Finset.sum_filter,
      ← Finset.univ_product_univ, Finset.sum_product]
  rw [he]
  simp_rw [disjoint_crossing_square_row G h]
  have hc : Fintype.card (Incidence.TriangleIndex G) = 231 := by
    change Fintype.card ↥(G.cliqueFinset 3) = 231
    rw [Fintype.card_coe, triangle_count_231 G h]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, hc]

theorem unordered_crossing_square_moment (h : G.IsSRGWith 99 14 1 2) :
    (∑ e ∈ unorderedDisjointTrianglePairs G, unorderedCrossingEdges G e ^ 2) = 33264 := by
  have hh := weighted_ordered_eq_twice_unordered G (fun m => m ^ 2)
  rw [ordered_crossing_square_moment G h] at hh
  omega

theorem unordered_crossing_edges_le_three (h : G.IsSRGWith 99 14 1 2)
    {e : Sym2 (Incidence.TriangleIndex G)} (he : e ∈ unorderedDisjointTrianglePairs G) :
    unorderedCrossingEdges G e ≤ 3 := by
  obtain ⟨L, M⟩ := e
  have hd : Disjoint L.val M.val :=
    (disjointTriangleGraph G).mem_edgeFinset.mp he
  simpa only [unorderedCrossingEdges_mk] using disjoint_crossing_edges_le_three G h L M hd

/-- The second factorial moment, expressed as counts N₂ + 3N₃. -/
theorem crossing_pair_second_factorial (h : G.IsSRGWith 99 14 1 2) :
    crossingPairCount G 2 + 3 * crossingPairCount G 3 = 4158 := by
  have hp : ∀ e ∈ unorderedDisjointTrianglePairs G,
      unorderedCrossingEdges G e ^ 2 = unorderedCrossingEdges G e +
      2 * (if unorderedCrossingEdges G e = 2 then 1 else 0) +
      6 * (if unorderedCrossingEdges G e = 3 then 1 else 0) := by
    intro e he
    have hb := unordered_crossing_edges_le_three G h he
    interval_cases hv : unorderedCrossingEdges G e <;> norm_num
  have hh : (∑ e ∈ unorderedDisjointTrianglePairs G, unorderedCrossingEdges G e ^ 2) =
      (∑ e ∈ unorderedDisjointTrianglePairs G, unorderedCrossingEdges G e) +
      2 * crossingPairCount G 2 + 6 * crossingPairCount G 3 := by
    calc
      _ = ∑ e ∈ unorderedDisjointTrianglePairs G,
          (unorderedCrossingEdges G e +
            2 * (if unorderedCrossingEdges G e = 2 then 1 else 0) +
            6 * (if unorderedCrossingEdges G e = 3 then 1 else 0)) :=
        Finset.sum_congr rfl hp
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [crossingPairCount]
  rw [unordered_crossing_square_moment G h, unordered_disjoint_crossing_moment G h] at hh
  omega

/-- Every multiplicity count passes from ordered pairs to edges with factor two. -/
theorem ordered_crossing_indicator (k : ℕ) :
    (∑ L : Incidence.TriangleIndex G, ∑ M : Incidence.TriangleIndex G,
      if Disjoint L.val M.val then (if triangleCrossEdges G L M = k then 1 else 0) else 0) =
      2 * crossingPairCount G k := by
  have hh := weighted_ordered_eq_twice_unordered G (fun m => if m = k then 1 else 0)
  have he : (∑ p ∈ orderedDisjointTrianglePairs G,
      if triangleCrossEdges G p.1 p.2 = k then 1 else 0) =
      ∑ L : Incidence.TriangleIndex G, ∑ M : Incidence.TriangleIndex G,
        if Disjoint L.val M.val then (if triangleCrossEdges G L M = k then 1 else 0) else 0 := by
    rw [orderedDisjointTrianglePairs, Finset.sum_filter,
      ← Finset.univ_product_univ, Finset.sum_product]
  rw [he] at hh
  simpa [crossingPairCount] using hh

/-- The defect parameter is an integer, not a truncated natural subtraction. -/
def triangleDelta : ℤ := (crossingPairCount G 2 : ℤ) - 693

theorem triangleDelta_eq_third_count (h : G.IsSRGWith 99 14 1 2) :
    triangleDelta G = 3465 - 3 * (crossingPairCount G 3 : ℤ) := by
  have hh : (crossingPairCount G 2 : ℤ) + 3 * (crossingPairCount G 3 : ℤ) = 4158 := by
    exact_mod_cast crossing_pair_second_factorial G h
  dsimp [triangleDelta]
  omega

theorem triangleDelta_divisible_three (h : G.IsSRGWith 99 14 1 2) :
    3 ∣ triangleDelta G := by
  refine ⟨1155 - (crossingPairCount G 3 : ℤ), ?_⟩
  rw [triangleDelta_eq_third_count G h]
  ring

/-- Cubic interpolation uses only m ≤ 3: (1−m)³ = 1−m²+2·1_{m=2}. -/
theorem integerGram_row_cube (h : G.IsSRGWith 99 14 1 2)
    (L : Incidence.TriangleIndex G) :
    (∑ M : Incidence.TriangleIndex G, integerTriangleGram G L M ^ 3) =
      -12 + 2 * (∑ M : Incidence.TriangleIndex G,
        if Disjoint L.val M.val then (if triangleCrossEdges G L M = 2 then (1 : ℤ) else 0)
        else 0) := by
  have h0 : (∑ M : Incidence.TriangleIndex G,
      if Disjoint L.val M.val then (1 : ℤ) else 0) = 212 := by
    exact_mod_cast disjoint_triangle_indicator_sum G h L
  have h2 : (∑ M : Incidence.TriangleIndex G,
      if Disjoint L.val M.val then (triangleCrossEdges G L M : ℤ) ^ 2 else 0) = 288 := by
    exact_mod_cast disjoint_crossing_square_row G h L
  have he : ∀ M : Incidence.TriangleIndex G, integerTriangleGram G L M ^ 3 =
      (if Disjoint L.val M.val then (1 : ℤ) else 0) -
      (if Disjoint L.val M.val then (triangleCrossEdges G L M : ℤ) ^ 2 else 0) +
      2 * (if Disjoint L.val M.val then
        (if triangleCrossEdges G L M = 2 then (1 : ℤ) else 0) else 0) +
      64 * (if M = L then 1 else 0) := by
    intro M
    by_cases hML : M = L
    · subst M
      have hnd : ¬Disjoint L.val L.val := by
        obtain ⟨u, hu⟩ := Finset.card_pos.mp (by rw [triangle_card G L]; norm_num)
        intro hd
        exact Finset.disjoint_left.mp hd hu hu
      simp only [hnd, if_false, if_true, integerTriangleGram_diag G L]
      norm_num
    · by_cases hd : Disjoint L.val M.val
      · simp only [hd, if_true, hML, if_false, integerGram_disjoint G L M hd,
          mul_zero, add_zero]
        have hb := disjoint_crossing_edges_le_three G h L M hd
        interval_cases hm : triangleCrossEdges G L M <;> norm_num
      · simp only [hd, if_false, hML, integerGram_meeting G h L M (Ne.symm hML) hd,
          zero_pow (by decide : 3 ≠ 0), mul_zero, add_zero, sub_zero]
  have hh := congrArg (fun f : Incidence.TriangleIndex G → ℤ => ∑ M, f M) (funext he)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hh
  rw [h0, h2] at hh
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hh
  omega

/-- The full cubic Gram sum is precisely four times the combinatorial defect. -/
theorem integerGram_cube_total (h : G.IsSRGWith 99 14 1 2) :
    (∑ L : Incidence.TriangleIndex G, ∑ M : Incidence.TriangleIndex G,
      integerTriangleGram G L M ^ 3) = 4 * triangleDelta G := by
  have hi : (∑ L : Incidence.TriangleIndex G, ∑ M : Incidence.TriangleIndex G,
      if Disjoint L.val M.val then
        (if triangleCrossEdges G L M = 2 then (1 : ℤ) else 0) else 0) =
      2 * (crossingPairCount G 2 : ℤ) := by
    exact_mod_cast ordered_crossing_indicator G 2
  simp_rw [integerGram_row_cube G h]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hi]
  have hc : Fintype.card (Incidence.TriangleIndex G) = 231 := by
    change Fintype.card ↥(G.cliqueFinset 3) = 231
    rw [Fintype.card_coe, triangle_count_231 G h]
  simp only [Finset.sum_const, Finset.card_univ, hc, smul_eq_mul]
  dsimp [triangleDelta]
  ring

#print axioms integerGram_row_square
#print axioms disjoint_shifted_square_row
#print axioms disjoint_crossing_square_row
#print axioms ordered_crossing_square_moment
#print axioms unordered_crossing_square_moment
#print axioms unordered_crossing_edges_le_three
#print axioms crossing_pair_second_factorial
#print axioms ordered_crossing_indicator
#print axioms triangleDelta_eq_third_count
#print axioms triangleDelta_divisible_three
#print axioms integerGram_row_cube
#print axioms integerGram_cube_total

end Conway99.TriangleSecondMoments
