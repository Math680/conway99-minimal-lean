import TrianglePairs
import GramEntries

/-! First moments of crossing edges between actual triangles. -/

namespace Conway99.TriangleMoments

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A point outside any actual triangle has at most one neighbor on it. -/
theorem exterior_triangle_neighbors_le_one (h : G.IsSRGWith 99 14 1 2)
    {s : Finset V} (hs : G.IsNClique 3 s) {u : V} (hu : u ∉ s) :
    (s.filter fun v => G.Adj u v).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  obtain ⟨has, hua⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbs, hub⟩ := Finset.mem_filter.mp hb
  by_contra hab
  obtain ⟨c, hac, hbc, hsc⟩ := triangle_third_vertex G hs has hbs hab
  have huc : u = c := edge_common_neighbor_eq G h
    (hs.isClique has hbs hab) hua.symm hub.symm hac hbc
  apply hu
  rw [huc, hsc]
  simp

/-- Crossing edges are the sum of their row counts. -/
theorem crossing_edges_row_sum (L M : Incidence.TriangleIndex G) :
    triangleCrossEdges G L M =
      ∑ u ∈ L.val, (M.val.filter fun v => G.Adj u v).card := by
  have he : (triangleCrossEdges G L M : ℚ) =
      ∑ u ∈ L.val, ((M.val.filter fun v => G.Adj u v).card : ℚ) := by
    rw [← triangle_adjacency_sum]
    apply Finset.sum_congr rfl
    intro u hu
    simp
  exact_mod_cast he

/-- For disjoint triangles the crossing edges form a matching, so m ≤ 3. -/
theorem disjoint_crossing_edges_le_three (h : G.IsSRGWith 99 14 1 2)
    (L M : Incidence.TriangleIndex G) (hd : Disjoint L.val M.val) :
    triangleCrossEdges G L M ≤ 3 := by
  rw [crossing_edges_row_sum]
  calc
    _ ≤ ∑ _u ∈ L.val, 1 := by
      apply Finset.sum_le_sum
      intro u hu
      exact exterior_triangle_neighbors_le_one G h
        (G.mem_cliqueFinset_iff.mp M.property) (fun hm => Finset.disjoint_left.mp hd hu hm)
    _ = 3 := by simp [triangle_card G L]

/-- Crossing-edge cardinality is symmetric in the two triangles. -/
theorem crossing_edges_symmetric (L M : Incidence.TriangleIndex G) :
    triangleCrossEdges G L M = triangleCrossEdges G M L := by
  have he : (triangleCrossEdges G L M : ℚ) = (triangleCrossEdges G M L : ℚ) := by
    rw [← triangle_adjacency_sum, ← triangle_adjacency_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro u hu
    simp [G.adj_comm u v]
  exact_mod_cast he

/-- The edge weight is well-defined on unordered pairs of triangles. -/
def unorderedCrossingEdges : Sym2 (Incidence.TriangleIndex G) → ℕ :=
  Sym2.lift ⟨triangleCrossEdges G, crossing_edges_symmetric G⟩

@[simp] theorem unorderedCrossingEdges_mk (L M : Incidence.TriangleIndex G) :
    unorderedCrossingEdges G s(L, M) = triangleCrossEdges G L M := by
  simp [unorderedCrossingEdges]

/-- A vertex of a triangle has exactly two neighbors on that triangle. -/
theorem internal_triangle_neighbor_count {s : Finset V} (hs : G.IsNClique 3 s)
    {u : V} (hu : u ∈ s) : (s.filter fun v => G.Adj u v).card = 2 := by
  have he : s.filter (fun v => G.Adj u v) = s.erase u := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hv, huv⟩
      exact ⟨huv.ne.symm, hv⟩
    · rintro ⟨hne, hv⟩
      exact ⟨hv, hs.isClique hu hv hne.symm⟩
  rw [he, Finset.card_erase_of_mem hu, hs.card_eq]

/-- Between distinct intersecting triangles exactly four oriented
adjacencies occur. Their sole common vertex accounts for all four. -/
theorem meeting_crossing_edges_four (h : G.IsSRGWith 99 14 1 2)
    (L M : Incidence.TriangleIndex G) (hne : L ≠ M)
    (hm : ¬Disjoint L.val M.val) : triangleCrossEdges G L M = 4 := by
  obtain ⟨a, haL, haM⟩ := Finset.not_disjoint_iff.mp hm
  have hsL := G.mem_cliqueFinset_iff.mp L.property
  have hsM := G.mem_cliqueFinset_iff.mp M.property
  have hrows : ∀ u ∈ L.val,
      (M.val.filter fun v => G.Adj u v).card = if u ∈ M.val then 2 else 1 := by
    intro u hu
    by_cases huM : u ∈ M.val
    · rw [if_pos huM]
      exact internal_triangle_neighbor_count G hsM huM
    · rw [if_neg huM]
      have hle := exterior_triangle_neighbors_le_one G h hsM huM
      have hneua : u ≠ a := fun he => huM (he ▸ haM)
      have hpos : 0 < (M.val.filter fun v => G.Adj u v).card :=
        Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr
          ⟨haM, hsL.isClique hu haL hneua⟩⟩
      omega
  have hic : (L.val ∩ M.val).card = 1 := by
    have hle := distinct_triangles_inter_card G h hne
    have hpos : 0 < (L.val ∩ M.val).card :=
      Finset.card_pos.mpr ⟨a, Finset.mem_inter.mpr ⟨haL, haM⟩⟩
    omega
  rw [crossing_edges_row_sum]
  trans ∑ u ∈ L.val, (1 + if u ∈ M.val then 1 else 0)
  · apply Finset.sum_congr rfl
    intro u hu
    rw [hrows u hu]
    by_cases hmem : u ∈ M.val <;> simp [hmem]
  · simp only [Finset.sum_add_distrib]
    have he : (∑ u ∈ L.val, if u ∈ M.val then 1 else 0) =
        (L.val ∩ M.val).card := by simp
    rw [he, hic]
    simp [triangle_card G L]

/-- Double counting incidences between the fourteen neighbors of a vertex
and the seven triangles through each neighbor. -/
theorem vertex_neighbor_triangle_sum (h : G.IsSRGWith 99 14 1 2) (u : V) :
    (∑ M : Incidence.TriangleIndex G,
      (M.val.filter fun v => G.Adj u v).card) = 98 := by
  have hd := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := fun (v : V) (s : Finset V) => v ∈ s)
    (s := G.neighborFinset u) (t := G.cliqueFinset 3)
  have hab : ∀ v, (G.cliqueFinset 3).bipartiteAbove
      (fun (v : V) (s : Finset V) => v ∈ s) v = Incidence.trianglesAt G v := by
    intro v
    rfl
  have hbe : ∀ s : Finset V, (G.neighborFinset u).bipartiteBelow
      (fun (v : V) (s : Finset V) => v ∈ s) s = s.filter (fun v => G.Adj u v) := by
    intro s
    ext v
    simp only [Finset.mem_bipartiteBelow, SimpleGraph.mem_neighborFinset, Finset.mem_filter]
    exact and_comm
  simp_rw [hab, Incidence.vertex_triangle_count G h, hbe] at hd
  simp only [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
    h.regular.degree_eq, smul_eq_mul] at hd
  rw [Finset.sum_coe_sort (G.cliqueFinset 3)
    (fun s : Finset V => (s.filter fun v => G.Adj u v).card)]
  omega

/-- The complete row sum over all triangles is 294. -/
theorem crossing_edges_total_row_sum (h : G.IsSRGWith 99 14 1 2)
    (L : Incidence.TriangleIndex G) :
    (∑ M : Incidence.TriangleIndex G, triangleCrossEdges G L M) = 294 := by
  simp_rw [crossing_edges_row_sum]
  rw [Finset.sum_comm]
  simp_rw [vertex_neighbor_triangle_sum G h]
  simp only [Finset.sum_const, smul_eq_mul, triangle_card G L]

/-- An index-level incidence count, expressed with the standard Fintype sum. -/
theorem meeting_triangle_indicator_sum (h : G.IsSRGWith 99 14 1 2)
    (L : Incidence.TriangleIndex G) :
    (∑ M : Incidence.TriangleIndex G, if ¬Disjoint L.val M.val then 1 else 0) = 19 := by
  rw [Finset.sum_coe_sort (G.cliqueFinset 3)
    (fun s : Finset V => if ¬Disjoint L.val s then (1 : ℕ) else 0)]
  rw [← Finset.sum_filter]
  simpa [TrianglePairs.meetingTriangles] using TrianglePairs.meeting_triangle_count_19 G h
    (G.mem_cliqueFinset_iff.mp L.property)

/-- Summing only over disjoint triangles leaves row sum 216. -/
theorem disjoint_crossing_edges_row_sum (h : G.IsSRGWith 99 14 1 2)
    (L : Incidence.TriangleIndex G) :
    (∑ M : Incidence.TriangleIndex G,
      if Disjoint L.val M.val then triangleCrossEdges G L M else 0) = 216 := by
  have hdecomp : ∀ M : Incidence.TriangleIndex G, triangleCrossEdges G L M =
      (if Disjoint L.val M.val then triangleCrossEdges G L M else 0) +
      4 * (if ¬Disjoint L.val M.val then 1 else 0) +
      2 * (if M = L then 1 else 0) := by
    intro M
    by_cases he : M = L
    · subst M
      have hnd : ¬Disjoint L.val L.val := by
        obtain ⟨u, hu⟩ := Finset.card_pos.mp (by rw [triangle_card G L]; norm_num)
        intro hd
        exact Finset.disjoint_left.mp hd hu hu
      simp only [hnd, not_false_eq_true, if_false, if_true, triangle_internal_edges G L]
    · by_cases hd : Disjoint L.val M.val
      · simp [he, hd]
      · simp [he, hd, meeting_crossing_edges_four G h L M (Ne.symm he) hd]
  have hh := congrArg (fun f : Incidence.TriangleIndex G → ℕ => ∑ M, f M)
    (funext hdecomp)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  rw [crossing_edges_total_row_sum G h L, meeting_triangle_indicator_sum G h L] at hh
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hh
  omega

/-- The first crossing-edge moment over actual ordered disjoint pairs. -/
theorem ordered_disjoint_crossing_moment (h : G.IsSRGWith 99 14 1 2) :
    (∑ p ∈ TrianglePairs.orderedDisjointTrianglePairs G,
      triangleCrossEdges G p.1 p.2) = 49896 := by
  have he : (∑ p ∈ TrianglePairs.orderedDisjointTrianglePairs G,
      triangleCrossEdges G p.1 p.2) =
      ∑ L : Incidence.TriangleIndex G, ∑ M : Incidence.TriangleIndex G,
        if Disjoint L.val M.val then triangleCrossEdges G L M else 0 := by
    rw [TrianglePairs.orderedDisjointTrianglePairs, Finset.sum_filter,
      ← Finset.univ_product_univ, Finset.sum_product]
  rw [he]
  simp_rw [disjoint_crossing_edges_row_sum G h]
  have hc : Fintype.card (Incidence.TriangleIndex G) = 231 := by
    change Fintype.card ↥(G.cliqueFinset 3) = 231
    rw [Fintype.card_coe, triangle_count_231 G h]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, hc]

/-- Weighted passage from ordered pairs to unordered pairs. The fibers of
the dart-to-edge map have cardinal two, independently of the edge weight. -/
theorem weighted_ordered_eq_twice_unordered (f : ℕ → ℕ) :
    (∑ p ∈ TrianglePairs.orderedDisjointTrianglePairs G,
      f (triangleCrossEdges G p.1 p.2)) =
      2 * (∑ e ∈ TrianglePairs.unorderedDisjointTrianglePairs G,
        f (unorderedCrossingEdges G e)) := by
  let H := TrianglePairs.disjointTriangleGraph G
  have he : (∑ d : H.Dart, f (unorderedCrossingEdges G d.edge)) =
      ∑ p ∈ TrianglePairs.orderedDisjointTrianglePairs G,
        f (triangleCrossEdges G p.1 p.2) := by
    apply Finset.sum_bij (fun d _ => d.toProd)
    · intro d hd
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, d.adj⟩
    · intro d hd d' hd' he
      exact SimpleGraph.Dart.toProd_injective he
    · intro p hp
      exact ⟨⟨p, (Finset.mem_filter.mp hp).2⟩, Finset.mem_univ _, rfl⟩
    · intro d hd
      rfl
  have hm : ∀ d ∈ (Finset.univ : Finset H.Dart), d.edge ∈ H.edgeFinset := by
    intro d hd
    exact H.mem_edgeFinset.mpr d.edge_mem
  have hf := Finset.sum_fiberwise_of_maps_to'
    (s := Finset.univ) (t := H.edgeFinset) (g := SimpleGraph.Dart.edge)
    hm (fun e => f (unorderedCrossingEdges G e))
  have hinner : ∀ e ∈ H.edgeFinset,
      (∑ d ∈ (Finset.univ : Finset H.Dart).filter (fun d => d.edge = e),
        f (unorderedCrossingEdges G e)) = 2 * f (unorderedCrossingEdges G e) := by
    intro e he
    rw [Finset.sum_const, smul_eq_mul,
      H.dart_edge_fiber_card e (H.mem_edgeFinset.mp he)]
  rw [← he, ← hf]
  change (∑ e ∈ H.edgeFinset,
    ∑ d ∈ (Finset.univ : Finset H.Dart).filter (fun d => d.edge = e),
      f (unorderedCrossingEdges G e)) =
      2 * ∑ e ∈ H.edgeFinset, f (unorderedCrossingEdges G e)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  exact hinner e he

theorem crossing_moment_ordered_eq_twice_unordered :
    (∑ p ∈ TrianglePairs.orderedDisjointTrianglePairs G,
      triangleCrossEdges G p.1 p.2) =
      2 * (∑ e ∈ TrianglePairs.unorderedDisjointTrianglePairs G,
        unorderedCrossingEdges G e) :=
  weighted_ordered_eq_twice_unordered G id

/-- The first crossing-edge moment over actual unordered disjoint pairs. -/
theorem unordered_disjoint_crossing_moment (h : G.IsSRGWith 99 14 1 2) :
    (∑ e ∈ TrianglePairs.unorderedDisjointTrianglePairs G,
      unorderedCrossingEdges G e) = 24948 := by
  have hh := crossing_moment_ordered_eq_twice_unordered G
  rw [ordered_disjoint_crossing_moment G h] at hh
  omega

#print axioms exterior_triangle_neighbors_le_one
#print axioms crossing_edges_row_sum
#print axioms disjoint_crossing_edges_le_three
#print axioms crossing_edges_symmetric
#print axioms meeting_crossing_edges_four
#print axioms vertex_neighbor_triangle_sum
#print axioms crossing_edges_total_row_sum
#print axioms meeting_triangle_indicator_sum
#print axioms disjoint_crossing_edges_row_sum
#print axioms ordered_disjoint_crossing_moment
#print axioms weighted_ordered_eq_twice_unordered
#print axioms crossing_moment_ordered_eq_twice_unordered
#print axioms unordered_disjoint_crossing_moment

end Conway99.TriangleMoments
