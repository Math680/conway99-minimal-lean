import TriangleCount
import Incidence
import Triangles

/-! Counts of intersecting and disjoint pairs of actual 3-cliques.
No numerical hypothesis about triangles is substituted for strong regularity.
-/

namespace Conway99.TrianglePairs

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Distinct triangles in a Conway graph meet in at most one vertex. -/
theorem distinct_triangle_intersection_le_one (h : G.IsSRGWith 99 14 1 2)
    {s t : Finset V} (hs : G.IsNClique 3 s) (ht : G.IsNClique 3 t)
    (hne : s ≠ t) : (s ∩ t).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  by_contra hab
  obtain ⟨has, hat⟩ := Finset.mem_inter.mp ha
  obtain ⟨hbs, hbt⟩ := Finset.mem_inter.mp hb
  obtain ⟨c, hac, hbc, hsc⟩ := triangle_third_vertex G hs has hbs hab
  obtain ⟨d, had, hbd, htd⟩ := triangle_third_vertex G ht hat hbt hab
  have hcd := edge_common_neighbor_eq G h (hs.isClique has hbs hab) hac hbc had hbd
  apply hne
  rw [hsc, htd, hcd]

def meetingTriangles (s : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter fun t => ¬Disjoint s t

def disjointTriangles (s : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter fun t => Disjoint s t

private theorem self_mem_meeting {s : Finset V} (hs : G.IsNClique 3 s) :
    s ∈ meetingTriangles G s := by
  refine Finset.mem_filter.mpr ⟨G.mem_cliqueFinset_iff.mpr hs, ?_⟩
  intro hd
  have hn : s.Nonempty := Finset.card_pos.mp (by rw [hs.card_eq]; norm_num)
  obtain ⟨u, hu⟩ := hn
  exact Finset.disjoint_left.mp hd hu hu

/-- There are eighteen other triangles meeting a fixed triangle. -/
theorem other_meeting_triangle_count (h : G.IsSRGWith 99 14 1 2)
    {s : Finset V} (hs : G.IsNClique 3 s) :
    ((meetingTriangles G s).erase s).card = 18 := by
  have hm : ∀ u ∈ s,
      (((meetingTriangles G s).erase s).bipartiteAbove
        (fun u (t : Finset V) => u ∈ t) u).card = 6 := by
    intro u hu
    have he : ((meetingTriangles G s).erase s).bipartiteAbove
        (fun u (t : Finset V) => u ∈ t) u =
        (Incidence.trianglesAt G u).erase s := by
      ext t
      simp only [Finset.mem_bipartiteAbove, Finset.mem_erase, meetingTriangles,
        Incidence.trianglesAt, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hne, htc, _⟩, hut⟩
        exact ⟨hne, htc, hut⟩
      · rintro ⟨hne, htc, hut⟩
        refine ⟨⟨hne, htc, ?_⟩, hut⟩
        intro hd
        exact (Finset.disjoint_left.mp hd hu hut)
    have hsm : s ∈ Incidence.trianglesAt G u :=
      Finset.mem_filter.mpr ⟨G.mem_cliqueFinset_iff.mpr hs, hu⟩
    rw [he, Finset.card_erase_of_mem hsm, Incidence.vertex_triangle_count G h u]
  have hn : ∀ t ∈ (meetingTriangles G s).erase s,
      (s.bipartiteBelow (fun u (t : Finset V) => u ∈ t) t).card = 1 := by
    intro t ht
    obtain ⟨hne, htm⟩ := Finset.mem_erase.mp ht
    obtain ⟨htc, hmeet⟩ := Finset.mem_filter.mp htm
    have he : s.bipartiteBelow (fun u (t : Finset V) => u ∈ t) t = s ∩ t := by
      ext u
      simp
    rw [he]
    have hle := distinct_triangle_intersection_le_one G h hs
      (G.mem_cliqueFinset_iff.mp htc) hne.symm
    have hpos : 0 < (s ∩ t).card := by
      apply Finset.card_pos.mpr
      simpa only [Finset.not_disjoint_iff_nonempty_inter] using hmeet
    omega
  have hd := Finset.card_mul_eq_card_mul (fun u (t : Finset V) => u ∈ t) hm hn
  rw [hs.card_eq] at hd
  omega

/-- Exactly nineteen triangles meet a triangle, including itself. -/
theorem meeting_triangle_count_19 (h : G.IsSRGWith 99 14 1 2)
    {s : Finset V} (hs : G.IsNClique 3 s) : (meetingTriangles G s).card = 19 := by
  have hh := other_meeting_triangle_count G h hs
  rw [Finset.card_erase_of_mem (self_mem_meeting G hs)] at hh
  have hpos := Finset.card_pos.mpr (show (meetingTriangles G s).Nonempty from
    ⟨s, self_mem_meeting G hs⟩)
  omega

/-- Exactly 212 actual triangles are disjoint from a fixed triangle. -/
theorem disjoint_triangle_count_212 (h : G.IsSRGWith 99 14 1 2)
    {s : Finset V} (hs : G.IsNClique 3 s) : (disjointTriangles G s).card = 212 := by
  have hd := (G.cliqueFinset 3).filter_card_add_filter_neg_card_eq_card
    (fun t => Disjoint s t)
  change (disjointTriangles G s).card + (meetingTriangles G s).card =
    (G.cliqueFinset 3).card at hd
  rw [meeting_triangle_count_19 G h hs, triangle_count_231 G h] at hd
  omega

/-- Vertices are actual triangles; adjacency means disjointness of their
underlying vertex sets. Hence its edges are unordered disjoint triangle pairs. -/
def disjointTriangleGraph : SimpleGraph (Incidence.TriangleIndex G) where
  Adj s t := Disjoint s.val t.val
  symm _ _ hd := hd.symm
  loopless s hd := by
    have hs := G.mem_cliqueFinset_iff.mp s.property
    have hn : s.val.Nonempty := Finset.card_pos.mp (by rw [hs.card_eq]; norm_num)
    obtain ⟨u, hu⟩ := hn
    exact Finset.disjoint_left.mp hd hu hu

instance disjointTriangleGraph_decidableAdj : DecidableRel (disjointTriangleGraph G).Adj := by
  intro s t
  change Decidable (Disjoint s.val t.val)
  infer_instance

/-- The disjointness graph on actual triangles is 212-regular. -/
theorem disjointTriangleGraph_regular (h : G.IsSRGWith 99 14 1 2) :
    (disjointTriangleGraph G).IsRegularOfDegree 212 := by
  intro s
  let e : (disjointTriangleGraph G).neighborSet s ≃
      ↥(disjointTriangles G s.val) :=
    { toFun := fun t => ⟨t.val.val, Finset.mem_filter.mpr ⟨t.val.property, t.property⟩⟩
      invFun := fun t =>
        ⟨⟨t.val, (Finset.mem_filter.mp t.property).1⟩,
          (Finset.mem_filter.mp t.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_congr e, Fintype.card_coe]
  exact disjoint_triangle_count_212 G h (G.mem_cliqueFinset_iff.mp s.property)

/-- Actual ordered triangle pairs, not just twice an assumed unordered count. -/
def orderedDisjointTrianglePairs :
    Finset (Incidence.TriangleIndex G × Incidence.TriangleIndex G) :=
  Finset.univ.filter fun p => Disjoint p.1.val p.2.val

def unorderedDisjointTrianglePairs : Finset (Sym2 (Incidence.TriangleIndex G)) :=
  (disjointTriangleGraph G).edgeFinset

theorem unordered_disjoint_triangle_pair_count (h : G.IsSRGWith 99 14 1 2) :
    (unorderedDisjointTrianglePairs G).card = 24486 := by
  have hd := (disjointTriangleGraph G).sum_degrees_eq_twice_card_edges
  have hr := disjointTriangleGraph_regular G h
  simp only [hr.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hd
  have hc : Fintype.card (Incidence.TriangleIndex G) = 231 := by
    change Fintype.card ↥(G.cliqueFinset 3) = 231
    rw [Fintype.card_coe, triangle_count_231 G h]
  rw [hc] at hd
  change (disjointTriangleGraph G).edgeFinset.card = 24486
  omega

theorem ordered_disjoint_triangle_pair_count (h : G.IsSRGWith 99 14 1 2) :
    (orderedDisjointTrianglePairs G).card = 48972 := by
  have hd := (disjointTriangleGraph G).two_mul_card_edgeFinset
  have hc := unordered_disjoint_triangle_pair_count G h
  change (disjointTriangleGraph G).edgeFinset.card = 24486 at hc
  rw [hc] at hd
  have he : (Finset.univ.filter fun p : Incidence.TriangleIndex G ×
      Incidence.TriangleIndex G => (disjointTriangleGraph G).Adj p.1 p.2) =
      orderedDisjointTrianglePairs G := rfl
  rw [he] at hd
  omega

#print axioms distinct_triangle_intersection_le_one
#print axioms other_meeting_triangle_count
#print axioms meeting_triangle_count_19
#print axioms disjoint_triangle_count_212
#print axioms disjointTriangleGraph_regular
#print axioms unordered_disjoint_triangle_pair_count
#print axioms ordered_disjoint_triangle_pair_count

end Conway99.TrianglePairs
