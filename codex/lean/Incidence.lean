import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic

/-! Exact incidence of vertices and actual 3-cliques. This source is autonomous. -/

namespace Conway99.Incidence

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def trianglesAt (u : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter fun s => u ∈ s

def trianglesThrough (u v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter fun s => u ∈ s ∧ v ∈ s

private theorem third_vertex {s : Finset V} (hs : G.IsNClique 3 s)
    {a b : V} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    ∃ c, G.Adj a c ∧ G.Adj b c ∧ s = {a, b, c} := by
  have hbe : b ∈ s.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have hc : ((s.erase a).erase b).card = 1 := by
    rw [Finset.card_erase_of_mem hbe, Finset.card_erase_of_mem ha, hs.card_eq]
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hc
  have hcm : c ∈ (s.erase a).erase b := by rw [hc]; simp
  have hcb : c ≠ b := (Finset.mem_erase.mp hcm).1
  have hca : c ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hcm).2).1
  have hcs : c ∈ s := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hcm)
  refine ⟨c, hs.isClique ha hcs hca.symm, hs.isClique hb hcs hcb.symm, ?_⟩
  ext v
  constructor
  · intro hv
    by_cases hva : v = a
    · simp [hva]
    by_cases hvb : v = b
    · simp [hvb]
    have hvr : v ∈ (s.erase a).erase b := by simp [hv, hva, hvb]
    rw [hc] at hvr
    have hvc : v = c := Finset.mem_singleton.mp hvr
    simp [hvc]
  · intro hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hcs

/-- Each adjacent pair occurs in exactly one ordinary 3-clique. -/
theorem adjacent_pair_triangle_count (h : G.IsSRGWith 99 14 1 2)
    {u v : V} (huv : G.Adj u v) : (trianglesThrough G u v).card = 1 := by
  obtain ⟨c, hc⟩ := Fintype.card_eq_one_iff.mp (h.of_adj u v huv)
  have hct : G.IsNClique 3 {u, v, c.val} :=
    G.is3Clique_triple_iff.mpr ⟨huv, c.property.1, c.property.2⟩
  apply Finset.card_eq_one.mpr
  refine ⟨{u, v, c.val}, ?_⟩
  ext s
  simp only [trianglesThrough, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hs, hus, hvs⟩
    obtain ⟨d, hud, hvd, hsd⟩ := third_vertex G hs hus hvs huv.ne
    have hdc : d = c.val := congrArg Subtype.val (hc ⟨d, ⟨hud, hvd⟩⟩)
    rw [hsd, hdc]
  · rintro rfl
    exact ⟨hct, by simp, by simp⟩

/-- Distinct nonadjacent vertices do not occur together in a triangle. -/
theorem nonadjacent_pair_triangle_count {u v : V} (hne : u ≠ v)
    (huv : ¬G.Adj u v) : (trianglesThrough G u v).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  obtain ⟨hsc, hus, hvs⟩ := Finset.mem_filter.mp hs
  exact huv ((G.mem_cliqueFinset_iff.mp hsc).isClique hus hvs hne)

/-- Exact joint incidence for distinct vertices. -/
theorem distinct_pair_triangle_count (h : G.IsSRGWith 99 14 1 2)
    {u v : V} (hne : u ≠ v) :
    (trianglesThrough G u v).card = if G.Adj u v then 1 else 0 := by
  by_cases huv : G.Adj u v
  · simp only [huv, if_true]
    exact adjacent_pair_triangle_count G h huv
  · simp only [huv, if_false]
    exact nonadjacent_pair_triangle_count G hne huv

/-- Every vertex lies in exactly seven triangles. -/
theorem vertex_triangle_count (h : G.IsSRGWith 99 14 1 2) (u : V) :
    (trianglesAt G u).card = 7 := by
  have hm : ∀ v ∈ G.neighborFinset u,
      ((trianglesAt G u).bipartiteAbove (fun v s => v ∈ s) v).card = 1 := by
    intro v hv
    have he : (trianglesAt G u).bipartiteAbove (fun v s => v ∈ s) v =
        trianglesThrough G u v := by
      ext s
      simp [trianglesAt, trianglesThrough, Finset.bipartiteAbove, and_assoc]
    rw [he]
    exact adjacent_pair_triangle_count G h (G.mem_neighborFinset u v |>.mp hv)
  have hn : ∀ s ∈ trianglesAt G u,
      ((G.neighborFinset u).bipartiteBelow (fun v s => v ∈ s) s).card = 2 := by
    intro s hs
    obtain ⟨hsc, hus⟩ := Finset.mem_filter.mp hs
    have hcl := G.mem_cliqueFinset_iff.mp hsc
    have he : (G.neighborFinset u).bipartiteBelow (fun v s => v ∈ s) s =
        s.erase u := by
      ext v
      simp only [Finset.mem_bipartiteBelow, SimpleGraph.mem_neighborFinset,
        Finset.mem_erase]
      constructor
      · rintro ⟨huv, hvs⟩
        exact ⟨huv.ne.symm, hvs⟩
      · rintro ⟨hne, hvs⟩
        exact ⟨hcl.isClique hus hvs hne.symm, hvs⟩
    rw [he, Finset.card_erase_of_mem hus, hcl.card_eq]
  have hd := Finset.card_mul_eq_card_mul (fun v (s : Finset V) => v ∈ s) hm hn
  rw [SimpleGraph.card_neighborFinset_eq_degree, h.regular.degree_eq] at hd
  omega

/-- Columns are indexed by actual 3-cliques, not arbitrary subsets. -/
abbrev TriangleIndex := ↥(G.cliqueFinset 3)

def vertexTriangleIncidence : Matrix V (TriangleIndex G) ℚ :=
  fun u t => if u ∈ t.val then 1 else 0

/-- An entry of BBᵀ counts triangles containing its two row vertices. -/
theorem incidence_product_entry (u v : V) :
    (vertexTriangleIncidence G * (vertexTriangleIncidence G).transpose) u v =
      ((trianglesThrough G u v).card : ℚ) := by
  have hp (s : Finset V) :
      (if u ∈ s then (1 : ℚ) else 0) * (if v ∈ s then 1 else 0) =
        if u ∈ s ∧ v ∈ s then 1 else 0 := by
    by_cases hu : u ∈ s <;> by_cases hv : v ∈ s <;> simp [hu, hv]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, vertexTriangleIncidence, hp]
  rw [Finset.sum_coe_sort (G.cliqueFinset 3)
    (fun s : Finset V => if u ∈ s ∧ v ∈ s then (1 : ℚ) else 0)]
  rw [← Finset.sum_filter]
  simp [trianglesThrough]

/-- The incidence identity BBᵀ = 7I + A over the rationals. -/
theorem incidence_product (h : G.IsSRGWith 99 14 1 2) :
    vertexTriangleIncidence G * (vertexTriangleIncidence G).transpose =
      (7 : ℕ) • (1 : Matrix V V ℚ) + G.adjMatrix ℚ := by
  ext u v
  rw [incidence_product_entry]
  simp only [Matrix.add_apply, nsmul_eq_mul]
  by_cases huv : u = v
  · subst v
    have hh : trianglesThrough G u u = trianglesAt G u := by
      simp [trianglesThrough, trianglesAt]
    rw [hh, vertex_triangle_count G h u]
    norm_num [Matrix.one_apply, Matrix.ofNat_apply, SimpleGraph.adjMatrix_apply]
  · rw [distinct_pair_triangle_count G h huv]
    by_cases ha : G.Adj u v <;>
      norm_num [Matrix.one_apply, Matrix.ofNat_apply, SimpleGraph.adjMatrix_apply, huv, ha]

#print axioms adjacent_pair_triangle_count
#print axioms nonadjacent_pair_triangle_count
#print axioms distinct_pair_triangle_count
#print axioms vertex_triangle_count
#print axioms incidence_product_entry
#print axioms incidence_product

end Conway99.Incidence
