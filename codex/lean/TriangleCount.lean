import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

/-! The actual `cliqueFinset 3` of a hypothetical Conway graph has 231 elements.
This file is self-contained, so its verification does not require an olean
compiled from a sibling file. No use is made of `SimpleGraph.conway_99`.
-/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A triangle containing two distinct named vertices has a third vertex. -/
theorem triangle_third_vertex {s : Finset V} (hs : G.IsNClique 3 s)
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

/-- Strong regularity with adjacent common-neighbor count one implies
    that each edge lies in exactly one triangle (`LocallyLinear`). -/
theorem srg_locally_linear (h : G.IsSRGWith 99 14 1 2) : G.LocallyLinear := by
  have hu : ∀ {a b c d : V}, G.Adj a b →
      G.Adj a c → G.Adj b c → G.Adj a d → G.Adj b d → c = d := by
    intro a b c d hab hac hbc had hbd
    obtain ⟨w, hw⟩ := Fintype.card_eq_one_iff.mp (h.of_adj a b hab)
    exact congrArg Subtype.val ((hw ⟨c, ⟨hac, hbc⟩⟩).trans
      (hw ⟨d, ⟨had, hbd⟩⟩).symm)
  constructor
  · rw [SimpleGraph.edgeDisjointTriangles_iff_mem_sym2_subsingleton]
    intro e he
    obtain ⟨a, b⟩ := e
    have hab : a ≠ b := by simpa only [Sym2.mk_isDiag_iff] using he
    intro s hs t ht
    have hsa : a ∈ s := (Finset.mem_sym2_iff.mp hs.2) a (by simp)
    have hsb : b ∈ s := (Finset.mem_sym2_iff.mp hs.2) b (by simp)
    have hta : a ∈ t := (Finset.mem_sym2_iff.mp ht.2) a (by simp)
    have htb : b ∈ t := (Finset.mem_sym2_iff.mp ht.2) b (by simp)
    have hsc : G.IsNClique 3 s := hs.1
    have htc : G.IsNClique 3 t := ht.1
    obtain ⟨c, hac, hbc, hsc⟩ := triangle_third_vertex G hsc hsa hsb hab
    obtain ⟨d, had, hbd, htc⟩ := triangle_third_vertex G htc hta htb hab
    have hab' : G.Adj a b := (show G.IsNClique 3 s from hs.1).isClique hsa hsb hab
    have hcd := hu hab' hac hbc had hbd
    rw [hsc, htc, hcd]
  · intro a b hab
    obtain ⟨c, _⟩ := Fintype.card_eq_one_iff.mp (h.of_adj a b hab)
    refine ⟨{a, b, c.val}, ?_, by simp, by simp⟩
    exact G.is3Clique_triple_iff.mpr ⟨hab, c.property.1, c.property.2⟩

/-- Double counting edge-triangle incidences gives the exact equality. -/
theorem triangle_edge_count_identity (h : G.IsSRGWith 99 14 1 2) :
    G.edgeFinset.card = 3 * (G.cliqueFinset 3).card :=
  (srg_locally_linear G h).card_edgeFinset

/-- The triangle count is 231, for the ordinary mathlib finset of 3-cliques. -/
theorem triangle_count_231 (h : G.IsSRGWith 99 14 1 2) :
    (G.cliqueFinset 3).card = 231 := by
  have hs := G.sum_degrees_eq_twice_card_edges
  simp only [h.regular.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hs
  rw [h.card, triangle_edge_count_identity G h] at hs
  omega

#print axioms triangle_third_vertex
#print axioms srg_locally_linear
#print axioms triangle_edge_count_identity
#print axioms triangle_count_231

end Conway99
