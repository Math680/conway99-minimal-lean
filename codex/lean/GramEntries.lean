import Gram
import TriangleCount

/-! Finite entry counts for the Gram matrix of actual triangles. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Number of oriented adjacencies from triangle `L` to triangle `M`. -/
def triangleCrossEdges (L M : Incidence.TriangleIndex G) : ℕ :=
  ((L.val.product M.val).filter fun p => G.Adj p.1 p.2).card

theorem triangle_card (L : Incidence.TriangleIndex G) : L.val.card = 3 :=
  (G.mem_cliqueFinset_iff.mp L.property).card_eq

theorem triangle_diagonal_sum (L M : Incidence.TriangleIndex G) :
    (∑ u ∈ L.val, ∑ v ∈ M.val, if u = v then (1 : ℚ) else 0) =
      ((L.val ∩ M.val).card : ℚ) := by
  simp

theorem triangle_adjacency_sum (L M : Incidence.TriangleIndex G) :
    (∑ u ∈ L.val, ∑ v ∈ M.val, if G.Adj u v then (1 : ℚ) else 0) =
      (triangleCrossEdges G L M : ℚ) := by
  rw [← Finset.sum_product L.val M.val
    (fun p : V × V => if G.Adj p.1 p.2 then (1 : ℚ) else 0)]
  simp [triangleCrossEdges, ← Finset.sum_filter]

theorem vertexGram_entry_linear (u v : V) :
    vertexGram G u v = 27 * (if u = v then (1 : ℚ) else 0) -
      9 * (if G.Adj u v then 1 else 0) + 1 := by
  rw [vertexGram_apply]
  by_cases huv : u = v
  · subst v
    norm_num
  · by_cases ha : G.Adj u v <;> norm_num [huv, ha]

theorem triangle_vertexGram_sum (L M : Incidence.TriangleIndex G) :
    (∑ u ∈ L.val, ∑ v ∈ M.val, vertexGram G u v) =
      27 * ((L.val ∩ M.val).card : ℚ) - 9 * (triangleCrossEdges G L M : ℚ) + 9 := by
  simp_rw [vertexGram_entry_linear]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [triangle_diagonal_sum, triangle_adjacency_sum]
  norm_num [triangle_card G L, triangle_card G M]

theorem triangle_internal_edges (L : Incidence.TriangleIndex G) :
    triangleCrossEdges G L L = 6 := by
  have hh : (∑ u ∈ L.val, ∑ v ∈ L.val, if G.Adj u v then (1 : ℚ) else 0) =
      ∑ u ∈ L.val, ∑ v ∈ L.val, (1 - if u = v then (1 : ℚ) else 0) := by
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    by_cases huv : u = v
    · subst v
      simp
    · have ha := (G.mem_cliqueFinset_iff.mp L.property).isClique hu hv huv
      simp [huv, ha]
  have he : (triangleCrossEdges G L L : ℚ) = 6 := by
    rw [← triangle_adjacency_sum, hh]
    simp only [Finset.sum_sub_distrib]
    rw [triangle_diagonal_sum]
    norm_num [triangle_card G L]
  exact_mod_cast he

/-- The matrix definition reduces to a finite sum over the two triangles. -/
theorem triangleGram_sum_entry (L M : Incidence.TriangleIndex G) :
    triangleGram G L M =
      (1 / 9 : ℚ) * (∑ u ∈ L.val, ∑ v ∈ M.val, vertexGram G u v) := by
  simp only [triangleGram, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.transpose_apply, Incidence.vertexTriangleIncidence,
    ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero, Fintype.sum_ite_mem]
  rw [Finset.sum_comm]

/-- Entry formula, including overlapping triangles and the diagonal. -/
theorem triangleGram_entry (L M : Incidence.TriangleIndex G) :
    triangleGram G L M = 3 * ((L.val ∩ M.val).card : ℚ) -
      (triangleCrossEdges G L M : ℚ) + 1 := by
  rw [triangleGram_sum_entry, triangle_vertexGram_sum]
  ring

/-- An explicitly defined integral matrix with exactly this rational Gram. -/
def integerTriangleGram : Matrix (Incidence.TriangleIndex G) (Incidence.TriangleIndex G) ℤ :=
  fun L M => 3 * ((L.val ∩ M.val).card : ℤ) - (triangleCrossEdges G L M : ℤ) + 1

theorem integerTriangleGram_cast (L M : Incidence.TriangleIndex G) :
    (integerTriangleGram G L M : ℚ) = triangleGram G L M := by
  rw [triangleGram_entry]
  simp [integerTriangleGram]

theorem integerTriangleGram_map :
    (integerTriangleGram G).map (Int.castRingHom ℚ) = triangleGram G := by
  ext L M
  exact integerTriangleGram_cast G L M

/-- Every triangle vector has squared norm four. -/
theorem triangleGram_diag (L : Incidence.TriangleIndex G) : triangleGram G L L = 4 := by
  rw [triangleGram_entry, triangle_internal_edges]
  norm_num [triangle_card G L]

theorem integerTriangleGram_diag (L : Incidence.TriangleIndex G) :
    integerTriangleGram G L L = 4 := by
  norm_num [integerTriangleGram, triangle_internal_edges, triangle_card G L]

/-- For disjoint triangles the entry is one minus the number of crossing edges. -/
theorem triangleGram_disjoint (L M : Incidence.TriangleIndex G)
    (hdis : Disjoint L.val M.val) :
    triangleGram G L M = 1 - (triangleCrossEdges G L M : ℚ) := by
  rw [triangleGram_entry, Finset.disjoint_iff_inter_eq_empty.mp hdis]
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero, zero_sub]
  ring

/-- In the strongly regular graph, two distinct triangles meet in at most one vertex. -/
theorem distinct_triangles_inter_card (h : G.IsSRGWith 99 14 1 2)
    {L M : Incidence.TriangleIndex G} (hne : L ≠ M) :
    (L.val ∩ M.val).card ≤ 1 := by
  have hval : L.val ≠ M.val := fun he => hne (Subtype.ext he)
  have hsub := (srg_locally_linear G h).1
    (show L.val ∈ G.cliqueSet 3 from G.mem_cliqueFinset_iff.mp L.property)
    (show M.val ∈ G.cliqueSet 3 from G.mem_cliqueFinset_iff.mp M.property) hval
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact hsub (Finset.mem_inter.mp ha) (Finset.mem_inter.mp hb)

#print axioms triangle_diagonal_sum
#print axioms triangle_adjacency_sum
#print axioms triangle_vertexGram_sum
#print axioms triangle_internal_edges
#print axioms triangleGram_sum_entry
#print axioms triangleGram_entry
#print axioms integerTriangleGram_map
#print axioms triangleGram_diag
#print axioms integerTriangleGram_diag
#print axioms triangleGram_disjoint
#print axioms distinct_triangles_inter_card

end Conway99
