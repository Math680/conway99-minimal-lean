import MixedGram
import GramEntries
import Triangles

/-! Exact entries and congruences for the mixed vertex--triangle Gram. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Number of neighbors of `u` lying on the actual triangle `L`. -/
def triangleNeighborCount (u : V) (L : Incidence.TriangleIndex G) : ℕ :=
  (L.val.filter (G.Adj u)).card

theorem triangleNeighborCount_eq (u : V) (L : Incidence.TriangleIndex G) :
    triangleNeighborCount G u L = (G.neighborFinset u ∩ L.val).card := by
  unfold triangleNeighborCount
  congr 1
  ext v
  simp [and_comm]

theorem triangle_neighbor_sum (u : V) (L : Incidence.TriangleIndex G) :
    (∑ v ∈ L.val, if G.Adj u v then (1 : ℚ) else 0) =
      (triangleNeighborCount G u L : ℚ) := by
  simp [triangleNeighborCount]

theorem triangle_neighbor_count_mem {u : V} (L : Incidence.TriangleIndex G)
    (hu : u ∈ L.val) : triangleNeighborCount G u L = 2 := by
  have he : L.val.filter (G.Adj u) = L.val.erase u := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hv, huv⟩
      exact ⟨huv.ne.symm, hv⟩
    · rintro ⟨hne, hv⟩
      exact ⟨hv, (G.mem_cliqueFinset_iff.mp L.property).isClique hu hv hne.symm⟩
  rw [triangleNeighborCount, he, Finset.card_erase_of_mem hu, triangle_card G L]

theorem triangle_neighbor_count_outside (h : G.IsSRGWith 99 14 1 2)
    {u : V} (L : Incidence.TriangleIndex G) (hu : u ∉ L.val) :
    triangleNeighborCount G u L ≤ 1 := by
  obtain ⟨a, b, c, hab, hac, hbc, hL⟩ :=
    G.is3Clique_iff.mp (G.mem_cliqueFinset_iff.mp L.property)
  have hne : u ≠ a ∧ u ≠ b ∧ u ≠ c := by simpa [hL] using hu
  rw [triangleNeighborCount_eq, hL]
  exact triangle_exterior_neighbor_card G h hab hbc hac.symm hne.1 hne.2.1 hne.2.2

/-- An entry of AB is exactly a triangle-neighbor count. -/
theorem adjacency_incidence_entry (u : V) (L : Incidence.TriangleIndex G) :
    (G.adjMatrix ℚ * Incidence.vertexTriangleIncidence G) u L =
      (triangleNeighborCount G u L : ℚ) := by
  simp only [Matrix.mul_apply, Incidence.vertexTriangleIncidence,
    mul_ite, mul_one, mul_zero, Fintype.sum_ite_mem, SimpleGraph.adjMatrix_apply]
  exact triangle_neighbor_sum G u L

/-- Formula for D=G0 B/3, with no SRG assumption needed. -/
theorem mixedGram_entry (u : V) (L : Incidence.TriangleIndex G) :
    mixedGram G u L = 1 + 9 * (if u ∈ L.val then (1 : ℚ) else 0) -
      3 * (triangleNeighborCount G u L : ℚ) := by
  simp only [mixedGram, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Incidence.vertexTriangleIncidence, mul_ite, mul_one, mul_zero, Fintype.sum_ite_mem]
  simp_rw [vertexGram_entry_linear]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [triangle_neighbor_sum]
  simp [triangle_card G L]
  by_cases hu : u ∈ L.val <;> simp [hu] <;> ring

/-- An integral matrix whose rational image is D. -/
def integerMixedGram : Matrix V (Incidence.TriangleIndex G) ℤ :=
  fun u L => 1 + 9 * (if u ∈ L.val then 1 else 0) - (3 : ℤ) * triangleNeighborCount G u L

theorem integerMixedGram_cast (u : V) (L : Incidence.TriangleIndex G) :
    (integerMixedGram G u L : ℚ) = mixedGram G u L := by
  rw [mixedGram_entry]
  simp [integerMixedGram]

theorem integerMixedGram_map :
    (integerMixedGram G).map (Int.castRingHom ℚ) = mixedGram G := by
  ext u L
  exact integerMixedGram_cast G u L

/-- Every integral mixed entry is congruent to one modulo three. -/
theorem integerMixedGram_mod_three (u : V) (L : Incidence.TriangleIndex G) :
    integerMixedGram G u L % 3 = 1 := by
  unfold integerMixedGram
  by_cases hu : u ∈ L.val <;> simp only [hu, if_true, if_false] <;> omega

theorem mixedGram_values (h : G.IsSRGWith 99 14 1 2)
    (u : V) (L : Incidence.TriangleIndex G) :
    mixedGram G u L = 4 ∨ mixedGram G u L = -2 ∨ mixedGram G u L = 1 := by
  rw [mixedGram_entry]
  by_cases hu : u ∈ L.val
  · rw [if_pos hu, triangle_neighbor_count_mem G L hu]
    norm_num
  · have hc := triangle_neighbor_count_outside G h L hu
    have hh : triangleNeighborCount G u L = 0 ∨ triangleNeighborCount G u L = 1 := by omega
    rcases hh with hh | hh <;> rw [if_neg hu, hh] <;> norm_num

/-- Pointwise square of D, expressed solely by incidence and adjacency. -/
theorem mixedGram_entry_square (h : G.IsSRGWith 99 14 1 2)
    (u : V) (L : Incidence.TriangleIndex G) :
    mixedGram G u L ^ 2 = 1 + 9 * Incidence.vertexTriangleIncidence G u L +
      3 * (G.adjMatrix ℚ * Incidence.vertexTriangleIncidence G) u L := by
  rw [mixedGram_entry, adjacency_incidence_entry]
  by_cases hu : u ∈ L.val
  · rw [triangle_neighbor_count_mem G L hu]
    norm_num [Incidence.vertexTriangleIncidence, hu]
  · have hc := triangle_neighbor_count_outside G h L hu
    have hh : triangleNeighborCount G u L = 0 ∨ triangleNeighborCount G u L = 1 := by omega
    rcases hh with hh | hh <;> rw [hh] <;>
      norm_num [Incidence.vertexTriangleIncidence, hu]

#print axioms triangle_neighbor_count_mem
#print axioms triangle_neighbor_count_outside
#print axioms adjacency_incidence_entry
#print axioms mixedGram_entry
#print axioms integerMixedGram_map
#print axioms integerMixedGram_mod_three
#print axioms mixedGram_values
#print axioms mixedGram_entry_square

end Conway99
