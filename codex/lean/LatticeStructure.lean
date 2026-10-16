import RationalLattice

/-! Finite generation, the vertex-to-triangle inclusion, and the eigenspace model. -/

namespace Conway99

open scoped BigOperators Matrix
open Incidence

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem canonicalLattice_fg : (canonicalLattice G).FG := by
  exact (IsNoetherian.noetherian (canonicalCoefficients (V := V))).map (coefficientCode G)

theorem vertexLattice_fg : (vertexLattice G).FG :=
  Submodule.fg_span (Set.finite_range _)

theorem triangleLattice_fg : (triangleLattice G).FG :=
  Submodule.fg_span (Set.finite_range _)

theorem rationalAmbient_eigen (h : G.IsSRGWith 99 14 1 2)
    {x : V → ℚ} (hx : x ∈ rationalAmbient G) :
    G.adjMatrix ℚ *ᵥ x = (-4 : ℚ) • x := by
  obtain ⟨c, rfl⟩ := hx
  have ha : vertexGram G * G.adjMatrix ℚ = (-4 : ℚ) • vertexGram G := by
    convert vertexGram_mul_adjacency G h using 1
  have ht := congrArg Matrix.transpose ha
  have he : G.adjMatrix ℚ * vertexGram G = (-4 : ℚ) • vertexGram G := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_smul, vertexGram_transpose,
      SimpleGraph.transpose_adjMatrix] using ht
  change G.adjMatrix ℚ *ᵥ (vertexGram G *ᵥ c) = _
  rw [Matrix.mulVec_mulVec, he, Matrix.smul_mulVec]
  rfl

theorem mixedGram_mul_transpose_incidence (h : G.IsSRGWith 99 14 1 2) :
    mixedGram G * (vertexTriangleIncidence G).transpose = vertexGram G := by
  have hb : vertexTriangleIncidence G * (vertexTriangleIncidence G).transpose =
      (7 : ℚ) • (1 : Matrix V V ℚ) + G.adjMatrix ℚ := by
    simpa only [ofNat_smul_eq_nsmul] using incidence_product G h
  have ha : vertexGram G * G.adjMatrix ℚ = (-4 : ℚ) • vertexGram G := by
    convert vertexGram_mul_adjacency G h using 1
  rw [mixedGram, Matrix.smul_mul, Matrix.mul_assoc, hb, Matrix.mul_add,
    Matrix.mul_smul, Matrix.mul_one, ha]
  rw [← add_smul, smul_smul]
  norm_num

theorem vertexCode_triangle_sum (h : G.IsSRGWith 99 14 1 2) (u : V) :
    vertexCode G u = ∑ L : TriangleIndex G,
      (if u ∈ L.val then (1 : ℤ) else 0) • triangleCode G L := by
  ext v
  have he := congrArg (fun M : Matrix V V ℚ => M v u)
    (mixedGram_mul_transpose_incidence G h)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, vertexTriangleIncidence] at he
  change vertexGram G v u = _
  rw [← he]
  simp only [Finset.sum_apply, Pi.smul_apply, triangleCode, vertexCode]
  apply Finset.sum_congr rfl
  intro L _
  split_ifs <;> simp

theorem vertexLattice_le_triangle (h : G.IsSRGWith 99 14 1 2) :
    vertexLattice G ≤ triangleLattice G := by
  apply Submodule.span_le.mpr
  rintro x ⟨u, rfl⟩
  rw [vertexCode_triangle_sum G h u]
  apply Submodule.sum_mem
  intro L _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨L, rfl⟩

theorem codePair_triangles (h : G.IsSRGWith 99 14 1 2) (L M : TriangleIndex G) :
    codePair (triangleCode G L) (triangleCode G M) = triangleGram G L M := by
  have he := congrArg
    (fun H : Matrix (TriangleIndex G) (TriangleIndex G) ℚ => H L M)
    (mixedGram_transpose_mul_self G h)
  change (∑ u, mixedGram G u L * mixedGram G u M) = 63 * triangleGram G L M at he
  change (∑ u, mixedGram G u L * mixedGram G u M) / 63 = _
  rw [he]
  ring

#print axioms canonicalLattice_fg
#print axioms vertexLattice_le_triangle
#print axioms codePair_triangles

end Conway99
