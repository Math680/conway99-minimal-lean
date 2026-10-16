import LatticeStructure

/-! The canonical integral module is a full lattice of rank 44. -/

namespace Conway99

open scoped BigOperators Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem canonicalLattice_rational_span :
    Submodule.span ℚ (canonicalLattice G : Set (V → ℚ)) = rationalAmbient G := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (canonicalLattice_le_ambient G)
  · change LinearMap.range (vertexGram G).mulVecLin ≤ _
    rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro x ⟨u, rfl⟩
    exact Submodule.subset_span (vertexCode_mem_canonical G u)

def canonicalInAmbient : Submodule ℤ (rationalAmbient G) :=
  (canonicalLattice G).comap ((rationalAmbient G).restrictScalars ℤ).subtype

theorem canonicalInAmbient_isLattice :
    Submodule.IsLattice ℚ (canonicalInAmbient G) := by
  let e : canonicalInAmbient G ≃ₗ[ℤ] canonicalLattice G :=
    Submodule.comapSubtypeEquivOfLe (canonicalLattice_le_ambient G)
  letI : Module.Finite ℤ (canonicalLattice G) :=
    Module.Finite.iff_fg.mpr (canonicalLattice_fg G)
  letI : Module.Finite ℤ (canonicalInAmbient G) := Module.Finite.equiv e.symm
  refine ⟨Module.Finite.iff_fg.mp inferInstance, ?_⟩
  apply Submodule.map_injective_of_injective (rationalAmbient G).injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  have himage : (rationalAmbient G).subtype ''
      (canonicalInAmbient G : Set (rationalAmbient G)) =
      (canonicalLattice G : Set (V → ℚ)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, canonicalLattice_le_ambient G hx⟩, hx, rfl⟩
  rw [himage, canonicalLattice_rational_span]

theorem canonicalLattice_finrank (h : G.IsSRGWith 99 14 1 2) :
    Module.finrank ℤ (canonicalLattice G) = 44 := by
  let e : canonicalInAmbient G ≃ₗ[ℤ] canonicalLattice G :=
    Submodule.comapSubtypeEquivOfLe (canonicalLattice_le_ambient G)
  letI : Submodule.IsLattice ℚ (canonicalInAmbient G) := canonicalInAmbient_isLattice G
  rw [← e.finrank_eq]
  apply Module.finrank_eq_of_rank_eq
  rw [Submodule.IsLattice.rank' ℚ, ← Module.finrank_eq_rank, rationalAmbient_finrank G h]

#print axioms canonicalLattice_rational_span
#print axioms canonicalLattice_finrank

end Conway99
