import RootRankFour
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! The actual rational span of all roots has dimension at most four.
No finiteness hypothesis on the set of roots is used. -/

namespace Conway99

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def canonicalLiftRoots (H : Submodule ℤ (CanonicalDiscriminant G)) : Set (V → ℚ) :=
  {x | x ∈ canonicalLift G H ∧ codePair x x = 2}

def rootSubspace (H : Submodule ℤ (CanonicalDiscriminant G)) : Submodule ℚ (V → ℚ) :=
  Submodule.span ℚ (canonicalLiftRoots G H)

theorem rootSubspace_le_ambient (H : Submodule ℤ (CanonicalDiscriminant G)) :
    rootSubspace G H ≤ rationalAmbient G := by
  apply Submodule.span_le.mpr
  intro x hx
  exact canonicalLift_le_ambient G H hx.1

theorem canonicalLift_rootSubspace_finrank_le_four (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G))
    (hH : ∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0) :
    Module.finrank ℚ (rootSubspace G H) ≤ 4 := by
  classical
  obtain ⟨r, hr, _hspan, hli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ (canonicalLiftRoots G H)
  have hfamily := canonicalLift_root_family_card_le_four G h H hH r
    (fun i => (hr i).1) (fun i => (hr i).2)
    (fun i j hij heq => hij (hli.injective heq))
    (fun i j hij heq => hij (hli.eq_of_smul_apply_eq_smul_apply
      (1 : ℚ) (-1 : ℚ) i j (by norm_num) (by simpa using heq)))
  simpa only [Fintype.card_fin, rootSubspace] using hfamily

#print axioms rootSubspace_le_ambient
#print axioms canonicalLift_rootSubspace_finrank_le_four

end Conway99
