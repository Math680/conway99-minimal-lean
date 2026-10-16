import LatticeBidual
import DiscriminantForm

/-! Nondegeneracy of the discriminant form follows from the proved bidual identity. -/

namespace Conway99

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem canonicalDiscriminant_polar_nondegenerate (h : G.IsSRGWith 99 14 1 2)
    (q : CanonicalDiscriminant G)
    (hq : ∀ r, QuadraticMap.polar (canonicalDiscriminantQuadratic G h) q r = 0) :
    q = 0 := by
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change (x : V → ℚ) ∈ canonicalLattice G
    apply canonicalLattice_bidual G _ x.property.1
    intro y hy
    exact (canonicalDiscriminantQuadratic_polar_zero_iff G h x ⟨y, hy⟩).mp
      (hq (Submodule.Quotient.mk ⟨y, hy⟩))

theorem canonicalDiscriminantForm_polar_nondegenerate (h : G.IsSRGWith 99 14 1 2)
    [Module (ZMod 7) (CanonicalDiscriminant G)] :
    LinearMap.BilinForm.Nondegenerate (canonicalDiscriminantBilinear G h) := by
  intro q hq
  apply canonicalDiscriminant_polar_nondegenerate G h q
  intro r
  exact hq r

#print axioms canonicalDiscriminant_polar_nondegenerate
#print axioms canonicalDiscriminantForm_polar_nondegenerate

end Conway99
