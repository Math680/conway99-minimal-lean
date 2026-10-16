import FiniteGaussWitt
import MilgramDiscriminantFourier
import DiscriminantWittLift

/-! The finite algebraic consequence of the actual discriminant Gauss identity.
The Gauss identity remains explicit; parity and the absence of a Lagrangian are proved.
-/

noncomputable section
namespace Conway99
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [Module (ZMod 7) (CanonicalDiscriminant G)]
variable [Fintype (CanonicalDiscriminant G)]

theorem canonicalDiscriminant_codim_two_of_gauss (h : G.IsSRGWith 99 14 1 2)
    (hg : (∑ d, canonicalDiscriminantPhase G h d) = -canonicalDiscriminantVolume G) :
    ∃ H : Submodule (ZMod 7) (CanonicalDiscriminant G),
      (∀ x ∈ H, canonicalDiscriminantQuadratic G h x = 0) ∧
      Module.finrank (ZMod 7) (CanonicalDiscriminant G) =
        2 * Module.finrank (ZMod 7) H + 2 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : Module.Finite (ZMod 7) (CanonicalDiscriminant G) := Module.Finite.of_finite
  apply sevenGauss_negative_sqrt_isotropic_codim_two (canonicalDiscriminantForm G h)
    (canonicalDiscriminantForm_polar_nondegenerate G h)
  simpa only [sevenGauss, canonicalDiscriminantPhase_eq_stdAddChar,
    canonicalDiscriminantForm_apply, canonicalDiscriminantVolume] using hg

theorem canonicalWittLiftData_exact_of_gauss (h : G.IsSRGWith 99 14 1 2)
    (hg : (∑ d, canonicalDiscriminantPhase G h d) = -canonicalDiscriminantVolume G) :
    ∃ data : CanonicalWittLiftData G, data.exponent = 2 * data.isotropicRank + 2 := by
  obtain ⟨H, hH, he⟩ := canonicalDiscriminant_codim_two_of_gauss G h hg
  exact ⟨canonicalWittLiftOfSubspace G h H hH (by omega) he.le, he⟩

#print axioms canonicalDiscriminant_codim_two_of_gauss
#print axioms canonicalWittLiftData_exact_of_gauss
end Conway99
