import MilgramOrthogonalSublattice
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Isomorphisms
import MilgramPhase

/-! The orthogonal full sublattice is an actual submodule, and its quotient
inside the canonical lattice is finite. No analytic transformation is assumed. -/

noncomputable section
namespace Conway99
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def orthogonalSublattice (e : Module.Basis (Fin 44) ℚ (rationalAmbient G)) :
    Submodule ℤ (rationalAmbient G) := Submodule.span ℤ (Set.range e)

theorem orthogonalSublattice_isLattice
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G)) :
    Submodule.IsLattice ℚ (orthogonalSublattice G e) := by
  refine ⟨Submodule.fg_span (Set.finite_range e), ?_⟩
  change Submodule.span ℚ (Submodule.span ℤ (Set.range e) : Set (rationalAmbient G)) = ⊤
  rw [Submodule.span_span_of_tower, e.span_eq]

theorem orthogonalSublattice_le_canonical
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G))
    (he : ∀ i, (e i : V → ℚ) ∈ canonicalLattice G) :
    orthogonalSublattice G e ≤ canonicalInAmbient G := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact he i

def orthogonalInsideCanonical (e : Module.Basis (Fin 44) ℚ (rationalAmbient G)) :
    Submodule ℤ (canonicalInAmbient G) :=
  (orthogonalSublattice G e).comap (canonicalInAmbient G).subtype

theorem orthogonalInsideCanonical_finite_quotient (h : G.IsSRGWith 99 14 1 2)
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G))
    (he : ∀ i, (e i : V → ℚ) ∈ canonicalLattice G) :
    Finite ((canonicalInAmbient G) ⧸ orthogonalInsideCanonical G e) := by
  letI : Submodule.IsLattice ℚ (canonicalInAmbient G) := canonicalInAmbient_isLattice G
  letI : Submodule.IsLattice ℚ (orthogonalSublattice G e) := orthogonalSublattice_isLattice G e
  let c : orthogonalInsideCanonical G e ≃ₗ[ℤ] orthogonalSublattice G e :=
    Submodule.comapSubtypeEquivOfLe (orthogonalSublattice_le_canonical G e he)
  apply Submodule.finiteQuotientOfFreeOfRankEq
  rw [c.finrank_eq]
  apply Module.finrank_eq_of_rank_eq
  rw [Submodule.IsLattice.rank' ℚ (orthogonalSublattice G e), Module.finrank_eq_rank,
    Submodule.IsLattice.rank' ℚ (canonicalInAmbient G)]

theorem exists_actual_orthogonal_sublattice (h : G.IsSRGWith 99 14 1 2) :
    ∃ e : Module.Basis (Fin 44) ℚ (rationalAmbient G),
      orthogonalSublattice G e ≤ canonicalInAmbient G ∧
      Submodule.IsLattice ℚ (orthogonalSublattice G e) ∧
      Finite ((canonicalInAmbient G) ⧸ orthogonalInsideCanonical G e) ∧
      ∃ a : Fin 44 → ℤ, (∀ i, 0 < a i) ∧
        (∀ i j, i ≠ j → codePair (e i : V → ℚ) (e j : V → ℚ) = 0) ∧
        ∀ i, codePair (e i : V → ℚ) (e i : V → ℚ) = (2*a i : ℤ) := by
  obtain ⟨e,he,ho,a,ha,hn⟩ := canonicalLattice_orthogonal_integral_basis G h
  exact ⟨e, orthogonalSublattice_le_canonical G e he, orthogonalSublattice_isLattice G e,
    orthogonalInsideCanonical_finite_quotient G h e he, a,ha,ho,hn⟩

def orthogonalVectorLattice (e : Module.Basis (Fin 44) ℚ (rationalAmbient G)) :
    Submodule ℤ (V → ℚ) :=
  (orthogonalSublattice G e).map ((rationalAmbient G).restrictScalars ℤ).subtype

theorem orthogonalVectorLattice_le_canonical
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G))
    (he : ∀ i, (e i : V → ℚ) ∈ canonicalLattice G) :
    orthogonalVectorLattice G e ≤ canonicalLattice G := by
  rintro _ ⟨x,hx,rfl⟩
  exact orthogonalSublattice_le_canonical G e he hx

def orthogonalInsideDual (e : Module.Basis (Fin 44) ℚ (rationalAmbient G)) :
    Submodule ℤ (canonicalDual G) :=
  (orthogonalVectorLattice G e).comap (canonicalDual G).subtype

theorem orthogonalInsideDual_le_canonical
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G))
    (he : ∀ i, (e i : V → ℚ) ∈ canonicalLattice G) :
    orthogonalInsideDual G e ≤ canonicalInsideDual G := by
  intro x hx
  exact orthogonalVectorLattice_le_canonical G e he hx

def canonicalDiscriminantViaOrthogonalEquiv
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G))
    (he : ∀ i, (e i : V → ℚ) ∈ canonicalLattice G) :
    (((canonicalDual G) ⧸ orthogonalInsideDual G e) ⧸
      (canonicalInsideDual G).map (orthogonalInsideDual G e).mkQ) ≃ₗ[ℤ]
      CanonicalDiscriminant G :=
  Submodule.quotientQuotientEquivQuotient _ _
    (orthogonalInsideDual_le_canonical G e he)

@[simp] theorem canonicalDiscriminantViaOrthogonalEquiv_mk_mk
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G))
    (he : ∀ i, (e i : V → ℚ) ∈ canonicalLattice G) (x : canonicalDual G) :
    canonicalDiscriminantViaOrthogonalEquiv G e he
      (Submodule.Quotient.mk (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x := rfl

theorem canonicalDiscriminantViaOrthogonalEquiv_phase
    (h : G.IsSRGWith 99 14 1 2)
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G))
    (he : ∀ i, (e i : V → ℚ) ∈ canonicalLattice G) (x : canonicalDual G) :
    canonicalDiscriminantPhase G h (canonicalDiscriminantViaOrthogonalEquiv G e he
      (Submodule.Quotient.mk (Submodule.Quotient.mk x))) =
      Complex.exp ((Real.pi : ℂ) * Complex.I *
        (codePair (x : V → ℚ) (x : V → ℚ) : ℂ)) := rfl

#print axioms exists_actual_orthogonal_sublattice
#print axioms canonicalDiscriminantViaOrthogonalEquiv
#print axioms canonicalDiscriminantViaOrthogonalEquiv_phase
end Conway99
