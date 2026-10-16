import MilgramOrthogonalModel
import Mathlib.LinearAlgebra.Basis.Submodule

/-! Actual dual and discriminant of the auxiliary full sublattice. -/
noncomputable section
namespace Conway99
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def orthogonalDual (e : Module.Basis (Fin 44) ℚ (rationalAmbient G)) :
    Submodule ℤ (rationalAmbient G) :=
  (ambientPairing G).dualSubmodule (orthogonalSublattice G e)

def orthogonalDualBasis (e : Module.Basis (Fin 44) ℚ (rationalAmbient G)) :
    Module.Basis (Fin 44) ℚ (rationalAmbient G) :=
  (ambientPairing G).dualBasis (ambientPairing_nondegenerate G) e

theorem orthogonalDual_eq_span
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G)) :
    orthogonalDual G e = Submodule.span ℤ (Set.range (orthogonalDualBasis G e)) :=
  LinearMap.BilinForm.dualSubmodule_span_of_basis _ (ambientPairing_nondegenerate G) e

theorem orthogonalDual_isLattice
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G)) :
    Submodule.IsLattice ℚ (orthogonalDual G e) := by
  rw [orthogonalDual_eq_span]
  exact orthogonalSublattice_isLattice G (orthogonalDualBasis G e)

theorem orthogonalSublattice_le_dual (h : G.IsSRGWith 99 14 1 2)
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G))
    (he : ∀ i, (e i : V → ℚ) ∈ canonicalLattice G) :
    orthogonalSublattice G e ≤ orthogonalDual G e := by
  intro x hx y hy
  obtain ⟨n,hn⟩ := canonicalLattice_integral G h
    (orthogonalSublattice_le_canonical G e he hx)
    (orthogonalSublattice_le_canonical G e he hy)
  exact Submodule.mem_one.mpr ⟨n,hn.symm⟩

def orthogonalInsideOrthogonalDual
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G)) :
    Submodule ℤ (orthogonalDual G e) :=
  (orthogonalSublattice G e).comap (orthogonalDual G e).subtype

abbrev OrthogonalDiscriminant
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G)) :=
  (orthogonalDual G e) ⧸ orthogonalInsideOrthogonalDual G e

theorem orthogonalDiscriminant_finite (h : G.IsSRGWith 99 14 1 2)
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G))
    (he : ∀ i, (e i : V → ℚ) ∈ canonicalLattice G) :
    Finite (OrthogonalDiscriminant G e) := by
  letI : Submodule.IsLattice ℚ (orthogonalDual G e) := orthogonalDual_isLattice G e
  letI : Submodule.IsLattice ℚ (orthogonalSublattice G e) := orthogonalSublattice_isLattice G e
  let c : orthogonalInsideOrthogonalDual G e ≃ₗ[ℤ] orthogonalSublattice G e :=
    Submodule.comapSubtypeEquivOfLe (orthogonalSublattice_le_dual G h e he)
  apply Submodule.finiteQuotientOfFreeOfRankEq
  rw [c.finrank_eq]
  apply Module.finrank_eq_of_rank_eq
  rw [Submodule.IsLattice.rank' ℚ (orthogonalSublattice G e), Module.finrank_eq_rank,
    Submodule.IsLattice.rank' ℚ (orthogonalDual G e)]

def canonicalDualIntoOrthogonalDual
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G))
    (he : ∀ i, (e i : V → ℚ) ∈ canonicalLattice G) :
    canonicalDual G →ₗ[ℤ] orthogonalDual G e where
  toFun x := ⟨⟨x.val,x.property.1⟩, by
    intro y hy
    obtain ⟨n,hn⟩ := x.property.2 y (orthogonalSublattice_le_canonical G e he hy)
    exact Submodule.mem_one.mpr ⟨n,hn.symm⟩⟩
  map_add' x y := rfl
  map_smul' a x := rfl

theorem canonicalDualIntoOrthogonalDual_injective
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G))
    (he : ∀ i, (e i : V → ℚ) ∈ canonicalLattice G) :
    Function.Injective (canonicalDualIntoOrthogonalDual G e he) := by
  intro x y hxy
  exact Subtype.ext (congrArg (fun z : orthogonalDual G e =>
    ((z : rationalAmbient G) : V → ℚ)) hxy)

theorem orthogonalDual_norm_even_shift (h : G.IsSRGWith 99 14 1 2)
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G))
    (he : ∀ i, (e i : V → ℚ) ∈ canonicalLattice G)
    (x y : orthogonalDual G e)
    (hxy : (x : rationalAmbient G) - (y : rationalAmbient G) ∈ orthogonalSublattice G e) :
    ∃ n : ℤ, codePair ((x : rationalAmbient G) : V → ℚ) ((x : rationalAmbient G) : V → ℚ) =
      codePair ((y : rationalAmbient G) : V → ℚ) ((y : rationalAmbient G) : V → ℚ) + 2*(n : ℚ) := by
  let d := (x : rationalAmbient G) - (y : rationalAmbient G)
  obtain ⟨a,ha⟩ := canonicalLattice_even G h (orthogonalSublattice_le_canonical G e he hxy)
  obtain ⟨b,hb⟩ := Submodule.mem_one.mp (y.property d hxy)
  have hd : ((x : rationalAmbient G) : V → ℚ) =
      ((y : rationalAmbient G) : V → ℚ) + (d : V → ℚ) := by simp [d]
  refine ⟨a+b, ?_⟩
  rw [hd, codePair_norm_add]
  change codePair (d : V → ℚ) (d : V → ℚ) = (2*a : ℤ) at ha
  change (b : ℚ) = codePair ((y : rationalAmbient G) : V → ℚ) (d : V → ℚ) at hb
  push_cast at ha ⊢
  rw [ha, ← hb]
  ring

def orthogonalDiscriminantPhase (h : G.IsSRGWith 99 14 1 2)
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G))
    (he : ∀ i, (e i : V → ℚ) ∈ canonicalLattice G) :
    OrthogonalDiscriminant G e → ℂ :=
  Quotient.lift (fun x : orthogonalDual G e =>
    milgramPhase (codePair ((x : rationalAmbient G) : V → ℚ)
      ((x : rationalAmbient G) : V → ℚ))) (by
    intro x y hxy
    have hm := (Submodule.quotientRel_def (orthogonalInsideOrthogonalDual G e)).mp hxy
    obtain ⟨n,hn⟩ := orthogonalDual_norm_even_shift G h e he x y hm
    dsimp only
    rw [hn, milgramPhase_even_shift])

#print axioms orthogonalDiscriminant_finite
#print axioms canonicalDualIntoOrthogonalDual_injective
#print axioms orthogonalDiscriminantPhase
end Conway99
