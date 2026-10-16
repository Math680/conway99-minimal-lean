import MilgramOrthogonalDiscriminant
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Group.AddChar

/-! The true quadratic phase and its nondegenerate character pairing on M*/M. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
namespace Conway99
open scoped BigOperators

theorem milgramPhase_two_eq_one_iff (r : ℚ) :
    milgramPhase (2*r) = 1 ↔ ∃ n : ℤ, r = (n : ℚ) := by
  constructor
  · intro hh
    unfold milgramPhase at hh
    push_cast at hh
    obtain ⟨n,hn⟩ := Complex.exp_eq_one_iff.mp hh
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hp) Complex.I_ne_zero
    have he : (2 * (Real.pi : ℂ) * Complex.I) * (r : ℂ) =
        (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) := by
      calc
        _ = (Real.pi : ℂ) * Complex.I * (2 * (r : ℂ)) := by ring
        _ = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hn
        _ = _ := by ring
    exact ⟨n, by exact_mod_cast (mul_left_cancel₀ hc he)⟩
  · rintro ⟨n,rfl⟩
    exact milgramPhase_even_int n

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (h : G.IsSRGWith 99 14 1 2)
variable (e : Module.Basis (Fin 44) ℚ (rationalAmbient G))
variable (he : ∀ i, (e i : V → ℚ) ∈ canonicalLattice G)

@[simp] theorem orthogonalDiscriminantPhase_mk (x : orthogonalDual G e) :
    orthogonalDiscriminantPhase G h e he (Submodule.Quotient.mk x) =
      milgramPhase (codePair ((x : rationalAmbient G) : V → ℚ)
        ((x : rationalAmbient G) : V → ℚ)) := rfl

theorem orthogonalDiscriminantPhase_ne_zero (x : OrthogonalDiscriminant G e) :
    orthogonalDiscriminantPhase G h e he x ≠ 0 := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro x
  exact Complex.exp_ne_zero _

@[simp] theorem orthogonalDiscriminantPhase_zero :
    orthogonalDiscriminantPhase G h e he 0 = 1 := by
  change milgramPhase (codePair (0 : V → ℚ) 0) = 1
  simp [codePair, milgramPhase_zero]

def orthogonalDiscriminantPair (x y : OrthogonalDiscriminant G e) : ℂ :=
  orthogonalDiscriminantPhase G h e he (x+y) /
    (orthogonalDiscriminantPhase G h e he x * orthogonalDiscriminantPhase G h e he y)

theorem orthogonalDiscriminantPair_mk (x y : orthogonalDual G e) :
    orthogonalDiscriminantPair G h e he (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      milgramPhase (2 * codePair ((x : rationalAmbient G) : V → ℚ)
        ((y : rationalAmbient G) : V → ℚ)) := by
  unfold orthogonalDiscriminantPair
  rw [← Submodule.Quotient.mk_add]
  simp only [orthogonalDiscriminantPhase_mk]
  change milgramPhase (codePair
      (((x : rationalAmbient G) : V → ℚ) + ((y : rationalAmbient G) : V → ℚ))
      (((x : rationalAmbient G) : V → ℚ) + ((y : rationalAmbient G) : V → ℚ))) / _ = _
  rw [codePair_norm_add, milgramPhase_add, milgramPhase_add]
  have hx : milgramPhase (codePair ((x : rationalAmbient G) : V → ℚ)
      ((x : rationalAmbient G) : V → ℚ)) ≠ 0 := Complex.exp_ne_zero _
  have hy : milgramPhase (codePair ((y : rationalAmbient G) : V → ℚ)
      ((y : rationalAmbient G) : V → ℚ)) ≠ 0 := Complex.exp_ne_zero _
  field_simp

theorem orthogonalDiscriminantPair_symmetric (x y : OrthogonalDiscriminant G e) :
    orthogonalDiscriminantPair G h e he x y = orthogonalDiscriminantPair G h e he y x := by
  simp [orthogonalDiscriminantPair, add_comm, mul_comm]

theorem orthogonalDiscriminantPair_add (x y z : OrthogonalDiscriminant G e) :
    orthogonalDiscriminantPair G h e he (x+y) z =
      orthogonalDiscriminantPair G h e he x z * orthogonalDiscriminantPair G h e he y z := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro x
  refine Submodule.Quotient.induction_on _ y ?_
  intro y
  refine Submodule.Quotient.induction_on _ z ?_
  intro z
  rw [← Submodule.Quotient.mk_add, orthogonalDiscriminantPair_mk,
    orthogonalDiscriminantPair_mk, orthogonalDiscriminantPair_mk]
  change milgramPhase (2*codePair
    (((x : rationalAmbient G) : V → ℚ) + ((y : rationalAmbient G) : V → ℚ))
    ((z : rationalAmbient G) : V → ℚ)) = _
  rw [codePair_add_left, mul_add, milgramPhase_add]

def orthogonalDiscriminantCharacter (x : OrthogonalDiscriminant G e) :
    AddChar (OrthogonalDiscriminant G e) ℂ where
  toFun := orthogonalDiscriminantPair G h e he x
  map_zero_eq_one' := by
    simp [orthogonalDiscriminantPair, orthogonalDiscriminantPhase_ne_zero]
  map_add_eq_mul' y z := by
    rw [orthogonalDiscriminantPair_symmetric,
      orthogonalDiscriminantPair_add, orthogonalDiscriminantPair_symmetric G h e he y,
      orthogonalDiscriminantPair_symmetric G h e he z]

theorem orthogonalDiscriminantPhase_quadratic (x y : OrthogonalDiscriminant G e) :
    orthogonalDiscriminantPhase G h e he (x+y) =
      orthogonalDiscriminantPhase G h e he x * orthogonalDiscriminantPhase G h e he y *
        orthogonalDiscriminantCharacter G h e he x y := by
  change orthogonalDiscriminantPhase G h e he (x+y) =
    (orthogonalDiscriminantPhase G h e he x * orthogonalDiscriminantPhase G h e he y) *
      (orthogonalDiscriminantPhase G h e he (x+y) /
        (orthogonalDiscriminantPhase G h e he x * orthogonalDiscriminantPhase G h e he y))
  have hx := orthogonalDiscriminantPhase_ne_zero G h e he x
  have hy := orthogonalDiscriminantPhase_ne_zero G h e he y
  field_simp

theorem orthogonalDiscriminantCharacter_nondegenerate (x : OrthogonalDiscriminant G e)
    (hx : x ≠ 0) : orthogonalDiscriminantCharacter G h e he x ≠ 1 := by
  refine Submodule.Quotient.induction_on _ x ?_ hx
  intro x hx hc
  have hm : (x : rationalAmbient G) ∈ (ambientPairing G).dualSubmodule (orthogonalDual G e) := by
    intro y hy
    have hp := congrArg (fun c : AddChar (OrthogonalDiscriminant G e) ℂ =>
      c (Submodule.Quotient.mk (⟨y,hy⟩ : orthogonalDual G e))) hc
    change orthogonalDiscriminantPair G h e he (Submodule.Quotient.mk x)
      (Submodule.Quotient.mk (⟨y,hy⟩ : orthogonalDual G e)) = 1 at hp
    rw [orthogonalDiscriminantPair_mk] at hp
    obtain ⟨n,hn⟩ := (milgramPhase_two_eq_one_iff _).mp hp
    exact Submodule.mem_one.mpr ⟨n,hn.symm⟩
  have hb : (ambientPairing G).dualSubmodule (orthogonalDual G e) = orthogonalSublattice G e :=
    LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis _
      (ambientPairing_nondegenerate G) (ambientPairing_symm G) e
  rw [hb] at hm
  apply hx
  rw [Submodule.Quotient.mk_eq_zero]
  exact hm

#print axioms milgramPhase_two_eq_one_iff
#print axioms orthogonalDiscriminantCharacter_nondegenerate
end Conway99
