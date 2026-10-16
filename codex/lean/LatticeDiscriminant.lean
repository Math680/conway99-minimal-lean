import LatticeDual
import LatticeStructure
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.FieldTheory.Finiteness

/-! Finiteness of the actual discriminant quotient, without determinant assumptions. -/

namespace Conway99

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def canonicalDualMultiple (h : G.IsSRGWith 99 14 1 2) :
    canonicalDual G →ₗ[ℤ] canonicalLattice G where
  toFun x := ⟨(21 : ℤ) • (x : V → ℚ), by
    simpa only [Int.cast_smul_eq_zsmul ℚ (21 : ℤ), Int.cast_ofNat] using
      canonicalDual_exponent_twenty_one G h x.property⟩
  map_add' x y := by ext u; simp [smul_add]
  map_smul' a x := by
    apply Subtype.ext
    change (21 : ℤ) • (a • (x : V → ℚ)) = a • ((21 : ℤ) • (x : V → ℚ))
    exact smul_comm _ _ _

theorem canonicalDualMultiple_injective (h : G.IsSRGWith 99 14 1 2) :
    Function.Injective (canonicalDualMultiple G h) := by
  intro x y hxy
  apply Subtype.ext
  ext u
  have he := congrArg (fun t : canonicalLattice G => (t : V → ℚ) u) hxy
  change (21 : ℤ) • (x : V → ℚ) u = (21 : ℤ) • (y : V → ℚ) u at he
  simp only [zsmul_eq_mul, Int.cast_ofNat] at he
  linarith

theorem canonicalDual_finiteModule (h : G.IsSRGWith 99 14 1 2) :
    Module.Finite ℤ (canonicalDual G) := by
  letI : Module.Finite ℤ (canonicalLattice G) :=
    Module.Finite.iff_fg.mpr (canonicalLattice_fg G)
  exact Module.Finite.of_injective (canonicalDualMultiple G h)
    (canonicalDualMultiple_injective G h)

theorem canonicalDiscriminant_finite (h : G.IsSRGWith 99 14 1 2) :
    Finite (CanonicalDiscriminant G) := by
  letI : Module.Finite ℤ (canonicalDual G) := canonicalDual_finiteModule G h
  apply Module.finite_of_fg_torsion
  intro q
  exact ⟨⟨21, by norm_num [mem_nonZeroDivisors_iff_ne_zero]⟩,
    canonicalDiscriminant_annihilated G h q⟩

def canonicalDiscriminant_zmodModule (h : G.IsSRGWith 99 14 1 2) :
    Module (ZMod 7) (CanonicalDiscriminant G) :=
  AddCommGroup.zmodModule (n := 7) (fun q => by
    simpa only [show (7 : ℤ) = (7 : ℕ) from rfl, natCast_zsmul] using
      canonicalDiscriminant_annihilated_seven G h q)

theorem canonicalDiscriminant_card_power_seven (h : G.IsSRGWith 99 14 1 2) :
    ∃ e : ℕ, Nat.card (CanonicalDiscriminant G) = 7 ^ e := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : Module (ZMod 7) (CanonicalDiscriminant G) := canonicalDiscriminant_zmodModule G h
  letI : Finite (CanonicalDiscriminant G) := canonicalDiscriminant_finite G h
  letI : Module.Finite (ZMod 7) (CanonicalDiscriminant G) := Module.Finite.of_finite
  refine ⟨Module.finrank (ZMod 7) (CanonicalDiscriminant G), ?_⟩
  simpa using (Module.natCard_eq_pow_finrank (K := ZMod 7) (V := CanonicalDiscriminant G))

theorem canonicalDiscriminant_no_three_torsion (h : G.IsSRGWith 99 14 1 2)
    (q : CanonicalDiscriminant G) (hq : (3 : ℤ) • q = 0) : q = 0 := by
  have he : (7 : ℤ) • q - (2 : ℤ) • ((3 : ℤ) • q) = q := by
    rw [smul_smul, ← sub_smul]
    norm_num
  rw [canonicalDiscriminant_annihilated_seven G h q, hq] at he
  simpa using he.symm

#print axioms canonicalDual_finiteModule
#print axioms canonicalDiscriminant_finite
#print axioms canonicalDiscriminant_card_power_seven
#print axioms canonicalDiscriminant_no_three_torsion

end Conway99
