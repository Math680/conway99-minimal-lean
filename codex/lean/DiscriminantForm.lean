import LatticeQuadratic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! The actual seven-primary discriminant norm, as a quadratic form over `ZMod 7`. -/

namespace Conway99

open scoped BigOperators Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem canonicalDualHalfNorm_zsmul (h : G.IsSRGWith 99 14 1 2)
    (a : ℤ) (x : canonicalDual G) :
    canonicalDualHalfNorm G h (a • x) = a * a * canonicalDualHalfNorm G h x := by
  have hx := canonicalDualHalfNorm_spec G h x
  have ha := canonicalDualHalfNorm_spec G h (a • x)
  change 7 * codePair (a • (x : V → ℚ)) (a • (x : V → ℚ)) = _ at ha
  simp only [← Int.cast_smul_eq_zsmul ℚ, codePair_smul_left, codePair_smul_right] at ha
  apply Int.cast_injective (α := ℚ)
  push_cast
  nlinarith

theorem canonicalDualHalfNorm_ternary (h : G.IsSRGWith 99 14 1 2)
    (x y z : canonicalDual G) :
    canonicalDualHalfNorm G h (x + y + z) - canonicalDualHalfNorm G h (x + y) -
      canonicalDualHalfNorm G h z =
    (canonicalDualHalfNorm G h (x + z) - canonicalDualHalfNorm G h x -
      canonicalDualHalfNorm G h z) +
    (canonicalDualHalfNorm G h (y + z) - canonicalDualHalfNorm G h y -
      canonicalDualHalfNorm G h z) := by
  have hxyz := canonicalDualHalfNorm_spec G h (x + y + z)
  have hxy := canonicalDualHalfNorm_spec G h (x + y)
  have hxz := canonicalDualHalfNorm_spec G h (x + z)
  have hyz := canonicalDualHalfNorm_spec G h (y + z)
  have hx := canonicalDualHalfNorm_spec G h x
  have hy := canonicalDualHalfNorm_spec G h y
  have hz := canonicalDualHalfNorm_spec G h z
  simp only [Submodule.coe_add, codePair_add_left, codePair_add_right] at hxyz hxy hxz hyz
  rw [codePair_symm (y : V → ℚ) (x : V → ℚ),
    codePair_symm (z : V → ℚ) (x : V → ℚ),
    codePair_symm (z : V → ℚ) (y : V → ℚ)] at hxyz
  rw [codePair_symm (y : V → ℚ) (x : V → ℚ)] at hxy
  rw [codePair_symm (z : V → ℚ) (x : V → ℚ)] at hxz
  rw [codePair_symm (z : V → ℚ) (y : V → ℚ)] at hyz
  apply Int.cast_injective (α := ℚ)
  push_cast
  linarith

theorem canonicalDiscriminantQuadratic_zsmul (h : G.IsSRGWith 99 14 1 2)
    (a : ℤ) (x : CanonicalDiscriminant G) :
    canonicalDiscriminantQuadratic G h (a • x) =
      (a : ZMod 7) * (a : ZMod 7) * canonicalDiscriminantQuadratic G h x := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro x
  rw [← Submodule.Quotient.mk_smul]
  simp only [canonicalDiscriminantQuadratic_mk, canonicalDualHalfNorm_zsmul,
    Int.cast_mul]

theorem canonicalDiscriminantQuadratic_polar_add (h : G.IsSRGWith 99 14 1 2)
    (x y z : CanonicalDiscriminant G) :
    QuadraticMap.polar (canonicalDiscriminantQuadratic G h) (x + y) z =
      QuadraticMap.polar (canonicalDiscriminantQuadratic G h) x z +
      QuadraticMap.polar (canonicalDiscriminantQuadratic G h) y z := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro x
  refine Submodule.Quotient.induction_on _ y ?_
  intro y
  refine Submodule.Quotient.induction_on _ z ?_
  intro z
  simp only [QuadraticMap.polar, ← Submodule.Quotient.mk_add,
    canonicalDiscriminantQuadratic_mk]
  simpa only [Int.cast_sub, Int.cast_add] using
    congrArg (fun a : ℤ => (a : ZMod 7)) (canonicalDualHalfNorm_ternary G h x y z)

noncomputable def canonicalDualPairInteger (h : G.IsSRGWith 99 14 1 2)
    (x y : canonicalDual G) : ℤ :=
  canonicalDualHalfNorm G h (x + y) - canonicalDualHalfNorm G h x -
    canonicalDualHalfNorm G h y

theorem canonicalDualPairInteger_spec (h : G.IsSRGWith 99 14 1 2)
    (x y : canonicalDual G) :
    7 * codePair (x : V → ℚ) (y : V → ℚ) =
      (canonicalDualPairInteger G h x y : ℚ) := by
  have hx := canonicalDualHalfNorm_spec G h x
  have hy := canonicalDualHalfNorm_spec G h y
  have hxy := canonicalDualHalfNorm_spec G h (x + y)
  simp only [Submodule.coe_add, codePair_norm_add] at hxy
  dsimp [canonicalDualPairInteger]
  push_cast
  linarith

theorem canonicalDiscriminantQuadratic_polar_mk (h : G.IsSRGWith 99 14 1 2)
    (x y : canonicalDual G) :
    QuadraticMap.polar (canonicalDiscriminantQuadratic G h)
      (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      (canonicalDualPairInteger G h x y : ZMod 7) := by
  simp only [QuadraticMap.polar, ← Submodule.Quotient.mk_add,
    canonicalDiscriminantQuadratic_mk, canonicalDualPairInteger, Int.cast_sub]

theorem canonicalDiscriminantQuadratic_polar_zero_iff (h : G.IsSRGWith 99 14 1 2)
    (x y : canonicalDual G) :
    QuadraticMap.polar (canonicalDiscriminantQuadratic G h)
      (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = 0 ↔
      ∃ n : ℤ, codePair (x : V → ℚ) (y : V → ℚ) = (n : ℚ) := by
  rw [canonicalDiscriminantQuadratic_polar_mk, ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hp := canonicalDualPairInteger_spec G h x y
    rw [hn] at hp
    push_cast at hp
    linarith
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Int.cast_injective (α := ℚ)
    have hp := canonicalDualPairInteger_spec G h x y
    rw [hn] at hp
    simpa only [Int.cast_mul, Int.cast_ofNat] using hp.symm

section FieldStructure

variable (h : G.IsSRGWith 99 14 1 2)

variable [Module (ZMod 7) (CanonicalDiscriminant G)]

include h

theorem canonicalDiscriminant_zmod_smul_eq (a : ZMod 7) (x : CanonicalDiscriminant G) :
    a • x = a.val • x := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  rw [Nat.cast_smul_eq_nsmul]

theorem canonicalDiscriminantQuadratic_smul (a : ZMod 7) (x : CanonicalDiscriminant G) :
    canonicalDiscriminantQuadratic G h (a • x) =
      (a * a) • canonicalDiscriminantQuadratic G h x := by
  rw [canonicalDiscriminant_zmod_smul_eq G h]
  have hh := canonicalDiscriminantQuadratic_zsmul G h (a.val : ℤ) x
  simpa only [natCast_zsmul, Int.cast_natCast, ZMod.natCast_zmod_val,
    smul_eq_mul] using hh

theorem canonicalDiscriminantQuadratic_zero :
    canonicalDiscriminantQuadratic G h 0 = 0 := by
  simpa using canonicalDiscriminantQuadratic_zsmul G h 0 0

theorem canonicalDiscriminantQuadratic_polar_nsmul (n : ℕ)
    (x y : CanonicalDiscriminant G) :
    QuadraticMap.polar (canonicalDiscriminantQuadratic G h) (n • x) y =
      n • QuadraticMap.polar (canonicalDiscriminantQuadratic G h) x y := by
  induction n with
  | zero => simp [QuadraticMap.polar, canonicalDiscriminantQuadratic_zero G h]
  | succ n ih =>
    rw [succ_nsmul, canonicalDiscriminantQuadratic_polar_add, ih, succ_nsmul]

theorem canonicalDiscriminantQuadratic_polar_smul (a : ZMod 7)
    (x y : CanonicalDiscriminant G) :
    QuadraticMap.polar (canonicalDiscriminantQuadratic G h) (a • x) y =
      a • QuadraticMap.polar (canonicalDiscriminantQuadratic G h) x y := by
  rw [canonicalDiscriminant_zmod_smul_eq G h,
    canonicalDiscriminantQuadratic_polar_nsmul]
  rw [← Nat.cast_smul_eq_nsmul (ZMod 7), ZMod.natCast_zmod_val]

noncomputable def canonicalDiscriminantForm : QuadraticForm (ZMod 7) (CanonicalDiscriminant G) :=
  QuadraticMap.ofPolar (canonicalDiscriminantQuadratic G h)
    (canonicalDiscriminantQuadratic_smul G h)
    (canonicalDiscriminantQuadratic_polar_add G h)
    (canonicalDiscriminantQuadratic_polar_smul G h)

@[simp] theorem canonicalDiscriminantForm_apply (x : CanonicalDiscriminant G) :
    canonicalDiscriminantForm G h x = canonicalDiscriminantQuadratic G h x := rfl

noncomputable def canonicalDiscriminantBilinear :
    LinearMap.BilinForm (ZMod 7) (CanonicalDiscriminant G) :=
  (canonicalDiscriminantForm G h).polarBilin

theorem canonicalDiscriminantBilinear_mk (x y : canonicalDual G) :
    canonicalDiscriminantBilinear G h (Submodule.Quotient.mk x)
      (Submodule.Quotient.mk y) = (canonicalDualPairInteger G h x y : ZMod 7) := by
  change QuadraticMap.polar (canonicalDiscriminantQuadratic G h)
    (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = _
  exact canonicalDiscriminantQuadratic_polar_mk G h x y

theorem canonicalDiscriminantBilinear_zero_iff (x y : canonicalDual G) :
    canonicalDiscriminantBilinear G h (Submodule.Quotient.mk x)
      (Submodule.Quotient.mk y) = 0 ↔
      ∃ n : ℤ, codePair (x : V → ℚ) (y : V → ℚ) = (n : ℚ) := by
  change QuadraticMap.polar (canonicalDiscriminantQuadratic G h)
    (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = 0 ↔ _
  exact canonicalDiscriminantQuadratic_polar_zero_iff G h x y

theorem canonicalDiscriminantBilinear_symmetric :
    (canonicalDiscriminantBilinear G h).IsSymm := by
  exact ⟨fun x y => QuadraticMap.polar_comm _ x y⟩

#print axioms canonicalDiscriminantForm
#print axioms canonicalDiscriminantQuadratic_smul
#print axioms canonicalDiscriminantBilinear_zero_iff

end FieldStructure
end Conway99
