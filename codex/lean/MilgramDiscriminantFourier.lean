import MilgramPhase
import MilgramFiniteGauss
import DiscriminantNondegenerate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-! The finite Fourier/Gauss cube for the actual canonical discriminant.
No quadratic, bicharacter, or orthogonality premise is left in the final theorem. -/

noncomputable section

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem canonicalDiscriminantPhase_eq_stdAddChar (h : G.IsSRGWith 99 14 1 2)
    (d : CanonicalDiscriminant G) :
    canonicalDiscriminantPhase G h d =
      ZMod.stdAddChar (canonicalDiscriminantQuadratic G h d) := by
  refine Submodule.Quotient.induction_on _ d ?_
  intro x
  rw [canonicalDiscriminantPhase_mk, canonicalDiscriminantQuadratic_mk,
    ZMod.stdAddChar_coe]
  unfold milgramPhase
  congr 1
  have hn := canonicalDualHalfNorm_spec G h x
  have hc : (7 : ℂ) * (codePair (x : V → ℚ) (x : V → ℚ) : ℂ) =
      2 * (canonicalDualHalfNorm G h x : ℂ) := by exact_mod_cast hn
  norm_num only [Nat.cast_ofNat]
  field_simp
  linear_combination hc

def canonicalDiscriminantFourierPair (h : G.IsSRGWith 99 14 1 2)
    (a b : CanonicalDiscriminant G) : ℂ :=
  ZMod.stdAddChar (-QuadraticMap.polar (canonicalDiscriminantQuadratic G h) a b)

theorem canonicalDiscriminantFourierPair_symmetric (h : G.IsSRGWith 99 14 1 2)
    (a b : CanonicalDiscriminant G) :
    canonicalDiscriminantFourierPair G h a b =
      canonicalDiscriminantFourierPair G h b a := by
  unfold canonicalDiscriminantFourierPair
  rw [QuadraticMap.polar_comm]

theorem canonicalDiscriminantFourierPair_add (h : G.IsSRGWith 99 14 1 2)
    (a b c : CanonicalDiscriminant G) :
    canonicalDiscriminantFourierPair G h (a + b) c =
      canonicalDiscriminantFourierPair G h a c * canonicalDiscriminantFourierPair G h b c := by
  unfold canonicalDiscriminantFourierPair
  rw [canonicalDiscriminantQuadratic_polar_add, neg_add, AddChar.map_add_eq_mul]

private theorem discriminantQuadratic_zero (h : G.IsSRGWith 99 14 1 2) :
    canonicalDiscriminantQuadratic G h 0 = 0 := by
  simpa using canonicalDiscriminantQuadratic_zsmul G h 0 0

theorem canonicalDiscriminantFourierPair_zero_left (h : G.IsSRGWith 99 14 1 2)
    (b : CanonicalDiscriminant G) : canonicalDiscriminantFourierPair G h 0 b = 1 := by
  simp [canonicalDiscriminantFourierPair, QuadraticMap.polar, discriminantQuadratic_zero G h,
    AddChar.map_zero_eq_one]

theorem canonicalDiscriminantPhase_neg_class (h : G.IsSRGWith 99 14 1 2)
    (a : CanonicalDiscriminant G) :
    canonicalDiscriminantPhase G h (-a) = canonicalDiscriminantPhase G h a := by
  rw [canonicalDiscriminantPhase_eq_stdAddChar, canonicalDiscriminantPhase_eq_stdAddChar]
  have hh := canonicalDiscriminantQuadratic_zsmul G h (-1) a
  simpa using congrArg (fun z : ZMod 7 => ZMod.stdAddChar z) hh

theorem canonicalDiscriminantPhase_quadratic (h : G.IsSRGWith 99 14 1 2)
    (a b : CanonicalDiscriminant G) :
    canonicalDiscriminantPhase G h (a + b) * canonicalDiscriminantFourierPair G h a b =
      canonicalDiscriminantPhase G h a * canonicalDiscriminantPhase G h b := by
  simp only [canonicalDiscriminantPhase_eq_stdAddChar, canonicalDiscriminantFourierPair]
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  unfold QuadraticMap.polar
  ring

def canonicalDiscriminantFourierCharacter (h : G.IsSRGWith 99 14 1 2)
    (a : CanonicalDiscriminant G) : AddChar (CanonicalDiscriminant G) ℂ where
  toFun := canonicalDiscriminantFourierPair G h a
  map_zero_eq_one' := by
    rw [canonicalDiscriminantFourierPair_symmetric,
      canonicalDiscriminantFourierPair_zero_left]
  map_add_eq_mul' b c := by
    rw [canonicalDiscriminantFourierPair_symmetric,
      canonicalDiscriminantFourierPair_add,
      canonicalDiscriminantFourierPair_symmetric G h b a,
      canonicalDiscriminantFourierPair_symmetric G h c a]

theorem canonicalDiscriminantFourierCharacter_ne_one (h : G.IsSRGWith 99 14 1 2)
    (a : CanonicalDiscriminant G) (ha : a ≠ 0) :
    canonicalDiscriminantFourierCharacter G h a ≠ 1 := by
  intro hchar
  apply ha
  apply canonicalDiscriminant_polar_nondegenerate G h a
  intro b
  have hb := congrArg (fun ψ : AddChar (CanonicalDiscriminant G) ℂ => ψ b) hchar
  change ZMod.stdAddChar (-QuadraticMap.polar (canonicalDiscriminantQuadratic G h) a b) = 1 at hb
  have hz := ZMod.injective_stdAddChar
    (hb.trans (AddChar.map_zero_eq_one (ZMod.stdAddChar (N := 7))).symm)
  exact neg_eq_zero.mp hz

theorem canonicalDiscriminantFourierPair_orthogonal (h : G.IsSRGWith 99 14 1 2)
    [Fintype (CanonicalDiscriminant G)] [DecidableEq (CanonicalDiscriminant G)]
    (a : CanonicalDiscriminant G) :
    (∑ b, canonicalDiscriminantFourierPair G h a b) =
      if a = 0 then (Fintype.card (CanonicalDiscriminant G) : ℂ) else 0 := by
  classical
  by_cases ha : a = 0
  · subst a
    simp [canonicalDiscriminantFourierPair_zero_left]
  · rw [if_neg ha]
    exact AddChar.sum_eq_zero_of_ne_one (canonicalDiscriminantFourierCharacter_ne_one G h a ha)

theorem canonicalDiscriminantFourierPair_mk (h : G.IsSRGWith 99 14 1 2)
    (x y : canonicalDual G) :
    canonicalDiscriminantFourierPair G h (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      Complex.exp (-(2 : ℂ) * Real.pi * Complex.I *
        (codePair (x : V → ℚ) (y : V → ℚ) : ℂ)) := by
  unfold canonicalDiscriminantFourierPair
  rw [canonicalDiscriminantQuadratic_polar_mk, ← Int.cast_neg, ZMod.stdAddChar_coe]
  congr 1
  have hn := canonicalDualPairInteger_spec G h x y
  have hc : (7 : ℂ) * (codePair (x : V → ℚ) (y : V → ℚ) : ℂ) =
      (canonicalDualPairInteger G h x y : ℂ) := by exact_mod_cast hn
  push_cast
  field_simp
  linear_combination hc

def canonicalDiscriminantFourier (h : G.IsSRGWith 99 14 1 2)
    [Fintype (CanonicalDiscriminant G)] (v : ℂ) :
    (CanonicalDiscriminant G → ℂ) →ₗ[ℂ] (CanonicalDiscriminant G → ℂ) :=
  normalizedTwistedFourier (canonicalDiscriminantPhase G h)
    (canonicalDiscriminantFourierPair G h) v

theorem canonicalDiscriminantFourier_cube (h : G.IsSRGWith 99 14 1 2)
    [Fintype (CanonicalDiscriminant G)] (v : ℂ) (hv : v ≠ 0)
    (hcard : (Fintype.card (CanonicalDiscriminant G) : ℂ) = v ^ 2)
    (f : CanonicalDiscriminant G → ℂ) :
    canonicalDiscriminantFourier G h v
      (canonicalDiscriminantFourier G h v (canonicalDiscriminantFourier G h v f)) =
      ((∑ b, canonicalDiscriminantPhase G h b) / v) • (fun a => f (-a)) := by
  classical
  unfold canonicalDiscriminantFourier
  apply normalizedTwistedFourier_cube (canonicalDiscriminantPhase G h)
    (canonicalDiscriminantFourierPair G h) v hv hcard
  · intro a hz
    have hh := canonicalDiscriminantPhase_pow_seven G h a
    rw [hz, zero_pow (by decide : 7 ≠ 0)] at hh
    exact zero_ne_one hh
  · exact canonicalDiscriminantPhase_zero G h
  · exact canonicalDiscriminantPhase_neg_class G h
  · exact canonicalDiscriminantFourierPair_symmetric G h
  · exact canonicalDiscriminantFourierPair_add G h
  · exact canonicalDiscriminantPhase_quadratic G h
  · exact canonicalDiscriminantFourierPair_orthogonal G h

def canonicalDiscriminantVolume [Fintype (CanonicalDiscriminant G)] : ℂ :=
  (Real.sqrt (Fintype.card (CanonicalDiscriminant G) : ℝ) : ℂ)

theorem canonicalDiscriminantVolume_ne_zero [Fintype (CanonicalDiscriminant G)] :
    canonicalDiscriminantVolume G ≠ 0 := by
  have hp : 0 < Real.sqrt (Fintype.card (CanonicalDiscriminant G) : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  intro hz
  unfold canonicalDiscriminantVolume at hz
  have hz' : Real.sqrt (Fintype.card (CanonicalDiscriminant G) : ℝ) = 0 := by
    exact_mod_cast hz
  linarith

theorem canonicalDiscriminantVolume_sq [Fintype (CanonicalDiscriminant G)] :
    (Fintype.card (CanonicalDiscriminant G) : ℂ) = canonicalDiscriminantVolume G ^ 2 := by
  unfold canonicalDiscriminantVolume
  exact_mod_cast (Real.sq_sqrt (show 0 ≤ (Fintype.card (CanonicalDiscriminant G) : ℝ) by positivity)).symm

theorem canonicalDiscriminantFourier_canonical_cube (h : G.IsSRGWith 99 14 1 2)
    [Fintype (CanonicalDiscriminant G)] (f : CanonicalDiscriminant G → ℂ) :
    canonicalDiscriminantFourier G h (canonicalDiscriminantVolume G)
      (canonicalDiscriminantFourier G h (canonicalDiscriminantVolume G)
        (canonicalDiscriminantFourier G h (canonicalDiscriminantVolume G) f)) =
      ((∑ b, canonicalDiscriminantPhase G h b) / canonicalDiscriminantVolume G) •
        (fun a => f (-a)) := by
  exact canonicalDiscriminantFourier_cube G h _ (canonicalDiscriminantVolume_ne_zero G)
    (canonicalDiscriminantVolume_sq G) f

#print axioms canonicalDiscriminantFourierPair_orthogonal
#print axioms canonicalDiscriminantFourier_cube
#print axioms canonicalDiscriminantFourier_canonical_cube

end Conway99
