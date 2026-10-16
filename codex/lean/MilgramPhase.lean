import LatticeQuadratic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Complex phases attached to the actual canonical discriminant.
No signature theorem or Poisson summation formula is assumed in this file. -/

noncomputable section

namespace Conway99

open scoped BigOperators

def milgramPhase (q : ℚ) : ℂ := Complex.exp (Real.pi * Complex.I * (q : ℂ))

theorem milgramPhase_even_shift (q : ℚ) (n : ℤ) :
    milgramPhase (q + 2 * (n : ℚ)) = milgramPhase q := by
  unfold milgramPhase
  push_cast
  rw [show (Real.pi : ℂ) * Complex.I * (q + 2 * n) =
    (Real.pi : ℂ) * Complex.I * q + (n : ℂ) * (2 * Real.pi * Complex.I) by ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem milgramPhase_neg (q : ℚ) :
    milgramPhase (-q) = star (milgramPhase q) := by
  unfold milgramPhase
  change Complex.exp _ = (starRingEnd ℂ) (Complex.exp _)
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ratCast, Rat.cast_neg]
  ring

theorem milgramPhase_zero : milgramPhase 0 = 1 := by simp [milgramPhase]

theorem milgramPhase_add (q r : ℚ) :
    milgramPhase (q + r) = milgramPhase q * milgramPhase r := by
  unfold milgramPhase
  push_cast
  rw [mul_add, Complex.exp_add]

theorem milgramPhase_nat_mul (n : ℕ) (q : ℚ) :
    milgramPhase ((n : ℚ) * q) = milgramPhase q ^ n := by
  unfold milgramPhase
  push_cast
  rw [show (Real.pi : ℂ) * Complex.I * (n * q) =
    (n : ℂ) * ((Real.pi : ℂ) * Complex.I * q) by ring,
    Complex.exp_nat_mul]

theorem milgramPhase_even_int (n : ℤ) : milgramPhase (2 * (n : ℚ)) = 1 := by
  simpa only [zero_add, milgramPhase_zero] using milgramPhase_even_shift 0 n

theorem milgramPhase_norm (q : ℚ) : ‖milgramPhase q‖ = 1 := by
  simp [milgramPhase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem milgram_phase_rank44 :
    Complex.exp ((Real.pi : ℂ) * Complex.I * (44 : ℂ) / 4) = -1 := by
  rw [show (Real.pi : ℂ) * Complex.I * (44 : ℂ) / 4 =
    (11 : ℕ) * (Real.pi * Complex.I) by ring]
  rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  norm_num

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem canonicalDual_norm_even_shift (h : G.IsSRGWith 99 14 1 2)
    (x y : canonicalDual G)
    (hxy : (x : V → ℚ) - (y : V → ℚ) ∈ canonicalLattice G) :
    ∃ n : ℤ, codePair (x : V → ℚ) (x : V → ℚ) =
      codePair (y : V → ℚ) (y : V → ℚ) + 2 * (n : ℚ) := by
  let d : V → ℚ := (x : V → ℚ) - (y : V → ℚ)
  obtain ⟨a, ha⟩ := canonicalLattice_even G h hxy
  obtain ⟨b, hb⟩ := y.property.2 d hxy
  have hd : (x : V → ℚ) = (y : V → ℚ) + d := by simp [d]
  refine ⟨a + b, ?_⟩
  rw [hd, codePair_norm_add]
  change codePair d d = (2 * a : ℤ) at ha
  push_cast at ha ⊢
  rw [ha, hb]
  ring

theorem canonicalDual_phase_shift (h : G.IsSRGWith 99 14 1 2)
    (x y : canonicalDual G)
    (hxy : (x : V → ℚ) - (y : V → ℚ) ∈ canonicalLattice G) :
    milgramPhase (codePair (x : V → ℚ) (x : V → ℚ)) =
      milgramPhase (codePair (y : V → ℚ) (y : V → ℚ)) := by
  obtain ⟨n, hn⟩ := canonicalDual_norm_even_shift G h x y hxy
  rw [hn, milgramPhase_even_shift]

def canonicalDiscriminantPhase (h : G.IsSRGWith 99 14 1 2) :
    CanonicalDiscriminant G → ℂ :=
  Quotient.lift (fun x : canonicalDual G =>
    milgramPhase (codePair (x : V → ℚ) (x : V → ℚ))) (by
      intro x y hxy
      exact canonicalDual_phase_shift G h x y
        ((Submodule.quotientRel_def (canonicalInsideDual G)).mp hxy))

theorem canonicalDiscriminantPhase_mk (h : G.IsSRGWith 99 14 1 2)
    (x : canonicalDual G) :
    canonicalDiscriminantPhase G h (Submodule.Quotient.mk x) =
      milgramPhase (codePair (x : V → ℚ) (x : V → ℚ)) := rfl

theorem canonicalDiscriminantPhase_zero (h : G.IsSRGWith 99 14 1 2) :
    canonicalDiscriminantPhase G h 0 = 1 := by
  change milgramPhase (codePair (0 : V → ℚ) 0) = 1
  simp [codePair, milgramPhase]

theorem canonicalDiscriminantPhase_pow_seven (h : G.IsSRGWith 99 14 1 2)
    (d : CanonicalDiscriminant G) : canonicalDiscriminantPhase G h d ^ 7 = 1 := by
  refine Submodule.Quotient.induction_on _ d ?_
  intro x
  rw [canonicalDiscriminantPhase_mk, ← milgramPhase_nat_mul]
  norm_num only [Nat.cast_ofNat]
  obtain ⟨n, hn⟩ := canonicalDual_half_norm_numerator G h x.property
  rw [hn, milgramPhase_even_int]

theorem canonicalDiscriminantPhase_norm (h : G.IsSRGWith 99 14 1 2)
    (d : CanonicalDiscriminant G) : ‖canonicalDiscriminantPhase G h d‖ = 1 := by
  refine Submodule.Quotient.induction_on _ d ?_
  intro x
  rw [canonicalDiscriminantPhase_mk]
  exact milgramPhase_norm _

#print axioms canonicalDiscriminantPhase
#print axioms milgram_phase_rank44

end Conway99
