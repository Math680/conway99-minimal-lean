import MilgramSummability
import MilgramDiscriminantFourier
import MilgramMonodromy

/-! Actual theta series indexed by discriminant classes.  The analytic
Poisson transformation is not asserted here without an explicit premise. -/

noncomputable section

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def CanonicalThetaFiber (d : CanonicalDiscriminant G) :=
  {x : canonicalDual G // Submodule.Quotient.mk x = d}

def canonicalClassTheta (d : CanonicalDiscriminant G) (z : ℂ) : ℂ :=
  ∑' x : CanonicalThetaFiber G d,
    Complex.exp ((Real.pi : ℂ) * Complex.I * z *
      (codePair (x.val : V → ℚ) (x.val : V → ℚ) : ℂ))

theorem canonicalClassTheta_norm_summable (h : G.IsSRGWith 99 14 1 2)
    (d : CanonicalDiscriminant G) {z : ℂ} (hz : 0 < z.im) :
    Summable (fun x : CanonicalThetaFiber G d =>
      ‖Complex.exp ((Real.pi : ℂ) * Complex.I * z *
        (codePair (x.val : V → ℚ) (x.val : V → ℚ) : ℂ))‖) :=
  (canonicalDual_theta_norm_summable G h hz).subtype _

theorem canonicalClassTheta_summable (h : G.IsSRGWith 99 14 1 2)
    (d : CanonicalDiscriminant G) {z : ℂ} (hz : 0 < z.im) :
    Summable (fun x : CanonicalThetaFiber G d =>
      Complex.exp ((Real.pi : ℂ) * Complex.I * z *
        (codePair (x.val : V → ℚ) (x.val : V → ℚ) : ℂ))) :=
  (canonicalClassTheta_norm_summable G h d hz).of_norm

theorem canonicalClassTheta_add_one (h : G.IsSRGWith 99 14 1 2)
    (d : CanonicalDiscriminant G) (z : ℂ) :
    canonicalClassTheta G d (z + 1) =
      canonicalDiscriminantPhase G h d * canonicalClassTheta G d z := by
  unfold canonicalClassTheta
  rw [← tsum_mul_left]
  apply tsum_congr
  intro x
  have hphase : Complex.exp ((Real.pi : ℂ) * Complex.I *
      (codePair (x.val : V → ℚ) (x.val : V → ℚ) : ℂ)) =
      canonicalDiscriminantPhase G h d := by
    calc
      _ = canonicalDiscriminantPhase G h (Submodule.Quotient.mk x.val) := rfl
      _ = _ := congrArg (canonicalDiscriminantPhase G h) x.property
  rw [show (Real.pi : ℂ) * Complex.I * (z + 1) *
      (codePair (x.val : V → ℚ) (x.val : V → ℚ) : ℂ) =
      (Real.pi : ℂ) * Complex.I *
        (codePair (x.val : V → ℚ) (x.val : V → ℚ) : ℂ) +
      (Real.pi : ℂ) * Complex.I * z *
        (codePair (x.val : V → ℚ) (x.val : V → ℚ) : ℂ) by ring,
    Complex.exp_add, hphase]

def canonicalThetaFiberNeg (d : CanonicalDiscriminant G) :
    CanonicalThetaFiber G d ≃ CanonicalThetaFiber G (-d) where
  toFun x := ⟨-x.val, by rw [Submodule.Quotient.mk_neg, x.property]⟩
  invFun x := ⟨-x.val, by rw [Submodule.Quotient.mk_neg, x.property, neg_neg]⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

theorem codePair_neg_self (x : V → ℚ) : codePair (-x) (-x) = codePair x x := by
  simp [codePair, neg_dotProduct, dotProduct_neg]

theorem canonicalClassTheta_neg_class (d : CanonicalDiscriminant G) (z : ℂ) :
    canonicalClassTheta G (-d) z = canonicalClassTheta G d z := by
  unfold canonicalClassTheta
  rw [← (canonicalThetaFiberNeg G d).tsum_eq]
  apply tsum_congr
  intro x
  change Complex.exp ((Real.pi : ℂ) * Complex.I * z *
    (codePair (-(x.val : V → ℚ)) (-(x.val : V → ℚ)) : ℂ)) = _
  rw [codePair_neg_self]

theorem gaussian_theta_term_imaginary (q : ℚ) (t : ℝ) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * (Complex.I * (t : ℂ)) * (q : ℂ)) =
      (Real.exp (-Real.pi * t * (q : ℝ)) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  calc
    _ = (-(Real.pi : ℂ) * t * q) := by
      ring_nf
      rw [Complex.I_sq]
      ring
    _ = _ := rfl

theorem canonicalClassTheta_imaginary (d : CanonicalDiscriminant G) (t : ℝ) :
    canonicalClassTheta G d (Complex.I * (t : ℂ)) =
      ((∑' x : CanonicalThetaFiber G d,
        Real.exp (-Real.pi * t * (codePair (x.val : V → ℚ) (x.val : V → ℚ) : ℝ))) : ℝ) := by
  unfold canonicalClassTheta
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro x
  exact gaussian_theta_term_imaginary _ _

theorem canonicalClassTheta_zero_at_I_re_pos (h : G.IsSRGWith 99 14 1 2) :
    0 < (canonicalClassTheta G 0 Complex.I).re := by
  have hs := canonicalClassTheta_norm_summable G h 0 (z := Complex.I) (by simp)
  have hs' : Summable (fun x : CanonicalThetaFiber G 0 =>
      Real.exp (-Real.pi * 1 * (codePair (x.val : V → ℚ) (x.val : V → ℚ) : ℝ))) := by
    convert hs using 1
    ext x
    have hterm := gaussian_theta_term_imaginary
      (codePair (x.val : V → ℚ) (x.val : V → ℚ)) 1
    simp only [Complex.ofReal_one, mul_one] at hterm
    rw [hterm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simp
  let x₀ : CanonicalThetaFiber G 0 := ⟨0, by simp⟩
  have hp := hs'.tsum_pos (fun x => (Real.exp_pos _).le) x₀ (Real.exp_pos _)
  have hi := canonicalClassTheta_imaginary G 0 1
  simp only [Complex.ofReal_one, mul_one] at hi
  rw [hi, Complex.ofReal_re]
  simpa only [mul_one] using hp

theorem canonicalClassTheta_zero_at_I_ne_zero (h : G.IsSRGWith 99 14 1 2) :
    canonicalClassTheta G 0 Complex.I ≠ 0 := by
  intro hz
  have hp := canonicalClassTheta_zero_at_I_re_pos G h
  rw [hz, Complex.zero_re] at hp
  exact (lt_irrefl 0) hp

def canonicalThetaVector (z : ℂ) : CanonicalDiscriminant G → ℂ :=
  fun d => canonicalClassTheta G d z

theorem canonicalThetaVector_I_ne_zero (h : G.IsSRGWith 99 14 1 2) :
    canonicalThetaVector G Complex.I ≠ 0 := by
  intro hz
  apply canonicalClassTheta_zero_at_I_ne_zero G h
  exact congrFun hz 0

section PoissonRaccord

variable [Fintype (CanonicalDiscriminant G)]

/-- The untwisted normalized finite Fourier operator S. -/
def canonicalDiscriminantS (h : G.IsSRGWith 99 14 1 2) :
    (CanonicalDiscriminant G → ℂ) →ₗ[ℂ] (CanonicalDiscriminant G → ℂ) :=
  normalizedTwistedFourier (fun _ => 1) (canonicalDiscriminantFourierPair G h)
    (canonicalDiscriminantVolume G)

theorem canonicalDiscriminantS_mul_phase (h : G.IsSRGWith 99 14 1 2)
    (f : CanonicalDiscriminant G → ℂ) :
    canonicalDiscriminantS G h (fun d => canonicalDiscriminantPhase G h d * f d) =
      canonicalDiscriminantFourier G h (canonicalDiscriminantVolume G) f := by
  unfold canonicalDiscriminantS canonicalDiscriminantFourier normalizedTwistedFourier
  funext a
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, twistedFourierLinear,
    twistedFourier]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem canonicalThetaVector_add_one (h : G.IsSRGWith 99 14 1 2) (z : ℂ) :
    canonicalThetaVector G (z + 1) =
      (fun d => canonicalDiscriminantPhase G h d * canonicalThetaVector G z d) := by
  funext d
  exact canonicalClassTheta_add_one G h d z

/-- The sole unproved analytic bridge in the theorem below.  This is a
property of the ACTUAL class theta series; it is not an axiom or an input
silently included in a notion of lattice. -/
def CanonicalThetaPoisson (h : G.IsSRGWith 99 14 1 2) : Prop :=
  ∀ z : ℂ, 0 < z.im →
    canonicalThetaVector G (-(1 : ℂ) / z) =
      (-Complex.I * z) ^ 22 • canonicalDiscriminantS G h (canonicalThetaVector G z)

theorem canonicalThetaVector_ST_of_poisson (h : G.IsSRGWith 99 14 1 2)
    (hP : CanonicalThetaPoisson G h) (z : ℂ) (hz : 0 < z.im) :
    canonicalThetaVector G (-(1 : ℂ) / (z + 1)) =
      (-Complex.I * (z + 1)) ^ 22 •
        canonicalDiscriminantFourier G h (canonicalDiscriminantVolume G)
          (canonicalThetaVector G z) := by
  have hp := hP (z + 1) (by simpa using hz)
  rw [canonicalThetaVector_add_one G h z, canonicalDiscriminantS_mul_phase G h] at hp
  exact hp

private theorem cycle_point_one :
    -(1 : ℂ) / (Complex.I + 1) = (-1 + Complex.I) / 2 := by
  apply Complex.ext <;>
    norm_num [Complex.div_re, Complex.div_im, Complex.normSq, Complex.add_re, Complex.add_im]

private theorem cycle_point_two :
    -(1 : ℂ) / (((-1 + Complex.I) / 2) + 1) = -1 + Complex.I := by
  apply Complex.ext <;>
    norm_num [Complex.div_re, Complex.div_im, Complex.normSq, Complex.add_re, Complex.add_im]

private theorem cycle_point_three :
    -(1 : ℂ) / ((-1 + Complex.I) + 1) = Complex.I := by
  apply Complex.ext <;>
    norm_num [Complex.div_re, Complex.div_im, Complex.normSq, Complex.add_re, Complex.add_im]

private theorem cycle_factor_one : -Complex.I * (Complex.I + 1) = 1 - Complex.I := by
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem cycle_factor_two :
    -Complex.I * (((-1 + Complex.I) / 2) + 1) = (1 - Complex.I) / 2 := by
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem cycle_factor_three : -Complex.I * ((-1 + Complex.I) + 1) = 1 := by
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Rank 44 Milgram for the real canonical discriminant, conditional only on
the explicitly displayed multidimensional Poisson property.  All convergence,
T-transformation, reflection, nonvanishing and finite Gauss algebra inputs
have been proved, not assumed. -/
theorem canonicalDiscriminant_gauss_of_poisson (h : G.IsSRGWith 99 14 1 2)
    (hP : CanonicalThetaPoisson G h) :
    (∑ d, canonicalDiscriminantPhase G h d) / canonicalDiscriminantVolume G = -1 := by
  let R := canonicalDiscriminantFourier G h (canonicalDiscriminantVolume G)
  let u₀ := canonicalThetaVector G Complex.I
  let u₁ := canonicalThetaVector G ((-1 + Complex.I) / 2)
  let u₂ := canonicalThetaVector G (-1 + Complex.I)
  let γ := (∑ d, canonicalDiscriminantPhase G h d) / canonicalDiscriminantVolume G
  have h₁ : u₁ = (1 - Complex.I) ^ 22 • R u₀ := by
    have hh := canonicalThetaVector_ST_of_poisson G h hP Complex.I (by simp)
    simpa only [cycle_point_one, cycle_factor_one] using hh
  have h₂ : u₂ = ((1 - Complex.I) / 2) ^ 22 • R u₁ := by
    have hz : 0 < (((-1 + Complex.I) / 2) : ℂ).im := by
      norm_num [Complex.div_im, Complex.normSq]
    have hh := canonicalThetaVector_ST_of_poisson G h hP ((-1 + Complex.I) / 2) hz
    simpa only [cycle_point_two, cycle_factor_two] using hh
  have h₃ : u₀ = R u₂ := by
    have hh := canonicalThetaVector_ST_of_poisson G h hP (-1 + Complex.I) (by simp)
    simpa only [cycle_point_three, cycle_factor_three, one_pow, one_smul] using hh
  have hGauss : R (R (R u₀)) = γ • u₀ := by
    have hh := canonicalDiscriminantFourier_canonical_cube G h u₀
    have hreflection : (fun a => u₀ (-a)) = u₀ := by
      funext a
      exact canonicalClassTheta_neg_class G a Complex.I
    rw [hreflection] at hh
    exact hh
  exact milgram44_from_three_point_cycle R u₀ u₁ u₂ γ h₁ h₂ h₃ hGauss
    (canonicalThetaVector_I_ne_zero G h)

theorem canonicalDiscriminant_gauss_sum_of_poisson (h : G.IsSRGWith 99 14 1 2)
    (hP : CanonicalThetaPoisson G h) :
    (∑ d, canonicalDiscriminantPhase G h d) = -canonicalDiscriminantVolume G := by
  have hh := (div_eq_iff (canonicalDiscriminantVolume_ne_zero G)).mp
    (canonicalDiscriminant_gauss_of_poisson G h hP)
  simpa only [neg_one_mul] using hh

end PoissonRaccord

#print axioms canonicalClassTheta_add_one
#print axioms canonicalClassTheta_neg_class
#print axioms canonicalClassTheta_zero_at_I_re_pos
#print axioms canonicalDiscriminant_gauss_sum_of_poisson

end Conway99
