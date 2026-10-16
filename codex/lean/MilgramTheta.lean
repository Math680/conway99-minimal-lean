import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-! Theta identities which hold without any analytic convergence hypotheses.
The sum is Lean's `tsum`; the identities are termwise and therefore valid even
before the Gaussian convergence theorem is supplied. -/

noncomputable section

namespace Conway99

open scoped BigOperators
open Filter Topology

def latticeTheta {X : Type*} (q : X → ℚ) (z : ℂ) : ℂ :=
  ∑' x, Complex.exp ((Real.pi : ℂ) * Complex.I * z * (q x : ℂ))

theorem latticeTheta_even_periodic {X : Type*} (q : X → ℚ)
    (heven : ∀ x, ∃ n : ℤ, q x = 2 * (n : ℚ)) (z : ℂ) :
    latticeTheta q (z + 1) = latticeTheta q z := by
  unfold latticeTheta
  apply tsum_congr
  intro x
  obtain ⟨n, hn⟩ := heven x
  rw [hn]
  push_cast
  rw [show (Real.pi : ℂ) * Complex.I * (z + 1) * (2 * n) =
    (Real.pi : ℂ) * Complex.I * z * (2 * n) +
      (n : ℂ) * (2 * Real.pi * Complex.I) by ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem latticeTheta_class_shift {X : Type*} (q : X → ℚ) (r : ℚ)
    (hclass : ∀ x, ∃ n : ℤ, q x = r + 2 * (n : ℚ)) (z : ℂ) :
    latticeTheta q (z - 1) =
      Complex.exp (-(Real.pi : ℂ) * Complex.I * (r : ℂ)) * latticeTheta q z := by
  unfold latticeTheta
  rw [← tsum_mul_left]
  apply tsum_congr
  intro x
  obtain ⟨n, hn⟩ := hclass x
  rw [hn]
  push_cast
  rw [show (Real.pi : ℂ) * Complex.I * (z - 1) * (r + 2 * n) =
    -(Real.pi : ℂ) * Complex.I * r +
      (Real.pi : ℂ) * Complex.I * z * (r + 2 * n) +
      (-n : ℂ) * (2 * Real.pi * Complex.I) by ring]
  rw [Complex.exp_add]
  have hnexp : Complex.exp ((-(n : ℂ)) * (2 * Real.pi * Complex.I)) = 1 := by
    simpa only [Int.cast_neg] using Complex.exp_int_mul_two_pi_mul_I (-n)
  rw [hnexp, mul_one, Complex.exp_add]

/-- In the concrete rank 44 case no branch of a complex power is needed. -/
def milgram44PoissonFactor (ε : ℝ) : ℂ :=
  (((-Complex.I) * (1 + Complex.I * (ε : ℂ))) ^ 22)⁻¹

theorem milgram44PoissonFactor_zero : milgram44PoissonFactor 0 = -1 := by
  have hi : (-Complex.I) ^ 22 = (-1 : ℂ) := by
    calc
      _ = ((-Complex.I) ^ 2) ^ 11 := by rw [← pow_mul]
      _ = (-1 : ℂ) ^ 11 := by rw [neg_sq, Complex.I_sq]
      _ = -1 := by norm_num
  unfold milgram44PoissonFactor
  simp only [Complex.ofReal_zero, mul_zero, add_zero, mul_one, hi]
  norm_num

theorem milgram44PoissonFactor_tendsto :
    Tendsto milgram44PoissonFactor (𝓝 (0 : ℝ)) (𝓝 (-1 : ℂ)) := by
  have hcont : ContinuousAt milgram44PoissonFactor (0 : ℝ) := by
    unfold milgram44PoissonFactor
    apply ContinuousAt.inv₀
    · fun_prop
    · norm_num [show (22 : ℕ) = 2 * 11 by decide, pow_mul, Complex.I_sq]
  simpa only [milgram44PoissonFactor_zero] using hcont.tendsto

/-- Last, purely analytic step of the rank 44 Milgram proof.  The two limits
and the Poisson identity are explicit premises, not axioms and not hidden in
a structure called "lattice".  Establishing these for the actual theta sums
is a separate, still necessary theorem. -/
theorem milgram44_of_theta_limits {v g : ℂ} (hv : v ≠ 0) (hvreal : star v = v)
    (tM tD : ℝ → ℂ)
    (hM : Tendsto tM (𝓝[>] (0 : ℝ)) (𝓝 v⁻¹))
    (hD : Tendsto tD (𝓝[>] (0 : ℝ)) (𝓝 (v⁻¹ * star g)))
    (hP : ∀ ε > 0,
      tM ε = v⁻¹ * milgram44PoissonFactor ε * tD ε) :
    g = -v := by
  have hF : Tendsto milgram44PoissonFactor (𝓝[>] (0 : ℝ)) (𝓝 (-1 : ℂ)) :=
    milgram44PoissonFactor_tendsto.mono_left nhdsWithin_le_nhds
  have hR : Tendsto (fun ε => v⁻¹ * milgram44PoissonFactor ε * tD ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (v⁻¹ * (-1) * (v⁻¹ * star g))) :=
    ((tendsto_const_nhds.mul hF).mul hD)
  have hEq : tM =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε => v⁻¹ * milgram44PoissonFactor ε * tD ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hP ε hε
  have hlim : v⁻¹ = v⁻¹ * (-1) * (v⁻¹ * star g) :=
    tendsto_nhds_unique hM (hR.congr' hEq.symm)
  have hg : star g = -v := by
    have hh := congrArg (fun z : ℂ => v ^ 2 * z) hlim
    field_simp [hv] at hh
    linear_combination hh
  have hstar : g = -(star v) := by
    have hh := congrArg star hg
    simpa using hh
  simpa only [hvreal] using hstar

#print axioms latticeTheta_even_periodic
#print axioms milgram44_of_theta_limits

end Conway99
