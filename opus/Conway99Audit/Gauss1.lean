import Mathlib

/-!
# Part C, step 1: the one-dimensional quadratic Gauss sum, with its sign

For even `c > 0`:  `∑_{x < c} exp(π i x² / c) = √c · exp(π i / 4)`.

This is the only analytic input of Milgram's formula (Appendix B of the paper).  The proof
uses the functional equation of the two-variable Jacobi theta function from Mathlib:
for `τ = 1/c + i/(c² t)` one computes `θ(0, τ)` in two ways,
* splitting the series by residues mod `c` and applying the functional equation to each class:
  `θ(0, τ) = √t · ∑_x e^{π i x²/c} θ(x/c, i t)`;
* applying the functional equation twice (with the period `τ ↦ τ + c`):
  `θ(0, τ) = √(c t) · e^{π i/4} · θ(0, -1/c + i t)`;
and lets `t → ∞`.
-/

open Complex Real Filter Topology

namespace Conway99

noncomputable section

lemma theta_add_two_mul (z τ : ℂ) (k : ℕ) : jacobiTheta₂ z (τ + 2 * k) = jacobiTheta₂ z τ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show τ + 2 * ((k + 1 : ℕ) : ℂ) = (τ + 2 * k) + 2 by push_cast; ring,
      jacobiTheta₂_add_right, ih]

/-- Splitting a summable series over `ℤ` by residues modulo `c`. -/
lemma tsum_split_mod (f : ℤ → ℂ) (hf : Summable f) (c : ℕ) (hc : 0 < c) :
    ∑' n, f n = ∑ x ∈ Finset.range c, ∑' m : ℤ, f (c * m + x) := by
  have hc' : (0 : ℤ) < c := by exact_mod_cast hc
  have key : ∀ x ∈ Finset.range c,
      HasSum (fun n : ℤ => if n % (c : ℤ) = x then f n else 0) (∑' m : ℤ, f (c * m + x)) := by
    intro x hx
    rw [Finset.mem_range] at hx
    have hinj : Function.Injective (fun m : ℤ => (c : ℤ) * m + x) := by
      intro a b h
      have : (c : ℤ) * a = c * b := by simpa using h
      exact mul_left_cancel₀ hc'.ne' this
    have hs : Summable (fun m : ℤ => f (c * m + x)) := hf.comp_injective hinj
    rw [← hinj.hasSum_iff]
    · have e : ((fun n : ℤ => if n % (c : ℤ) = x then f n else 0) ∘ fun m : ℤ => (c : ℤ) * m + x)
          = fun m : ℤ => f (c * m + x) := by
        funext m
        have : ((c : ℤ) * m + x) % c = x := by
          rw [Int.add_comm, Int.add_mul_emod_self_left]
          exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hx)
        simp [this]
      rw [e]; exact hs.hasSum
    · intro n hn
      rw [if_neg]
      intro h
      apply hn
      refine ⟨n / c, ?_⟩
      simp only
      have := Int.emod_add_mul_ediv n c
      rw [h] at this; linarith
  have hsum := hasSum_sum key
  have e : (fun n : ℤ => ∑ x ∈ Finset.range c, if n % (c : ℤ) = x then f n else 0) = f := by
    funext n
    have h0 : 0 ≤ n % (c : ℤ) := Int.emod_nonneg n hc'.ne'
    have h1 : n % (c : ℤ) < c := Int.emod_lt_of_pos n hc'
    have : ∀ x : ℕ, (n % (c : ℤ) = x) ↔ (x = (n % (c : ℤ)).toNat) := by
      intro x; constructor
      · intro h; rw [h]; simp
      · intro h; rw [h, Int.toNat_of_nonneg h0]
    simp_rw [this]
    rw [Finset.sum_ite_eq']
    rw [if_pos]
    rw [Finset.mem_range]
    omega
  rw [e] at hsum
  exact hsum.tsum_eq

/-- `exp (π i (c m + x)² / c) = exp (π i x² / c)` for even `c`. -/
lemma exp_quad_period (c : ℕ) (hc : 0 < c) (hce : Even c) (m : ℤ) (x : ℕ) :
    cexp (π * I * ((c * m + x : ℤ) : ℂ) ^ 2 / c) = cexp (π * I * (x : ℂ) ^ 2 / c) := by
  obtain ⟨a, ha⟩ := hce
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have e : π * I * ((c * m + x : ℤ) : ℂ) ^ 2 / c
      = π * I * (x : ℂ) ^ 2 / c + ((a * m ^ 2 + m * x : ℤ) : ℂ) * (2 * π * I) := by
    have hca : (c : ℂ) = 2 * (a : ℂ) := by rw [ha]; push_cast; ring
    push_cast
    have ha0 : (a : ℂ) ≠ 0 := by
      intro h; apply hc0; rw [hca, h, mul_zero]
    rw [hca]
    field_simp
    ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- First computation of `θ(0, τ)`, `τ = 1/c + i/(c² t)`. -/
lemma stepA (c : ℕ) (hc : 0 < c) (hce : Even c) (t : ℝ) (ht : 0 < t) :
    jacobiTheta₂ 0 (1 / c + I * ((1 / (c ^ 2 * t) : ℝ) : ℂ)) =
      Real.sqrt t * ∑ x ∈ Finset.range c,
        cexp (π * I * (x : ℂ) ^ 2 / c) * jacobiTheta₂ ((x : ℂ) / c) (I * t) := by
  set ε : ℝ := 1 / (c ^ 2 * t) with hε
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hεpos : 0 < ε := by rw [hε]; positivity
  set τ : ℂ := 1 / c + I * ε with hτ
  have hτim : 0 < τ.im := by simp [hτ, hεpos]
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast hεpos.ne'
  have hεt : (c : ℂ) ^ 2 * ε * t = 1 := by
    rw [hε]; push_cast; field_simp
  have hsum : Summable (fun n : ℤ => jacobiTheta₂_term n 0 τ) :=
    (summable_jacobiTheta₂_term_iff 0 τ).2 hτim
  rw [jacobiTheta₂, tsum_split_mod _ hsum c hc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  -- each residue class
  have hterm : ∀ m : ℤ, jacobiTheta₂_term (c * m + x) 0 τ
      = cexp (π * I * (x : ℂ) ^ 2 / c) * cexp (-π * ε * (x : ℂ) ^ 2) *
        jacobiTheta₂_term m (I * c * x * ε) (I * c ^ 2 * ε) := by
    intro m
    have h1 := exp_quad_period c hc hce m x
    rw [jacobiTheta₂_term, jacobiTheta₂_term, ← h1, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [hτ]; push_cast
    field_simp
    ring_nf
    rw [I_sq]; ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hdef : ∑' m : ℤ, jacobiTheta₂_term m (I * c * x * ε) (I * c ^ 2 * ε)
      = jacobiTheta₂ (I * c * x * ε) (I * c ^ 2 * ε) := rfl
  rw [hdef]
  have hτ' : 0 < (I * (c : ℂ) ^ 2 * ε).im := by
    have : (I * (c : ℂ) ^ 2 * ε).im = (c : ℝ) ^ 2 * ε := by
      rw [show I * (c : ℂ) ^ 2 * ε = I * (((c : ℝ) ^ 2 * ε : ℝ) : ℂ) by push_cast; ring,
        Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [this]; exact mul_pos (pow_pos hcR 2) hεpos
  have hfe := jacobiTheta₂_functional_equation (I * c * x * ε) (I * c ^ 2 * ε)
  have hA : (-I * (I * (c : ℂ) ^ 2 * ε)) = ((1 / t : ℝ) : ℂ) := by
    push_cast
    rw [← hεt]; field_simp; ring_nf; rw [I_sq]; ring
  have hB : (-π * I * (I * c * x * ε) ^ 2 / (I * c ^ 2 * ε)) = π * ε * (x : ℂ) ^ 2 := by
    field_simp; ring_nf; simp only [I_sq]; ring
  have hC : (I * c * x * ε) / (I * c ^ 2 * ε) = (x : ℂ) / c := by
    field_simp
  have hD : -1 / (I * (c : ℂ) ^ 2 * ε) = I * t := by
    rw [div_eq_iff (by simp [hc0, hε0])]
    rw [show I * t * (I * (c : ℂ) ^ 2 * ε) = I ^ 2 * ((c : ℂ) ^ 2 * ε * t) by ring, hεt, I_sq]
    ring
  rw [hfe, hA, hB, hC, hD]
  have hsq : ((1 / t : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt (1 / t) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
  rw [hsq, Real.sqrt_div' 1 ht.le, Real.sqrt_one]
  have hexp : cexp (-π * ε * (x : ℂ) ^ 2) * cexp (π * ε * (x : ℂ) ^ 2) = 1 := by
    rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
  push_cast
  simp only [one_div, inv_inv]
  linear_combination (Real.sqrt t * cexp (π * I * (x : ℂ) ^ 2 / c) *
    jacobiTheta₂ ((x : ℂ) / c) (I * t)) * hexp

/-- On the right half-plane the principal square root is multiplicative. -/
lemma cpow_half_mul {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    (u * v) ^ (1 / 2 : ℂ) = u ^ (1 / 2 : ℂ) * v ^ (1 / 2 : ℂ) := by
  have hu0 : u ≠ 0 := fun h => by rw [h] at hu; simp at hu
  have hv0 : v ≠ 0 := fun h => by rw [h] at hv; simp at hv
  rw [cpow_def_of_ne_zero (mul_ne_zero hu0 hv0), cpow_def_of_ne_zero hu0,
    cpow_def_of_ne_zero hv0, ← Complex.exp_add]
  congr 1
  have h1 := abs_arg_lt_pi_div_two_iff.2 (Or.inl hu)
  have h2 := abs_arg_lt_pi_div_two_iff.2 (Or.inl hv)
  rw [abs_lt] at h1 h2
  rw [(log_mul_eq_add_log_iff hu0 hv0).2 ⟨by linarith, by linarith⟩]
  ring

/-- `(-i r)^{1/2} = √r · e^{-iπ/4}` for `r > 0`. -/
lemma cpow_half_negI (r : ℝ) (hr : 0 < r) :
    (-I * r) ^ (1 / 2 : ℂ) = Real.sqrt r * cexp (-(π * I / 4)) := by
  have h0 : (-I * r : ℂ) ≠ 0 := by
    apply mul_ne_zero (neg_ne_zero.2 I_ne_zero); exact_mod_cast hr.ne'
  rw [cpow_def_of_ne_zero h0]
  have hlog : Complex.log (-I * r) = Real.log r + (-(π / 2)) * I := by
    apply Complex.ext
    · rw [Complex.log_re]
      simp [Complex.norm_real, abs_of_pos hr]
    · rw [Complex.log_im, mul_comm, Complex.arg_real_mul _ hr, Complex.arg_neg_I]
      simp
  rw [hlog, show ((Real.log r : ℂ) + -(π / 2) * I) * (1 / 2)
      = ((Real.log r / 2 : ℝ) : ℂ) + (-(π * I / 4)) by push_cast; ring,
    Complex.exp_add, ← Complex.ofReal_exp]
  congr 2
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr]; ring_nf

/-- Second computation of `θ(0, τ)`, `τ = 1/c + i/(c² t)`: two functional equations. -/
lemma stepC (c : ℕ) (hc : 0 < c) (hce : Even c) (t : ℝ) (ht : 0 < t) :
    jacobiTheta₂ 0 (1 / c + I * ((1 / (c ^ 2 * t) : ℝ) : ℂ)) =
      Real.sqrt (c * t) * cexp (π * I / 4) * jacobiTheta₂ 0 (-1 / c + I * t) := by
  set ε : ℝ := 1 / (c ^ 2 * t) with hε
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast hεpos.ne'
  have hεt : (c : ℂ) ^ 2 * ε * t = 1 := by
    rw [hε]; push_cast; field_simp
  set τ : ℂ := 1 / c + I * ε with hτ
  have hτim : 0 < τ.im := by
    rw [hτ, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    simp [hεpos]
  have hτ0 : τ ≠ 0 := fun h => by rw [h] at hτim; simp at hτim
  set w : ℂ := -1 / τ + c with hw
  have hcτ : (c : ℂ) * τ - 1 = I * c * ε := by rw [hτ]; field_simp; ring
  have hw' : w = I * c * ε / τ := by
    rw [hw, ← hcτ]; field_simp; ring
  have hw0 : w ≠ 0 := by
    rw [hw']; exact div_ne_zero (mul_ne_zero (mul_ne_zero I_ne_zero hc0) hε0) hτ0
  have hwim : 0 < w.im := by
    rw [hw, Complex.add_im, Complex.natCast_im, add_zero, neg_div, Complex.neg_im,
      div_im, one_re, one_im]
    simp only [zero_mul, zero_div, sub_zero, zero_sub, neg_neg, one_mul]
    exact div_pos hτim (Complex.normSq_pos.2 hτ0)
  -- functional equation at `τ`
  have h1 := jacobiTheta₂_functional_equation 0 τ
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    Complex.exp_zero, mul_one] at h1
  -- period `c`
  obtain ⟨k, hk⟩ := hce
  have h2 : jacobiTheta₂ 0 (-1 / τ) = jacobiTheta₂ 0 w := by
    rw [hw, show (c : ℂ) = 2 * (k : ℂ) by rw [hk]; push_cast; ring, theta_add_two_mul]
  -- functional equation at `w`
  have h3 := jacobiTheta₂_functional_equation 0 w
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    Complex.exp_zero, mul_one] at h3
  have h4 : -1 / w = -1 / c + I * t := by
    rw [hw', div_div_eq_mul_div, div_eq_iff (mul_ne_zero (mul_ne_zero I_ne_zero hc0) hε0)]
    rw [hτ]
    field_simp
    linear_combination hεt - (c : ℂ) ^ 2 * ε * t * I_sq
  -- the prefactor
  have hre1 : 0 < (-I * τ).re := by
    rw [neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im]; simp [hτim]
  have hre2 : 0 < (-I * w).re := by
    rw [neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im]; simp [hwim]
  have hprod : (-I * τ) * (-I * w) = -I * ((1 / (c * t) : ℝ) : ℂ) := by
    rw [hw']
    field_simp
    push_cast
    field_simp
    linear_combination -hεt + (c : ℂ) ^ 2 * ε * t * I_sq
  have hpre : (-I * τ) ^ (1 / 2 : ℂ) * (-I * w) ^ (1 / 2 : ℂ)
      = Real.sqrt (1 / (c * t)) * cexp (-(π * I / 4)) := by
    rw [← cpow_half_mul hre1 hre2, hprod, cpow_half_negI _ (by positivity)]
  rw [h1, h2, h3, h4]
  have hct : Real.sqrt (1 / (c * t)) * Real.sqrt (c * t) = 1 := by
    rw [← Real.sqrt_mul (by positivity)]; field_simp; simp
  have hexp : cexp (-(π * I / 4)) * cexp (π * I / 4) = 1 := by
    rw [← Complex.exp_add]; simp
  have hA : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by
    intro h; rw [h, zero_mul] at hpre
    have : (Real.sqrt (1 / (c * t)) : ℂ) * cexp (-(π * I / 4)) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne') (Complex.exp_ne_zero _)
    exact this hpre.symm
  have hB : (-I * w) ^ (1 / 2 : ℂ) ≠ 0 := by
    intro h; rw [h, mul_zero] at hpre
    have : (Real.sqrt (1 / (c * t)) : ℂ) * cexp (-(π * I / 4)) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne') (Complex.exp_ne_zero _)
    exact this hpre.symm
  have hctC : (Real.sqrt (1 / (c * t)) : ℂ) * (Real.sqrt (c * t) : ℂ) = 1 := by exact_mod_cast hct
  generalize jacobiTheta₂ 0 (-1 / c + I * t) = Θ
  generalize (-I * τ) ^ (1 / 2 : ℂ) = A at hpre hA ⊢
  generalize (-I * w) ^ (1 / 2 : ℂ) = B at hpre hB ⊢
  have e1 : 1 / A * (1 / B * Θ) = Θ / (A * B) := by field_simp
  rw [e1, hpre, div_eq_iff (by
    exact mul_ne_zero (by exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne')
      (Complex.exp_ne_zero _))]
  linear_combination (-Θ * (cexp (-(π * I / 4)) * cexp (π * I / 4))) * hctC - Θ * hexp

/-- `θ(a, b + i t) → 1` as `t → ∞`, for real `a`, `b` (dominated convergence). -/
lemma tendsto_theta_one (a b : ℝ) :
    Tendsto (fun t : ℝ => jacobiTheta₂ (a : ℂ) ((b : ℂ) + I * t)) atTop (𝓝 1) := by
  have hnorm : ∀ (n : ℤ) (t : ℝ),
      ‖jacobiTheta₂_term n (a : ℂ) ((b : ℂ) + I * t)‖ = rexp (-π * n ^ 2 * t) := by
    intro n t
    rw [norm_jacobiTheta₂_term]
    congr 1
    simp
  have hlim : ∀ n : ℤ, Tendsto (fun t : ℝ => jacobiTheta₂_term n (a : ℂ) ((b : ℂ) + I * t))
      atTop (𝓝 (if n = 0 then 1 else 0)) := by
    intro n
    by_cases hn : n = 0
    · subst hn; simp [jacobiTheta₂_term]
    · rw [if_neg hn, tendsto_zero_iff_norm_tendsto_zero]
      simp_rw [hnorm]
      apply Real.tendsto_exp_atBot.comp
      have hpos : 0 < π * (n : ℝ) ^ 2 := by
        have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
        positivity
      exact tendsto_id.const_mul_atTop_of_neg (by linarith)
  have hsum : Summable (fun n : ℤ => rexp (-π * n ^ 2)) := by
    have h := ((summable_jacobiTheta₂_term_iff 0 I).2 (by simp)).norm
    convert h using 1
    funext n
    rw [norm_jacobiTheta₂_term]
    simp
  have hbound : ∀ᶠ t : ℝ in atTop, ∀ n : ℤ,
      ‖jacobiTheta₂_term n (a : ℂ) ((b : ℂ) + I * t)‖ ≤ rexp (-π * n ^ 2) := by
    filter_upwards [eventually_ge_atTop 1] with t ht n
    rw [hnorm]
    apply Real.exp_le_exp.2
    have : 0 ≤ π * (n : ℝ) ^ 2 := by positivity
    nlinarith
  have h := tendsto_tsum_of_dominated_convergence hsum hlim hbound
  rw [tsum_ite_eq] at h
  exact h

/-- **The quadratic Gauss sum with its sign**, for even moduli:
`∑_{x<c} e^{π i x²/c} = √c · e^{π i/4}`. -/
theorem gauss_sum_even (c : ℕ) (hc : 0 < c) (hce : Even c) :
    ∑ x ∈ Finset.range c, cexp (π * I * (x : ℂ) ^ 2 / c) = Real.sqrt c * cexp (π * I / 4) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hid : ∀ t : ℝ, 0 < t →
      ∑ x ∈ Finset.range c, cexp (π * I * (x : ℂ) ^ 2 / c) * jacobiTheta₂ ((x : ℂ) / c) (I * t)
        = Real.sqrt c * cexp (π * I / 4) * jacobiTheta₂ 0 (-1 / c + I * t) := by
    intro t ht
    have hA := stepA c hc hce t ht
    have hC := stepC c hc hce t ht
    rw [hA, Real.sqrt_mul hcR.le] at hC
    push_cast at hC
    have hst : (Real.sqrt t : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 ht).ne'
    apply mul_left_cancel₀ hst
    linear_combination hC
  have hF : Tendsto (fun t : ℝ => ∑ x ∈ Finset.range c,
      cexp (π * I * (x : ℂ) ^ 2 / c) * jacobiTheta₂ ((x : ℂ) / c) (I * t)) atTop
      (𝓝 (∑ x ∈ Finset.range c, cexp (π * I * (x : ℂ) ^ 2 / c))) := by
    apply tendsto_finsetSum
    intro x _
    have h := (tendsto_theta_one ((x : ℝ) / c) 0).const_mul (cexp (π * I * (x : ℂ) ^ 2 / c))
    rw [mul_one] at h
    convert h using 2 with t
    push_cast; simp
  have hG : Tendsto (fun t : ℝ => (Real.sqrt c : ℂ) * cexp (π * I / 4) *
      jacobiTheta₂ 0 (-1 / c + I * t)) atTop (𝓝 ((Real.sqrt c : ℂ) * cexp (π * I / 4))) := by
    have h := (tendsto_theta_one 0 (-1 / c)).const_mul ((Real.sqrt c : ℂ) * cexp (π * I / 4))
    rw [mul_one] at h
    convert h using 2 with t
    push_cast; ring_nf
  have hF' : Tendsto (fun t : ℝ => (Real.sqrt c : ℂ) * cexp (π * I / 4) *
      jacobiTheta₂ 0 (-1 / c + I * t)) atTop
      (𝓝 (∑ x ∈ Finset.range c, cexp (π * I * (x : ℂ) ^ 2 / c))) := by
    apply hF.congr'
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact hid t ht
  exact tendsto_nhds_unique hF' hG

end

end Conway99
