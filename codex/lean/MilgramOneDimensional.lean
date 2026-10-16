import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Algebra.BigOperators.Fin

/-! Shifted Poisson summation in one dimension, with the shift retained in
the Fourier phase.  All sums are actual analytic sums over the integers. -/

noncomputable section

open scoped BigOperators

namespace Conway99

/-- The shifted Gaussian Poisson identity, including complex shifts. -/
theorem shifted_gaussian_poisson {a : ℂ} (ha : 0 < a.re) (s : ℂ) :
    (∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) * a * ((n : ℂ) + s) ^ 2)) =
      1 / a ^ (1 / 2 : ℂ) *
        ∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) / a * (n : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * s) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  calc
    _ = Complex.exp (-(Real.pi : ℂ) * a * s ^ 2) *
        ∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) * a * (n : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * (-a * s) * (n : ℂ)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [← Complex.exp_add]
      congr 1
      ring
    _ = Complex.exp (-(Real.pi : ℂ) * a * s ^ 2) *
        (1 / a ^ (1 / 2 : ℂ) *
          ∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) / a *
            ((n : ℂ) + Complex.I * (-a * s)) ^ 2)) := by
      rw [Complex.tsum_exp_neg_quadratic ha]
    _ = _ := by
      rw [← mul_assoc, mul_comm (Complex.exp _) _, mul_assoc,
        ← tsum_mul_left]
      congr 1
      apply tsum_congr
      intro n
      rw [← Complex.exp_add]
      congr 1
      field_simp
      ring_nf
      rw [Complex.I_sq]
      ring

/-- The usual theta series of the coset `s + ℤ` in an orthogonal line
of squared generator length `m`. -/
def orthogonalLineTheta (m : ℝ) (s z : ℂ) : ℂ :=
  ∑' n : ℤ, Complex.exp ((Real.pi : ℂ) * Complex.I * z * m *
    ((n : ℂ) + s) ^ 2)

/-- Poisson transformation of an orthogonal line, in Fourier-series form.
No discriminant-group or finite-sum hypothesis is assumed. -/
theorem orthogonalLineTheta_poisson {m : ℝ} (hm : 0 < m)
    (s : ℂ) {z : ℂ} (hz : 0 < z.im) :
    orthogonalLineTheta m s z =
      1 / (-Complex.I * z * m) ^ (1 / 2 : ℂ) *
        ∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) / (-Complex.I * z * m) *
          (n : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * s) := by
  have hpos : 0 < (-Complex.I * z * (m : ℂ)).re := by
    simpa [Complex.mul_re, Complex.mul_im] using mul_pos hz hm
  convert shifted_gaussian_poisson hpos s using 1
  unfold orthogonalLineTheta
  apply tsum_congr
  intro n
  congr 1
  ring

/-- Absolute convergence of the shifted-line theta sum. -/
theorem orthogonalLineTheta_summable {m : ℝ} (hm : 0 < m)
    (s : ℂ) {z : ℂ} (hz : 0 < z.im) :
    Summable (fun n : ℤ => Complex.exp ((Real.pi : ℂ) * Complex.I * z * m *
      ((n : ℂ) + s) ^ 2)) := by
  have hpos : 0 < ((m : ℂ) * z).im := by
    simpa using mul_pos hm hz
  have hs := ((summable_jacobiTheta₂_term_iff ((m : ℂ) * z * s)
    ((m : ℂ) * z)).mpr hpos).mul_left
      (Complex.exp ((Real.pi : ℂ) * Complex.I * z * m * s ^ 2))
  apply hs.congr
  intro n
  unfold jacobiTheta₂_term
  rw [← Complex.exp_add]
  congr 1
  ring

/-- Euclidean-division reindexing of the integer line by residue and quotient. -/
def integerResidueEquiv (M : ℕ) (hM : 0 < M) : ℤ ≃ Fin M × ℤ where
  toFun n := (⟨(n % (M : ℤ)).toNat, by
    have h0 := Int.emod_nonneg n (by omega : (M : ℤ) ≠ 0)
    have hlt := Int.emod_lt_of_pos n (by omega : (0 : ℤ) < M)
    omega⟩, n / M)
  invFun p := (p.1.val : ℤ) + (M : ℤ) * p.2
  left_inv n := by
    have h0 := Int.emod_nonneg n (by omega : (M : ℤ) ≠ 0)
    have he := Int.emod_add_mul_ediv n (M : ℤ)
    dsimp
    omega
  right_inv p := by
    obtain ⟨⟨r, hr⟩, q⟩ := p
    apply Prod.ext
    · apply Fin.ext
      dsimp
      have hmod : ((r : ℤ) + (M : ℤ) * q) % M = r := by
        rw [Int.add_mul_emod_self_left,
          Int.emod_eq_of_lt (by omega) (by omega)]
      rw [hmod]
      simp
    · dsimp
      rw [Int.add_mul_ediv_left _ _ (by omega : (M : ℤ) ≠ 0),
        Int.ediv_eq_zero_of_lt (by omega) (by omega), zero_add]

/-- Partition a genuinely convergent integer sum into all residue classes. -/
theorem integer_tsum_by_residues {M : ℕ} (hM : 0 < M)
    {f : ℤ → ℂ} (hf : Summable f) :
    (∑' n : ℤ, f n) =
      ∑ r : Fin M, ∑' q : ℤ, f ((r.val : ℤ) + (M : ℤ) * q) := by
  let e := integerResidueEquiv M hM
  rw [← e.symm.tsum_eq f]
  have hs : Summable (fun p : Fin M × ℤ => f (e.symm p)) :=
    hf.comp_injective e.symm.injective
  rw [hs.tsum_prod, tsum_fintype]
  rfl

theorem quadraticGaussian_summable {a : ℂ} (ha : 0 < a.re) (b : ℂ) :
    Summable (fun n : ℤ => Complex.exp (-(Real.pi : ℂ) * a * (n : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * b * (n : ℂ))) := by
  have hpos : 0 < (Complex.I * a).im := by simpa using ha
  have hs := (summable_jacobiTheta₂_term_iff (-Complex.I * b)
    (Complex.I * a)).mpr hpos
  apply hs.congr
  intro n
  unfold jacobiTheta₂_term
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Finite discriminant Fourier transformation for a rank-one lattice
of positive integral squared length `M`.  The formula is valid even when
`M` is odd; evenness is needed only for the separate T-transformation. -/
theorem orthogonalLineTheta_finite_poisson {M : ℕ} (hM : 0 < M)
    (l : ℤ) {z : ℂ} (hz : 0 < z.im) :
    orthogonalLineTheta M ((l : ℂ) / M) z =
      1 / (-Complex.I * z * M) ^ (1 / 2 : ℂ) *
        ∑ r : Fin M, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * r.val * l / M) *
          orthogonalLineTheta M ((r.val : ℂ) / M) (-1 / z) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hm0 : (M : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  let a : ℂ := -Complex.I * z * M
  have ha : 0 < a.re := by
    simpa [a, Complex.mul_re, Complex.mul_im] using mul_pos hz hm
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hi : 0 < (a⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos ha (Complex.normSq_pos.mpr ha0)
  rw [orthogonalLineTheta_poisson hm _ hz]
  congr 1
  have hs := quadraticGaussian_summable hi (Complex.I * ((l : ℂ) / M))
  have hs' : Summable (fun n : ℤ => Complex.exp (-(Real.pi : ℂ) / a *
      (n : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((l : ℂ) / M))) := by
    convert hs using 1
    ext n
    congr 1
    ring
  change (∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) / a *
    (n : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((l : ℂ) / M))) = _
  rw [integer_tsum_by_residues hM hs']
  apply Finset.sum_congr rfl
  intro r _
  unfold orthogonalLineTheta
  rw [← tsum_mul_left]
  apply tsum_congr
  intro q
  push_cast
  have heq : -(Real.pi : ℂ) / a * ((r.val : ℂ) + (M : ℂ) * q) ^ 2 +
      2 * (Real.pi : ℂ) * Complex.I * ((r.val : ℂ) + (M : ℂ) * q) *
        ((l : ℂ) / M) =
      2 * (Real.pi : ℂ) * Complex.I * r.val * l / M +
      (Real.pi : ℂ) * Complex.I * (-1 / z) * M *
        ((q : ℂ) + (r.val : ℂ) / M) ^ 2 +
      (q * l : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    dsimp [a]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [heq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
    Complex.exp_add]

/-- Multiplication by a positive real does not cross a complex-power branch cut. -/
theorem cpow_mul_positive_real (c : ℂ) (hc : c ≠ 0)
    {m : ℝ} (hm : 0 < m) (t : ℂ) :
    (c * m) ^ t = c ^ t * (m : ℂ) ^ t := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hc hm0),
    Complex.cpow_def_of_ne_zero hc, Complex.cpow_def_of_ne_zero hm0,
    Complex.log_mul_ofReal m hm c hc, Complex.ofReal_log hm.le]
  rw [add_mul, Complex.exp_add]
  ring

/-- All 44 square-root automorphy factors combine into an ordinary
integer power.  No arbitrary square-root sign or branch choice remains. -/
theorem rank44_poisson_factor (c : ℂ) (hc : c ≠ 0)
    (m : Fin 44 → ℝ) (hm : ∀ i, 0 < m i) :
    (∏ i, 1 / (c * m i) ^ (1 / 2 : ℂ)) =
      1 / (c ^ 22 * ∏ i, (m i : ℂ) ^ (1 / 2 : ℂ)) := by
  simp_rw [cpow_mul_positive_real c hc (hm _) (1 / 2 : ℂ)]
  rw [Finset.prod_div_distrib, Finset.prod_const_one, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 2
  calc
    (c ^ (1 / 2 : ℂ)) ^ 44 = ((c ^ (1 / 2 : ℂ)) ^ 2) ^ 22 := by
      rw [← pow_mul]
    _ = c ^ 22 := by
      have hsq : (c ^ (1 / 2 : ℂ)) ^ 2 = c := by
        simpa using Complex.cpow_nat_inv_pow c (by norm_num : (2 : ℕ) ≠ 0)
      rw [hsq]

theorem orthogonal_volume_square (n : ℕ) (M : Fin n → ℕ) :
    (∏ i, (M i : ℂ) ^ (1 / 2 : ℂ)) ^ 2 =
      (Fintype.card (∀ i, Fin (M i)) : ℂ) := by
  rw [← Finset.prod_pow, Fintype.card_pi]
  push_cast
  apply Finset.prod_congr rfl
  intro i _
  simpa using Complex.cpow_nat_inv_pow (M i : ℂ) (by norm_num : (2 : ℕ) ≠ 0)

theorem orthogonal_volume_ne_zero (n : ℕ) (M : Fin n → ℕ)
    (hM : ∀ i, 0 < M i) :
    (∏ i, (M i : ℂ) ^ (1 / 2 : ℂ)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Complex.cpow_ne_zero_iff.mpr
  left
  exact_mod_cast (ne_of_gt (hM i))

/-- Actual 44-line theta products satisfy a finite discriminant Fourier
identity with the integer-weight automorphy factor.  The finite discriminant
is the full dependent product of the 44 cyclic residue sets. -/
theorem orthogonal44_finite_poisson (M : Fin 44 → ℕ)
    (hM : ∀ i, 0 < M i) (l : Fin 44 → ℤ) {z : ℂ} (hz : 0 < z.im) :
    (∏ i, orthogonalLineTheta (M i) ((l i : ℂ) / M i) z) =
      1 / ((-Complex.I * z) ^ 22 * ∏ i, (M i : ℂ) ^ (1 / 2 : ℂ)) *
        ∑ r : ∀ i, Fin (M i),
          (∏ i, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (r i).val * l i / M i)) *
          ∏ i, orthogonalLineTheta (M i) (((r i).val : ℂ) / M i) (-1 / z) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hc : -Complex.I * z ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hz0
  calc
    _ = ∏ i, (1 / (-Complex.I * z * M i) ^ (1 / 2 : ℂ)) *
        ∑ r : Fin (M i), Complex.exp (2 * (Real.pi : ℂ) * Complex.I * r.val * l i / M i) *
          orthogonalLineTheta (M i) ((r.val : ℂ) / M i) (-1 / z) := by
      apply Finset.prod_congr rfl
      intro i _
      exact orthogonalLineTheta_finite_poisson (hM i) (l i) hz
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      have hf := rank44_poisson_factor (-Complex.I * z) hc
        (fun i => (M i : ℝ)) (fun i => by
          dsimp
          exact_mod_cast hM i)
      simp only [Complex.ofReal_natCast] at hf
      rw [hf, Fintype.prod_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.prod_mul_distrib]

/-- Forward S-transformation in rank 44, already in the integer-weight
normalization needed by the Milgram three-point cycle. -/
theorem orthogonal44_S (M : Fin 44 → ℕ) (hM : ∀ i, 0 < M i)
    (l : Fin 44 → ℤ) {z : ℂ} (hz : 0 < z.im) :
    (∏ i, orthogonalLineTheta (M i) ((l i : ℂ) / M i) (-1 / z)) =
      ((-Complex.I * z) ^ 22 / ∏ i, (M i : ℂ) ^ (1 / 2 : ℂ)) *
        ∑ r : ∀ i, Fin (M i),
          (∏ i, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (r i).val * l i / M i)) *
          ∏ i, orthogonalLineTheta (M i) (((r i).val : ℂ) / M i) z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hz' : 0 < (-(1 : ℂ) / z).im := by
    simp only [neg_div, one_div, Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos hz (Complex.normSq_pos.mpr hz0)
  have hdouble : -(1 : ℂ) / (-(1 : ℂ) / z) = z := by field_simp
  have hfactor : -Complex.I * (-(1 : ℂ) / z) = (-Complex.I * z)⁻¹ := by
    apply mul_right_cancel₀ (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hz0)
    rw [inv_mul_cancel₀ (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hz0)]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have hs := orthogonal44_finite_poisson M hM l hz'
  rw [hdouble, hfactor] at hs
  have hcoeff : 1 / (((-Complex.I * z)⁻¹) ^ 22 *
      ∏ i, (M i : ℂ) ^ (1 / 2 : ℂ)) =
      (-Complex.I * z) ^ 22 / (∏ i, (M i : ℂ) ^ (1 / 2 : ℂ)) := by
    rw [inv_pow]
    simp only [one_div, mul_inv_rev, inv_inv, div_eq_mul_inv]
    ring
  rw [hcoeff] at hs
  exact hs

/-- Fubini for a finite product of absolutely convergent complex series,
with the full integer tuple as the summation index. -/
theorem finite_integer_product_tsum (n : ℕ) (f : Fin n → ℤ → ℂ)
    (hf : ∀ i, Summable (fun k => ‖f i k‖)) :
    Summable (fun x : Fin n → ℤ => ‖∏ i, f i (x i)‖) ∧
      (∑' x : Fin n → ℤ, ∏ i, f i (x i)) = ∏ i, ∑' k : ℤ, f i k := by
  induction n with
  | zero =>
    constructor
    · exact (hasSum_fintype _).summable
    · simp
  | succ n ih =>
    obtain ⟨hgnorm, hgvalue⟩ := ih (fun i => f i.succ) (fun i => hf i.succ)
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)
    have hpair := (hf 0).mul_norm hgnorm
    have hfull : Summable (fun x : Fin (n + 1) → ℤ => ‖∏ i, f i (x i)‖) := by
      have hh := hpair.comp_injective e.symm.injective
      convert hh using 1
      ext x
      simp [e, Fin.prod_univ_succ, Fin.consEquiv, Fin.tail]
    refine ⟨hfull, ?_⟩
    rw [← e.tsum_eq]
    simp only [e, Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ]
    rw [← tsum_mul_tsum_of_summable_norm (hf 0) hgnorm, hgvalue]

/-- The theta product is literally the convergent sum over all integer
coordinates of the orthogonal lattice, not an abstract surrogate. -/
theorem orthogonal_theta_product_eq_tsum (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, 0 < m i) (s : Fin n → ℂ) {z : ℂ} (hz : 0 < z.im) :
    (∏ i, orthogonalLineTheta (m i) (s i) z) =
      ∑' x : Fin n → ℤ, Complex.exp ((Real.pi : ℂ) * Complex.I * z *
        ∑ i, (m i : ℂ) * ((x i : ℂ) + s i) ^ 2) := by
  have hf : ∀ i, Summable (fun k : ℤ =>
      ‖Complex.exp ((Real.pi : ℂ) * Complex.I * z * m i * ((k : ℂ) + s i) ^ 2)‖) := by
    intro i
    exact summable_norm_iff.mpr (orthogonalLineTheta_summable (hm i) (s i) hz)
  rw [show (∏ i, orthogonalLineTheta (m i) (s i) z) =
      ∏ i, ∑' k : ℤ, Complex.exp ((Real.pi : ℂ) * Complex.I * z * m i *
        ((k : ℂ) + s i) ^ 2) from rfl]
  rw [← (finite_integer_product_tsum n _ hf).2]
  apply tsum_congr
  intro x
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem orthogonalLineTheta_neg_shift (m : ℝ) (s z : ℂ) :
    orthogonalLineTheta m (-s) z = orthogonalLineTheta m s z := by
  unfold orthogonalLineTheta
  rw [← (Equiv.neg ℤ).tsum_eq]
  apply tsum_congr
  intro n
  simp only [Equiv.neg_apply, Int.cast_neg]
  congr 1
  ring

theorem orthogonalLineTheta_shift_int (m : ℝ) (s z : ℂ) (k : ℤ) :
    orthogonalLineTheta m (s + k) z = orthogonalLineTheta m s z := by
  unfold orthogonalLineTheta
  calc
    _ = ∑' n : ℤ, Complex.exp ((Real.pi : ℂ) * Complex.I * z * m *
        (((n + k : ℤ) : ℂ) + s) ^ 2) := by
      apply tsum_congr
      intro n
      push_cast
      congr 1
      ring
    _ = _ := (Equiv.addRight k).tsum_eq (fun n : ℤ =>
      Complex.exp ((Real.pi : ℂ) * Complex.I * z * m * ((n : ℂ) + s) ^ 2))

/-- At i every real-shifted orthogonal theta component is strictly positive. -/
theorem orthogonalLineTheta_I_re_pos {m : ℝ} (hm : 0 < m) (s : ℝ) :
    0 < (orthogonalLineTheta m s Complex.I).re := by
  have ht (n : ℤ) : Complex.exp ((Real.pi : ℂ) * Complex.I * Complex.I * m *
      ((n : ℂ) + (s : ℂ)) ^ 2) =
      (Real.exp (-Real.pi * m * ((n : ℝ) + s) ^ 2) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hs := orthogonalLineTheta_summable hm (s : ℂ) (z := Complex.I) (by simp)
  have hreal : Summable (fun n : ℤ => Real.exp (-Real.pi * m * ((n : ℝ) + s) ^ 2)) := by
    have hr := (Complex.hasSum_re hs.hasSum).summable
    simpa only [ht, Complex.ofReal_re] using hr
  unfold orthogonalLineTheta
  rw [Complex.re_tsum hs]
  simp only [ht, Complex.ofReal_re]
  exact hreal.tsum_pos (fun _ => (Real.exp_pos _).le) 0 (Real.exp_pos _)

theorem orthogonalLineTheta_I_ne_zero {m : ℝ} (hm : 0 < m) (s : ℝ) :
    orthogonalLineTheta m s Complex.I ≠ 0 := by
  intro h
  have hp := orthogonalLineTheta_I_re_pos hm s
  rw [h, Complex.zero_re] at hp
  exact (lt_irrefl 0) hp

theorem orthogonal_theta_product_I_ne_zero (n : ℕ) (m s : Fin n → ℝ)
    (hm : ∀ i, 0 < m i) :
    (∏ i, orthogonalLineTheta (m i) (s i) Complex.I) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact orthogonalLineTheta_I_ne_zero (hm i) (s i)

theorem orthogonal_theta_product_neg_shift (n : ℕ) (m : Fin n → ℝ)
    (s : Fin n → ℂ) (z : ℂ) :
    (∏ i, orthogonalLineTheta (m i) (-s i) z) =
      ∏ i, orthogonalLineTheta (m i) (s i) z := by
  apply Finset.prod_congr rfl
  intro i _
  exact orthogonalLineTheta_neg_shift (m i) (s i) z

/-- T-transformation for the even rank-one lattice of squared length `2a`.
This identifies its actual finite discriminant quadratic phase. -/
theorem orthogonalLineTheta_add_one {a : ℕ} (ha : 0 < a)
    (l : ℤ) (z : ℂ) :
    orthogonalLineTheta (2 * a) ((l : ℂ) / (2 * a)) (z + 1) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * (l : ℂ) ^ 2 / (2 * a)) *
        orthogonalLineTheta (2 * a) ((l : ℂ) / (2 * a)) z := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
  unfold orthogonalLineTheta
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  push_cast
  have heq : (Real.pi : ℂ) * Complex.I * (z + 1) * (2 * a) *
      ((n : ℂ) + (l : ℂ) / (2 * a)) ^ 2 =
      (Real.pi : ℂ) * Complex.I * (l : ℂ) ^ 2 / (2 * a) +
      (Real.pi : ℂ) * Complex.I * z * (2 * a) *
        ((n : ℂ) + (l : ℂ) / (2 * a)) ^ 2 +
      ((a : ℤ) * n ^ 2 + l * n : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    field_simp
    ring
  rw [heq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
    Complex.exp_add]

#print axioms shifted_gaussian_poisson
#print axioms orthogonalLineTheta_poisson
#print axioms orthogonalLineTheta_summable
#print axioms integer_tsum_by_residues
#print axioms orthogonalLineTheta_finite_poisson
#print axioms orthogonalLineTheta_add_one
#print axioms rank44_poisson_factor
#print axioms orthogonal_volume_square
#print axioms orthogonal44_finite_poisson
#print axioms orthogonal44_S
#print axioms orthogonal_theta_product_eq_tsum
#print axioms orthogonalLineTheta_I_ne_zero
#print axioms orthogonal_theta_product_I_ne_zero

end Conway99
