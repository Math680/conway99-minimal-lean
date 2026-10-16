import MilgramOneDimensional
import MilgramCyclicPhase
import MilgramMonodromy

noncomputable section
open scoped BigOperators

namespace Conway99.DiagonalTheta

def line (M : ℕ) (r : ZMod M) (z : ℂ) : ℂ :=
  orthogonalLineTheta M ((r.val : ℂ) / M) z

theorem line_neg (M : ℕ) [NeZero M] (r : ZMod M) (z : ℂ) :
    line M (-r) z = line M r z := by
  obtain ⟨k, hk⟩ := CyclicPhase.neg_val_div M r
  unfold line
  rw [hk, orthogonalLineTheta_shift_int, neg_div,
    orthogonalLineTheta_neg_shift]

theorem line_add_one (M : ℕ) [NeZero M] (hM : Even M) (r : ZMod M) (z : ℂ) :
    line M r (z + 1) = CyclicPhase.phase M r * line M r z := by
  obtain ⟨a, ha⟩ := hM
  have hMa : M = 2 * a := by omega
  have ha0 : 0 < a := by have := NeZero.ne M; omega
  subst M
  simpa [line, CyclicPhase.phase, CyclicPhase.intPhase, two_mul] using
    orthogonalLineTheta_add_one ha0 (r.val : ℤ) z

theorem line_I_ne_zero (M : ℕ) [NeZero M] (r : ZMod M) :
    line M r Complex.I ≠ 0 := by
  have hm : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hh := orthogonalLineTheta_I_ne_zero hm ((r.val : ℝ) / M)
  simpa only [line, Complex.ofReal_div, Complex.ofReal_natCast] using hh

variable (M : Fin 44 → ℕ) [∀ i, NeZero (M i)]

def theta (r : DiagonalPhase.Discriminant M) (z : ℂ) : ℂ :=
  ∏ i, line (M i) (r i) z

def volume : ℂ := ∏ i, (M i : ℂ) ^ (1 / 2 : ℂ)

theorem volume_ne_zero : volume M ≠ 0 :=
  orthogonal_volume_ne_zero 44 M (fun i => Nat.pos_of_ne_zero (NeZero.ne (M i)))

theorem volume_sq : (volume M) ^ 2 =
    (Fintype.card (DiagonalPhase.Discriminant M) : ℂ) := by
  unfold volume
  rw [← Finset.prod_pow, Fintype.card_pi]
  push_cast
  apply Finset.prod_congr rfl
  intro i _
  simpa using Complex.cpow_nat_inv_pow (M i : ℂ) (by norm_num : (2 : ℕ) ≠ 0)

theorem volume_eq_sqrt_card : volume M =
    (Real.sqrt (Fintype.card (DiagonalPhase.Discriminant M) : ℝ) : ℂ) := by
  let p : ℝ := ∏ i, Real.sqrt (M i : ℝ)
  have hvol : volume M = (p : ℂ) := by
    unfold volume p
    push_cast
    apply Finset.prod_congr rfl
    intro i _
    simpa [Real.sqrt_eq_rpow] using
      (Complex.ofReal_cpow (Nat.cast_nonneg (M i)) (1 / 2 : ℝ)).symm
  have hp : 0 ≤ p := Finset.prod_nonneg (fun i _ => Real.sqrt_nonneg _)
  have hs : p ^ 2 = (Fintype.card (DiagonalPhase.Discriminant M) : ℝ) := by
    have hh := volume_sq M
    rw [hvol] at hh
    exact_mod_cast hh
  have he := (Real.sqrt_eq_iff_eq_sq (Nat.cast_nonneg _) hp).mpr hs.symm
  rw [hvol, he]

theorem theta_neg (r : DiagonalPhase.Discriminant M) (z : ℂ) :
    theta M (-r) z = theta M r z := by
  unfold theta
  apply Finset.prod_congr rfl
  intro i _
  exact line_neg (M i) (r i) z

theorem theta_add_one (hM : ∀ i, Even (M i))
    (r : DiagonalPhase.Discriminant M) (z : ℂ) :
    theta M r (z + 1) = DiagonalPhase.phase M r * theta M r z := by
  unfold theta DiagonalPhase.phase
  simp_rw [line_add_one _ (hM _)]
  exact Finset.prod_mul_distrib

theorem theta_I_ne_zero (r : DiagonalPhase.Discriminant M) :
    theta M r Complex.I ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact line_I_ne_zero (M i) (r i)

theorem theta_S (r : DiagonalPhase.Discriminant M)
    {z : ℂ} (hz : 0 < z.im) :
    theta M r (-1 / z) = ((-Complex.I * z) ^ 22 / volume M) *
      ∑ b, DiagonalPhase.pairing M r b * theta M b z := by
  have hs := orthogonal44_S M (fun i => Nat.pos_of_ne_zero (NeZero.ne (M i)))
    (fun i => ((r i).val : ℤ)) hz
  simp only [Int.cast_natCast] at hs
  have hsum :
      (∑ b : ∀ i, Fin (M i),
        (∏ i, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b i).val * (r i).val / M i)) *
          ∏ i, orthogonalLineTheta (M i) (((b i).val : ℂ) / M i) z) =
        ∑ b, DiagonalPhase.pairing M (-r) b * theta M b z := by
    rw [← DiagonalPhase.sum_finEquiv M (fun b =>
      DiagonalPhase.pairing M (-r) b * theta M b z)]
    apply Finset.sum_congr rfl
    intro b _
    simp only [DiagonalPhase.positive_pairing_exp_val, theta, line,
      DiagonalPhase.finEquiv_val]
  rw [hsum, DiagonalPhase.positive_fourier_eq_negative M r (fun b => theta M b z)
    (fun b => theta_neg M b z)] at hs
  exact hs

def fourier : (DiagonalPhase.Discriminant M → ℂ) →ₗ[ℂ]
    (DiagonalPhase.Discriminant M → ℂ) :=
  normalizedTwistedFourier (DiagonalPhase.phase M) (DiagonalPhase.pairing M) (volume M)

theorem theta_ST (hM : ∀ i, Even (M i)) {z : ℂ} (hz : 0 < z.im) :
    (fun r => theta M r (-1 / (z + 1))) =
      (-Complex.I * (z + 1)) ^ 22 • fourier M (fun r => theta M r z) := by
  funext r
  rw [theta_S M r (by simpa using hz : 0 < (z + 1).im)]
  simp only [theta_add_one M hM]
  change _ = (-Complex.I * (z + 1)) ^ 22 * ((volume M)⁻¹ *
    ∑ b, DiagonalPhase.pairing M r b * DiagonalPhase.phase M b * theta M b z)
  simp only [mul_assoc, div_eq_mul_inv]

private theorem cycle_one : -(1 : ℂ) / (Complex.I + 1) = (-1 + Complex.I) / 2 := by
  apply Complex.ext <;>
    norm_num [Complex.div_re, Complex.div_im, Complex.normSq, Complex.add_re, Complex.add_im]

private theorem cycle_two :
    -(1 : ℂ) / (((-1 + Complex.I) / 2) + 1) = -1 + Complex.I := by
  apply Complex.ext <;>
    norm_num [Complex.div_re, Complex.div_im, Complex.normSq, Complex.add_re, Complex.add_im]

private theorem cycle_three : -(1 : ℂ) / ((-1 + Complex.I) + 1) = Complex.I := by
  apply Complex.ext <;>
    norm_num [Complex.div_re, Complex.div_im, Complex.normSq, Complex.add_re, Complex.add_im]

private theorem factor_one : -Complex.I * (Complex.I + 1) = 1 - Complex.I := by
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem factor_two :
    -Complex.I * (((-1 + Complex.I) / 2) + 1) = (1 - Complex.I) / 2 := by
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem factor_three : -Complex.I * ((-1 + Complex.I) + 1) = 1 := by
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Milgram's exact negative sign for every positive even diagonal lattice
of rank 44.  The Gauss sum is the actual finite sum on its cyclic discriminant,
and every analytic transformation premise has been discharged above. -/
theorem normalized_gauss_eq_neg_one (hM : ∀ i, Even (M i)) :
    (∑ r, DiagonalPhase.phase M r) / volume M = -1 := by
  let R := fourier M
  let u₀ : DiagonalPhase.Discriminant M → ℂ := fun r => theta M r Complex.I
  let u₁ : DiagonalPhase.Discriminant M → ℂ := fun r => theta M r ((-1 + Complex.I) / 2)
  let u₂ : DiagonalPhase.Discriminant M → ℂ := fun r => theta M r (-1 + Complex.I)
  let γ := (∑ r, DiagonalPhase.phase M r) / volume M
  have h₁ : u₁ = (1 - Complex.I) ^ 22 • R u₀ := by
    have hh := theta_ST M hM (z := Complex.I) (by simp)
    simpa only [cycle_one, factor_one] using hh
  have h₂ : u₂ = ((1 - Complex.I) / 2) ^ 22 • R u₁ := by
    have hz : 0 < (((-1 + Complex.I) / 2) : ℂ).im := by
      norm_num [Complex.div_im, Complex.normSq]
    have hh := theta_ST M hM hz
    simpa only [cycle_two, factor_two] using hh
  have h₃ : u₀ = R u₂ := by
    have hh := theta_ST M hM (z := -1 + Complex.I) (by simp)
    simpa only [cycle_three, factor_three, one_pow, one_smul] using hh
  have hGauss : R (R (R u₀)) = γ • u₀ := by
    have hh := DiagonalPhase.normalized_fourier_cube M hM (volume M)
      (volume_ne_zero M) (volume_sq M).symm u₀
    have hreflect : (fun r => u₀ (-r)) = u₀ := by
      funext r
      exact theta_neg M r Complex.I
    rw [hreflect] at hh
    exact hh
  have hu : u₀ ≠ 0 := by
    intro hh
    exact theta_I_ne_zero M 0 (congrFun hh 0)
  exact milgram44_from_three_point_cycle R u₀ u₁ u₂ γ h₁ h₂ h₃ hGauss hu

theorem normalized_gauss_sqrt_card_eq_neg_one (hM : ∀ i, Even (M i)) :
    (∑ r, DiagonalPhase.phase M r) /
      (Real.sqrt (Fintype.card (DiagonalPhase.Discriminant M) : ℝ) : ℂ) = -1 := by
  rw [← volume_eq_sqrt_card M]
  exact normalized_gauss_eq_neg_one M hM

#print axioms normalized_gauss_eq_neg_one
#print axioms normalized_gauss_sqrt_card_eq_neg_one

#print axioms theta_S
#print axioms theta_ST

#print axioms theta_add_one
#print axioms theta_I_ne_zero

end Conway99.DiagonalTheta
