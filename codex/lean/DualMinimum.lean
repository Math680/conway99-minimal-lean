import IntegerEigenMinimum
import LatticeLift

/-! The minimum of the actual canonical dual, and the integral code of a root. -/

namespace Conway99

open scoped BigOperators Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem codePair_integer_norm (x : V → ℚ) (z : V → ℤ)
    (hz : ∀ u, x u = (z u : ℚ)) :
    63 * codePair x x = ((∑ u, z u ^ 2 : ℤ) : ℚ) := by
  simp only [codePair, dotProduct]
  have he : (∑ u, x u * x u) = ((∑ u, z u ^ 2 : ℤ) : ℚ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro u _
    rw [hz]
    ring
  rw [he]
  ring

theorem nonzero_common_residue_norm_bound (hcard : Fintype.card V = 99)
    (z : V → ℤ) (r : ℤ) (hz : ∀ u, z u % 3 = r % 3)
    (hr : r % 3 ≠ 0) (hs : ∑ u, z u = 0) : 198 ≤ ∑ u, z u ^ 2 := by
  have hres : r % 3 = 1 ∨ r % 3 = 2 := by omega
  have hcalc (e : ℤ) (he : e = 1 ∨ e = -1)
      (heq : ∀ u, z u % 3 = e % 3) : 198 ≤ ∑ u, z u ^ 2 := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset V))
      (fun u _ => nonzero_residue_square (z u) e he (heq u))
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hs, mul_zero, add_zero,
      Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul] at hh
    norm_num at hh
    exact hh
  rcases hres with hh | hh
  · exact hcalc 1 (Or.inl rfl) (fun u => by rw [hz u, hh]; norm_num)
  · exact hcalc (-1) (Or.inr rfl) (fun u => by rw [hz u, hh]; norm_num)

theorem canonicalDual_divide_coordinates (h : G.IsSRGWith 99 14 1 2)
    {x : V → ℚ} (hx : IsCanonicalDual G x) (z : V → ℤ)
    (hz : ∀ u, x u = (z u : ℚ)) (hdiv : ∀ u, 3 ∣ z u) :
    ∃ b : V → ℤ, x = (3 : ℚ) • (fun u => (b u : ℚ)) ∧
      (fun u => (b u : ℚ)) ∈ rationalAmbient G ∧
      (∑ u, z u ^ 2) = 9 * ∑ u, b u ^ 2 := by
  choose b hb using hdiv
  have hxb : x = (3 : ℚ) • (fun u => (b u : ℚ)) := by
    ext u
    simpa only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_ofNat] using
      (hz u).trans (by exact_mod_cast hb u)
  refine ⟨b, hxb, ?_, ?_⟩
  · have hh := (rationalAmbient G).smul_mem (1 / 3 : ℚ) hx.1
    rw [hxb, smul_smul] at hh
    norm_num at hh
    exact hh
  · simp_rw [hb, mul_pow]
    rw [← Finset.mul_sum]
    norm_num

theorem canonicalDual_minimum_two (h : G.IsSRGWith 99 14 1 2)
    {x : V → ℚ} (hx : IsCanonicalDual G x) (hx0 : x ≠ 0) : 2 ≤ codePair x x := by
  obtain ⟨z, hz⟩ := canonicalDual_integer_coordinates G h hx
  have hs : ∑ u, z u = 0 := by
    have hh := rationalAmbient_sum_zero G h hx.1
    simp_rw [hz] at hh
    exact_mod_cast hh
  have hn := codePair_integer_norm x z hz
  let u₀ : V := Classical.choice (Fintype.card_pos_iff.mp (by rw [h.card]; norm_num))
  have hres := canonicalDual_common_residue G h hx z hz
  by_cases hr : z u₀ % 3 = 0
  · have hd : ∀ u, 3 ∣ z u := fun u => Int.dvd_of_emod_eq_zero (by rw [hres u u₀, hr])
    obtain ⟨b, hxb, hbE, hbn⟩ := canonicalDual_divide_coordinates G h hx z hz hd
    have hb0 : b ≠ 0 := by
      intro he
      apply hx0
      rw [hxb]
      ext u
      simp [he]
    have hmin := integerAmbient_minimum_fourteen G h b hb0 hbE
    have hminq : (14 : ℚ) ≤ ((∑ u, b u ^ 2 : ℤ) : ℚ) := by exact_mod_cast hmin
    have hbnq : ((∑ u, z u ^ 2 : ℤ) : ℚ) =
        9 * ((∑ u, b u ^ 2 : ℤ) : ℚ) := by exact_mod_cast hbn
    linarith
  · have hm := nonzero_common_residue_norm_bound h.card z (z u₀)
      (fun u => hres u u₀) hr hs
    have hmq : (198 : ℚ) ≤ ((∑ u, z u ^ 2 : ℤ) : ℚ) := by exact_mod_cast hm
    linarith

theorem canonicalDual_root_integral_code (h : G.IsSRGWith 99 14 1 2)
    {x : V → ℚ} (hx : IsCanonicalDual G x) (hn : codePair x x = 2) :
    ∃ b : V → ℤ, x = (3 : ℚ) • (fun u => (b u : ℚ)) ∧
      (fun u => (b u : ℚ)) ∈ rationalAmbient G ∧
      (∑ u, b u = 0) ∧ (∑ u, b u ^ 2 = 14) ∧
      (∀ u, b u = -1 ∨ b u = 0 ∨ b u = 1) := by
  obtain ⟨z, hz⟩ := canonicalDual_integer_coordinates G h hx
  have hs : ∑ u, z u = 0 := by
    have hh := rationalAmbient_sum_zero G h hx.1
    simp_rw [hz] at hh
    exact_mod_cast hh
  have hnorm : ∑ u, z u ^ 2 = 126 := by
    have hh := codePair_integer_norm x z hz
    rw [hn] at hh
    exact_mod_cast hh.symm
  let u₀ : V := Classical.choice (Fintype.card_pos_iff.mp (by rw [h.card]; norm_num))
  have hres := canonicalDual_common_residue G h hx z hz
  have hr : z u₀ % 3 = 0 := by
    by_contra hh
    have hm := nonzero_common_residue_norm_bound h.card z (z u₀)
      (fun u => hres u u₀) hh hs
    omega
  have hd : ∀ u, 3 ∣ z u := fun u => Int.dvd_of_emod_eq_zero (by rw [hres u u₀, hr])
  obtain ⟨b, hxb, hbE, hbn⟩ := canonicalDual_divide_coordinates G h hx z hz hd
  have h14 : ∑ u, b u ^ 2 = 14 := by omega
  have hs0 := integerAmbient_sum_zero G h b hbE
  exact ⟨b, hxb, hbE, hs0, h14,
    integer_eigen_small_coordinates G b hs0 (integerAmbient_eigen G h b hbE) h14.le⟩

theorem canonicalLift_minimum_two (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G)) {x : V → ℚ}
    (hx : x ∈ canonicalLift G H) (hx0 : x ≠ 0) : 2 ≤ codePair x x :=
  canonicalDual_minimum_two G h (canonicalLift_le_dual G H hx) hx0

def IsCanonicalLiftDual (H : Submodule ℤ (CanonicalDiscriminant G)) (x : V → ℚ) : Prop :=
  x ∈ rationalAmbient G ∧ ∀ y ∈ canonicalLift G H, ∃ n : ℤ, codePair x y = (n : ℚ)

theorem canonicalLiftDual_le_canonicalDual (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G)) {x : V → ℚ}
    (hx : IsCanonicalLiftDual G H x) : IsCanonicalDual G x :=
  ⟨hx.1, fun y hy => hx.2 y (canonicalLattice_le_lift G h H hy)⟩

theorem canonicalLiftDual_minimum_two (h : G.IsSRGWith 99 14 1 2)
    (H : Submodule ℤ (CanonicalDiscriminant G)) {x : V → ℚ}
    (hx : IsCanonicalLiftDual G H x) (hx0 : x ≠ 0) : 2 ≤ codePair x x :=
  canonicalDual_minimum_two G h (canonicalLiftDual_le_canonicalDual G h H hx) hx0

#print axioms canonicalDual_minimum_two
#print axioms canonicalDual_root_integral_code
#print axioms canonicalLift_minimum_two
#print axioms canonicalLiftDual_minimum_two

end Conway99
