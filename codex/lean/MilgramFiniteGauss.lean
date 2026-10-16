import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-! Finite quadratic-phase Fourier algebra.  The hypotheses are precisely
the completing-square and character-orthogonality identities. -/

noncomputable section

namespace Conway99

open scoped BigOperators

variable {D : Type*} [AddCommGroup D] [Fintype D] [DecidableEq D]

def twistedFourier (q : D → ℂ) (β : D → D → ℂ) (f : D → ℂ) (a : D) : ℂ :=
  ∑ b, β a b * q b * f b

theorem quadratic_phase_fourier (q : D → ℂ) (β : D → D → ℂ)
    (hq : ∀ a, q a ≠ 0)
    (hcomplete : ∀ a b, q (b - a) = q b * q a * β a b) (a : D) :
    (∑ b, β a b * q b) = (∑ b, q b) / q a := by
  apply mul_right_cancel₀ (hq a)
  calc
    (∑ b, β a b * q b) * q a = ∑ b, q (b - a) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      rw [hcomplete]
      ring
    _ = ∑ b, q b := by
      simpa only [sub_eq_add_neg] using Equiv.sum_comp (Equiv.addRight (-a)) q
    _ = ((∑ b, q b) / q a) * q a := by field_simp [hq a]

theorem twistedFourier_twice (q : D → ℂ) (β : D → D → ℂ)
    (hβsym : ∀ a b, β a b = β b a)
    (hβadd : ∀ a b c, β (a + b) c = β a c * β b c)
    (hF : ∀ a, (∑ b, β a b * q b) = (∑ b, q b) / q a)
    (f : D → ℂ) (a : D) :
    twistedFourier q β (twistedFourier q β f) a =
      (∑ b, q b) * ∑ c, (q c / q (a + c)) * f c := by
  unfold twistedFourier
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  calc
    (∑ b, β a b * q b * (β b c * q c * f c)) =
        (q c * f c) * ∑ b, β (a + c) b * q b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [hβadd, hβsym b c]
      ring
    _ = _ := by rw [hF]; ring

theorem twistedFourier_cube (q : D → ℂ) (β : D → D → ℂ)
    (hq : ∀ a, q a ≠ 0)
    (hqneg : ∀ a, q (-a) = q a)
    (hβsym : ∀ a b, β a b = β b a)
    (hβadd : ∀ a b c, β (a + b) c = β a c * β b c)
    (hquad : ∀ a b, q (a + b) * β a b = q a * q b)
    (hF : ∀ a, (∑ b, β a b * q b) = (∑ b, q b) / q a)
    (horth : ∀ a, (∑ b, β a b) = if a = 0 then (Fintype.card D : ℂ) else 0)
    (f : D → ℂ) (a : D) :
    twistedFourier q β (twistedFourier q β (twistedFourier q β f)) a =
      (∑ b, q b) * (Fintype.card D : ℂ) * f (-a) := by
  have hratio (c : D) : q c / q (a + c) = β a c / q a := by
    field_simp [hq a, hq (a + c)]
    linear_combination -(hquad a c)
  have hsum : (∑ e, (q e * f e / q a) * (∑ c, β (a + e) c)) =
      (Fintype.card D : ℂ) * f (-a) := by
    rw [Finset.sum_eq_single (-a)]
    · rw [horth]
      simp only [add_neg_cancel, if_pos, hqneg]
      field_simp [hq a]
    · intro e _ hne
      have hne' : a + e ≠ 0 := by
        intro he
        apply hne
        exact eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using he)
      rw [horth, if_neg hne', mul_zero]
    · simp
  calc
    _ = (∑ b, q b) * ∑ c, (q c / q (a + c)) * twistedFourier q β f c :=
      twistedFourier_twice q β hβsym hβadd hF _ _
    _ = (∑ b, q b) * ∑ e, (q e * f e / q a) * (∑ c, β (a + e) c) := by
      congr 1
      simp_rw [hratio, twistedFourier, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro c _
      rw [hβadd, hβsym e c]
      ring
    _ = _ := by rw [hsum]; ring

theorem quadratic_phase_completing_square (q : D → ℂ) (β : D → D → ℂ)
    (hq : ∀ a, q a ≠ 0) (hqzero : q 0 = 1) (hqneg : ∀ a, q (-a) = q a)
    (hβsym : ∀ a b, β a b = β b a)
    (hβadd : ∀ a b c, β (a + b) c = β a c * β b c)
    (hquad : ∀ a b, q (a + b) * β a b = q a * q b) :
    ∀ a b, q (b - a) = q b * q a * β a b := by
  have hzero (a : D) : β 0 a = 1 := by
    have hh := hquad 0 a
    rw [zero_add, hqzero, one_mul] at hh
    exact mul_left_cancel₀ (hq a) (by simpa only [mul_one] using hh)
  have hinv (a b : D) : β (-a) b * β a b = 1 := by
    rw [← hβadd, neg_add_cancel, hzero]
  intro a b
  have hh := hquad b (-a)
  rw [← sub_eq_add_neg, hqneg] at hh
  have hi : β b (-a) * β a b = 1 := by
    rw [hβsym b (-a)]
    exact hinv a b
  calc
    q (b - a) = (q (b - a) * β b (-a)) * β a b := by rw [mul_assoc, hi, mul_one]
    _ = _ := by rw [hh]

theorem twistedFourier_cube_of_quadratic (q : D → ℂ) (β : D → D → ℂ)
    (hq : ∀ a, q a ≠ 0) (hqzero : q 0 = 1) (hqneg : ∀ a, q (-a) = q a)
    (hβsym : ∀ a b, β a b = β b a)
    (hβadd : ∀ a b c, β (a + b) c = β a c * β b c)
    (hquad : ∀ a b, q (a + b) * β a b = q a * q b)
    (horth : ∀ a, (∑ b, β a b) = if a = 0 then (Fintype.card D : ℂ) else 0)
    (f : D → ℂ) (a : D) :
    twistedFourier q β (twistedFourier q β (twistedFourier q β f)) a =
      (∑ b, q b) * (Fintype.card D : ℂ) * f (-a) := by
  exact twistedFourier_cube q β hq hqneg hβsym hβadd hquad
    (quadratic_phase_fourier q β hq
      (quadratic_phase_completing_square q β hq hqzero hqneg hβsym hβadd hquad))
    horth f a

def twistedFourierLinear (q : D → ℂ) (β : D → D → ℂ) :
    (D → ℂ) →ₗ[ℂ] (D → ℂ) where
  toFun := twistedFourier q β
  map_add' := by
    intro f g
    funext a
    simp only [twistedFourier, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c f
    funext a
    simp only [twistedFourier, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring

def normalizedTwistedFourier (q : D → ℂ) (β : D → D → ℂ) (v : ℂ) :
    (D → ℂ) →ₗ[ℂ] (D → ℂ) := v⁻¹ • twistedFourierLinear q β

theorem normalizedTwistedFourier_cube (q : D → ℂ) (β : D → D → ℂ)
    (v : ℂ) (hv : v ≠ 0) (hcard : (Fintype.card D : ℂ) = v ^ 2)
    (hq : ∀ a, q a ≠ 0) (hqzero : q 0 = 1) (hqneg : ∀ a, q (-a) = q a)
    (hβsym : ∀ a b, β a b = β b a)
    (hβadd : ∀ a b c, β (a + b) c = β a c * β b c)
    (hquad : ∀ a b, q (a + b) * β a b = q a * q b)
    (horth : ∀ a, (∑ b, β a b) = if a = 0 then (Fintype.card D : ℂ) else 0)
    (f : D → ℂ) :
    normalizedTwistedFourier q β v
      (normalizedTwistedFourier q β v (normalizedTwistedFourier q β v f)) =
      ((∑ b, q b) / v) • (fun a => f (-a)) := by
  unfold normalizedTwistedFourier
  simp only [LinearMap.smul_apply, map_smul, smul_smul]
  funext a
  simp only [Pi.smul_apply, smul_eq_mul, twistedFourierLinear]
  change v⁻¹ * v⁻¹ * v⁻¹ *
    twistedFourier q β (twistedFourier q β (twistedFourier q β f)) a =
      ((∑ b, q b) / v) * f (-a)
  rw [twistedFourier_cube_of_quadratic q β hq hqzero hqneg hβsym hβadd hquad horth,
    hcard]
  field_simp [hv]

#print axioms quadratic_phase_fourier
#print axioms twistedFourier_twice
#print axioms twistedFourier_cube
#print axioms normalizedTwistedFourier_cube

end Conway99
