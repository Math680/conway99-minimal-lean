import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.Complex.Basic

/-! Finite isotropic averaging, independent of analytic Poisson summation.
This is also the algebraic part of passing from an orthogonal sublattice
to a glued overlattice. -/

noncomputable section

namespace Conway99

attribute [local instance] Classical.propDecidable

open scoped BigOperators

variable {A : Type*} [AddCommGroup A] [Fintype A]

theorem quadratic_phase_isotropic_average (q : A → ℂ) (beta : A → AddChar A ℂ)
    (H : AddSubgroup A)
    (hquad : ∀ x y, q (x + y) = q x * q y * beta x y)
    (hiso : ∀ y ∈ H, q y = 1) :
    (∑ x : A, q x) =
      ∑ x : A, if (∀ y : H, beta x y = 1) then q x else 0 := by
  classical
  let chi (x : A) : AddChar H ℂ := (beta x).compAddMonoidHom H.subtype
  have hrow (x : A) : (∑ y : H, q (x + y)) =
      if (∀ y : H, beta x y = 1) then (Fintype.card H : ℂ) * q x else 0 := by
    have ht (y : H) : q (x + y) = q x * chi x y := by
      rw [hquad, hiso y y.property, mul_one]
      rfl
    simp_rw [ht]
    rw [← Finset.mul_sum]
    by_cases hx : ∀ y : H, beta x y = 1
    · rw [if_pos hx]
      have hc : chi x = 1 := by
        ext y
        exact hx y
      simp [hc, mul_comm]
    · rw [if_neg hx]
      have hc : chi x ≠ 1 := by
        intro hh
        apply hx
        intro y
        have he := congrArg (fun c : AddChar H ℂ => c y) hh
        exact he
      rw [AddChar.sum_eq_zero_of_ne_one hc, mul_zero]
  have hdouble : (∑ x : A, ∑ y : H, q (x + y)) =
      (Fintype.card H : ℂ) * ∑ x : A, q x := by
    rw [Finset.sum_comm]
    have hs (y : H) : (∑ x : A, q (x + y)) = ∑ x : A, q x :=
      Equiv.sum_comp (Equiv.addRight (y : A)) q
    simp_rw [hs]
    simp
  have he : (∑ x : A, if (∀ y : H, beta x y = 1)
      then (Fintype.card H : ℂ) * q x else 0) =
      (Fintype.card H : ℂ) *
        ∑ x : A, if (∀ y : H, beta x y = 1) then q x else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun x _ => hrow x), he] at hdouble
  have hcard : (Fintype.card H : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Fintype.card_pos (α := H))
  exact mul_left_cancel₀ hcard hdouble.symm

#print axioms quadratic_phase_isotropic_average

end Conway99
