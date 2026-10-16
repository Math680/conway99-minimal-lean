import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Fin.Tuple.Basic
import LatticeQuadratic

/-! Absolute convergence of Gaussian sums on integer coordinate spaces.
This is the analytic domination input needed for theta series of lattices. -/

noncomputable section

namespace Conway99

open scoped BigOperators

theorem summable_integer_gaussian {a : ℝ} (ha : 0 < a) :
    Summable (fun m : ℤ => Real.exp (-a * (m : ℝ) ^ 2)) := by
  have h := summable_pow_mul_jacobiTheta₂_term_bound 0
    (show 0 < a / Real.pi from div_pos ha Real.pi_pos) 0
  simp only [pow_zero, one_mul] at h
  convert h using 1
  ext m
  congr 1
  field_simp
  ring

theorem summable_integer_coordinate_gaussian (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Summable (fun m : Fin n → ℤ => Real.exp (-a * ∑ i, (m i : ℝ) ^ 2)) := by
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
    have hs := (summable_integer_gaussian ha).mul_of_nonneg ih
      (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)
    apply (e.summable_iff (f := fun m : Fin (n + 1) → ℤ =>
      Real.exp (-a * ∑ i, (m i : ℝ) ^ 2))).mp
    simpa only [Function.comp_apply, e, Fin.consEquiv, Equiv.coe_fn_mk,
      Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_add, Real.exp_add] using hs

theorem summable_fintype_coordinate_gaussian {ι : Type*} [Fintype ι]
    {a : ℝ} (ha : 0 < a) :
    Summable (fun m : ι → ℤ => Real.exp (-a * ∑ i, (m i : ℝ) ^ 2)) := by
  classical
  let d := Fintype.equivFin ι
  let e : (ι → ℤ) ≃ (Fin (Fintype.card ι) → ℤ) :=
    { toFun := fun m i => m (d.symm i)
      invFun := fun m i => m (d i)
      left_inv := by intro m; funext i; simp
      right_inv := by intro m; funext i; simp }
  have hs := e.summable_iff.mpr (summable_integer_coordinate_gaussian (Fintype.card ι) ha)
  convert hs using 1
  ext m
  congr 2
  exact (Equiv.sum_comp d.symm (fun i => (m i : ℝ) ^ 2)).symm

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def canonicalDualIntegerCode (h : G.IsSRGWith 99 14 1 2)
    (x : canonicalDual G) : V → ℤ :=
  Classical.choose (canonicalDual_integer_coordinates G h x.property)

theorem canonicalDualIntegerCode_spec (h : G.IsSRGWith 99 14 1 2)
    (x : canonicalDual G) (i : V) :
    (x : V → ℚ) i = (canonicalDualIntegerCode G h x i : ℚ) :=
  Classical.choose_spec (canonicalDual_integer_coordinates G h x.property) i

theorem canonicalDualIntegerCode_injective (h : G.IsSRGWith 99 14 1 2) :
    Function.Injective (canonicalDualIntegerCode G h) := by
  intro x y hxy
  apply Subtype.ext
  funext i
  rw [canonicalDualIntegerCode_spec G h x i, canonicalDualIntegerCode_spec G h y i, hxy]

theorem canonicalDual_norm_integer_code (h : G.IsSRGWith 99 14 1 2)
    (x : canonicalDual G) :
    (codePair (x : V → ℚ) (x : V → ℚ) : ℝ) =
      (∑ i, (canonicalDualIntegerCode G h x i : ℝ) ^ 2) / 63 := by
  unfold codePair
  simp only [dotProduct, Rat.cast_div, Rat.cast_sum, Rat.cast_mul, Rat.cast_ofNat]
  simp_rw [canonicalDualIntegerCode_spec G h x, Rat.cast_intCast]
  simp only [sq]

theorem canonicalDual_theta_norm_summable (h : G.IsSRGWith 99 14 1 2)
    {z : ℂ} (hz : 0 < z.im) :
    Summable (fun x : canonicalDual G =>
      ‖Complex.exp ((Real.pi : ℂ) * Complex.I * z *
        (codePair (x : V → ℚ) (x : V → ℚ) : ℂ))‖) := by
  have ha : 0 < Real.pi * z.im / 63 := by positivity
  have hs := (summable_fintype_coordinate_gaussian (ι := V) ha).comp_injective
    (canonicalDualIntegerCode_injective G h)
  convert hs using 1
  ext x
  rw [Complex.norm_exp]
  congr 1
  have hcast : (codePair (x : V → ℚ) (x : V → ℚ) : ℂ) =
      ((codePair (x : V → ℚ) (x : V → ℚ) : ℝ) : ℂ) := by simp
  rw [hcast]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [canonicalDual_norm_integer_code G h x]
  ring

theorem canonicalDual_theta_summable (h : G.IsSRGWith 99 14 1 2)
    {z : ℂ} (hz : 0 < z.im) :
    Summable (fun x : canonicalDual G =>
      Complex.exp ((Real.pi : ℂ) * Complex.I * z *
        (codePair (x : V → ℚ) (x : V → ℚ) : ℂ))) :=
  (canonicalDual_theta_norm_summable G h hz).of_norm

#print axioms summable_integer_coordinate_gaussian
#print axioms canonicalDual_theta_summable

end Conway99
