import LatticeParity
import LatticeDiscriminant

/-! Integral numerators of the seven-primary discriminant pairing and norm. -/

namespace Conway99

open scoped BigOperators Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem codePair_smul_left (a : ℚ) (x y : V → ℚ) :
    codePair (a • x) y = a * codePair x y := by
  simp only [codePair, smul_dotProduct, smul_eq_mul]
  ring

theorem codePair_smul_right (a : ℚ) (x y : V → ℚ) :
    codePair x (a • y) = a * codePair x y := by
  rw [codePair_symm, codePair_smul_left, codePair_symm]

theorem codePair_add_left (x y z : V → ℚ) :
    codePair (x + y) z = codePair x z + codePair y z := by
  simp only [codePair, add_dotProduct, add_div]

theorem codePair_add_right (x y z : V → ℚ) :
    codePair x (y + z) = codePair x y + codePair x z := by
  simp only [codePair, dotProduct_add, add_div]

theorem codePair_norm_add (x y : V → ℚ) :
    codePair (x + y) (x + y) =
      codePair x x + 2 * codePair x y + codePair y y := by
  rw [codePair_add_left, codePair_add_right, codePair_add_right, codePair_symm y x]
  ring

theorem canonicalDual_pair_numerator (h : G.IsSRGWith 99 14 1 2)
    {x y : V → ℚ} (hx : IsCanonicalDual G x) (hy : IsCanonicalDual G y) :
    ∃ n : ℤ, 7 * codePair x y = (n : ℚ) := by
  obtain ⟨n, hn⟩ := hx.2 _ (canonicalDual_exponent_seven G h hy)
  exact ⟨n, by simpa only [codePair_smul_right] using hn⟩

theorem canonicalDual_half_norm_numerator (h : G.IsSRGWith 99 14 1 2)
    {x : V → ℚ} (hx : IsCanonicalDual G x) :
    ∃ n : ℤ, 7 * codePair x x = 2 * (n : ℚ) := by
  obtain ⟨a, ha⟩ := canonicalDual_pair_numerator G h hx hx
  obtain ⟨b, hb⟩ := canonicalLattice_even G h (canonicalDual_exponent_seven G h hx)
  rw [codePair_smul_left, codePair_smul_right] at hb
  have he : 7 * a = 2 * b := by
    exact_mod_cast (show (7 : ℚ) * (a : ℚ) = 2 * (b : ℚ) by
      push_cast at hb
      nlinarith)
  refine ⟨b - 3 * a, ?_⟩
  push_cast
  have heq : (7 : ℚ) * (a : ℚ) = 2 * (b : ℚ) := by exact_mod_cast he
  linarith

noncomputable def canonicalDualHalfNorm (h : G.IsSRGWith 99 14 1 2)
    (x : canonicalDual G) : ℤ :=
  Classical.choose (canonicalDual_half_norm_numerator G h x.property)

theorem canonicalDualHalfNorm_spec (h : G.IsSRGWith 99 14 1 2)
    (x : canonicalDual G) :
    7 * codePair (x : V → ℚ) (x : V → ℚ) =
      2 * (canonicalDualHalfNorm G h x : ℚ) :=
  Classical.choose_spec (canonicalDual_half_norm_numerator G h x.property)

theorem canonicalDualHalfNorm_shift (h : G.IsSRGWith 99 14 1 2)
    (x y : canonicalDual G) (hxy : (x : V → ℚ) - (y : V → ℚ) ∈ canonicalLattice G) :
    7 ∣ canonicalDualHalfNorm G h x - canonicalDualHalfNorm G h y := by
  let d : V → ℚ := (x : V → ℚ) - (y : V → ℚ)
  obtain ⟨a, ha⟩ := canonicalLattice_even G h hxy
  obtain ⟨b, hb⟩ := y.property.2 d hxy
  have hd : (x : V → ℚ) = (y : V → ℚ) + d := by simp [d]
  have hn := codePair_norm_add (y : V → ℚ) d
  rw [← hd] at hn
  have hnx := canonicalDualHalfNorm_spec G h x
  have hny := canonicalDualHalfNorm_spec G h y
  change codePair d d = (2 * a : ℤ) at ha
  have he : canonicalDualHalfNorm G h x - canonicalDualHalfNorm G h y = 7 * (a + b) := by
    apply Int.cast_injective (α := ℚ)
    push_cast at ha ⊢
    nlinarith
  exact ⟨a + b, he⟩

noncomputable def canonicalDiscriminantQuadratic (h : G.IsSRGWith 99 14 1 2) :
    CanonicalDiscriminant G → ZMod 7 :=
  Quotient.lift (fun x : canonicalDual G => (canonicalDualHalfNorm G h x : ZMod 7))
    (by
      intro x y hxy
      have hd : (x : V → ℚ) - (y : V → ℚ) ∈ canonicalLattice G := by
        have hh := (Submodule.quotientRel_def (canonicalInsideDual G)).mp hxy
        exact hh
      have hv := canonicalDualHalfNorm_shift G h x y hd
      apply sub_eq_zero.mp
      rw [← Int.cast_sub]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hv)

theorem canonicalDiscriminantQuadratic_mk (h : G.IsSRGWith 99 14 1 2)
    (x : canonicalDual G) :
    canonicalDiscriminantQuadratic G h (Submodule.Quotient.mk x) =
      (canonicalDualHalfNorm G h x : ZMod 7) := rfl

#print axioms canonicalDual_half_norm_numerator
#print axioms canonicalDiscriminantQuadratic

end Conway99
