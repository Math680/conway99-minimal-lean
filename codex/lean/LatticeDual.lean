import RationalLattice

/-! Dual codes and the exponent bound 21, in the canonical rational model. -/

namespace Conway99

open scoped BigOperators Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def IsCanonicalDual (x : V → ℚ) : Prop :=
  x ∈ rationalAmbient G ∧ ∀ y ∈ canonicalLattice G,
    ∃ n : ℤ, codePair x y = (n : ℚ)

theorem canonicalDual_integer_coordinates (h : G.IsSRGWith 99 14 1 2)
    {x : V → ℚ} (hx : IsCanonicalDual G x) :
    ∃ z : V → ℤ, ∀ u, x u = (z u : ℚ) := by
  have hz (u : V) : ∃ n : ℤ, x u = (n : ℚ) := by
    obtain ⟨n, hn⟩ := hx.2 (vertexCode G u) (vertexCode_mem_canonical G u)
    exact ⟨n, by simpa only [codePair_vertexCode G h hx.1] using hn⟩
  choose z hz using hz
  exact ⟨z, hz⟩

theorem differenceCode_mem_canonical (u v : V) :
    coefficientCode G (Pi.single u 1 - Pi.single v 1) ∈ canonicalLattice G := by
  refine ⟨_, ?_, rfl⟩
  change 3 ∣ ∑ t, ((Pi.single u 1 - Pi.single v 1 : V → ℤ) t)
  simp [Finset.sum_sub_distrib]

theorem canonicalDual_coordinate_differences (h : G.IsSRGWith 99 14 1 2)
    {x : V → ℚ} (hx : IsCanonicalDual G x) (u v : V) :
    ∃ n : ℤ, x u - x v = 3 * (n : ℚ) := by
  obtain ⟨n, hn⟩ := hx.2 _ (differenceCode_mem_canonical G u v)
  rw [codePair_coefficientCode G h hx.1] at hn
  have he : (∑ t, x t * ((Pi.single u 1 - Pi.single v 1 : V → ℤ) t : ℤ)) = x u - x v := by
    simp [Pi.single_apply, Int.cast_sub, mul_sub, mul_ite, Finset.sum_sub_distrib]
  rw [he] at hn
  exact ⟨n, by linarith⟩

theorem canonicalDual_common_residue (h : G.IsSRGWith 99 14 1 2)
    {x : V → ℚ} (hx : IsCanonicalDual G x)
    (z : V → ℤ) (hz : ∀ u, x u = (z u : ℚ)) (u v : V) :
    z u % 3 = z v % 3 := by
  obtain ⟨n, hn⟩ := canonicalDual_coordinate_differences G h hx u v
  rw [hz u, hz v] at hn
  have he : z u - z v = 3 * n := by exact_mod_cast hn
  omega

theorem canonicalDual_exponent_twenty_one (h : G.IsSRGWith 99 14 1 2)
    {x : V → ℚ} (hx : IsCanonicalDual G x) :
    (21 : ℚ) • x ∈ canonicalLattice G := by
  obtain ⟨z, hz⟩ := canonicalDual_integer_coordinates G h hx
  have hs : ∑ u, z u = 0 := by
    have hq := rationalAmbient_sum_zero G h hx.1
    simp_rw [hz] at hq
    exact_mod_cast hq
  refine ⟨z, ?_, ?_⟩
  · change 3 ∣ ∑ u, z u
    rw [hs]
    exact dvd_zero _
  · change (1 / 3 : ℚ) • (vertexGram G *ᵥ (fun u => (z u : ℚ))) = _
    have he : (fun u => (z u : ℚ)) = x := funext (fun u => (hz u).symm)
    rw [he, rationalAmbient_fixed G h hx.1, smul_smul]
    norm_num

theorem canonicalLattice_mem_dual (h : G.IsSRGWith 99 14 1 2)
    {x : V → ℚ} (hx : x ∈ canonicalLattice G) : IsCanonicalDual G x := by
  exact ⟨canonicalLattice_le_ambient G hx,
    fun _ hy => canonicalLattice_integral G h hx hy⟩

/-- Removing the common residue gives an integral coefficient vector whose sum
is divisible by three because 99 is divisible by nine. This avoids Smith normal
form for eliminating the three-primary discriminant. -/
theorem canonicalDual_exponent_seven (h : G.IsSRGWith 99 14 1 2)
    {x : V → ℚ} (hx : IsCanonicalDual G x) :
    (7 : ℚ) • x ∈ canonicalLattice G := by
  classical
  have hv : Nonempty V := Fintype.card_pos_iff.mp (by rw [h.card]; norm_num)
  let u₀ : V := Classical.choice hv
  obtain ⟨z, hz⟩ := canonicalDual_integer_coordinates G h hx
  have hcoords (v : V) : ∃ a : ℤ, z v = z u₀ + 3 * a := by
    obtain ⟨a, ha⟩ := canonicalDual_coordinate_differences G h hx v u₀
    rw [hz v, hz u₀] at ha
    have he : z v - z u₀ = 3 * a := by exact_mod_cast ha
    exact ⟨a, by omega⟩
  choose c hc using hcoords
  have hsumz : ∑ u, z u = 0 := by
    have he := rationalAmbient_sum_zero G h hx.1
    simp_rw [hz] at he
    exact_mod_cast he
  have hsumc : ∑ u, c u = -33 * z u₀ := by
    have he : ∑ u, z u = 99 * z u₀ + 3 * ∑ u, c u := by
      rw [Finset.sum_congr rfl (fun u _ => hc u)]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, h.card, nsmul_eq_mul]
      norm_num
    omega
  have hconstant : vertexGram G *ᵥ (fun _ : V => (z u₀ : ℚ)) = 0 := by
    ext u
    change (∑ v, vertexGram G u v * (z u₀ : ℚ)) = 0
    rw [← Finset.sum_mul, vertexGram_row_sum_zero G h, zero_mul]
  have hdecomp : x = (fun _ : V => (z u₀ : ℚ)) +
      (3 : ℚ) • (fun u => (c u : ℚ)) := by
    ext u
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Int.cast_add, Int.cast_mul, Int.cast_ofNat] using (hz u).trans (by exact_mod_cast hc u)
  have he := rationalAmbient_fixed G h hx.1
  conv_lhs at he =>
    rw [hdecomp, Matrix.mulVec_add, hconstant, zero_add, Matrix.mulVec_smul]
  refine ⟨c, ?_, ?_⟩
  · change 3 ∣ ∑ u, c u
    rw [hsumc]
    exact ⟨-11 * z u₀, by ring⟩
  · change (1 / 3 : ℚ) • (vertexGram G *ᵥ (fun u => (c u : ℚ))) = _
    ext u
    have hu := congrFun he u
    simp only [Pi.smul_apply, smul_eq_mul] at hu ⊢
    linarith

def canonicalDual : Submodule ℤ (V → ℚ) where
  carrier := {x | IsCanonicalDual G x}
  zero_mem' := by
    refine ⟨(rationalAmbient G).zero_mem, ?_⟩
    intro y hy
    exact ⟨0, by simp [codePair]⟩
  add_mem' := by
    intro x z hx hz
    refine ⟨(rationalAmbient G).add_mem hx.1 hz.1, ?_⟩
    intro y hy
    obtain ⟨a, ha⟩ := hx.2 y hy
    obtain ⟨b, hb⟩ := hz.2 y hy
    refine ⟨a + b, ?_⟩
    change ((x + z) ⬝ᵥ y) / 63 = _
    rw [add_dotProduct, add_div]
    change codePair x y + codePair z y = _
    rw [ha, hb, Int.cast_add]
  smul_mem' := by
    intro a x hx
    refine ⟨(rationalAmbient G).restrictScalars ℤ |>.smul_mem a hx.1, ?_⟩
    intro y hy
    obtain ⟨b, hb⟩ := hx.2 y hy
    refine ⟨a * b, ?_⟩
    change ((a • x) ⬝ᵥ y) / 63 = _
    rw [smul_dotProduct]
    simpa only [codePair, Int.cast_mul, zsmul_eq_mul, mul_div_assoc] using
      congrArg (fun q : ℚ => (a : ℚ) * q) hb

def canonicalInsideDual : Submodule ℤ (canonicalDual G) :=
  (canonicalLattice G).comap (canonicalDual G).subtype

abbrev CanonicalDiscriminant := (canonicalDual G) ⧸ (canonicalInsideDual G)

theorem canonicalDiscriminant_annihilated (h : G.IsSRGWith 99 14 1 2)
    (q : CanonicalDiscriminant G) : (21 : ℤ) • q = 0 := by
  refine Submodule.Quotient.induction_on _ q ?_
  intro x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  change (21 : ℤ) • (x : V → ℚ) ∈ canonicalLattice G
  have hh := canonicalDual_exponent_twenty_one G h x.property
  simpa only [Int.cast_smul_eq_zsmul ℚ (21 : ℤ), Int.cast_ofNat] using hh

theorem canonicalDiscriminant_annihilated_seven (h : G.IsSRGWith 99 14 1 2)
    (q : CanonicalDiscriminant G) : (7 : ℤ) • q = 0 := by
  refine Submodule.Quotient.induction_on _ q ?_
  intro x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  change (7 : ℤ) • (x : V → ℚ) ∈ canonicalLattice G
  have hh := canonicalDual_exponent_seven G h x.property
  simpa only [Int.cast_smul_eq_zsmul ℚ (7 : ℤ), Int.cast_ofNat] using hh

#print axioms canonicalDual_integer_coordinates
#print axioms canonicalDual_common_residue
#print axioms canonicalDual_exponent_twenty_one
#print axioms canonicalDual_exponent_seven
#print axioms canonicalDiscriminant_annihilated
#print axioms canonicalDiscriminant_annihilated_seven

end Conway99
