import MilgramOrthogonalDiscriminant
import MilgramCyclicPhase
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Isomorphisms

/-! Integral coordinates for the actual orthogonal dual lattice. -/
noncomputable section
namespace Conway99
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def orthogonalDualIntegralBasis
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G)) :
    Module.Basis (Fin 44) ℤ (orthogonalDual G e) :=
  ((orthogonalDualBasis G e).restrictScalars ℤ).map
    (LinearEquiv.ofEq _ _ (orthogonalDual_eq_span G e).symm)

@[simp] theorem orthogonalDualIntegralBasis_coe
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G)) (i : Fin 44) :
    ((orthogonalDualIntegralBasis G e i : orthogonalDual G e) : rationalAmbient G) =
      orthogonalDualBasis G e i := by
  change (((orthogonalDualBasis G e).restrictScalars ℤ i) : rationalAmbient G) = _
  exact Module.Basis.restrictScalars_apply _ _ _

theorem orthogonalDualIntegralBasis_repr
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G))
    (x : orthogonalDual G e) (i : Fin 44) :
    ((orthogonalDualIntegralBasis G e).repr x i : ℚ) =
      codePair ((x : rationalAmbient G) : V → ℚ) (e i : V → ℚ) := by
  change algebraMap ℤ ℚ ((orthogonalDualIntegralBasis G e).repr x i) = _
  simp only [orthogonalDualIntegralBasis, Module.Basis.map_repr,
    LinearEquiv.trans_apply, LinearEquiv.ofEq_symm,
    Module.Basis.restrictScalars_repr_apply]
  exact LinearMap.BilinForm.dualBasis_repr_apply _ _ e _ i

theorem orthogonal_basis_eq_mul_dual
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G)) (a : Fin 44 → ℤ)
    (ho : ∀ i j, i ≠ j → codePair (e i : V → ℚ) (e j : V → ℚ) = 0)
    (hn : ∀ i, codePair (e i : V → ℚ) (e i : V → ℚ) = (2*a i : ℤ))
    (i : Fin 44) :
    e i = (2*a i : ℤ) • orthogonalDualBasis G e i := by
  apply (orthogonalDualBasis G e).repr.injective
  ext j
  rw [map_zsmul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply]
  change ((ambientPairing G).dualBasis (ambientPairing_nondegenerate G) e).repr (e i) j = _
  rw [LinearMap.BilinForm.dualBasis_repr_apply]
  by_cases hij : i = j
  · subst j
    simpa [ambientPairing] using hn i
  · simp only [hij, if_false, smul_zero]
    exact ho i j hij

def orthogonalReduction
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G)) (m : Fin 44 → ℕ) :
    orthogonalDual G e →ₗ[ℤ] (∀ i, ZMod (m i)) where
  toFun x i := ((orthogonalDualIntegralBasis G e).repr x i : ZMod (m i))
  map_add' x y := by ext i; simp
  map_smul' z x := by ext i; simp [zsmul_eq_mul]

theorem orthogonalReduction_surjective
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G)) (m : Fin 44 → ℕ) :
    Function.Surjective (orthogonalReduction G e m) := by
  intro y
  choose z hz using (fun i => ZMod.intCast_surjective (y i))
  refine ⟨(orthogonalDualIntegralBasis G e).equivFun.symm z, ?_⟩
  ext i
  change (((orthogonalDualIntegralBasis G e).repr
    ((orthogonalDualIntegralBasis G e).equivFun.symm z)) i : ZMod (m i)) = y i
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  exact hz i

theorem orthogonalDualIntegralBasis_sum_repr
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G)) (x : orthogonalDual G e) :
    (x : rationalAmbient G) = ∑ i,
      ((orthogonalDualIntegralBasis G e).repr x i) • orthogonalDualBasis G e i := by
  have hh := congrArg (fun z : orthogonalDual G e => (z : rationalAmbient G))
    ((orthogonalDualIntegralBasis G e).sum_repr x)
  simpa only [Submodule.coe_sum, SetLike.val_smul, orthogonalDualIntegralBasis_coe] using hh.symm

theorem orthogonalReduction_ker
    (h : G.IsSRGWith 99 14 1 2)
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G))
    (he : ∀ i, (e i : V → ℚ) ∈ canonicalLattice G)
    (a : Fin 44 → ℤ) (ha : ∀ i, 0 < a i)
    (ho : ∀ i j, i ≠ j → codePair (e i : V → ℚ) (e j : V → ℚ) = 0)
    (hn : ∀ i, codePair (e i : V → ℚ) (e i : V → ℚ) = (2*a i : ℤ)) :
    LinearMap.ker (orthogonalReduction G e (fun i => 2*(a i).natAbs)) =
      orthogonalInsideOrthogonalDual G e := by
  classical
  have hm : ∀ i, ((2*(a i).natAbs : ℕ) : ℤ) = 2*a i := by
    intro i
    rw [Nat.cast_mul, Nat.cast_ofNat, Int.natCast_natAbs, abs_of_pos (ha i)]
  ext x
  change orthogonalReduction G e (fun i => 2*(a i).natAbs) x = 0 ↔
    (x : rationalAmbient G) ∈ orthogonalSublattice G e
  constructor
  · intro hx
    have hc : ∀ i, ∃ z : ℤ, (orthogonalDualIntegralBasis G e).repr x i = (2*a i)*z := by
      intro i
      have hi := congrFun hx i
      change (((orthogonalDualIntegralBasis G e).repr x i : ℤ) : ZMod (2*(a i).natAbs)) = 0 at hi
      obtain ⟨z,hz⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hi
      exact ⟨z, by simpa only [hm] using hz⟩
    choose z hz using hc
    have heq : (x : rationalAmbient G) = ∑ i, z i • e i := by
      rw [orthogonalDualIntegralBasis_sum_repr]
      apply Finset.sum_congr rfl
      intro i _
      rw [hz, orthogonal_basis_eq_mul_dual G e a ho hn i, smul_smul, mul_comm]
    rw [heq]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self i)))
  · intro hx
    have hx' : (x : rationalAmbient G) ∈ Submodule.span ℤ (Set.range e) := hx
    have hc := (e.mem_span_iff_repr_mem ℤ (x : rationalAmbient G)).mp hx'
    choose z hz using hc
    simp only [eq_intCast] at hz
    apply funext
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    rw [hm]
    refine ⟨z i, ?_⟩
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_mul, orthogonalDualIntegralBasis_repr]
    have hex : (x : rationalAmbient G) = ∑ j, (e.repr (x : rationalAmbient G) j) • e j :=
      (e.sum_repr _).symm
    rw [hex]
    change (ambientPairing G) (∑ j, (e.repr (x : rationalAmbient G) j) • e j) (e i) = _
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    have ht : ∀ j, codePair (e j : V → ℚ) (e i : V → ℚ) =
        if j = i then (2*a i : ℤ) else 0 := by
      intro j
      by_cases hj : j = i
      · subst j; simp [hn]
      · simp [hj, ho j i hj]
    change ∑ j, e.repr (x : rationalAmbient G) j * codePair (e j : V → ℚ) (e i : V → ℚ) = _
    simp_rw [ht]
    simp only [apply_ite, Int.cast_zero, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← hz i]
    ring

def orthogonalDiscriminantCoordinateEquiv
    (h : G.IsSRGWith 99 14 1 2)
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G))
    (he : ∀ i, (e i : V → ℚ) ∈ canonicalLattice G)
    (a : Fin 44 → ℤ) (ha : ∀ i, 0 < a i)
    (ho : ∀ i j, i ≠ j → codePair (e i : V → ℚ) (e j : V → ℚ) = 0)
    (hn : ∀ i, codePair (e i : V → ℚ) (e i : V → ℚ) = (2*a i : ℤ)) :
    OrthogonalDiscriminant G e ≃ₗ[ℤ] (∀ i, ZMod (2*(a i).natAbs)) :=
  (Submodule.quotEquivOfEq _ _ (orthogonalReduction_ker G h e he a ha ho hn).symm).trans
    ((orthogonalReduction G e (fun i => 2*(a i).natAbs)).quotKerEquivOfSurjective
      (orthogonalReduction_surjective G e _))

@[simp] theorem orthogonalDiscriminantCoordinateEquiv_mk
    (h : G.IsSRGWith 99 14 1 2)
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G))
    (he : ∀ i, (e i : V → ℚ) ∈ canonicalLattice G)
    (a : Fin 44 → ℤ) (ha : ∀ i, 0 < a i)
    (ho : ∀ i j, i ≠ j → codePair (e i : V → ℚ) (e j : V → ℚ) = 0)
    (hn : ∀ i, codePair (e i : V → ℚ) (e i : V → ℚ) = (2*a i : ℤ))
    (x : orthogonalDual G e) :
    orthogonalDiscriminantCoordinateEquiv G h e he a ha ho hn (Submodule.Quotient.mk x) =
      orthogonalReduction G e (fun i => 2*(a i).natAbs) x := rfl

theorem orthogonalDual_norm_coordinates
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G))
    (a : Fin 44 → ℤ) (ha : ∀ i, 0 < a i)
    (ho : ∀ i j, i ≠ j → codePair (e i : V → ℚ) (e j : V → ℚ) = 0)
    (hn : ∀ i, codePair (e i : V → ℚ) (e i : V → ℚ) = (2*a i : ℤ))
    (x : orthogonalDual G e) :
    codePair ((x : rationalAmbient G) : V → ℚ) ((x : rationalAmbient G) : V → ℚ) =
      ∑ i, (((orthogonalDualIntegralBasis G e).repr x i : ℚ)^2) / (2*a i : ℤ) := by
  have hp (i : Fin 44) :
      (ambientPairing G) (x : rationalAmbient G) (orthogonalDualBasis G e i) =
        ((orthogonalDualIntegralBasis G e).repr x i : ℚ) / (2*a i : ℤ) := by
    have hc := orthogonalDualIntegralBasis_repr G e x i
    rw [orthogonal_basis_eq_mul_dual G e a ho hn i] at hc
    change _ = (ambientPairing G) (x : rationalAmbient G)
      ((2*a i : ℤ) • orthogonalDualBasis G e i) at hc
    rw [map_zsmul, zsmul_eq_mul] at hc
    have hne : ((2*a i : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt (mul_pos (by norm_num : (0:ℤ)<2) (ha i)))
    apply (eq_div_iff hne).mpr
    simpa only [mul_comm] using hc.symm
  change (ambientPairing G) (x : rationalAmbient G) (x : rationalAmbient G) = _
  conv_lhs => arg 2; rw [orthogonalDualIntegralBasis_sum_repr G e x]
  rw [map_sum]
  simp only [map_zsmul, zsmul_eq_mul, hp]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem orthogonalDiscriminantCoordinateEquiv_phase
    (h : G.IsSRGWith 99 14 1 2)
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G))
    (he : ∀ i, (e i : V → ℚ) ∈ canonicalLattice G)
    (a : Fin 44 → ℤ) (ha : ∀ i, 0 < a i)
    (ho : ∀ i j, i ≠ j → codePair (e i : V → ℚ) (e j : V → ℚ) = 0)
    (hn : ∀ i, codePair (e i : V → ℚ) (e i : V → ℚ) = (2*a i : ℤ)) :
    letI : ∀ i, NeZero (2*(a i).natAbs) := fun i =>
      ⟨Nat.mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr (ne_of_gt (ha i)))⟩
    ∀ x : OrthogonalDiscriminant G e,
      orthogonalDiscriminantPhase G h e he x =
        DiagonalPhase.phase (fun i => 2*(a i).natAbs)
          (orthogonalDiscriminantCoordinateEquiv G h e he a ha ho hn x) := by
  letI : ∀ i, NeZero (2*(a i).natAbs) := fun i =>
    ⟨Nat.mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr (ne_of_gt (ha i)))⟩
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    rw [orthogonalDiscriminantCoordinateEquiv_mk]
    change milgramPhase (codePair ((x : rationalAmbient G) : V → ℚ)
      ((x : rationalAmbient G) : V → ℚ)) = _
    rw [orthogonalDual_norm_coordinates G e a ha ho hn x]
    change _ = DiagonalPhase.phase (fun i => 2*(a i).natAbs)
      (fun i => (((orthogonalDualIntegralBasis G e).repr x i : ℤ) : ZMod (2*(a i).natAbs)))
    rw [DiagonalPhase.phase_intCast_sum (fun i => 2*(a i).natAbs)
      (fun i => even_two_mul _) (fun i => (orthogonalDualIntegralBasis G e).repr x i)]
    unfold milgramPhase
    congr 1
    push_cast
    apply congrArg (fun z : ℂ => (Real.pi : ℂ)*Complex.I*z)
    apply Finset.sum_congr rfl
    intro i _
    have hz : ((a i).natAbs : ℤ) = a i := by
      rw [Int.natCast_natAbs, abs_of_pos (ha i)]
    have hc : ((a i).natAbs : ℂ) = (a i : ℂ) := by
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℂ)) hz
    simp only [hc, Int.cast_mul, Int.cast_ofNat]

theorem orthogonalDiscriminant_gauss_product
    (h : G.IsSRGWith 99 14 1 2)
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G))
    [Fintype (OrthogonalDiscriminant G e)]
    (he : ∀ i, (e i : V → ℚ) ∈ canonicalLattice G)
    (a : Fin 44 → ℤ) (ha : ∀ i, 0 < a i)
    (ho : ∀ i j, i ≠ j → codePair (e i : V → ℚ) (e j : V → ℚ) = 0)
    (hn : ∀ i, codePair (e i : V → ℚ) (e i : V → ℚ) = (2*a i : ℤ)) :
    letI : ∀ i, NeZero (2*(a i).natAbs) := fun i =>
      ⟨Nat.mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr (ne_of_gt (ha i)))⟩
    (∑ x, orthogonalDiscriminantPhase G h e he x) =
      ∏ i, ∑ r : ZMod (2*(a i).natAbs), CyclicPhase.phase (2*(a i).natAbs) r := by
  classical
  letI : ∀ i, NeZero (2*(a i).natAbs) := fun i =>
    ⟨Nat.mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr (ne_of_gt (ha i)))⟩
  rw [← DiagonalPhase.gauss_product]
  exact Fintype.sum_equiv
    (orthogonalDiscriminantCoordinateEquiv G h e he a ha ho hn).toEquiv
    _ _ (orthogonalDiscriminantCoordinateEquiv_phase G h e he a ha ho hn)

theorem orthogonalDiscriminant_card_coordinates
    (h : G.IsSRGWith 99 14 1 2)
    (e : Module.Basis (Fin 44) ℚ (rationalAmbient G))
    [Fintype (OrthogonalDiscriminant G e)]
    (he : ∀ i, (e i : V → ℚ) ∈ canonicalLattice G)
    (a : Fin 44 → ℤ) (ha : ∀ i, 0 < a i)
    (ho : ∀ i j, i ≠ j → codePair (e i : V → ℚ) (e j : V → ℚ) = 0)
    (hn : ∀ i, codePair (e i : V → ℚ) (e i : V → ℚ) = (2*a i : ℤ)) :
    Fintype.card (OrthogonalDiscriminant G e) = ∏ i, 2*(a i).natAbs := by
  classical
  letI : ∀ i, NeZero (2*(a i).natAbs) := fun i =>
    ⟨Nat.mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr (ne_of_gt (ha i)))⟩
  rw [Fintype.card_congr (orthogonalDiscriminantCoordinateEquiv G h e he a ha ho hn).toEquiv,
    Fintype.card_pi]
  simp only [ZMod.card]

#print axioms orthogonalDiscriminant_card_coordinates
#print axioms orthogonalDiscriminant_gauss_product
#print axioms orthogonalDiscriminantCoordinateEquiv_phase
#print axioms orthogonalDiscriminantCoordinateEquiv
#print axioms orthogonalDual_norm_coordinates
#print axioms orthogonalReduction_ker
#print axioms orthogonalReduction_surjective
#print axioms orthogonalDualIntegralBasis_repr
#print axioms orthogonal_basis_eq_mul_dual
end Conway99
