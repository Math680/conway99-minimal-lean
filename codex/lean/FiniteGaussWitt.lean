import FiniteWittReduction
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section
namespace Conway99
open scoped BigOperators
open Module
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Invertible (2 : ZMod 7) := invertibleOfNonzero (by decide)

def sevenGauss {M : Type*} [AddCommGroup M] [Module (ZMod 7) M]
    [Fintype M] (Q : QuadraticForm (ZMod 7) M) : ℂ :=
  ∑ x, ZMod.stdAddChar (Q x)

private theorem seven_square_partition (f : ZMod 7 → ℂ) (a : ZMod 7) (ha : a ≠ 0) :
    (∑ x : ZMod 7, f (a * x ^ 2)) + (∑ x : ZMod 7, f (-a * x ^ 2)) =
      2 * ∑ x : ZMod 7, f x := by
  have hm : ((Finset.univ : Finset (ZMod 7)).val.map (fun x => a * x ^ 2)) +
      ((Finset.univ : Finset (ZMod 7)).val.map (fun x => -a * x ^ 2)) =
      (Finset.univ : Finset (ZMod 7)).val + (Finset.univ : Finset (ZMod 7)).val := by
    revert a
    decide
  have hh := congrArg (fun s : Multiset (ZMod 7) => (s.map f).sum) hm
  simpa [Multiset.map_add, Multiset.map_map, Function.comp_def, Multiset.sum_add,
    ← Finset.sum_eq_multiset_sum, two_mul] using hh

private theorem seven_char_sum : (∑ x : ZMod 7, ZMod.stdAddChar x) = 0 := by
  apply AddChar.sum_eq_zero_of_ne_one
  intro h
  have h1 := congrArg (fun c : AddChar (ZMod 7) ℂ => c 1) h
  have hz := ZMod.injective_stdAddChar
    (h1.trans (AddChar.map_zero_eq_one (ZMod.stdAddChar (N := 7))).symm)
  exact (by decide : (1 : ZMod 7) ≠ 0) hz

theorem seven_one_gauss_neg (a : ZMod 7) (ha : a ≠ 0) :
    (∑ x : ZMod 7, ZMod.stdAddChar (-a * x ^ 2)) =
      -(∑ x : ZMod 7, ZMod.stdAddChar (a * x ^ 2)) := by
  have h := seven_square_partition (fun x => ZMod.stdAddChar x) a ha
  rw [seven_char_sum, mul_zero] at h
  exact eq_neg_of_add_eq_zero_right h

theorem seven_char_conj (x : ZMod 7) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  change star ((ZMod.toCircle x : Circle) : ℂ) = ((ZMod.toCircle (-x) : Circle) : ℂ)
  rw [AddChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj (ZMod.toCircle x)).symm

private theorem seven_char_map_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 7) :
    ZMod.stdAddChar (∑ i ∈ s, f i) = ∏ i ∈ s, ZMod.stdAddChar (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, AddChar.map_add_eq_mul, ih]

variable {M : Type*} [AddCommGroup M] [Module (ZMod 7) M]
variable [FiniteDimensional (ZMod 7) M] [Fintype M]

theorem sevenGauss_diagonal (Q : QuadraticForm (ZMod 7) M)
    {ι : Type*} [Fintype ι] (e : Basis ι (ZMod 7) M)
    (he : (QuadraticMap.associatedHom (ZMod 7) Q).IsOrthoᵢ e) :
    sevenGauss Q = ∏ i, ∑ x : ZMod 7, ZMod.stdAddChar (Q (e i) * x ^ 2) := by
  classical
  letI : Invertible (2 : ZMod 7) := invertibleOfNonzero (by decide)
  unfold sevenGauss
  rw [← Equiv.sum_comp e.equivFun.symm.toEquiv (fun x => ZMod.stdAddChar (Q x))]
  have hdiag := Q.basisRepr_eq_of_iIsOrtho e he
  have h (v : ι → ZMod 7) : Q (e.equivFun.symm v) = ∑ i, Q (e i) * v i ^ 2 := by
    have hh := congrArg (fun q : QuadraticForm (ZMod 7) (ι → ZMod 7) => q v) hdiag
    simpa [QuadraticMap.basisRepr, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
      pow_two] using hh
  change (∑ v : ι → ZMod 7, ZMod.stdAddChar (Q (e.equivFun.symm v))) = _
  simp_rw [h]
  simp_rw [seven_char_map_sum]
  exact (Fintype.prod_sum (fun (i : ι) (x : ZMod 7) =>
    ZMod.stdAddChar (Q (e i) * x ^ 2))).symm

theorem sevenGauss_conj (Q : QuadraticForm (ZMod 7) M)
    (hnd : LinearMap.BilinForm.Nondegenerate Q.polarBilin) :
    star (sevenGauss Q) = (-1 : ℂ) ^ Module.finrank (ZMod 7) M * sevenGauss Q := by
  classical
  letI : Invertible (2 : ZMod 7) := invertibleOfNonzero (by decide)
  let B := QuadraticMap.associatedHom (ZMod 7) Q
  have hBnd : LinearMap.BilinForm.Nondegenerate B := by
    intro x hx
    apply hnd x
    intro y
    have hh := congrArg (fun b : LinearMap.BilinMap (ZMod 7) M (ZMod 7) => b x y)
      (Q.two_nsmul_associated (ZMod 7))
    change 2 • B x y = Q.polarBilin x y at hh
    rw [hx y, smul_zero] at hh
    exact hh.symm
  obtain ⟨e, he⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (Q.associated_isSymm (ZMod 7))
  have hcoeff (i : Fin (Module.finrank (ZMod 7) M)) : Q (e i) ≠ 0 := by
    have hi := LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate he hBnd i
    change B (e i) (e i) ≠ 0 at hi
    rwa [QuadraticMap.associated_eq_self_apply] at hi
  rw [sevenGauss_diagonal Q e he]
  change (starRingEnd ℂ) (∏ i, ∑ x : ZMod 7, ZMod.stdAddChar (Q (e i) * x ^ 2)) = _
  rw [map_prod]
  have hchar (x : ZMod 7) : (starRingEnd ℂ) (ZMod.stdAddChar x) =
      ZMod.stdAddChar (-x) := seven_char_conj x
  simp_rw [map_sum, hchar, ← neg_mul,
    seven_one_gauss_neg _ (hcoeff _)]
  rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin]

theorem sevenGauss_negative_real_even (Q : QuadraticForm (ZMod 7) M)
    (hnd : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (r : ℝ) (hr : 0 < r) (hg : sevenGauss Q = -(r : ℂ)) :
    Even (Module.finrank (ZMod 7) M) := by
  have hc := sevenGauss_conj Q hnd
  rw [hg] at hc
  simp only [star_neg, Complex.star_def, Complex.conj_ofReal] at hc
  have hn : -(r : ℂ) ≠ 0 := neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (ne_of_gt hr))
  have hp : (-1 : ℂ) ^ Module.finrank (ZMod 7) M = 1 :=
    mul_right_cancel₀ hn (by simpa only [one_mul] using hc.symm)
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1)).mp hp

private def sevenSubspaceCharacter (Q : QuadraticForm (ZMod 7) M)
    (H : Submodule (ZMod 7) M) (x : M) : AddChar H ℂ where
  toFun y := ZMod.stdAddChar (Q.polarBilin x y)
  map_zero_eq_one' := by simp [AddChar.map_zero_eq_one]
  map_add_eq_mul' y z := by simp [AddChar.map_add_eq_mul]

theorem sevenGauss_of_isotropic_self_orthogonal (Q : QuadraticForm (ZMod 7) M)
    (H : Submodule (ZMod 7) M) [Fintype H] (hH : SevenTotallyIsotropic Q H)
    (hself : LinearMap.BilinForm.orthogonal Q.polarBilin H = H) :
    sevenGauss Q = (Fintype.card H : ℂ) := by
  classical
  have hsum (x : M) : (∑ y : H, ZMod.stdAddChar (Q (x + y))) =
      if x ∈ H then (Fintype.card H : ℂ) else 0 := by
    have hphase (y : H) : ZMod.stdAddChar (Q (x + y)) =
        ZMod.stdAddChar (Q x) * sevenSubspaceCharacter Q H x y := by
      change ZMod.stdAddChar (Q (x + y)) =
        ZMod.stdAddChar (Q x) * ZMod.stdAddChar (Q.polarBilin x y)
      rw [← AddChar.map_add_eq_mul]
      congr 1
      change Q (x + y) = Q x + (Q (x + y) - Q x - Q y)
      rw [hH y y.property]
      ring
    simp_rw [hphase]
    rw [← Finset.mul_sum]
    by_cases hx : x ∈ H
    · rw [if_pos hx, hH x hx, AddChar.map_zero_eq_one, one_mul]
      have hc : sevenSubspaceCharacter Q H x = 1 := by
        ext y
        change ZMod.stdAddChar (Q.polarBilin x y) = 1
        have hb : Q.polarBilin y x = 0 := (hself.symm ▸ hx) y y.property
        rw [show Q.polarBilin x y = Q.polarBilin y x from QuadraticMap.polar_comm Q x y,
          hb, AddChar.map_zero_eq_one]
      simp [hc]
    · rw [if_neg hx]
      have hc : sevenSubspaceCharacter Q H x ≠ 1 := by
        intro hc
        apply hx
        rw [← hself]
        intro y hy
        have hh := congrArg (fun c : AddChar H ℂ => c ⟨y, hy⟩) hc
        change ZMod.stdAddChar (Q.polarBilin x y) = 1 at hh
        have hz := ZMod.injective_stdAddChar
          (hh.trans (AddChar.map_zero_eq_one (ZMod.stdAddChar (N := 7))).symm)
        change Q.polarBilin y x = 0
        rw [show Q.polarBilin y x = Q.polarBilin x y from QuadraticMap.polar_comm Q y x]
        exact hz
      rw [AddChar.sum_eq_zero_of_ne_one hc, mul_zero]
  have hdouble : (∑ x : M, ∑ y : H, ZMod.stdAddChar (Q (x + y))) =
      (Fintype.card H : ℂ) * sevenGauss Q := by
    rw [Finset.sum_comm]
    have hs (y : H) : (∑ x : M, ZMod.stdAddChar (Q (x + y))) = sevenGauss Q := by
      exact Equiv.sum_comp (Equiv.addRight (y : M)) (fun x => ZMod.stdAddChar (Q x))
    simp_rw [hs]
    simp
  have hcount : (∑ x : M, if x ∈ H then (Fintype.card H : ℂ) else 0) =
      (Fintype.card H : ℂ) * (Fintype.card H : ℂ) := by
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 1
    exact_mod_cast (Fintype.card_subtype (fun x : M => x ∈ H)).symm
  simp_rw [hsum] at hdouble
  rw [hcount] at hdouble
  have hcard : (Fintype.card H : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos (α := H)))
  exact mul_left_cancel₀ hcard hdouble.symm

theorem sevenGauss_negative_real_no_half (Q : QuadraticForm (ZMod 7) M)
    (hnd : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (r : ℝ) (hr : 0 < r) (hg : sevenGauss Q = -(r : ℂ))
    (H : Submodule (ZMod 7) M) (hH : SevenTotallyIsotropic Q H) :
    2 * Module.finrank (ZMod 7) H ≠ Module.finrank (ZMod 7) M := by
  classical
  intro hhalf
  have hsym : LinearMap.BilinForm.IsSymm Q.polarBilin :=
    ⟨fun x y => QuadraticMap.polar_comm Q x y⟩
  have hd := LinearMap.BilinForm.finrank_orthogonal hnd hsym.isRefl H
  have hself : LinearMap.BilinForm.orthogonal Q.polarBilin H = H :=
    (Submodule.eq_of_le_of_finrank_le (seven_isotropic_le_orthogonal Q hH) (by omega)).symm
  have hpos := sevenGauss_of_isotropic_self_orthogonal Q H hH hself
  rw [hg] at hpos
  have heq : -r = (Fintype.card H : ℝ) := by exact_mod_cast hpos
  have hcard : (0 : ℝ) < Fintype.card H := by exact_mod_cast (Fintype.card_pos (α := H))
  linarith

theorem sevenGauss_negative_real_isotropic_codim_two (Q : QuadraticForm (ZMod 7) M)
    (hnd : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (r : ℝ) (hr : 0 < r) (hg : sevenGauss Q = -(r : ℂ)) :
    ∃ H : Submodule (ZMod 7) M, SevenTotallyIsotropic Q H ∧
      Module.finrank (ZMod 7) M = 2 * Module.finrank (ZMod 7) H + 2 := by
  exact seven_exists_half_rank_minus_one_isotropic Q hnd
    (sevenGauss_negative_real_even Q hnd r hr hg)
    (sevenGauss_negative_real_no_half Q hnd r hr hg)

theorem sevenGauss_negative_sqrt_isotropic_codim_two (Q : QuadraticForm (ZMod 7) M)
    (hnd : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (hg : sevenGauss Q = -(Real.sqrt (Fintype.card M : ℝ) : ℂ)) :
    ∃ H : Submodule (ZMod 7) M, SevenTotallyIsotropic Q H ∧
      Module.finrank (ZMod 7) M = 2 * Module.finrank (ZMod 7) H + 2 := by
  apply sevenGauss_negative_real_isotropic_codim_two Q hnd _ _ hg
  exact Real.sqrt_pos.mpr (by exact_mod_cast (Fintype.card_pos (α := M)))

#print axioms sevenGauss_negative_real_isotropic_codim_two
#print axioms sevenGauss_negative_sqrt_isotropic_codim_two

end Conway99
