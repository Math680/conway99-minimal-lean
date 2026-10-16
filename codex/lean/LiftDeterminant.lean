import LatticeDeterminant
import LatticeLift
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

/-! The determinant-index-square relation and the determinant-49 isotropic lift. -/

namespace Conway99

open Module LinearMap

section General

variable {E ι : Type*} [AddCommGroup E] [Module ℚ E]
variable [Fintype ι] [DecidableEq ι]

theorem gramDet_index_square
    (B : LinearMap.BilinForm ℚ E) (b c : Basis ι ℚ E)
    (hi : Submodule.span ℤ (Set.range b) ≤ Submodule.span ℤ (Set.range c)) :
    Matrix.det (fun i j => B (b i) (b j)) =
      (Nat.card ((Submodule.span ℤ (Set.range c)) ⧸
        ((Submodule.span ℤ (Set.range b)).comap
          (Submodule.span ℤ (Set.range c)).subtype)) : ℚ) ^ 2 *
      Matrix.det (fun i j => B (c i) (c j)) := by
  let N := Submodule.span ℤ (Set.range b)
  let M := Submodule.span ℤ (Set.range c)
  have hind := AddSubgroup.relIndex_eq_abs_det N.toAddSubgroup M.toAddSubgroup hi b c
    (Submodule.span_int_eq_addSubgroupClosure _)
    (Submodule.span_int_eq_addSubgroupClosure _)
  have hcard : N.toAddSubgroup.relIndex M.toAddSubgroup = Nat.card (M ⧸ N.comap M.subtype) := rfl
  rw [hcard] at hind
  have hd := congrArg Matrix.det (_root_.BilinForm.toMatrix_mul_basis_toMatrix c b B)
  simp only [Matrix.det_mul, Matrix.det_transpose] at hd
  have hm : ∀ (a : Basis ι ℚ E),
      _root_.BilinForm.toMatrix a B = (fun i j => B (a i) (a j)) := by
    intro a
    ext i j
    exact _root_.BilinForm.toMatrix_apply a B i j
  rw [hm, hm] at hd
  rw [hind, sq_abs, Basis.det_apply]
  exact hd.symm.trans (by ring)

theorem abs_gramDet_index_square
    (B : LinearMap.BilinForm ℚ E) (b c : Basis ι ℚ E)
    (hi : Submodule.span ℤ (Set.range b) ≤ Submodule.span ℤ (Set.range c)) :
    |Matrix.det (fun i j => B (b i) (b j))| =
      (Nat.card ((Submodule.span ℤ (Set.range c)) ⧸
        ((Submodule.span ℤ (Set.range b)).comap
          (Submodule.span ℤ (Set.range c)).subtype)) : ℚ) ^ 2 *
      |Matrix.det (fun i j => B (c i) (c j))| := by
  rw [gramDet_index_square B b c hi, abs_mul, abs_of_nonneg (sq_nonneg _)]

end General

section Canonical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem codeGram_det_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → V → ℚ) : 0 ≤ Matrix.det (fun i j => codePair (x i) (x j)) := by
  let C : Matrix V ι ℝ := fun v i => (x i v : ℝ)
  have hm : Matrix.map (fun i j => codePair (x i) (x j)) (Rat.castHom ℝ) =
      (1 / 63 : ℝ) • (C.conjTranspose * C) := by
    ext i j
    simp [codePair, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct,
      C, div_eq_mul_inv]
    ring
  have hn := ((Matrix.posSemidef_conjTranspose_mul_self C).smul
    (by norm_num : (0 : ℝ) ≤ 1 / 63)).det_nonneg
  rw [← hm] at hn
  have hc : 0 ≤ ((Matrix.det (fun i j => codePair (x i) (x j)) : ℚ) : ℝ) := by
    change 0 ≤ (Rat.castHom ℝ) (Matrix.det (fun i j => codePair (x i) (x j)))
    rw [RingHom.map_det]
    exact hn
  exact_mod_cast hc

theorem lattice_extendedBasis_span {E : Type*} [AddCommGroup E] [Module ℚ E]
    (L : Submodule ℤ E) [Submodule.IsLattice ℚ L] {ι : Type*}
    (b : Basis ι ℤ L) : Submodule.span ℤ (Set.range (b.extendOfIsLattice ℚ)) = L := by
  have hr : Set.range (b.extendOfIsLattice ℚ) = L.subtype '' Set.range b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨b i, ⟨i, rfl⟩, by simp⟩
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by simp⟩
  rw [hr, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem canonicalLiftInAmbient_quotient_card
    (H : Submodule ℤ (CanonicalDiscriminant G)) :
    Nat.card ((canonicalLiftInAmbient G H) ⧸
      (canonicalInAmbient G).comap (canonicalLiftInAmbient G H).subtype) = Nat.card H := by
  let e : canonicalLiftInAmbient G H ≃ₗ[ℤ] canonicalLift G H :=
    Submodule.comapSubtypeEquivOfLe (canonicalLift_le_ambient G H)
  let P := (canonicalInAmbient G).comap (canonicalLiftInAmbient G H).subtype
  have hp : P.map e = canonicalInsideLift G H := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  exact (Nat.card_congr
    (Submodule.Quotient.equiv P (canonicalInsideLift G H) e hp).toEquiv).trans
      (canonicalLift_index G H)

theorem canonicalLift_gramDet_index_square
    (h : G.IsSRGWith 99 14 1 2) (H : Submodule ℤ (CanonicalDiscriminant G))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ (canonicalInAmbient G))
    (c : Basis ι ℤ (canonicalLiftInAmbient G H)) :
    Matrix.det (fun i j => codePair ((b i : rationalAmbient G) : V → ℚ)
      ((b j : rationalAmbient G) : V → ℚ)) =
      (Nat.card H : ℚ) ^ 2 * Matrix.det
        (fun i j => codePair ((c i : rationalAmbient G) : V → ℚ)
          ((c j : rationalAmbient G) : V → ℚ)) := by
  letI : Submodule.IsLattice ℚ (canonicalInAmbient G) := canonicalInAmbient_isLattice G
  letI : Submodule.IsLattice ℚ (canonicalLiftInAmbient G H) :=
    canonicalLiftInAmbient_isLattice G h H
  have hs := lattice_extendedBasis_span _ b
  have ht := lattice_extendedBasis_span _ c
  have hi : canonicalInAmbient G ≤ canonicalLiftInAmbient G H :=
    fun _ hx => canonicalLattice_le_lift G h H hx
  have hd := gramDet_index_square (ambientPairing G)
    (b.extendOfIsLattice ℚ) (c.extendOfIsLattice ℚ) (by rwa [hs, ht])
  rw [hs, ht, canonicalLiftInAmbient_quotient_card] at hd
  simpa only [Basis.extendOfIsLattice_apply, ambientPairing] using hd

theorem canonicalLift_abs_gramDet_eq49
    (h : G.IsSRGWith 99 14 1 2) (H : Submodule ℤ (CanonicalDiscriminant G))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ (canonicalInAmbient G))
    (c : Basis ι ℤ (canonicalLiftInAmbient G H)) (e d : ℕ)
    (hD : Nat.card (CanonicalDiscriminant G) = 7 ^ e)
    (hH : Nat.card H = 7 ^ d) (hed : e = 2 * d + 2) :
    |Matrix.det (fun i j => codePair ((c i : rationalAmbient G) : V → ℚ)
      ((c j : rationalAmbient G) : V → ℚ))| = 49 := by
  have hd := congrArg abs (canonicalLift_gramDet_index_square G h H b c)
  rw [abs_mul, abs_of_nonneg (sq_nonneg (Nat.card H : ℚ)),
    ← canonicalDiscriminant_card_eq_abs_gramDet G h b, hD, hH] at hd
  push_cast at hd
  have hp : (7 : ℚ) ^ e = ((7 : ℚ) ^ d) ^ 2 * 49 := by
    rw [hed, Nat.mul_comm 2 d, pow_add, pow_mul]
    norm_num
  apply mul_left_cancel₀ (pow_ne_zero 2 (pow_ne_zero d (by norm_num : (7 : ℚ) ≠ 0)))
  exact hd.symm.trans hp

theorem canonicalLift_gramDet_eq49
    (h : G.IsSRGWith 99 14 1 2) (H : Submodule ℤ (CanonicalDiscriminant G))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ (canonicalInAmbient G))
    (c : Basis ι ℤ (canonicalLiftInAmbient G H)) (e d : ℕ)
    (hD : Nat.card (CanonicalDiscriminant G) = 7 ^ e)
    (hH : Nat.card H = 7 ^ d) (hed : e = 2 * d + 2) :
    Matrix.det (fun i j => codePair ((c i : rationalAmbient G) : V → ℚ)
      ((c j : rationalAmbient G) : V → ℚ)) = 49 := by
  have ha := canonicalLift_abs_gramDet_eq49 G h H b c e d hD hH hed
  rwa [abs_of_nonneg (codeGram_det_nonneg (fun i => ((c i : rationalAmbient G) : V → ℚ)))] at ha

noncomputable def canonicalLiftIntegralGram
    (h : G.IsSRGWith 99 14 1 2) (H : Submodule ℤ (CanonicalDiscriminant G))
    (hH : ∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0)
    {ι : Type*} (c : Basis ι ℤ (canonicalLiftInAmbient G H)) : Matrix ι ι ℤ :=
  fun i j => Classical.choose
    (canonicalLift_integral G h H hH (c i).property (c j).property)

theorem canonicalLiftIntegralGram_spec
    (h : G.IsSRGWith 99 14 1 2) (H : Submodule ℤ (CanonicalDiscriminant G))
    (hH : ∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0)
    {ι : Type*} (c : Basis ι ℤ (canonicalLiftInAmbient G H)) (i j : ι) :
    (canonicalLiftIntegralGram G h H hH c i j : ℚ) =
      codePair ((c i : rationalAmbient G) : V → ℚ)
        ((c j : rationalAmbient G) : V → ℚ) :=
  (Classical.choose_spec
    (canonicalLift_integral G h H hH (c i).property (c j).property)).symm

theorem canonicalLiftIntegralGram_det_natAbs_eq49
    (h : G.IsSRGWith 99 14 1 2) (H : Submodule ℤ (CanonicalDiscriminant G))
    (hiso : ∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ (canonicalInAmbient G))
    (c : Basis ι ℤ (canonicalLiftInAmbient G H)) (e d : ℕ)
    (hD : Nat.card (CanonicalDiscriminant G) = 7 ^ e)
    (hH : Nat.card H = 7 ^ d) (hed : e = 2 * d + 2) :
    (canonicalLiftIntegralGram G h H hiso c).det.natAbs = 49 := by
  have hm : (canonicalLiftIntegralGram G h H hiso c).map (Int.castRingHom ℚ) =
      (fun i j => codePair ((c i : rationalAmbient G) : V → ℚ)
        ((c j : rationalAmbient G) : V → ℚ)) := by
    ext i j
    exact canonicalLiftIntegralGram_spec G h H hiso c i j
  have hd : ((canonicalLiftIntegralGram G h H hiso c).det : ℚ) =
      Matrix.det (fun i j => codePair ((c i : rationalAmbient G) : V → ℚ)
        ((c j : rationalAmbient G) : V → ℚ)) := by
    change (Int.castRingHom ℚ) (canonicalLiftIntegralGram G h H hiso c).det = _
    rw [RingHom.map_det]
    change Matrix.det ((canonicalLiftIntegralGram G h H hiso c).map (Int.castRingHom ℚ)) = _
    rw [hm]
  have ha := canonicalLift_abs_gramDet_eq49 G h H b c e d hD hH hed
  rw [← hd] at ha
  have ha' : |(canonicalLiftIntegralGram G h H hiso c).det| = (49 : ℤ) := by
    exact_mod_cast ha
  rw [Int.abs_eq_natAbs] at ha'
  exact_mod_cast ha'

theorem canonicalLiftIntegralGram_det_eq49
    (h : G.IsSRGWith 99 14 1 2) (H : Submodule ℤ (CanonicalDiscriminant G))
    (hiso : ∀ q ∈ H, canonicalDiscriminantQuadratic G h q = 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ (canonicalInAmbient G))
    (c : Basis ι ℤ (canonicalLiftInAmbient G H)) (e d : ℕ)
    (hD : Nat.card (CanonicalDiscriminant G) = 7 ^ e)
    (hH : Nat.card H = 7 ^ d) (hed : e = 2 * d + 2) :
    (canonicalLiftIntegralGram G h H hiso c).det = 49 := by
  have ha := canonicalLift_gramDet_eq49 G h H b c e d hD hH hed
  have hm : (canonicalLiftIntegralGram G h H hiso c).map (Int.castRingHom ℚ) =
      (fun i j => codePair ((c i : rationalAmbient G) : V → ℚ)
        ((c j : rationalAmbient G) : V → ℚ)) := by
    ext i j
    exact canonicalLiftIntegralGram_spec G h H hiso c i j
  have hd : ((canonicalLiftIntegralGram G h H hiso c).det : ℚ) = 49 := by
    change (Int.castRingHom ℚ) (canonicalLiftIntegralGram G h H hiso c).det = _
    rw [RingHom.map_det]
    change Matrix.det ((canonicalLiftIntegralGram G h H hiso c).map (Int.castRingHom ℚ)) = _
    rw [hm]
    exact ha
  exact_mod_cast hd

end Canonical

#print axioms gramDet_index_square
#print axioms canonicalLift_gramDet_index_square
#print axioms canonicalLift_abs_gramDet_eq49
#print axioms canonicalLiftIntegralGram_det_natAbs_eq49
#print axioms canonicalLiftIntegralGram_det_eq49

end Conway99
