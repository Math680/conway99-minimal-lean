import LatticeBidual
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-! Determinant-index bridge for the actual bilinear lattice pairing. -/

namespace Conway99

open Module LinearMap

section General

variable {E ι : Type*} [AddCommGroup E] [Module ℚ E]
variable [Fintype ι] [DecidableEq ι]

theorem lattice_gram_card_quotient
    (B : LinearMap.BilinForm ℚ E) (hB : B.Nondegenerate) (b : Basis ι ℚ E)
    (hi : Submodule.span ℤ (Set.range b) ≤
      B.dualSubmodule (Submodule.span ℤ (Set.range b))) :
    (Nat.card ((B.dualSubmodule (Submodule.span ℤ (Set.range b))) ⧸
      ((Submodule.span ℤ (Set.range b)).comap
        (B.dualSubmodule (Submodule.span ℤ (Set.range b))).subtype)) : ℚ) =
      |Matrix.det (fun i j => B (b i) (b j))| := by
  let N := Submodule.span ℤ (Set.range b)
  let D := B.dualSubmodule N
  have hD : D.toAddSubgroup = AddSubgroup.closure (Set.range (B.dualBasis hB b)) := by
    rw [show D = Submodule.span ℤ (Set.range (B.dualBasis hB b)) from
      B.dualSubmodule_span_of_basis hB b]
    exact Submodule.span_int_eq_addSubgroupClosure _
  have hN : N.toAddSubgroup = AddSubgroup.closure (Set.range b) :=
    Submodule.span_int_eq_addSubgroupClosure _
  have hind := AddSubgroup.relIndex_eq_abs_det N.toAddSubgroup D.toAddSubgroup hi
    b (B.dualBasis hB b) hN hD
  have hcard : N.toAddSubgroup.relIndex D.toAddSubgroup =
      Nat.card (D ⧸ N.comap D.subtype) := rfl
  rw [hcard] at hind
  rw [hind, Basis.det_apply]
  congr 1
  have he : (B.dualBasis hB b).toMatrix b =
      Matrix.transpose (fun i j => B (b i) (b j)) := by
    ext i j
    simpa only [Basis.toMatrix_apply] using B.dualBasis_repr_apply hB b (b j) i
  rw [he, Matrix.det_transpose]

end General

section Canonical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def canonicalAmbientDualEquiv :
    (ambientPairing G).dualSubmodule (canonicalInAmbient G) ≃ₗ[ℤ] canonicalDual G where
  toFun x := ⟨(x : rationalAmbient G), (ambient_dual_iff G _).mp x.property⟩
  invFun x := ⟨⟨(x : V → ℚ), x.property.1⟩, (ambient_dual_iff G _).mpr x.property⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' a x := rfl

theorem canonicalDiscriminant_card_eq_abs_gramDet
    (h : G.IsSRGWith 99 14 1 2) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ (canonicalInAmbient G)) :
    (Nat.card (CanonicalDiscriminant G) : ℚ) =
      |Matrix.det (fun i j => codePair
        ((b i : rationalAmbient G) : V → ℚ)
        ((b j : rationalAmbient G) : V → ℚ))| := by
  letI : Submodule.IsLattice ℚ (canonicalInAmbient G) := canonicalInAmbient_isLattice G
  let bq := b.extendOfIsLattice ℚ
  let D := (ambientPairing G).dualSubmodule (canonicalInAmbient G)
  let P : Submodule ℤ D := (canonicalInAmbient G).comap D.subtype
  have hspan : Submodule.span ℤ (Set.range bq) = canonicalInAmbient G := by
    have hr : Set.range bq = (canonicalInAmbient G).subtype '' Set.range b := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨b i, ⟨i, rfl⟩, by simp [bq]⟩
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, by simp [bq]⟩
    rw [hr, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hi : canonicalInAmbient G ≤ D := by
    intro x hx y hy
    obtain ⟨n, hn⟩ := canonicalLattice_integral G h hx hy
    exact Submodule.mem_one.mpr ⟨n, hn.symm⟩
  have hp : P.map (canonicalAmbientDualEquiv G : D →ₗ[ℤ] canonicalDual G) =
      canonicalInsideDual G := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨(canonicalAmbientDualEquiv G).symm x, hx,
        (canonicalAmbientDualEquiv G).apply_symm_apply x⟩
  have hc : Nat.card (D ⧸ P) = Nat.card (CanonicalDiscriminant G) :=
    Nat.card_congr (Submodule.Quotient.equiv P (canonicalInsideDual G)
      (canonicalAmbientDualEquiv G) hp).toEquiv
  have hg := lattice_gram_card_quotient (ambientPairing G)
    (ambientPairing_nondegenerate G) bq (by simpa only [hspan] using hi)
  rw [hspan] at hg
  rw [← hc]
  simpa only [bq, Basis.extendOfIsLattice_apply, ambientPairing] using hg

noncomputable def canonicalIntegralGram
    (h : G.IsSRGWith 99 14 1 2) {ι : Type*}
    (b : Basis ι ℤ (canonicalInAmbient G)) : Matrix ι ι ℤ :=
  fun i j => Classical.choose
    (canonicalLattice_integral G h (b i).property (b j).property)

theorem canonicalIntegralGram_spec
    (h : G.IsSRGWith 99 14 1 2) {ι : Type*}
    (b : Basis ι ℤ (canonicalInAmbient G)) (i j : ι) :
    (canonicalIntegralGram G h b i j : ℚ) =
      codePair ((b i : rationalAmbient G) : V → ℚ)
        ((b j : rationalAmbient G) : V → ℚ) :=
  (Classical.choose_spec
    (canonicalLattice_integral G h (b i).property (b j).property)).symm

theorem canonicalDiscriminant_card_eq_natAbs_integralGramDet
    (h : G.IsSRGWith 99 14 1 2) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ (canonicalInAmbient G)) :
    Nat.card (CanonicalDiscriminant G) = (canonicalIntegralGram G h b).det.natAbs := by
  have hm : (canonicalIntegralGram G h b).map (Int.castRingHom ℚ) =
      (fun i j => codePair ((b i : rationalAmbient G) : V → ℚ)
        ((b j : rationalAmbient G) : V → ℚ)) := by
    ext i j
    exact canonicalIntegralGram_spec G h b i j
  have hd : ((canonicalIntegralGram G h b).det : ℚ) =
      Matrix.det (fun i j => codePair ((b i : rationalAmbient G) : V → ℚ)
        ((b j : rationalAmbient G) : V → ℚ)) := by
    change (Int.castRingHom ℚ) (canonicalIntegralGram G h b).det = _
    rw [RingHom.map_det]
    change Matrix.det ((canonicalIntegralGram G h b).map (Int.castRingHom ℚ)) = _
    rw [hm]
  have hc := canonicalDiscriminant_card_eq_abs_gramDet G h b
  rw [← hd] at hc
  have hc' : (Nat.card (CanonicalDiscriminant G) : ℤ) =
      |(canonicalIntegralGram G h b).det| := by exact_mod_cast hc
  rw [Int.abs_eq_natAbs] at hc'
  exact Int.ofNat_inj.mp hc'

theorem canonicalIntegralGram_det_power_seven
    (h : G.IsSRGWith 99 14 1 2) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ (canonicalInAmbient G)) :
    ∃ e : ℕ, (canonicalIntegralGram G h b).det.natAbs = 7 ^ e := by
  obtain ⟨e, he⟩ := canonicalDiscriminant_card_power_seven G h
  exact ⟨e, (canonicalDiscriminant_card_eq_natAbs_integralGramDet G h b).symm.trans he⟩

end Canonical

#print axioms lattice_gram_card_quotient
#print axioms canonicalDiscriminant_card_eq_abs_gramDet
#print axioms canonicalDiscriminant_card_eq_natAbs_integralGramDet
#print axioms canonicalIntegralGram_det_power_seven

end Conway99
