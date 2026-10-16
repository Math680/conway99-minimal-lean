import FiniteWittSeven
import Mathlib.Order.Preorder.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-! Maximal totally isotropic subspaces and the anisotropic remainder over F7. -/

namespace Conway99

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

variable {M : Type*} [AddCommGroup M] [Module (ZMod 7) M]
variable [FiniteDimensional (ZMod 7) M]

def SevenTotallyIsotropic (Q : QuadraticForm (ZMod 7) M)
    (H : Submodule (ZMod 7) M) : Prop := ∀ x ∈ H, Q x = 0

theorem seven_exists_maximal_isotropic (Q : QuadraticForm (ZMod 7) M) :
    ∃ H : Submodule (ZMod 7) M, SevenTotallyIsotropic Q H ∧
      ∀ J, SevenTotallyIsotropic Q J → H ≤ J → J = H := by
  classical
  let C : Set (Submodule (ZMod 7) M) := {H | SevenTotallyIsotropic Q H}
  have hc : C.Nonempty := ⟨⊥, by
    intro x hx
    have hx0 : x = 0 := hx
    rw [hx0, Q.map_zero]⟩
  have hf : ((fun H : Submodule (ZMod 7) M => Module.finrank (ZMod 7) H) '' C).Finite := by
    apply (Set.finite_Iic (Module.finrank (ZMod 7) M)).subset
    rintro n ⟨H, _, rfl⟩
    exact H.finrank_le
  obtain ⟨H, hH, hmax⟩ := Set.Finite.exists_maximalFor'
    (fun H : Submodule (ZMod 7) M => Module.finrank (ZMod 7) H) C hf hc
  refine ⟨H, hH, ?_⟩
  intro J hJ hle
  exact (Submodule.eq_of_le_of_finrank_le hle
    (hmax hJ (Submodule.finrank_mono hle))).symm

theorem seven_isotropic_le_orthogonal (Q : QuadraticForm (ZMod 7) M)
    {H : Submodule (ZMod 7) M} (hH : SevenTotallyIsotropic Q H) :
    H ≤ LinearMap.BilinForm.orthogonal Q.polarBilin H := by
  intro x hx y hy
  change Q (y + x) - Q y - Q x = 0
  rw [hH _ (H.add_mem hy hx), hH _ hy, hH _ hx]
  simp

theorem seven_isotropic_extend (Q : QuadraticForm (ZMod 7) M)
    {H : Submodule (ZMod 7) M} (hH : SevenTotallyIsotropic Q H)
    {x : M} (hx : x ∈ LinearMap.BilinForm.orthogonal Q.polarBilin H) (hq : Q x = 0) :
    SevenTotallyIsotropic Q (H ⊔ (ZMod 7) ∙ x) := by
  intro z hz
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hz
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
  have hb : Q.polarBilin u (a • x) = 0 := by
    rw [map_smul, smul_eq_mul, show Q.polarBilin u x = 0 from hx u hu, mul_zero]
  have ho : Q.IsOrtho u (a • x) := QuadraticMap.isOrtho_polarBilin.mp hb
  rw [QuadraticMap.isOrtho_def.mp ho, hH _ hu, Q.map_smul, hq, smul_zero, zero_add]

theorem seven_maximal_isotropic_orthogonal_null
    (Q : QuadraticForm (ZMod 7) M) {H : Submodule (ZMod 7) M}
    (hH : SevenTotallyIsotropic Q H)
    (hmax : ∀ J, SevenTotallyIsotropic Q J → H ≤ J → J = H)
    {x : M} (hx : x ∈ LinearMap.BilinForm.orthogonal Q.polarBilin H) (hq : Q x = 0) : x ∈ H := by
  have hj := hmax (H ⊔ (ZMod 7) ∙ x) (seven_isotropic_extend Q hH hx hq) le_sup_left
  rw [← hj]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)

theorem seven_maximal_isotropic_remainder
    (Q : QuadraticForm (ZMod 7) M) {H : Submodule (ZMod 7) M}
    (hH : SevenTotallyIsotropic Q H)
    (hmax : ∀ J, SevenTotallyIsotropic Q J → H ≤ J → J = H) :
    ∃ S : Submodule (ZMod 7) (LinearMap.BilinForm.orthogonal Q.polarBilin H),
      IsCompl (H.comap (LinearMap.BilinForm.orthogonal Q.polarBilin H).subtype) S ∧
      (Q.comp ((LinearMap.BilinForm.orthogonal Q.polarBilin H).subtype.comp S.subtype)).Anisotropic ∧
      Module.finrank (ZMod 7) S ≤ 2 := by
  let K := LinearMap.BilinForm.orthogonal Q.polarBilin H
  obtain ⟨S, hs⟩ := (H.comap K.subtype).exists_isCompl
  have ha : (Q.comp (K.subtype.comp S.subtype)).Anisotropic := by
    intro x hx
    have hh : ((x : K) : M) ∈ H :=
      seven_maximal_isotropic_orthogonal_null Q hH hmax (x : K).property hx
    apply Subtype.ext
    have hz : (x : K) = 0 := Submodule.disjoint_def.mp hs.disjoint _ hh x.property
    exact hz
  exact ⟨S, hs, ha, quadratic_seven_anisotropic_finrank_le_two _ ha⟩

theorem seven_exists_large_isotropic
    (Q : QuadraticForm (ZMod 7) M)
    (hnd : LinearMap.BilinForm.Nondegenerate Q.polarBilin) :
    ∃ H : Submodule (ZMod 7) M, SevenTotallyIsotropic Q H ∧
      2 * Module.finrank (ZMod 7) H ≤ Module.finrank (ZMod 7) M ∧
      Module.finrank (ZMod 7) M ≤ 2 * Module.finrank (ZMod 7) H + 2 := by
  obtain ⟨H, hH, hmax⟩ := seven_exists_maximal_isotropic Q
  obtain ⟨S, hs, _, hS⟩ := seven_maximal_isotropic_remainder Q hH hmax
  have hHK := seven_isotropic_le_orthogonal Q hH
  have hr : Module.finrank (ZMod 7) (H.comap (LinearMap.BilinForm.orthogonal Q.polarBilin H).subtype) =
      Module.finrank (ZMod 7) H :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hHK)
  have hc := Submodule.finrank_add_eq_of_isCompl hs
  rw [hr] at hc
  have hsym : LinearMap.BilinForm.IsSymm Q.polarBilin := ⟨fun x y => QuadraticMap.polar_comm Q x y⟩
  have hk := LinearMap.BilinForm.finrank_orthogonal hnd hsym.isRefl H
  rw [hk] at hc
  have hn := H.finrank_le
  exact ⟨H, hH, by omega, by omega⟩

theorem seven_exists_half_rank_minus_one_isotropic
    (Q : QuadraticForm (ZMod 7) M)
    (hnd : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (heven : Even (Module.finrank (ZMod 7) M))
    (hno : ∀ H : Submodule (ZMod 7) M, SevenTotallyIsotropic Q H →
      2 * Module.finrank (ZMod 7) H ≠ Module.finrank (ZMod 7) M) :
    ∃ H : Submodule (ZMod 7) M, SevenTotallyIsotropic Q H ∧
      Module.finrank (ZMod 7) M = 2 * Module.finrank (ZMod 7) H + 2 := by
  obtain ⟨H, hH, hlo, hhi⟩ := seven_exists_large_isotropic Q hnd
  have hn := hno H hH
  obtain ⟨e, he⟩ := heven
  exact ⟨H, hH, by omega⟩

#print axioms seven_exists_maximal_isotropic
#print axioms seven_maximal_isotropic_remainder
#print axioms seven_exists_large_isotropic
#print axioms seven_exists_half_rank_minus_one_isotropic

end Conway99
