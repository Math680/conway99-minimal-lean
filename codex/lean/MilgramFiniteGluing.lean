import MilgramIsotropicAverage
import Mathlib.GroupTheory.Coset.Basic

/-! Finite gluing identities. These are generic algebraic theorems, not
an assertion that the analytic Milgram bridge has been completed. -/

noncomputable section
namespace Conway99
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {A : Type*} [AddCommGroup A] [Fintype A]

theorem sum_comp_add_quotient (H : AddSubgroup A)
    [Fintype (A ⧸ H)] (f : A ⧸ H → ℂ) :
    (∑ x : A, f (QuotientAddGroup.mk x)) =
      (Fintype.card H : ℂ) * ∑ x : A ⧸ H, f x := by
  classical
  let e : A ≃ (A ⧸ H) × H := AddSubgroup.addGroupEquivQuotientProdAddSubgroup
  have hf (x : A) : (e x).1 = QuotientAddGroup.mk x := rfl
  have he := e.sum_comp (fun p => f p.1)
  simp_rw [hf] at he
  rw [he, Fintype.sum_prod_type]
  simp [Finset.sum_mul, mul_comm]

def phaseAnnihilator (beta : A → AddChar A ℂ) (H : AddSubgroup A) : AddSubgroup A where
  carrier := {x | ∀ y ∈ H, beta y x = 1}
  zero_mem' := by simp
  add_mem' := by
    intro x z hx hz y hy
    rw [AddChar.map_add_eq_mul, hx y hy, hz y hy, mul_one]
  neg_mem' := by
    intro x hx y hy
    rw [AddChar.map_neg_eq_inv, hx y hy, inv_one]

@[simp] theorem mem_phaseAnnihilator (beta : A → AddChar A ℂ) (H : AddSubgroup A) (x : A) :
    x ∈ phaseAnnihilator beta H ↔ ∀ y ∈ H, beta y x = 1 := Iff.rfl

theorem isotropic_le_phaseAnnihilator (q : A → ℂ) (beta : A → AddChar A ℂ)
    (H : AddSubgroup A)
    (hquad : ∀ x y, q (x + y) = q x * q y * beta x y)
    (hiso : ∀ x ∈ H, q x = 1) : H ≤ phaseAnnihilator beta H := by
  intro x hx y hy
  have hh := hquad y x
  rw [hiso (y+x) (H.add_mem hy hx), hiso y hy, hiso x hx, one_mul, one_mul] at hh
  exact hh.symm

theorem quadratic_phase_sum_annihilator (q : A → ℂ) (beta : A → AddChar A ℂ)
    (H : AddSubgroup A)
    (hquad : ∀ x y, q (x + y) = q x * q y * beta x y)
    (hsymm : ∀ x y, beta x y = beta y x)
    (hiso : ∀ y ∈ H, q y = 1) :
    (∑ x : A, q x) = ∑ x : phaseAnnihilator beta H, q x := by
  classical
  rw [quadratic_phase_isotropic_average q beta H hquad hiso]
  have hp (x : A) : (∀ y : H, beta x y = 1) ↔ x ∈ phaseAnnihilator beta H := by
    constructor
    · intro hx y hy
      rw [← hsymm]
      exact hx ⟨y,hy⟩
    · intro hx y
      rw [hsymm]
      exact hx y y.property
  simp_rw [hp]
  simp only [← Finset.sum_filter]
  simpa using (Finset.sum_subtype_eq_sum_filter
    (s := Finset.univ) (p := fun x => x ∈ phaseAnnihilator beta H) q).symm

def descendCosetInvariant (H : AddSubgroup A) (q : A → ℂ)
    (hq : ∀ x y, y ∈ H → q (x+y) = q x) : A ⧸ H → ℂ :=
  Quotient.lift q (by
    intro x y hxy
    have hm : -x + y ∈ H := QuotientAddGroup.leftRel_apply.mp hxy
    have hh := hq x (-x+y) hm
    simpa using hh.symm)

@[simp] theorem descendCosetInvariant_mk (H : AddSubgroup A) (q : A → ℂ)
    (hq : ∀ x y, y ∈ H → q (x+y) = q x) (x : A) :
    descendCosetInvariant H q hq (QuotientAddGroup.mk x) = q x := rfl

theorem quadratic_phase_periodic_on_annihilator (q : A → ℂ)
    (beta : A → AddChar A ℂ) (H : AddSubgroup A)
    (hquad : ∀ x y, q (x+y) = q x * q y * beta x y)
    (hsymm : ∀ x y, beta x y = beta y x)
    (hiso : ∀ y ∈ H, q y = 1) :
    ∀ x y : phaseAnnihilator beta H, y ∈ H.addSubgroupOf (phaseAnnihilator beta H) →
      q ((x+y : phaseAnnihilator beta H) : A) = q (x : A) := by
  intro x y hy
  change q ((x : A) + (y : A)) = q (x : A)
  rw [hquad, hiso y hy, hsymm, x.property y hy, mul_one, mul_one]

def gluedPhase (q : A → ℂ) (beta : A → AddChar A ℂ) (H : AddSubgroup A)
    (hquad : ∀ x y, q (x+y) = q x * q y * beta x y)
    (hsymm : ∀ x y, beta x y = beta y x)
    (hiso : ∀ y ∈ H, q y = 1) :
    (phaseAnnihilator beta H) ⧸ H.addSubgroupOf (phaseAnnihilator beta H) → ℂ :=
  descendCosetInvariant _ (fun x => q (x : A))
    (quadratic_phase_periodic_on_annihilator q beta H hquad hsymm hiso)

theorem quadratic_phase_gluing_sum (q : A → ℂ) (beta : A → AddChar A ℂ)
    (H : AddSubgroup A)
    (hquad : ∀ x y, q (x+y) = q x * q y * beta x y)
    (hsymm : ∀ x y, beta x y = beta y x)
    (hiso : ∀ y ∈ H, q y = 1)
    [Fintype ((phaseAnnihilator beta H) ⧸ H.addSubgroupOf (phaseAnnihilator beta H))] :
    (∑ x : A, q x) = (Fintype.card H : ℂ) *
      ∑ x, gluedPhase q beta H hquad hsymm hiso x := by
  classical
  rw [quadratic_phase_sum_annihilator q beta H hquad hsymm hiso]
  have hs := sum_comp_add_quotient (H.addSubgroupOf (phaseAnnihilator beta H))
    (gluedPhase q beta H hquad hsymm hiso)
  have hc : Fintype.card (H.addSubgroupOf (phaseAnnihilator beta H)) = Fintype.card H :=
    Fintype.card_congr (AddSubgroup.addSubgroupOfEquivOfLe
      (isotropic_le_phaseAnnihilator q beta H hquad hiso)).toEquiv
  simpa only [gluedPhase, descendCosetInvariant_mk, hc] using hs

theorem phaseAnnihilator_card (beta : A → AddChar A ℂ) (H : AddSubgroup A)
    (hsymm : ∀ x y, beta x y = beta y x)
    (hnd : ∀ x : A, x ≠ 0 → beta x ≠ 1) :
    Fintype.card A = Fintype.card H * Fintype.card (phaseAnnihilator beta H) := by
  classical
  let P := phaseAnnihilator beta H
  have hr (x : A) : (∑ y : H, beta y x) =
      if x ∈ P then (Fintype.card H : ℂ) else 0 := by
    let chi : AddChar H ℂ := (beta x).compAddMonoidHom H.subtype
    have hrow : (∑ y : H, beta y x) = ∑ y : H, chi y := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hsymm y x
    rw [hrow]
    by_cases hx : x ∈ P
    · rw [if_pos hx]
      have hc : chi = 1 := by
        ext y
        exact (hsymm x y).trans (hx y y.property)
      simp [hc]
    · rw [if_neg hx]
      apply AddChar.sum_eq_zero_of_ne_one
      intro hc
      apply hx
      intro y hy
      have he := congrArg (fun c : AddChar H ℂ => c ⟨y,hy⟩) hc
      exact (hsymm y x).trans he
  have hc (y : H) : (∑ x : A, beta y x) =
      if y = 0 then (Fintype.card A : ℂ) else 0 := by
    by_cases hy : y = 0
    · subst y
      rw [if_pos rfl]
      have hz : beta 0 = 1 := by
        ext x
        rw [hsymm, AddChar.map_zero_eq_one]
        rfl
      simp [hz]
    · rw [if_neg hy]
      exact AddChar.sum_eq_zero_of_ne_one (hnd y (by
        intro he
        exact hy (Subtype.ext he)))
  have hd : (∑ x : A, ∑ y : H, beta y x) = (Fintype.card A : ℂ) := by
    rw [Finset.sum_comm]
    simp_rw [hc]
    simp
  have hp : (∑ x : A, if x ∈ P then (Fintype.card H : ℂ) else 0) =
      (Fintype.card H : ℂ) * (Fintype.card P : ℂ) := by
    rw [← Finset.sum_filter]
    have he := Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset A)) (p := fun x => x ∈ P)
      (fun _ : A => (Fintype.card H : ℂ))
    rw [← he]
    simp [mul_comm]
  simp_rw [hr] at hd
  rw [hp] at hd
  exact_mod_cast hd.symm

theorem quadratic_phase_gluing_card (q : A → ℂ) (beta : A → AddChar A ℂ)
    (H : AddSubgroup A)
    (hquad : ∀ x y, q (x+y) = q x * q y * beta x y)
    (hsymm : ∀ x y, beta x y = beta y x)
    (hiso : ∀ y ∈ H, q y = 1)
    (hnd : ∀ x : A, x ≠ 0 → beta x ≠ 1)
    [Fintype ((phaseAnnihilator beta H) ⧸ H.addSubgroupOf (phaseAnnihilator beta H))] :
    Fintype.card A = Fintype.card H ^ 2 *
      Fintype.card ((phaseAnnihilator beta H) ⧸ H.addSubgroupOf (phaseAnnihilator beta H)) := by
  let P := phaseAnnihilator beta H
  let J := H.addSubgroupOf P
  have he : P ≃ (P ⧸ J) × J := AddSubgroup.addGroupEquivQuotientProdAddSubgroup
  have hp := Fintype.card_congr he
  rw [Fintype.card_prod] at hp
  have hc : Fintype.card J = Fintype.card H :=
    Fintype.card_congr (AddSubgroup.addSubgroupOfEquivOfLe
      (isotropic_le_phaseAnnihilator q beta H hquad hiso)).toEquiv
  rw [hc] at hp
  rw [phaseAnnihilator_card beta H hsymm hnd, hp]
  ring

theorem quadratic_phase_gluing_normalized (q : A → ℂ) (beta : A → AddChar A ℂ)
    (H : AddSubgroup A)
    (hquad : ∀ x y, q (x+y) = q x * q y * beta x y)
    (hsymm : ∀ x y, beta x y = beta y x)
    (hiso : ∀ y ∈ H, q y = 1)
    (hnd : ∀ x : A, x ≠ 0 → beta x ≠ 1)
    [Fintype ((phaseAnnihilator beta H) ⧸ H.addSubgroupOf (phaseAnnihilator beta H))] :
    (∑ x : A, q x) / (Real.sqrt (Fintype.card A) : ℂ) =
      (∑ x, gluedPhase q beta H hquad hsymm hiso x) /
        (Real.sqrt (Fintype.card ((phaseAnnihilator beta H) ⧸
          H.addSubgroupOf (phaseAnnihilator beta H))) : ℂ) := by
  let B := (phaseAnnihilator beta H) ⧸ H.addSubgroupOf (phaseAnnihilator beta H)
  have hc := quadratic_phase_gluing_card q beta H hquad hsymm hiso hnd
  have hcr : (Fintype.card A : ℝ) = (Fintype.card H : ℝ)^2 * (Fintype.card B : ℝ) := by
    exact_mod_cast hc
  have hs : Real.sqrt (Fintype.card A) =
      (Fintype.card H : ℝ) * Real.sqrt (Fintype.card B) := by
    rw [hcr, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
  have hsc : (Real.sqrt (Fintype.card A) : ℂ) =
      (Fintype.card H : ℂ) * (Real.sqrt (Fintype.card B) : ℂ) := by
    exact_mod_cast hs
  have hn : (Fintype.card H : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Fintype.card_pos (α := H))
  rw [quadratic_phase_gluing_sum q beta H hquad hsymm hiso, hsc]
  exact mul_div_mul_left _ _ hn

#print axioms sum_comp_add_quotient
#print axioms isotropic_le_phaseAnnihilator
#print axioms quadratic_phase_sum_annihilator
#print axioms quadratic_phase_gluing_sum
#print axioms quadratic_phase_gluing_card
#print axioms quadratic_phase_gluing_normalized
end Conway99
