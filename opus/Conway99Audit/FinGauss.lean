import Mathlib

/-!
# Part C, step 3: two lemmas on finite abelian groups

* `sum_eq_sum_good`: if `φ (x + h) = φ x · β x h` for `h` in a subgroup `H`, with `β x`
  multiplicative on `H`, then `∑_x φ x = ∑_{x : β x ≡ 1 on H} φ x` (character orthogonality).
* `sum_comp_surj`: summing `f ∘ π` over `A` for a surjective homomorphism `π : A → B`.
-/

open Finset

namespace Conway99

lemma sum_eq_sum_good {F : Type*} [AddCommGroup F] [Fintype F] (φ : F → ℂ) (β : F → F → ℂ)
    (H : AddSubgroup F) [Fintype H]
    (hβ : ∀ x h1 h2, β x (h1 + h2) = β x h1 * β x h2)
    (hφ : ∀ x, ∀ h ∈ H, φ (x + h) = φ x * β x h)
    [DecidablePred (fun x => ∀ h ∈ H, β x h = 1)] :
    ∑ x, φ x = ∑ x ∈ univ.filter (fun x => ∀ h ∈ H, β x h = 1), φ x := by
  -- `U x = ∑_{h ∈ H} β x h` is `|H|` or `0`
  have hU : ∀ x, ¬ (∀ h ∈ H, β x h = 1) → ∑ h : H, β x h = 0 := by
    intro x hx
    push Not at hx
    obtain ⟨h0, hh0, hne⟩ := hx
    have hshift : ∑ h : H, β x h = (∑ h : H, β x h) * β x h0 := by
      rw [Finset.sum_mul]
      refine (Fintype.sum_equiv (Equiv.addRight (⟨h0, hh0⟩ : H)) _ _ ?_).symm
      intro h
      simp [hβ]
    have : (∑ h : H, β x h) * (1 - β x h0) = 0 := by linear_combination hshift
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd (by linear_combination -h) hne
  have hU1 : ∀ x, (∀ h ∈ H, β x h = 1) → ∑ h : H, β x h = Fintype.card H := by
    intro x hx
    rw [Finset.sum_congr rfl (fun (h : H) _ => hx (h : F) h.2)]
    simp
  set T : F → ℂ := fun x => ∑ h : H, φ (x + h) with hT
  have hTx : ∀ x, T x = φ x * ∑ h : H, β x h := by
    intro x; simp only [hT]; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun h _ => hφ x h h.2)
  have htot : ∑ x, T x = Fintype.card H * ∑ x, φ x := by
    simp only [hT]
    rw [Finset.sum_comm]
    have : ∀ h : H, ∑ x, φ (x + h) = ∑ x, φ x :=
      fun h => Fintype.sum_equiv (Equiv.addRight (h : F)) _ _ (fun x => rfl)
    rw [Finset.sum_congr rfl (fun h _ => this h), sum_const, nsmul_eq_mul, card_univ]
  have hgood : ∑ x, T x = Fintype.card H * ∑ x ∈ univ.filter (fun x => ∀ h ∈ H, β x h = 1), φ x := by
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [hTx]
    split_ifs with hx
    · rw [hU1 x hx]; ring
    · rw [hU x hx]; ring
  have hcard : (Fintype.card H : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hcard
  rw [← htot, hgood]

/-- Summing `f ∘ π` for a surjective homomorphism `π`. -/
lemma sum_comp_surj {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B]
    [DecidableEq B] (π : A →+ B) (hπ : Function.Surjective π) (f : B → ℂ) :
    (Fintype.card B : ℂ) * ∑ a, f (π a) = Fintype.card A * ∑ b, f b := by
  classical
  have hfib : ∀ b, (univ.filter (fun a => π a = b)).card = (univ.filter (fun a => π a = 0)).card :=
    fun b => AddMonoidHom.card_fiber_eq_of_mem_range π (hπ b) ⟨0, map_zero π⟩
  set k := (univ.filter (fun a => π a = (0 : B))).card with hk
  have hsum : ∑ a, f (π a) = k * ∑ b, f b := by
    rw [← Finset.sum_fiberwise univ π (fun a => f (π a)), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_congr rfl (fun a ha => by rw [(Finset.mem_filter.1 ha).2]), sum_const,
      hfib b, nsmul_eq_mul]
  have hcardA : Fintype.card A = Fintype.card B * k := by
    rw [← card_univ, Finset.card_eq_sum_card_fiberwise (f := π) (t := univ)
      (fun a _ => mem_univ _)]
    rw [Finset.sum_congr rfl (fun b _ => hfib b), sum_const, card_univ, smul_eq_mul]
  rw [hsum, hcardA]; push_cast; ring

end Conway99
