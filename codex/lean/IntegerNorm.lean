import Core

/-!
Evenness of an integral Gram norm and the numerical norm gap used in section 3.
These are numerical interfaces; the construction of their data from the graph
is not claimed in this file.
-/

namespace Conway99

open scoped BigOperators
open Finset

/-- An integral symmetric matrix with even diagonal defines an even quadratic form. -/
theorem symmetric_integral_norm_even {n : Type*} [Fintype n]
    (S : Matrix n n ℤ) (c : n → ℤ)
    (hsym : ∀ j k, S j k = S k j) (hdiag : ∀ j, 2 ∣ S j j) :
    2 ∣ ∑ j, ∑ k, c j * c k * S j k := by
  classical
  let F : n × n → ZMod 2 := fun p =>
    (c p.1 : ZMod 2) * (c p.2 : ZMod 2) * (S p.1 p.2 : ZMod 2)
  have hd (j : n) : (S j j : ZMod 2) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr (hdiag j)
  have hf : ∑ p : n × n, F p = 0 := by
    apply Finset.sum_ninvolution Prod.swap
    · intro p
      dsimp [F]
      rw [hsym p.2 p.1]
      calc
        (c p.1 : ZMod 2) * c p.2 * S p.1 p.2 +
            (c p.2 : ZMod 2) * c p.1 * S p.1 p.2 =
          (2 : ZMod 2) * ((c p.1 : ZMod 2) * c p.2 * S p.1 p.2) := by ring
        _ = 0 := by
          have ht : (2 : ZMod 2) = 0 := by decide
          rw [ht, zero_mul]
    · intro p hp hfix
      have h : p.1 = p.2 := by simpa using congrArg Prod.snd hfix
      apply hp
      simp [F, h, hd]
    · intro p
      exact mem_univ _
    · intro p
      exact Prod.swap_swap p
  rw [Fintype.sum_prod_type] at hf
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
  simpa [F] using hf

theorem diagonal_four_integral_norm_even {n : Type*} [Fintype n]
    (S : Matrix n n ℤ) (c : n → ℤ)
    (hsym : ∀ j k, S j k = S k j) (hdiag : ∀ j, S j j = 4) :
    2 ∣ ∑ j, ∑ k, c j * c k * S j k := by
  apply symmetric_integral_norm_even S c hsym
  intro j
  rw [hdiag j]
  norm_num

/-- The selected coordinate excludes zero norm and norm two. No lattice is assumed. -/
theorem integer_image_norm_gap (q : ℤ) (z : Fin 99 → ℤ) (r : ℤ) (u : Fin 99)
    (_hq : 0 ≤ q) (heven : 2 ∣ q)
    (hsum : ∑ v, z v = 0) (hnorm : ∑ v, z v ^ 2 = 63 * q)
    (hres : ∀ v, z v % 3 = r % 3)
    (hu : z u = 4 ∨ z u = -2 ∨ z u = 1) : 4 ≤ q := by
  have hsingle : z u ^ 2 ≤ ∑ v, z v ^ 2 := by
    exact Finset.single_le_sum (fun v _ => sq_nonneg (z v)) (mem_univ u)
  have hu_pos : 0 < z u ^ 2 := by
    rcases hu with hu | hu | hu <;> rw [hu] <;> norm_num
  have hpos : 0 < q := by nlinarith
  have hnotroot : q ≠ 2 := by
    intro hq
    have hn : ∑ v, z v ^ 2 = 126 := by rw [hnorm, hq]; norm_num
    have hdiv := root_coordinate_divisibility z r hres hsum hn u
    rcases hu with hu | hu | hu <;> rw [hu] at hdiv <;> norm_num at hdiv
  exact even_image_gap q hpos heven hnotroot

/-- Coordinate-independent version, reindexed through an explicit equivalence. -/
theorem integer_image_norm_gap_of_card {V : Type*} [Fintype V]
    (hcard : Fintype.card V = 99) (q : ℤ) (z : V → ℤ) (r : ℤ) (u : V)
    (hq : 0 ≤ q) (heven : 2 ∣ q)
    (hsum : ∑ v, z v = 0) (hnorm : ∑ v, z v ^ 2 = 63 * q)
    (hres : ∀ v, z v % 3 = r % 3)
    (hu : z u = 4 ∨ z u = -2 ∨ z u = 1) : 4 ≤ q := by
  classical
  let e : Fin 99 ≃ V := Fintype.equivOfCardEq (by simpa using hcard.symm)
  have hs : (∑ v : Fin 99, z (e v)) = ∑ v, z v :=
    Fintype.sum_equiv e (fun v => z (e v)) z (fun _ => rfl)
  have hn : (∑ v : Fin 99, z (e v) ^ 2) = ∑ v, z v ^ 2 :=
    Fintype.sum_equiv e (fun v => z (e v) ^ 2) (fun v => z v ^ 2) (fun _ => rfl)
  apply integer_image_norm_gap q (fun v => z (e v)) r (e.symm u) hq heven
  · rw [hs]
    exact hsum
  · rw [hn]
    exact hnorm
  · intro v
    exact hres (e v)
  · simpa using hu

#print axioms symmetric_integral_norm_even
#print axioms diagonal_four_integral_norm_even
#print axioms integer_image_norm_gap
#print axioms integer_image_norm_gap_of_card

end Conway99
