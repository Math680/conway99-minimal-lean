import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
Individually checked algebraic parts of the minimal proof.
This file does NOT yet prove the final theorem from an SRG hypothesis.
Every premise that is still an interface to the geometric proof is explicit.
-/

namespace Conway99

open scoped BigOperators
open Finset

theorem nonzero_residue_square (z e : ℤ) (he : e = 1 ∨ e = -1)
    (hz : z % 3 = e % 3) : 2 ≤ z ^ 2 + e * z := by
  rcases he with rfl | rfl
  · have : z ≤ -2 ∨ 1 ≤ z := by omega
    rcases this with h | h <;> nlinarith
  · have : z ≤ -1 ∨ 2 ≤ z := by omega
    rcases this with h | h <;> nlinarith

theorem no_nonzero_common_residue
    (z : Fin 99 → ℤ) (e : ℤ) (he : e = 1 ∨ e = -1)
    (hz : ∀ u, z u % 3 = e % 3)
    (hsum : ∑ u, z u = 0) (hnorm : ∑ u, z u ^ 2 = 126) : False := by
  have hh := Finset.sum_le_sum (s := (univ : Finset (Fin 99)))
    (fun u _ => nonzero_residue_square (z u) e he (hz u))
  simp only [sum_add_distrib, ← mul_sum, hsum, hnorm, mul_zero, add_zero,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  norm_num at hh

theorem root_coordinate_divisibility (z : Fin 99 → ℤ) (r : ℤ)
    (hz : ∀ u, z u % 3 = r % 3)
    (hsum : ∑ u, z u = 0) (hnorm : ∑ u, z u ^ 2 = 126) :
    ∀ u, 3 ∣ z u := by
  have hr : r % 3 = 0 := by
    by_contra h
    have hres : r % 3 = 1 ∨ r % 3 = 2 := by omega
    rcases hres with hres | hres
    · exact no_nonzero_common_residue z 1 (Or.inl rfl)
        (fun u => by rw [hz u, hres]; norm_num) hsum hnorm
    · exact no_nonzero_common_residue z (-1) (Or.inr rfl)
        (fun u => by rw [hz u, hres]; norm_num) hsum hnorm
  intro u
  exact Int.dvd_of_emod_eq_zero (by rw [hz u, hr])

theorem even_image_gap (q : ℤ) (hpos : 0 < q) (heven : 2 ∣ q)
    (hnotroot : q ≠ 2) : 4 ≤ q := by
  obtain ⟨m, rfl⟩ := heven
  omega

theorem diagonal_rounding (k : ℤ) (h4 : 4 ∣ k) (hgap : 396 ≤ 7 * k) : 60 ≤ k := by
  obtain ⟨q, rfl⟩ := h4
  omega

/-- Arithmetic endpoint only: the trace identity and diagonal bounds remain premises. -/
theorem delta_from_diagonal_data (d : ℤ) (K : Fin 231 → ℤ)
    (h4 : ∀ i, 4 ∣ K i) (hgap : ∀ i, 396 ≤ 7 * K i)
    (htrace : ∑ i, K i = 84 * d) : 165 ≤ d := by
  have hh := Finset.sum_le_sum (s := (univ : Finset (Fin 231)))
    (fun i _ => diagonal_rounding (K i) (h4 i) (hgap i))
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, htrace] at hh
  omega

theorem counting_endpoint (N₂ N₃ d : ℤ)
    (hmoment : N₂ + 3 * N₃ = 4158) (hd : d = N₂ - 693)
    (hbound : 165 ≤ d) :
    d = 3465 - 3 * N₃ ∧ 3 ∣ d ∧ 858 ≤ N₂ ∧ N₃ ≤ 1100 := by
  refine ⟨by omega, ?_, by omega, by omega⟩
  refine ⟨1155 - N₃, ?_⟩
  omega

private theorem twice_square_sub (x : ZMod 4) : 2 * (x ^ 2 - x) = 0 := by
  revert x
  decide

/-- Pairing (j,k) with (k,j) gives a shorter proof of the diagonal congruence.
The diagonal assumption here is precisely the image of S_jj = 4 modulo 4. -/
theorem symmetric_square_contraction_mod4 {n : Type*} [Fintype n]
    (S : Matrix n n (ZMod 4)) (a : n → ZMod 4)
    (hsym : ∀ j k, S j k = S k j) (hdiag : ∀ j, S j j = 0) :
    (∑ j, ∑ k, a j * a k * (S j k) ^ 2) =
      ∑ j, ∑ k, a j * a k * S j k := by
  classical
  let F : n × n → ZMod 4 := fun p =>
    a p.1 * a p.2 * ((S p.1 p.2) ^ 2 - S p.1 p.2)
  have hf : ∑ p : n × n, F p = 0 := by
    apply Finset.sum_ninvolution Prod.swap
    · intro p
      dsimp [F]
      rw [hsym p.2 p.1]
      calc
        a p.1 * a p.2 * (S p.1 p.2 ^ 2 - S p.1 p.2) +
            a p.2 * a p.1 * (S p.1 p.2 ^ 2 - S p.1 p.2) =
          (a p.1 * a p.2) * (2 * (S p.1 p.2 ^ 2 - S p.1 p.2)) := by ring
        _ = 0 := by rw [twice_square_sub]; ring
    · intro p hp hfix
      have h : p.1 = p.2 := by simpa using congrArg Prod.snd hfix
      apply hp
      simp [F, h, hdiag]
    · intro p
      exact mem_univ _
    · intro p
      exact Prod.swap_swap p
  rw [Fintype.sum_prod_type] at hf
  apply sub_eq_zero.mp
  simpa only [sum_sub_distrib, mul_sub, F] using hf

theorem idempotent_contraction_mod4 {n : Type*} [Fintype n]
    (S : Matrix n n (ZMod 4)) (i : n)
    (hsym : ∀ j k, S j k = S k j) (hdiag : ∀ j, S j j = 0)
    (hmul : S * S = S) :
    (∑ j, ∑ k, S i j * S i k * (S j k) ^ 2) = 0 := by
  rw [symmetric_square_contraction_mod4 S (S i) hsym hdiag]
  have hcube : S * (S * S) = S := by rw [hmul, hmul]
  have he := congrArg (fun M : Matrix n n (ZMod 4) => M i i) hcube
  simp only [Matrix.mul_apply, mul_sum] at he
  rw [hdiag i] at he
  convert he using 1
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  rw [hsym k i]
  ring

/-- Fully proved diagonal divisibility for an arbitrary integer Gram
matrix with diagonal 4 and S² = 21 S. No tensor congruence is assumed. -/
theorem diagonal_contraction_divisible_four {n : Type*} [Fintype n]
    (S : Matrix n n ℤ) (i : n)
    (hsym : ∀ j k, S j k = S k j) (hdiag : ∀ j, S j j = 4)
    (hmul : S * S = (21 : ℤ) • S) :
    4 ∣ ∑ j, ∑ k, S i j * S i k * (S j k) ^ 2 := by
  let R : Matrix n n (ZMod 4) := fun j k => (S j k : ZMod 4)
  have hrsym : ∀ j k, R j k = R k j := fun j k => by dsimp [R]; rw [hsym j k]
  have hrdiag : ∀ j, R j j = 0 := fun j => by
    dsimp [R]
    rw [hdiag j]
    exact ZMod.natCast_self 4
  have hrmul : R * R = R := by
    ext j k
    have he := congrArg (fun M : Matrix n n ℤ => (M j k : ZMod 4)) hmul
    have hc21 : (21 : ZMod 4) = 1 := by decide
    simpa [Matrix.mul_apply, Matrix.smul_apply, R, hc21] using he
  have hc := idempotent_contraction_mod4 R i hrsym hrdiag hrmul
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp
  simpa [R] using hc

def diagonalContraction {n : Type*} [Fintype n] (S : Matrix n n ℤ) (i : n) : ℤ :=
  ∑ j, ∑ k, S i j * S i k * (S j k) ^ 2

/-- The trace identity is proved from the Gram equation, not assumed. -/
theorem contraction_total {n : Type*} [Fintype n] (S : Matrix n n ℤ)
    (hsym : ∀ j k, S j k = S k j) (hmul : S * S = (21 : ℤ) • S) :
    (∑ i, diagonalContraction S i) = 21 * ∑ j, ∑ k, (S j k) ^ 3 := by
  have hp (j k : n) : (∑ i, S i j * S i k) = 21 * S j k := by
    calc
      (∑ i, S i j * S i k) = (S * S) j k := by
        simp only [Matrix.mul_apply]
        apply sum_congr rfl
        intro i _
        rw [hsym i j]
      _ = _ := by rw [hmul]; rfl
  unfold diagonalContraction
  calc
    (∑ i, ∑ j, ∑ k, S i j * S i k * S j k ^ 2) =
        ∑ j, ∑ k, ∑ i, S i j * S i k * S j k ^ 2 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      rw [sum_comm]
    _ = ∑ j, ∑ k, (∑ i, S i j * S i k) * S j k ^ 2 := by
      simp only [sum_mul]
    _ = ∑ j, ∑ k, (21 * S j k) * S j k ^ 2 := by simp_rw [hp]
    _ = 21 * ∑ j, ∑ k, S j k ^ 3 := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro k _
      ring

/-- Conditional interface to sections 2--3. The cubic count and geometric
image gap still have to be constructed from the graph. -/
theorem delta_from_gram_data (S : Matrix (Fin 231) (Fin 231) ℤ) (d : ℤ)
    (hsym : ∀ j k, S j k = S k j) (hdiag : ∀ j, S j j = 4)
    (hmul : S * S = (21 : ℤ) • S)
    (hcube : (∑ j, ∑ k, S j k ^ 3) = 4 * d)
    (hgap : ∀ i, 396 ≤ 7 * diagonalContraction S i) : 165 ≤ d := by
  apply delta_from_diagonal_data d (diagonalContraction S)
    (fun i => diagonal_contraction_divisible_four S i hsym hdiag hmul) hgap
  rw [contraction_total S hsym hmul, hcube]
  ring

#print axioms root_coordinate_divisibility
#print axioms even_image_gap
#print axioms diagonal_contraction_divisible_four
#print axioms contraction_total
#print axioms delta_from_gram_data

#print axioms nonzero_residue_square
#print axioms no_nonzero_common_residue
#print axioms delta_from_diagonal_data
#print axioms counting_endpoint
#print axioms symmetric_square_contraction_mod4
#print axioms idempotent_contraction_mod4

end Conway99
