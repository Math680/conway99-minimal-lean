import Conway99Audit.NHatFinal

/-!
# Theorem 1.1 of the minimal proof, in full

For every strongly regular graph `srg(99,14,1,2)`:
* `N₂ + 3 N₃ = 4158`, `δ = N₂ - 693 = 3465 - 3 N₃ ∈ 3ℤ`, `δ ≥ 165` (so `N₂ ≥ 858`, `N₃ ≤ 1100`);
* there is an even integral lattice `N̂ ⊇ N ⊇ Λ` (profile coordinates), of rank `44` and Gram
  determinant `49`, with `min N̂* ≥ 2`, roots `= 3 ×` biplane vectors, `Φ(N̂) = A₁^ρ`, `ρ ≤ 3`.

Profile coordinates: a vector `f` of the paper's `ℝ⁴⁴` is recorded by `z = Wᵀ f ∈ ℝ^V`
(`z_u = w_u · f`), with `f · g = z · z' / 63`; `x_L ↦ P(·, L)`, `w_u ↦ G₀ e_u`.  Since
`N ⊆ N̂`, the dual `N̂*` consists of the `z ∈ N*` (`Ndual`) with `63 ∣ z · m` for `m ∈ N̂`.
The rank is the cardinality of a `ℤ`-basis, the determinant that of the Gram matrix
`(b_i · b_j / 63)`.
-/

open Finset SimpleGraph Matrix

namespace Conway99

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem theorem_1_1 (hG : G.IsSRGWith 99 14 1 2) :
    (Nm G 2 + 3 * Nm G 3 = 4158 ∧ ((Nm G 2 : ℤ) - 693) = 3465 - 3 * (Nm G 3 : ℤ) ∧
      (3 : ℤ) ∣ ((Nm G 2 : ℤ) - 693) ∧ 165 ≤ (Nm G 2 : ℤ) - 693 ∧ 858 ≤ Nm G 2 ∧ Nm G 3 ≤ 1100) ∧
    ∃ L : EvenOverlattice G,
      (∀ t : Tr G, (fun u => P G u t) ∈ L.L) ∧
      (∀ z ∈ Ndual G, (∀ m ∈ L.L, 63 ∣ z ⬝ᵥ m) → z ≠ 0 → 126 ≤ z ⬝ᵥ z) ∧
      (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ L.L.toIntSubmodule),
        Fintype.card ι = 44) ∧
      (∃ b : Module.Basis (Fin 44) ℤ L.L.toIntSubmodule, (gram L b).det = 49) ∧
      (∀ z ∈ L.L, z ≠ 0 → 126 ≤ z ⬝ᵥ z) ∧
      (∀ z ∈ L.L, z ⬝ᵥ z = 126 → ∃ b : V → ℤ, z = (3 : ℤ) • b ∧ IsM4 G b ∧ Biplane G b) ∧
      (∀ z ∈ L.L, ∀ z' ∈ L.L, z ⬝ᵥ z = 126 → z' ⬝ᵥ z' = 126 → z' ≠ z → z' ≠ -z →
        z ⬝ᵥ z' = 0) ∧
      (∀ z : Fin 4 → V → ℤ, (∀ i, z i ∈ L.L) → (∀ i, z i ⬝ᵥ z i = 126) →
        (∀ i j, i ≠ j → z j ≠ z i ∧ z j ≠ -z i) → False) :=
  by
    obtain ⟨L, h1, h2⟩ := theorem_1_1_lattice hG
    exact ⟨part_A hG, L, h1, fun z hz _ hne => min_dual hG hz.1 hz.2 hne, h2⟩

end Conway99
