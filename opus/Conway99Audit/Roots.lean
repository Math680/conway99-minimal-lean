import Conway99Audit.Biplane

/-!
# Part B, step 2: the auxiliary lattice in coordinates, roots, and orthogonality (§§4.1, 5.1, 5.2)

**Dictionary.** For `f ∈ ℝ⁴⁴` put `z = Wᵀ f ∈ ℝ^V` (its *profile*, `z_u = w_u · f`).  Then
`f · g = (z · z') / 63`, `Wᵀ` is injective, and its image is the `-4` eigenspace of `A`.
The lattice `N = {(1/3) Σ c_u w_u : 3 ∣ Σ c}` has profiles `Nvec c = G0 c / 3`.
An even integral lattice `N̂ ⊇ N` therefore corresponds exactly to an additive subgroup
`L ⊆ ℤ^V` of `-4` eigenvectors containing all `Nvec c`, with `63 ∣ z·z'` and `126 ∣ z·z`.
A root (`f² = 2`) is a profile with `z·z = 126`.

Note that the determinant 49 of `N̂` plays no role in the root bound: everything below holds
for every even integral overlattice of `N` (in particular for `N̂` and for `N` itself).
-/

open Finset SimpleGraph Matrix

namespace Conway99

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- Profile of `(1/3) Σ c_u w_u`, i.e. `G0 c / 3` (exact when `3 ∣ Σ c`). -/
def Nvec (c : V → ℤ) : V → ℤ := fun u => 9 * c u - 3 * (A G *ᵥ c) u + (∑ v, c v) / 3

variable (G) in
/-- An even integral overlattice of `N`, in profile coordinates. -/
structure EvenOverlattice where
  L : AddSubgroup (V → ℤ)
  eig : ∀ z ∈ L, IsM4 G z
  contains : ∀ c : V → ℤ, 3 ∣ ∑ v, c v → Nvec G c ∈ L
  integral : ∀ z ∈ L, ∀ z' ∈ L, 63 ∣ z ⬝ᵥ z'
  even : ∀ z ∈ L, 126 ∣ z ⬝ᵥ z

/-- `e_u - e_v`. -/
def ediff (u v : V) : V → ℤ := fun w => (if w = u then 1 else 0) - (if w = v then 1 else 0)

lemma sum_ediff (u v : V) : ∑ w, ediff u v w = 0 := by
  simp [ediff, Finset.sum_sub_distrib]

lemma dot_ediff (z : V → ℤ) (u v : V) : z ⬝ᵥ ediff u v = z u - z v := by
  simp [dotProduct, ediff, mul_sub, Finset.sum_sub_distrib]

lemma dot_A_symm (x y : V → ℤ) : x ⬝ᵥ (A G *ᵥ y) = (A G *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, A_symm]

lemma dot_single (z : V → ℤ) (u : V) : z ⬝ᵥ Pi.single u 1 = z u := by
  simp [dotProduct, Pi.single_apply]

section SRG

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

/-- `z · Nvec (e_u - e_v) = 21 (z_u - z_v)` for a `-4` eigenvector `z`. -/
lemma dot_Nvec_diff {z : V → ℤ} (hz : IsM4 G z) (u v : V) :
    z ⬝ᵥ Nvec G (ediff u v) = 21 * (z u - z v) := by
  have hN : Nvec G (ediff u v) = (9 : ℤ) • ediff u v - (3 : ℤ) • (A G *ᵥ ediff u v) := by
    funext w; simp only [Nvec, sum_ediff, Int.zero_ediv, add_zero, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
  rw [hN, dotProduct_sub, dotProduct_smul, dotProduct_smul, dot_A_symm, hz, smul_dotProduct,
    dot_ediff]
  simp only [smul_eq_mul, Pi.smul_apply]; ring

/-- Profiles of an even integral overlattice have all coordinates congruent modulo 3. -/
lemma EvenOverlattice.res (L : EvenOverlattice G) {z : V → ℤ} (hz : z ∈ L.L) (u v : V) :
    3 ∣ z u - z v := by
  have h63 := L.integral z hz _ (L.contains (ediff u v) (by rw [sum_ediff]; exact dvd_zero 3))
  rw [dot_Nvec_diff hG (L.eig z hz)] at h63
  omega

/-- Minimum of the dual: a nonzero `-4` eigenvector with congruent coordinates has norm ≥ 126
(i.e. `f² ≥ 2` for `0 ≠ f ∈ N*`, minimal proof (20)). -/
theorem min_dual {z : V → ℤ} (hz : IsM4 G z) (hres : ∀ u v, 3 ∣ z u - z v) (hne : z ≠ 0) :
    126 ≤ z ⬝ᵥ z := by
  have hcard := card_V hG
  have hsum := hz.sum_zero hG
  obtain ⟨u0⟩ := nonempty_V hG
  by_cases h3 : 3 ∣ z u0
  · -- all coordinates divisible by 3: z = 3 b
    have hall : ∀ u, 3 ∣ z u := fun u => by have := hres u u0; omega
    set b : V → ℤ := fun u => z u / 3 with hb
    have hzb : z = (3 : ℤ) • b := by
      funext u; simp only [hb, Pi.smul_apply, smul_eq_mul]; exact (Int.mul_ediv_cancel' (hall u)).symm
    have hbM : IsM4 G b := by
      have h := hz; unfold IsM4 at h ⊢; rw [hzb, Matrix.mulVec_smul] at h
      funext u; have := congrFun h u; simp only [Pi.smul_apply, smul_eq_mul] at this ⊢; linarith
    have hbne : b ≠ 0 := by intro h0; apply hne; rw [hzb, h0, smul_zero]
    have := lemma51_ge hG hbM hbne
    rw [hzb, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; linarith
  · -- common nonzero residue
    have hr : ∀ u, z u % 3 = z u0 % 3 := fun u => by have := hres u u0; omega
    have hr' : z u0 % 3 = 1 ∨ z u0 % 3 = 2 := by omega
    rcases hr' with h1 | h1
    · have hb : ∀ v, 2 ≤ z v * z v + z v := by
        intro v
        have hv := hr v; rw [h1] at hv
        obtain ⟨k, hk⟩ : ∃ k, z v = 3 * k + 1 := ⟨z v / 3, by omega⟩
        have hkk : 0 ≤ k * (k + 1) := by
          rcases le_or_gt 0 k with h | h
          · positivity
          · nlinarith
        rw [hk]; nlinarith
      have : ∑ v : V, (2 : ℤ) ≤ ∑ v, (z v * z v + z v) := Finset.sum_le_sum (fun v _ => hb v)
      rw [Finset.sum_add_distrib, hsum, sum_const, card_univ, hcard] at this
      simp only [dotProduct]; norm_num at this; linarith
    · have hb : ∀ v, 2 ≤ z v * z v - z v := by
        intro v
        have hv := hr v; rw [h1] at hv
        obtain ⟨k, hk⟩ : ∃ k, z v = 3 * k + 2 := ⟨z v / 3, by omega⟩
        have hkk : 0 ≤ k * (k + 1) := by
          rcases le_or_gt 0 k with h | h
          · positivity
          · nlinarith
        rw [hk]; nlinarith
      have : ∑ v : V, (2 : ℤ) ≤ ∑ v, (z v * z v - z v) := Finset.sum_le_sum (fun v _ => hb v)
      rw [Finset.sum_sub_distrib, hsum, sum_const, card_univ, hcard] at this
      simp only [dotProduct]; norm_num at this; linarith

/-- (21): a root is `3 b` with `b` a biplane vector. -/
theorem root_struct (L : EvenOverlattice G) {z : V → ℤ} (hz : z ∈ L.L) (h126 : z ⬝ᵥ z = 126) :
    ∃ b : V → ℤ, z = (3 : ℤ) • b ∧ IsM4 G b ∧ Biplane G b := by
  have hzM := L.eig z hz
  have hres := L.res hG hz
  have hcard := card_V hG
  have hsum := hzM.sum_zero hG
  obtain ⟨u0⟩ := nonempty_V hG
  have h3 : 3 ∣ z u0 := by
    by_contra h3
    have hr : ∀ u, z u % 3 = z u0 % 3 := fun u => by have := hres u u0; omega
    have hr' : z u0 % 3 = 1 ∨ z u0 % 3 = 2 := by omega
    rcases hr' with h1 | h1
    · have hb : ∀ v, 2 ≤ z v * z v + z v := by
        intro v
        have hv := hr v; rw [h1] at hv
        obtain ⟨k, hk⟩ : ∃ k, z v = 3 * k + 1 := ⟨z v / 3, by omega⟩
        have hkk : 0 ≤ k * (k + 1) := by
          rcases le_or_gt 0 k with h | h
          · positivity
          · nlinarith
        rw [hk]; nlinarith
      have : ∑ v : V, (2 : ℤ) ≤ ∑ v, (z v * z v + z v) := Finset.sum_le_sum (fun v _ => hb v)
      rw [Finset.sum_add_distrib, hsum, sum_const, card_univ, hcard] at this
      have h2 : ∑ v, z v * z v = 126 := h126
      rw [h2] at this; norm_num at this
    · have hb : ∀ v, 2 ≤ z v * z v - z v := by
        intro v
        have hv := hr v; rw [h1] at hv
        obtain ⟨k, hk⟩ : ∃ k, z v = 3 * k + 2 := ⟨z v / 3, by omega⟩
        have hkk : 0 ≤ k * (k + 1) := by
          rcases le_or_gt 0 k with h | h
          · positivity
          · nlinarith
        rw [hk]; nlinarith
      have : ∑ v : V, (2 : ℤ) ≤ ∑ v, (z v * z v - z v) := Finset.sum_le_sum (fun v _ => hb v)
      rw [Finset.sum_sub_distrib, hsum, sum_const, card_univ, hcard] at this
      have h2 : ∑ v, z v * z v = 126 := h126
      rw [h2] at this; norm_num at this
  have hall : ∀ u, 3 ∣ z u := fun u => by have := hres u u0; omega
  set b : V → ℤ := fun u => z u / 3 with hb
  have hzb : z = (3 : ℤ) • b := by
    funext u; simp only [hb, Pi.smul_apply, smul_eq_mul]; exact (Int.mul_ediv_cancel' (hall u)).symm
  have hbM : IsM4 G b := by
    have h := hzM; unfold IsM4 at h ⊢; rw [hzb, Matrix.mulVec_smul] at h
    funext u; have := congrFun h u; simp only [Pi.smul_apply, smul_eq_mul] at this ⊢; linarith
  have hb14 : b ⬝ᵥ b = 14 := by
    rw [hzb, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h126; linarith
  have hbne : b ≠ 0 := by intro h0; rw [h0] at hb14; simp at hb14
  exact ⟨b, hzb, hbM, lemma51 hG hbM hbne hb14.le⟩

end SRG

end Conway99
