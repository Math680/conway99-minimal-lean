import LatticeBidual
import LatticeParity
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.RingTheory.Localization.Integer

/-! An actual orthogonal full-rank sublattice of the canonical lattice.
This supports an alternative Milgram route via one-dimensional theta
identities and finite gluing. It does not assert that route is complete. -/

namespace Conway99

open scoped BigOperators Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem canonicalLattice_multiple_of_finite_family
    (h : G.IsSRGWith 99 14 1 2) {I : Type*} [Fintype I]
    (f : I → rationalAmbient G) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ i, (m : ℚ) • (f i : V → ℚ) ∈ canonicalLattice G := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (fun p : I × V => (f p.1 : V → ℚ) p.2)
  have hc (p : I × V) : ∃ c : ℤ, (c : ℚ) = (d.val : ℚ) * (f p.1 : V → ℚ) p.2 := by
    obtain ⟨c, hc⟩ := hd p
    exact ⟨c, by simpa [Algebra.smul_def] using hc⟩
  choose c hc using hc
  have hdz : d.val ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
  refine ⟨21 * d.val, mul_ne_zero (by norm_num) hdz, ?_⟩
  intro i
  have hsum : (∑ u, c (i,u)) = 0 := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    simp_rw [hc]
    rw [← Finset.mul_sum, rationalAmbient_sum_zero G h (f i).property]
    simp
  have hcoef : (fun u => c (i,u)) ∈ canonicalCoefficients (V := V) := by
    change 3 ∣ ∑ u, c (i,u)
    rw [hsum]
    exact dvd_zero _
  have heq : coefficientCode G (fun u => c (i,u)) =
      ((21 * d.val : ℤ) : ℚ) • (f i : V → ℚ) := by
    have hcoords : (fun u => (c (i,u) : ℚ)) = (d.val : ℚ) • (f i : V → ℚ) := by
      ext u
      exact hc (i,u)
    change (1 / 3 : ℚ) • ((vertexGram G) *ᵥ (fun u => (c (i,u) : ℚ))) = _
    rw [hcoords, Matrix.mulVec_smul, rationalAmbient_fixed G h (f i).property]
    simp only [smul_smul, Int.cast_mul, Int.cast_ofNat]
    congr 1
    ring
  rw [← heq]
  exact Submodule.mem_map.mpr ⟨(fun u => c (i,u)), hcoef, rfl⟩

theorem canonicalLattice_orthogonal_integral_basis
    (h : G.IsSRGWith 99 14 1 2) :
    ∃ e : Module.Basis (Fin 44) ℚ (rationalAmbient G),
      (∀ i, (e i : V → ℚ) ∈ canonicalLattice G) ∧
      (∀ i j, i ≠ j → codePair (e i : V → ℚ) (e j : V → ℚ) = 0) ∧
      ∃ a : Fin 44 → ℤ, (∀ i, 0 < a i) ∧
        ∀ i, codePair (e i : V → ℚ) (e i : V → ℚ) = (2 * a i : ℤ) := by
  classical
  letI : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  have hex := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.mp (ambientPairing_symm G))
  rw [rationalAmbient_finrank G h] at hex
  obtain ⟨b, hb⟩ := hex
  obtain ⟨m, hm, hmem⟩ := canonicalLattice_multiple_of_finite_family G h b
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  let u : ℚˣ := Units.mk0 (m : ℚ) hmq
  let e := b.unitsSMul (fun _ => u)
  have he (i : Fin 44) : (e i : V → ℚ) = (m : ℚ) • (b i : V → ℚ) := by
    simp [e, Module.Basis.unitsSMul_apply, u]
  have hem (i : Fin 44) : (e i : V → ℚ) ∈ canonicalLattice G := by
    rw [he]
    exact hmem i
  have hn (i : Fin 44) := canonicalLattice_even G h (hem i)
  choose a ha using hn
  refine ⟨e, hem, ?_, a, ?_, ha⟩
  · intro i j hij
    rw [he, he, codePair_smul_left, codePair_smul_right]
    have hh : codePair (b i : V → ℚ) (b j : V → ℚ) = 0 := hb hij
    rw [hh]
    simp
  · intro i
    have hne : (e i : V → ℚ) ≠ 0 := by
      intro hz
      exact e.ne_zero i (Subtype.ext hz)
    have hp := codePair_pos (e i : V → ℚ) hne
    rw [ha i] at hp
    have hh : (0 : ℤ) < 2 * a i := by exact_mod_cast hp
    omega

#print axioms canonicalLattice_multiple_of_finite_family
#print axioms canonicalLattice_orthogonal_integral_basis

end Conway99
