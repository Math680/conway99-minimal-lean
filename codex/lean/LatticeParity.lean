import RationalLattice
import IntegerNorm

/-! Evenness of the canonical lattice, using the actual coefficient constraint. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem square_mod_two (a : ZMod 2) : a ^ 2 = a := by
  fin_cases a <;> decide

theorem coefficientBilinear_mod_two (c : V → ℤ) :
    (coefficientBilinear G c c : ZMod 2) = ∑ u, (c u : ZMod 2) := by
  let H : Matrix V V ℤ := fun u v =>
    2 * (if u = v then 1 else 0) - (if G.Adj u v then 1 else 0)
  have heven := symmetric_integral_norm_even H c
    (by intro u v; simp [H, eq_comm, SimpleGraph.adj_comm])
    (by intro u; simp [H])
  have heq : coefficientBilinear G c c =
      (∑ u, ∑ v, c u * c v * H u v) + ∑ u, c u ^ 2 := by
    have hdiag : (∑ u, ∑ v, c u * c v * (if u = v then 1 else 0)) =
        ∑ u, c u ^ 2 := by
      simp [mul_ite, pow_two]
    rw [← hdiag]
    simp only [coefficientBilinear, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    dsimp [H]
    ring
  have hz : ((∑ u, ∑ v, c u * c v * H u v : ℤ) : ZMod 2) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr heven
  rw [heq, Int.cast_add, hz, zero_add, Int.cast_sum]
  simp only [Int.cast_pow, square_mod_two]

theorem canonicalLattice_even (h : G.IsSRGWith 99 14 1 2)
    {x : V → ℚ} (hx : x ∈ canonicalLattice G) :
    ∃ n : ℤ, codePair x x = (2 * n : ℤ) := by
  obtain ⟨c, hc, rfl⟩ := hx
  obtain ⟨a, ha⟩ := hc
  have hn : 2 ∣ a ^ 2 + coefficientBilinear G c c := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    have hs : (∑ u, (c u : ZMod 2)) = (a : ZMod 2) := by
      have ht : ((∑ u, c u : ℤ) : ZMod 2) = ((3 * a : ℤ) : ZMod 2) :=
        congrArg (fun z : ℤ => (z : ZMod 2)) ha
      have hthree : (3 : ZMod 2) = 1 := by decide
      simpa only [Int.cast_sum, Int.cast_mul, Int.cast_ofNat, hthree, one_mul] using ht
    rw [Int.cast_add, Int.cast_pow, coefficientBilinear_mod_two G c, hs,
      square_mod_two]
    have hh : (2 : ZMod 2) = 0 := by decide
    rw [← two_mul, hh, zero_mul]
  obtain ⟨n, hn⟩ := hn
  refine ⟨n, ?_⟩
  rw [coefficientCode_pair_formula G h]
  have hca : (∑ u, (c u : ℚ)) = 3 * (a : ℚ) := by exact_mod_cast ha
  have hq : (a : ℚ) ^ 2 + (coefficientBilinear G c c : ℚ) = (2 * n : ℤ) := by
    exact_mod_cast hn
  rw [hca]
  convert hq using 1 <;> ring

#print axioms canonicalLattice_even

end Conway99
