import LatticeStructure

/-! Initial norm estimates for integral minus-four eigenvectors.
The final support-counting bound is developed separately. -/

namespace Conway99

open scoped BigOperators Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem integerAmbient_sum_zero (h : G.IsSRGWith 99 14 1 2) (b : V → ℤ)
    (hb : (fun u => (b u : ℚ)) ∈ rationalAmbient G) : ∑ u, b u = 0 := by
  exact_mod_cast rationalAmbient_sum_zero G h hb

theorem integerAmbient_eigen (h : G.IsSRGWith 99 14 1 2) (b : V → ℤ)
    (hb : (fun u => (b u : ℚ)) ∈ rationalAmbient G) (u : V) :
    (∑ v, if G.Adj u v then b v else 0) = -4 * b u := by
  have he := congrFun (rationalAmbient_eigen G h hb) u
  simp only [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply,
    Pi.smul_apply, smul_eq_mul, ite_mul, one_mul, zero_mul] at he
  exact_mod_cast he

theorem int_abs_le_square (a : ℤ) : |a| ≤ a ^ 2 := by
  have ha := abs_nonneg a
  have hs := sq_abs a
  by_cases hz : |a| = 0
  · nlinarith
  · have h1 : 1 ≤ |a| := by omega
    nlinarith

theorem integer_eigen_l1_bound (b : V → ℤ) (hs : ∑ u, b u = 0)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u) (u : V) :
    8 * |b u| ≤ ∑ v, |b v| := by
  let p : ℤ := ∑ v, max (b v) 0
  let n : ℤ := ∑ v, max (-b v) 0
  have hpn : p = n := by
    have ht : ∑ v, b v = p - n := by
      change ∑ v, b v = (∑ v, max (b v) 0) - ∑ v, max (-b v) 0
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro v _
      omega
    omega
  have hl1 : ∑ v, |b v| = p + n := by
    change ∑ v, |b v| = (∑ v, max (b v) 0) + ∑ v, max (-b v) 0
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rcases le_total 0 (b v) with hv | hv
    · rw [abs_of_nonneg hv]; omega
    · rw [abs_of_nonpos hv]; omega
  have hlo : -n ≤ ∑ v, if G.Adj u v then b v else 0 := by
    change -(∑ v, max (-b v) 0) ≤ _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro v _
    split_ifs <;> omega
  have hup : (∑ v, if G.Adj u v then b v else 0) ≤ p := by
    apply Finset.sum_le_sum
    intro v _
    split_ifs <;> omega
  rw [he] at hlo hup
  rw [hl1]
  rcases le_total 0 (b u) with hu | hu
  · rw [abs_of_nonneg hu]; omega
  · rw [abs_of_nonpos hu]; omega

theorem integer_eigen_large_coordinate (b : V → ℤ) (hs : ∑ u, b u = 0)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u)
    (u : V) (hu : 2 ≤ |b u|) : 18 ≤ ∑ v, b v ^ 2 := by
  have hl := integer_eigen_l1_bound G b hs he u
  have hg : b u ^ 2 - |b u| ≤ ∑ v, (b v ^ 2 - |b v|) := by
    exact Finset.single_le_sum (fun v _ => sub_nonneg.mpr (int_abs_le_square (b v)))
      (Finset.mem_univ u)
  rw [Finset.sum_sub_distrib] at hg
  have hsq := sq_abs (b u)
  nlinarith

theorem integer_eigen_small_coordinates (b : V → ℤ) (hs : ∑ u, b u = 0)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u)
    (hn : (∑ v, b v ^ 2) ≤ 14) (u : V) : b u = -1 ∨ b u = 0 ∨ b u = 1 := by
  have ha : |b u| ≤ 1 := by
    by_contra hnot
    have hh := integer_eigen_large_coordinate G b hs he u (by omega)
    omega
  have hb := abs_le.mp ha
  omega

#print axioms integerAmbient_eigen
#print axioms integer_eigen_l1_bound
#print axioms integer_eigen_small_coordinates

end Conway99
