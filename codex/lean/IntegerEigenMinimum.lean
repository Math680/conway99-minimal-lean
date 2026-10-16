import IntegerEigenNorm
import BipartiteSupportBound

/-! The minimum squared Euclidean norm of a nonzero integral -4 eigenvector.
The support count does not assume the two supports are cocliques. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def positiveCodeSupport (b : V → ℤ) : Finset V := Finset.univ.filter (fun u => b u = 1)
def negativeCodeSupport (b : V → ℤ) : Finset V := Finset.univ.filter (fun u => b u = -1)

theorem sign_code_sum (b : V → ℤ)
    (hb : ∀ u, b u = -1 ∨ b u = 0 ∨ b u = 1) :
    ∑ u, b u = (positiveCodeSupport b).card - (negativeCodeSupport b).card := by
  have ht (u : V) : b u = (if b u = 1 then 1 else 0) - (if b u = -1 then 1 else 0) := by
    rcases hb u with hh | hh | hh <;> simp [hh]
  rw [Finset.sum_congr rfl (fun u _ => ht u), Finset.sum_sub_distrib]
  simp [positiveCodeSupport, negativeCodeSupport, Finset.sum_boole]

theorem sign_code_norm (b : V → ℤ)
    (hb : ∀ u, b u = -1 ∨ b u = 0 ∨ b u = 1) :
    ∑ u, b u ^ 2 = (positiveCodeSupport b).card + (negativeCodeSupport b).card := by
  have ht (u : V) : b u ^ 2 = (if b u = 1 then 1 else 0) + (if b u = -1 then 1 else 0) := by
    rcases hb u with hh | hh | hh <;> simp [hh]
  simp_rw [ht, Finset.sum_add_distrib]
  simp [positiveCodeSupport, negativeCodeSupport, Finset.sum_boole]

theorem sign_code_neighbor_sum (b : V → ℤ)
    (hb : ∀ u, b u = -1 ∨ b u = 0 ∨ b u = 1) (u : V) :
    (∑ v, if G.Adj u v then b v else 0) =
      ((positiveCodeSupport b).filter (G.Adj u)).card -
      ((negativeCodeSupport b).filter (G.Adj u)).card := by
  have ht (v : V) : (if G.Adj u v then b v else 0) =
      (if b v = 1 ∧ G.Adj u v then 1 else 0) -
      (if b v = -1 ∧ G.Adj u v then 1 else 0) := by
    rcases hb v with hh | hh | hh <;> by_cases ha : G.Adj u v <;> simp [hh, ha]
  simp_rw [ht, Finset.sum_sub_distrib]
  simp [positiveCodeSupport, negativeCodeSupport, Finset.filter_filter, Finset.sum_boole]

theorem integer_eigen_minimum_fourteen (h : G.IsSRGWith 99 14 1 2)
    (b : V → ℤ) (hb : b ≠ 0) (hs : ∑ u, b u = 0)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u) :
    14 ≤ ∑ u, b u ^ 2 := by
  by_contra hnot
  have hn : (∑ u, b u ^ 2) ≤ 14 := by omega
  have hsign := integer_eigen_small_coordinates G b hs he hn
  have hbal : (positiveCodeSupport b).card = (negativeCodeSupport b).card := by
    have hh := sign_code_sum b hsign
    omega
  have hp : (positiveCodeSupport b).Nonempty := by
    by_contra hnP
    have hzero : (positiveCodeSupport b).card = 0 := by
      simpa only [Finset.not_nonempty_iff_eq_empty, Finset.card_eq_zero] using hnP
    have hnzero : (negativeCodeSupport b).card = 0 := by omega
    apply hb
    funext u
    rcases hsign u with hu | hu | hu
    · have hm : u ∈ negativeCodeSupport b := by simp [negativeCodeSupport, hu]
      have hh := Finset.card_pos.mpr ⟨u, hm⟩
      omega
    · exact hu
    · have hm : u ∈ positiveCodeSupport b := by simp [positiveCodeSupport, hu]
      have hh := Finset.card_pos.mpr ⟨u, hm⟩
      omega
  have hpdeg : ∀ u ∈ positiveCodeSupport b,
      4 ≤ ((negativeCodeSupport b).filter (G.Adj u)).card := by
    intro u hu
    have hv : b u = 1 := (Finset.mem_filter.mp hu).2
    have hh := sign_code_neighbor_sum G b hsign u
    rw [he, hv] at hh
    omega
  have hndeg : ∀ u ∈ negativeCodeSupport b,
      4 ≤ ((positiveCodeSupport b).filter (G.Adj u)).card := by
    intro u hu
    have hv : b u = -1 := (Finset.mem_filter.mp hu).2
    have hh := sign_code_neighbor_sum G b hsign u
    rw [he, hv] at hh
    omega
  have hseven := bipartite_four_neighbors_support_bound G h _ _ hp hpdeg hndeg
  have hnorm := sign_code_norm b hsign
  omega

theorem integerAmbient_minimum_fourteen (h : G.IsSRGWith 99 14 1 2)
    (b : V → ℤ) (hb : b ≠ 0)
    (hE : (fun u => (b u : ℚ)) ∈ rationalAmbient G) :
    14 ≤ ∑ u, b u ^ 2 :=
  integer_eigen_minimum_fourteen G h b hb (integerAmbient_sum_zero G h b hE)
    (integerAmbient_eigen G h b hE)

#print axioms integer_eigen_minimum_fourteen
#print axioms integerAmbient_minimum_fourteen

end Conway99
