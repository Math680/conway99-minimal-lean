import FourDirectionsGeometry
import ProfileBudget

/-! Actual affine eigen-equations of the six profiles. The affine equation
is derived from SRG common-neighbour counts, not assumed. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def profileVertexBase (v u : V) : ℤ :=
  (if u = v then 3 else 0) - (if G.Adj v u then 1 else 0)

theorem profile_common_neighbors_card (h : G.IsSRGWith 99 14 1 2) (u v : V) :
    (Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj v w)).card =
      if u = v then 14 else if G.Adj u v then 1 else 2 := by
  have heq : Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj v w) =
      (G.commonNeighbors u v).toFinset := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
    rfl
  by_cases huv : u = v
  · subst v
    simpa [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter] using h.regular.degree_eq u
  · rw [heq, Set.toFinset_card, if_neg huv]
    by_cases ha : G.Adj u v
    · rw [if_pos ha, h.of_adj u v ha]
    · rw [if_neg ha, h.of_not_adj huv ha]

theorem profileVertexBase_affine_eigen (h : G.IsSRGWith 99 14 1 2) (v u : V) :
    (∑ w, if G.Adj u w then profileVertexBase G v w else 0) =
      -4 * profileVertexBase G v u - 2 := by
  have hdelta : (∑ w, if G.Adj u w then (if w = v then (3 : ℤ) else 0) else 0) =
      if G.Adj u v then 3 else 0 := by
    have ht (w : V) : (if G.Adj u w then (if w = v then (3 : ℤ) else 0) else 0) =
        if w = v then (if G.Adj u v then 3 else 0) else 0 := by
      by_cases hw : w = v <;> simp [hw]
    simp_rw [ht]
    simp
  have hcommon :
      (∑ w, if G.Adj u w then (if G.Adj v w then (1 : ℤ) else 0) else 0) =
        (Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj v w)).card := by
    simp only [← ite_and]
    simp
  have ht (w : V) : (if G.Adj u w then profileVertexBase G v w else 0) =
      (if G.Adj u w then (if w = v then 3 else 0) else 0) -
      (if G.Adj u w then (if G.Adj v w then 1 else 0) else 0) := by
    by_cases hw : G.Adj u w <;> simp [profileVertexBase, hw]
  simp_rw [ht]
  rw [Finset.sum_sub_distrib]
  rw [hdelta, hcommon, profile_common_neighbors_card G h u v]
  by_cases huv : u = v
  · subst v
    simp [profileVertexBase]
  · by_cases ha : G.Adj u v
    · have hav : G.Adj v u := ha.symm
      simp [profileVertexBase, huv, ha, hav]
    · have hav : ¬G.Adj v u := fun hh => ha hh.symm
      simp [profileVertexBase, huv, ha, hav]

theorem profile_subtract_eigenvectors {ι : Type*} [DecidableEq ι]
    (a : V → ℤ) (b : ι → V → ℤ) (eps : ι → ℤ) (D : Finset ι)
    (ha : ∀ u, (∑ w, if G.Adj u w then a w else 0) = -4 * a u - 2)
    (hb : ∀ i u, (∑ w, if G.Adj u w then b i w else 0) = -4 * b i u) (u : V) :
    (∑ w, if G.Adj u w then a w - ∑ i ∈ D, eps i * b i w else 0) =
      -4 * (a u - ∑ i ∈ D, eps i * b i u) - 2 := by
  have ht (w : V) :
      (if G.Adj u w then a w - ∑ i ∈ D, eps i * b i w else 0) =
      (if G.Adj u w then a w else 0) -
        ∑ i ∈ D, eps i * (if G.Adj u w then b i w else 0) := by
    by_cases hw : G.Adj u w <;> simp [hw]
  simp_rw [ht]
  rw [Finset.sum_sub_distrib, ha u, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hb]
  have hs : (∑ i ∈ D, eps i * (-4 * b i u)) = -4 * ∑ i ∈ D, eps i * b i u := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

namespace FourDirectionSystem

variable {G} (F : FourDirectionSystem G)

def profile (v : V) (D : Finset (Fin 4)) (u : V) : ℤ :=
  profileVertexBase G v u - ∑ i ∈ D, F.code i v * F.code i u

theorem profile_affine_eigen (h : G.IsSRGWith 99 14 1 2)
    (v : V) (D : Finset (Fin 4)) (u : V) :
    (∑ w, if G.Adj u w then F.profile v D w else 0) = -4 * F.profile v D u - 2 :=
  profile_subtract_eigenvectors G (profileVertexBase G v) F.code (fun i => F.code i v) D
    (profileVertexBase_affine_eigen G h v) F.eigen u

end FourDirectionSystem

theorem ternary_affine_profile_degrees (ell : V → ℤ)
    (hs : ∀ u, ell u = -1 ∨ ell u = 0 ∨ ell u = 1)
    (he : ∀ u, (∑ w, if G.Adj u w then ell w else 0) = -4 * ell u - 2) :
    (∀ p ∈ positiveCodeSupport ell,
      profileDegree G (negativeCodeSupport ell) p = profileDegree G (positiveCodeSupport ell) p + 6) ∧
    (∀ b ∈ negativeCodeSupport ell,
      profileDegree G (positiveCodeSupport ell) b = profileDegree G (negativeCodeSupport ell) b + 2) := by
  constructor
  · intro p hp
    have hval := (Finset.mem_filter.mp hp).2
    have hh := sign_code_neighbor_sum G ell hs p
    rw [he p, hval] at hh
    unfold profileDegree
    omega
  · intro b hb
    have hval := (Finset.mem_filter.mp hb).2
    have hh := sign_code_neighbor_sum G ell hs b
    rw [he b, hval] at hh
    unfold profileDegree
    omega

theorem ternary_affine_profile_edge_budget (h : G.IsSRGWith 99 14 1 2) (ell : V → ℤ)
    (hs : ∀ u, ell u = -1 ∨ ell u = 0 ∨ ell u = 1)
    (he : ∀ u, (∑ w, if G.Adj u w then ell w else 0) = -4 * ell u - 2)
    (hP : (positiveCodeSupport ell).card = 6) (hB : (negativeCodeSupport ell).card = 17) :
    profileEdgeCount G (positiveCodeSupport ell) ≤ 1 ∧
      profileEdgeCount G (negativeCodeSupport ell) = profileEdgeCount G (positiveCodeSupport ell) + 1 := by
  have hh := ternary_affine_profile_degrees G ell hs he
  exact profile_six_seventeen_edges G h _ _ hP hB hh.1 hh.2

theorem affine_profile_sum (h : G.IsSRGWith 99 14 1 2) (ell : V → ℤ)
    (he : ∀ u, (∑ w, if G.Adj u w then ell w else 0) = -4 * ell u - 2) :
    (∑ u, ell u) = -11 := by
  have hcol (w : V) : (∑ u, if G.Adj u w then ell w else 0) = 14 * ell w := by
    have hdeg : (Finset.univ.filter (G.Adj w)).card = 14 := by
      simpa [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter] using h.regular.degree_eq w
    simp only [G.adj_comm _ w, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul,
      mul_zero, add_zero]
    rw [hdeg]
    norm_num
  have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun u _ => he u)
  rw [Finset.sum_comm] at hh
  simp_rw [hcol] at hh
  rw [← Finset.mul_sum] at hh
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, h.card, nsmul_eq_mul] at hh
  omega

theorem ternary_affine_profile_cardinalities_of_norm (h : G.IsSRGWith 99 14 1 2)
    (ell : V → ℤ) (hs : ∀ u, ell u = -1 ∨ ell u = 0 ∨ ell u = 1)
    (he : ∀ u, (∑ w, if G.Adj u w then ell w else 0) = -4 * ell u - 2)
    (hn : (∑ u, ell u ^ 2) = 23) :
    (positiveCodeSupport ell).card = 6 ∧ (negativeCodeSupport ell).card = 17 := by
  have hsum := sign_code_sum ell hs
  have hnorm := sign_code_norm ell hs
  rw [affine_profile_sum G h ell he] at hsum
  rw [hn] at hnorm
  omega

#print axioms profileVertexBase_affine_eigen
#print axioms FourDirectionSystem.profile_affine_eigen
#print axioms ternary_affine_profile_degrees
#print axioms ternary_affine_profile_edge_budget
#print axioms affine_profile_sum
#print axioms ternary_affine_profile_cardinalities_of_norm

end Conway99
