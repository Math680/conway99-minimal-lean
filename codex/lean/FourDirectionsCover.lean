import RootCentersBound
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! The 39-point complement and weight moments of four root directions.
The structure explicitly records the already-derived geometric separation hypotheses.
-/

namespace Conway99

open scoped BigOperators Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

structure FourDirectionSystem where
  code : Fin 4 → V → ℤ
  biplane : ∀ i, SignedBiplaneCode G (code i)
  eigen : ∀ i u, (∑ v, if G.Adj u v then code i v else 0) = -4 * code i u
  isolated_disjoint : Pairwise (fun i j => Disjoint (rootIsolated G (code i)) (rootIsolated G (code j)))
  support_avoids_isolated : ∀ i j, Disjoint (rootSupport (code i)) (rootIsolated G (code j))
  support_intersections : ∀ i j, i ≠ j → (rootSupport (code i) ∩ rootSupport (code j)).card = 4

namespace FourDirectionSystem

variable {G} (F : FourDirectionSystem G)

def isolatedUnion : Finset V := Finset.univ.biUnion (fun i => rootIsolated G (F.code i))
def W : Finset V := Finset.univ \ F.isolatedUnion
def weight (u : V) : ℤ := ∑ i : Fin 4, if u ∈ rootSupport (F.code i) then 1 else 0
def weightCount (a : ℤ) : ℕ := (F.W.filter (fun u => F.weight u = a)).card

theorem support_subset_W (i : Fin 4) : rootSupport (F.code i) ⊆ F.W := by
  intro u hu
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hh
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hh
  exact Finset.disjoint_left.mp (F.support_avoids_isolated i j) hu hj

theorem isolatedUnion_card (h : G.IsSRGWith 99 14 1 2) : F.isolatedUnion.card = 60 := by
  rw [isolatedUnion, Finset.card_biUnion (by
    intro i _ j _ hij
    exact F.isolated_disjoint hij)]
  simp only [signed_biplane_isolated_card G h _ (F.biplane _) (F.eigen _),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

theorem W_card (h : G.IsSRGWith 99 14 1 2) : F.W.card = 39 := by
  rw [W, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    h.card, F.isolatedUnion_card h]

theorem weight_nonneg (u : V) : 0 ≤ F.weight u :=
  Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

theorem weight_le_four (u : V) : F.weight u ≤ 4 := by
  have hh : F.weight u ≤ ∑ _i : Fin 4, (1 : ℤ) :=
    Finset.sum_le_sum (fun _ _ => by split_ifs <;> norm_num)
  norm_num at hh ⊢
  exact hh

theorem weight_zero_iff (u : V) : F.weight u = 0 ↔ ∀ i, u ∉ rootSupport (F.code i) := by
  constructor
  · intro hz i hi
    have hh : (if u ∈ rootSupport (F.code i) then (1 : ℤ) else 0) ≤ F.weight u := by
      unfold weight
      exact Finset.single_le_sum (f := fun j => if u ∈ rootSupport (F.code j) then (1 : ℤ) else 0)
        (fun j _ => by dsimp only; split_ifs <;> norm_num) (Finset.mem_univ i)
    rw [if_pos hi, hz] at hh
    omega
  · intro hh
    simp [weight, hh]

theorem support_indicator_sum (i : Fin 4) :
    (∑ u ∈ F.W, if u ∈ rootSupport (F.code i) then (1 : ℤ) else 0) = 14 := by
  have heq : F.W.filter (fun u => u ∈ rootSupport (F.code i)) = rootSupport (F.code i) := by
    exact Finset.eq_of_subset_of_card_le
      (by intro u hu; exact (Finset.mem_filter.mp hu).2)
      (by
        apply Finset.card_le_card
        intro u hu
        exact Finset.mem_filter.mpr ⟨F.support_subset_W i hu, hu⟩)
  simp only [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
    nsmul_eq_mul, mul_one]
  rw [heq, signed_biplane_support_card G _ (F.biplane i)]
  norm_num

theorem weight_sum : (∑ u ∈ F.W, F.weight u) = 56 := by
  simp only [weight]
  rw [Finset.sum_comm]
  simp only [F.support_indicator_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  norm_num

theorem support_indicator_pair_sum (i j : Fin 4) :
    (∑ u ∈ F.W, (if u ∈ rootSupport (F.code i) then (1 : ℤ) else 0) *
      (if u ∈ rootSupport (F.code j) then 1 else 0)) = if i = j then 14 else 4 := by
  have hp (u : V) :
      (if u ∈ rootSupport (F.code i) then (1 : ℤ) else 0) *
        (if u ∈ rootSupport (F.code j) then 1 else 0) =
      if u ∈ rootSupport (F.code i) ∩ rootSupport (F.code j) then 1 else 0 := by
    by_cases hi : u ∈ rootSupport (F.code i) <;> by_cases hj : u ∈ rootSupport (F.code j) <;>
      simp [hi, hj]
  rw [Finset.sum_congr rfl (fun u _ => hp u)]
  have heq : F.W.filter (fun u => u ∈ rootSupport (F.code i) ∩ rootSupport (F.code j)) =
      rootSupport (F.code i) ∩ rootSupport (F.code j) := by
    ext u
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hu => ⟨F.support_subset_W i (Finset.mem_inter.mp hu).1, hu⟩⟩
  simp only [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
    nsmul_eq_mul, mul_one, heq]
  by_cases hij : i = j
  · subst j
    simp [Finset.inter_self, signed_biplane_support_card G _ (F.biplane i)]
  · rw [F.support_intersections i j hij, if_neg hij]
    norm_num

theorem weight_square_sum : (∑ u ∈ F.W, F.weight u ^ 2) = 104 := by
  have hp (u : V) : F.weight u ^ 2 = ∑ i : Fin 4, ∑ j : Fin 4,
      (if u ∈ rootSupport (F.code i) then (1 : ℤ) else 0) *
      (if u ∈ rootSupport (F.code j) then 1 else 0) := by
    simp only [weight, pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun u _ => hp u), Finset.sum_comm]
  have hs (i : Fin 4) :
      (∑ u ∈ F.W, ∑ j : Fin 4,
        (if u ∈ rootSupport (F.code i) then (1 : ℤ) else 0) *
        (if u ∈ rootSupport (F.code j) then 1 else 0)) =
      ∑ j : Fin 4, if i = j then (14 : ℤ) else 4 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact F.support_indicator_pair_sum i j
  rw [Finset.sum_congr rfl (fun i _ => hs i)]
  decide

theorem weight_cost_sum (h : G.IsSRGWith 99 14 1 2) :
    (∑ u ∈ F.W, (F.weight u - 1) * (F.weight u - 2)) = 14 := by
  have hp (u : V) : (F.weight u - 1) * (F.weight u - 2) = F.weight u ^ 2 - 3 * F.weight u + 2 := by
    ring
  rw [Finset.sum_congr rfl (fun u _ => hp u), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, F.weight_sum, F.weight_square_sum]
  simp only [Finset.sum_const, nsmul_eq_mul, F.W_card h]
  norm_num

theorem zero_mem_shell (h : G.IsSRGWith 99 14 1 2) (o : V)
    (ho : o ∈ F.W) (hz : F.weight o = 0) (i : Fin 4) : o ∈ rootShell G (F.code i) := by
  have hc := (F.weight_zero_iff o).mp hz i
  have hi : o ∉ rootIsolated G (F.code i) := by
    intro hm
    exact (Finset.mem_sdiff.mp ho).2 (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hm⟩)
  have hp := congrFun (signed_biplane_indicator_partition G h _ (F.biplane i) (F.eigen i)) o
  by_contra hs
  simp [Pi.add_apply, finiteIndicator, hc, hi, hs] at hp

theorem zero_isolated_neighbors (h : G.IsSRGWith 99 14 1 2) (o : V)
    (ho : o ∈ F.W) (hz : F.weight o = 0) (i : Fin 4) :
    ((rootIsolated G (F.code i)).filter (G.Adj o)).card = 3 := by
  have hh := congrFun (signed_biplane_isolated_adjacency G h _ (F.biplane i) (F.eigen i)) o
  rw [finiteIndicator_adjacency] at hh
  have hs := F.zero_mem_shell h o ho hz i
  simp only [Pi.smul_apply, smul_eq_mul, finiteIndicator, if_pos hs, mul_one] at hh
  exact_mod_cast hh

theorem zero_support_neighbors (h : G.IsSRGWith 99 14 1 2) (o : V)
    (ho : o ∈ F.W) (hz : F.weight o = 0) (i : Fin 4) :
    ((rootSupport (F.code i)).filter (G.Adj o)).card = 2 := by
  have hh := congrFun (signed_biplane_support_adjacency G h _ (F.biplane i) (F.eigen i)) o
  rw [finiteIndicator_adjacency] at hh
  have hs := F.zero_mem_shell h o ho hz i
  have hc := (F.weight_zero_iff o).mp hz i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, finiteIndicator, if_pos hs,
    if_neg hc, mul_zero, zero_add, mul_one] at hh
  exact_mod_cast hh

theorem zero_W_neighbors (h : G.IsSRGWith 99 14 1 2) (o : V)
    (ho : o ∈ F.W) (hz : F.weight o = 0) : (F.W.filter (G.Adj o)).card = 2 := by
  have hi : (F.isolatedUnion.filter (G.Adj o)).card = 12 := by
    have heq : F.isolatedUnion.filter (G.Adj o) =
        Finset.univ.biUnion (fun i => (rootIsolated G (F.code i)).filter (G.Adj o)) := by
      ext u
      simp only [isolatedUnion, Finset.mem_filter, Finset.mem_biUnion]
      aesop
    rw [heq, Finset.card_biUnion (by
      intro i _ j _ hij
      exact Finset.disjoint_filter_filter (F.isolated_disjoint hij))]
    simp only [F.zero_isolated_neighbors h o ho hz, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin]
    norm_num
  have hdeg : (Finset.univ.filter (G.Adj o)).card = 14 := by
    simpa [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter] using h.regular.degree_eq o
  have hd : Disjoint (F.W.filter (G.Adj o)) (F.isolatedUnion.filter (G.Adj o)) := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hu).1).2 (Finset.mem_filter.mp hv).1
  have heq : F.W.filter (G.Adj o) ∪ F.isolatedUnion.filter (G.Adj o) =
      Finset.univ.filter (G.Adj o) := by
    ext u
    simp only [W, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
      true_and]
    tauto
  have hh := Finset.card_union_of_disjoint hd
  rw [heq, hdeg, hi] at hh
  omega

theorem zero_neighbors_weight_sum (h : G.IsSRGWith 99 14 1 2) (o : V)
    (ho : o ∈ F.W) (hz : F.weight o = 0) :
    (∑ u ∈ F.W.filter (G.Adj o), F.weight u) = 8 := by
  unfold weight
  rw [Finset.sum_comm]
  have hh (i : Fin 4) :
      (∑ u ∈ F.W.filter (G.Adj o), if u ∈ rootSupport (F.code i) then (1 : ℤ) else 0) = 2 := by
    have heq : (F.W.filter (G.Adj o)).filter (fun u => u ∈ rootSupport (F.code i)) =
        (rootSupport (F.code i)).filter (G.Adj o) := by
      ext u
      simp only [Finset.mem_filter]
      exact ⟨fun hu => ⟨hu.2, hu.1.2⟩, fun hu => ⟨⟨F.support_subset_W i hu.1, hu.2⟩, hu.1⟩⟩
    simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one, mul_zero, add_zero]
    rw [heq, F.zero_support_neighbors h o ho hz i]
    norm_num
  simp only [hh, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num

theorem zero_neighbors_weight_four (h : G.IsSRGWith 99 14 1 2) (o : V)
    (ho : o ∈ F.W) (hz : F.weight o = 0) :
    ∀ u ∈ F.W.filter (G.Adj o), F.weight u = 4 := by
  have heq : (∑ u ∈ F.W.filter (G.Adj o), F.weight u) =
      ∑ _u ∈ F.W.filter (G.Adj o), (4 : ℤ) := by
    rw [F.zero_neighbors_weight_sum h o ho hz]
    simp [F.zero_W_neighbors h o ho hz]
  exact (Finset.sum_eq_sum_iff_of_le (fun u _ => F.weight_le_four u)).mp heq

theorem zero_forces_two_weight_four (h : G.IsSRGWith 99 14 1 2) (o : V)
    (ho : o ∈ F.W) (hz : F.weight o = 0) : 2 ≤ F.weightCount 4 := by
  rw [← F.zero_W_neighbors h o ho hz]
  apply Finset.card_le_card
  intro u hu
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1,
    F.zero_neighbors_weight_four h o ho hz u hu⟩

theorem weight_cost_lower (h : G.IsSRGWith 99 14 1 2) :
    2 * (F.weightCount 0 : ℤ) + 6 * (F.weightCount 4 : ℤ) ≤ 14 := by
  have hp (u : V) :
      (if F.weight u = 0 then (2 : ℤ) else 0) + (if F.weight u = 4 then 6 else 0) ≤
      (F.weight u - 1) * (F.weight u - 2) := by
    have hlo := F.weight_nonneg u
    have hhi := F.weight_le_four u
    generalize F.weight u = n at *
    interval_cases n <;> norm_num
  have hh := Finset.sum_le_sum (s := F.W) (fun u _ => hp u)
  rw [Finset.sum_add_distrib, F.weight_cost_sum h] at hh
  simpa [Finset.sum_ite, Finset.sum_const, weightCount, nsmul_eq_mul, mul_comm] using hh

theorem zero_weight_count_le_one (h : G.IsSRGWith 99 14 1 2) : F.weightCount 0 ≤ 1 := by
  by_cases hz : F.weightCount 0 = 0
  · omega
  · have hpos : 0 < F.weightCount 0 := Nat.pos_of_ne_zero hz
    obtain ⟨o, ho⟩ := Finset.card_pos.mp hpos
    have hfour := F.zero_forces_two_weight_four h o (Finset.mem_filter.mp ho).1 (Finset.mem_filter.mp ho).2
    have hcost := F.weight_cost_lower h
    omega

theorem sum_weight_indicator (a c : ℤ) :
    (∑ u ∈ F.W, if F.weight u = a then c else 0) = (F.weightCount a : ℤ) * c := by
  simp [Finset.sum_ite, Finset.sum_const, weightCount, nsmul_eq_mul]

theorem weight_count_sum (h : G.IsSRGWith 99 14 1 2) :
    (F.weightCount 0 : ℤ) + F.weightCount 1 + F.weightCount 2 +
      F.weightCount 3 + F.weightCount 4 = 39 := by
  have hp (u : V) :
      (if F.weight u = 0 then (1 : ℤ) else 0) +
      (if F.weight u = 1 then 1 else 0) + (if F.weight u = 2 then 1 else 0) +
      (if F.weight u = 3 then 1 else 0) + (if F.weight u = 4 then 1 else 0) = 1 := by
    have hlo := F.weight_nonneg u
    have hhi := F.weight_le_four u
    generalize F.weight u = n at *
    interval_cases n <;> norm_num
  have hh := Finset.sum_congr (s₁ := F.W) rfl (fun u _ => hp u)
  simp only [Finset.sum_add_distrib, F.sum_weight_indicator, mul_one,
    Finset.sum_const, nsmul_eq_mul, F.W_card h] at hh
  norm_num at hh
  exact hh

theorem weight_count_moment :
    (F.weightCount 1 : ℤ) + 2 * F.weightCount 2 +
      3 * F.weightCount 3 + 4 * F.weightCount 4 = 56 := by
  have hp (u : V) :
      (if F.weight u = 1 then (1 : ℤ) else 0) + (if F.weight u = 2 then 2 else 0) +
      (if F.weight u = 3 then 3 else 0) + (if F.weight u = 4 then 4 else 0) = F.weight u := by
    have hlo := F.weight_nonneg u
    have hhi := F.weight_le_four u
    generalize F.weight u = n at *
    interval_cases n <;> norm_num
  have hh := Finset.sum_congr (s₁ := F.W) rfl (fun u _ => hp u)
  simpa only [Finset.sum_add_distrib, F.sum_weight_indicator, mul_one, one_mul, mul_comm,
    F.weight_sum] using hh

theorem weight_count_square_moment :
    (F.weightCount 1 : ℤ) + 4 * F.weightCount 2 +
      9 * F.weightCount 3 + 16 * F.weightCount 4 = 104 := by
  have hp (u : V) :
      (if F.weight u = 1 then (1 : ℤ) else 0) + (if F.weight u = 2 then 4 else 0) +
      (if F.weight u = 3 then 9 else 0) + (if F.weight u = 4 then 16 else 0) = F.weight u ^ 2 := by
    have hlo := F.weight_nonneg u
    have hhi := F.weight_le_four u
    generalize F.weight u = n at *
    interval_cases n <;> norm_num
  have hh := Finset.sum_congr (s₁ := F.W) rfl (fun u _ => hp u)
  simpa only [Finset.sum_add_distrib, F.sum_weight_indicator, mul_one, one_mul, mul_comm,
    F.weight_square_sum] using hh

theorem weight_count_balance (h : G.IsSRGWith 99 14 1 2) :
    F.weightCount 0 + F.weightCount 3 + 3 * F.weightCount 4 = 7 := by
  have hs := F.weight_count_sum h
  have hm := F.weight_count_moment
  have hq := F.weight_count_square_moment
  omega

theorem one_zero_weight_profile (h : G.IsSRGWith 99 14 1 2) (hz : F.weightCount 0 = 1) :
    F.weightCount 1 = 24 ∧ F.weightCount 2 = 12 ∧
      F.weightCount 3 = 0 ∧ F.weightCount 4 = 2 := by
  have hpos : 0 < F.weightCount 0 := by omega
  obtain ⟨o, ho⟩ := Finset.card_pos.mp hpos
  have hfour := F.zero_forces_two_weight_four h o (Finset.mem_filter.mp ho).1 (Finset.mem_filter.mp ho).2
  have hb := F.weight_count_balance h
  have hs := F.weight_count_sum h
  have hm := F.weight_count_moment
  omega

#print axioms W_card
#print axioms weight_sum
#print axioms weight_square_sum
#print axioms weight_cost_sum
#print axioms zero_weight_count_le_one
#print axioms weight_count_balance
#print axioms one_zero_weight_profile

end FourDirectionSystem
end Conway99
