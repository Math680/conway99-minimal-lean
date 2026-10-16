import ZeroCasePartition
import ProfileBudget

/-! Integer row equations supplied to a finite neighbourhood certificate. -/

namespace Conway99
namespace FourDirectionSystem

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (F : FourDirectionSystem G)

def singleNeighborCount (v : V) (a : Fin 4 × Bool) : ℕ :=
  ((F.singleClass a).filter (G.Adj v)).card

theorem singleClass_code {a : Fin 4 × Bool} {u : V} (hu : u ∈ F.singleClass a)
    (i : Fin 4) : F.code i u = if i = a.1 then (if a.2 then 1 else -1) else 0 := by
  by_cases hi : i = a.1
  · subst i
    simp only [ite_true]
    exact (F.singleClass_mem hu).2.2
  · rw [if_neg hi]
    obtain ⟨j, hj⟩ := F.simple_active_unique (F.singleClass_mem hu).2.1
    have haj : a.1 = j := (hj a.1).mp (F.singleClass_code_ne hu)
    by_contra hn
    exact hi ((hj i).mp hn |>.trans haj.symm)

theorem zero_case_row_degree (h : G.IsSRGWith 99 14 1 2) (hz : F.weightCount 0 = 0)
    {v : V} (hv : v ∈ F.W) :
    (F.coreVertices.filter (G.Adj v)).card + ∑ a, F.singleNeighborCount v a =
      2 + 3 * (F.weight v).toNat := by
  have hh := F.zero_case_neighbor_partition hz v
  have hd := F.W_neighbor_degree h hv
  have hn := F.weight_nonneg v
  dsimp only [singleNeighborCount]
  omega

theorem zero_case_row_moment (hz : F.weightCount 0 = 0) (v : V) (i : Fin 4) :
    (∑ u ∈ F.coreVertices.filter (G.Adj v), F.code i u) +
      ∑ a : Fin 4 × Bool, (F.singleNeighborCount v a : ℤ) *
        (if i = a.1 then (if a.2 then 1 else -1) else 0) = -4 * F.code i v := by
  have hh := F.W_neighbor_code_moment v i
  rw [F.zero_case_W_partition hz, Finset.filter_union,
    Finset.sum_union (Finset.disjoint_filter_filter F.core_single_disjoint)] at hh
  rw [singleUnion, Finset.filter_biUnion, Finset.sum_biUnion] at hh
  · have hc (a : Fin 4 × Bool) :
        (∑ u ∈ (F.singleClass a).filter (G.Adj v), F.code i u) =
          (F.singleNeighborCount v a : ℤ) *
            (if i = a.1 then (if a.2 then 1 else -1) else 0) := by
      rw [Finset.sum_congr rfl (fun u hu => F.singleClass_code (Finset.mem_filter.mp hu).1 i)]
      simp [singleNeighborCount, Finset.sum_const, nsmul_eq_mul]
    simpa only [hc] using hh
  · intro a ha b hb hab
    exact Finset.disjoint_filter_filter (F.singleClass_pairwise_disjoint hab)

theorem singleNeighborCount_le (v : V) (a : Fin 4 × Bool) :
    F.singleNeighborCount v a ≤ (F.singleClass a).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem singleNeighborCount_zero_same_sign {v : V} (a : Fin 4 × Bool)
    (hv : F.code a.1 v = if a.2 then 1 else -1) : F.singleNeighborCount v a = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  have hs := F.singleClass_mem (Finset.mem_filter.mp hu).1
  have hn := F.singleClass_code_ne (Finset.mem_filter.mp hu).1
  exact F.same_nonzero_coordinate_not_adj a.1 hn (hs.2.2.trans hv.symm)
    (Finset.mem_filter.mp hu).2.symm

theorem zero_case_common_partition (hz : F.weightCount 0 = 0) (v w : V) :
    (F.W.filter (fun u => G.Adj v u ∧ G.Adj w u)).card =
      (F.coreVertices.filter (fun u => G.Adj v u ∧ G.Adj w u)).card +
        ∑ a : Fin 4 × Bool, ((F.singleClass a).filter (fun u => G.Adj v u ∧ G.Adj w u)).card := by
  rw [F.zero_case_W_partition hz, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter F.core_single_disjoint)]
  congr 1
  rw [singleUnion, Finset.filter_biUnion, Finset.card_biUnion]
  intro a ha b hb hab
  exact Finset.disjoint_filter_filter (F.singleClass_pairwise_disjoint hab)

theorem singleClass_common_lower (v w : V) (a : Fin 4 × Bool) :
    F.singleNeighborCount v a + F.singleNeighborCount w a - (F.singleClass a).card ≤
      ((F.singleClass a).filter (fun u => G.Adj v u ∧ G.Adj w u)).card := by
  let A := (F.singleClass a).filter (G.Adj v)
  let B := (F.singleClass a).filter (G.Adj w)
  have hu : A ∪ B ⊆ F.singleClass a :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hcard := Finset.card_union_add_card_inter A B
  have hle := Finset.card_le_card hu
  have heq : A ∩ B = (F.singleClass a).filter (fun u => G.Adj v u ∧ G.Adj w u) := by
    ext u
    simp [A, B, and_assoc, and_left_comm]
  rw [heq] at hcard
  change A.card + B.card - (F.singleClass a).card ≤ _
  omega

theorem zero_case_row_common_budget (h : G.IsSRGWith 99 14 1 2)
    (hz : F.weightCount 0 = 0) {v w : V} (hne : v ≠ w) :
    (F.coreVertices.filter (fun u => G.Adj v u ∧ G.Adj w u)).card +
      (∑ a : Fin 4 × Bool, (F.singleNeighborCount v a + F.singleNeighborCount w a -
        (F.singleClass a).card)) + (if G.Adj v w then 1 else 0) ≤ 2 := by
  have heq := F.zero_case_common_partition hz v w
  have hlo := Finset.sum_le_sum (s := Finset.univ) (fun a _ => F.singleClass_common_lower v w a)
  have hhi := profile_common_neighbors_bound G h F.W v w hne
  rw [heq] at hhi
  omega

theorem zero_case_row_common_upper (h : G.IsSRGWith 99 14 1 2)
    (hz : F.weightCount 0 = 0) {v w : V} (hne : v ≠ w)
    (hno : ∀ i, F.code i v ≠ 0 ∨ F.code i w ≠ 0) :
    (if G.Adj v w then 1 else 2) ≤
      (F.coreVertices.filter (fun u => G.Adj v u ∧ G.Adj w u)).card +
        ∑ a : Fin 4 × Bool, min (F.singleNeighborCount v a) (F.singleNeighborCount w a) := by
  have hh := F.W_common_neighbors_exact_of_no_shared_zero h hne hno
  rw [F.zero_case_common_partition hz v w] at hh
  have hb (a : Fin 4 × Bool) :
      ((F.singleClass a).filter (fun u => G.Adj v u ∧ G.Adj w u)).card ≤
        min (F.singleNeighborCount v a) (F.singleNeighborCount w a) := by
    apply le_min
    · apply Finset.card_le_card
      intro u hu
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2.1⟩
    · apply Finset.card_le_card
      intro u hu
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2.2⟩
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hb a)
  omega

private theorem nat_truncated_sub_cast (a b c : ℕ) :
    ((a + b - c : ℕ) : ℤ) = max 0 ((a : ℤ) + b - c) := by
  omega

theorem zero_case_row_common_budget_int (h : G.IsSRGWith 99 14 1 2)
    (hz : F.weightCount 0 = 0) {v w : V} (hne : v ≠ w) :
    ((F.coreVertices.filter (fun u => G.Adj v u ∧ G.Adj w u)).card : ℤ) +
      (∑ a : Fin 4 × Bool, max 0 ((F.singleNeighborCount v a : ℤ) +
        F.singleNeighborCount w a - (F.singleClass a).card)) ≤
      if G.Adj v w then 1 else 2 := by
  have hh := F.zero_case_row_common_budget h hz hne
  have hi : ((F.coreVertices.filter (fun u => G.Adj v u ∧ G.Adj w u)).card : ℤ) +
      (∑ a : Fin 4 × Bool, ((F.singleNeighborCount v a + F.singleNeighborCount w a -
        (F.singleClass a).card : ℕ) : ℤ)) + (if G.Adj v w then 1 else 0) ≤ 2 := by
    exact_mod_cast hh
  simp_rw [nat_truncated_sub_cast] at hi
  by_cases ha : G.Adj v w <;> simp only [ha, ite_true, ite_false] at hi ⊢ <;> omega

theorem zero_case_row_common_upper_int (h : G.IsSRGWith 99 14 1 2)
    (hz : F.weightCount 0 = 0) {v w : V} (hne : v ≠ w)
    (hno : ∀ i, F.code i v ≠ 0 ∨ F.code i w ≠ 0) :
    (if G.Adj v w then (1 : ℤ) else 2) ≤
      ((F.coreVertices.filter (fun u => G.Adj v u ∧ G.Adj w u)).card : ℤ) +
        ∑ a : Fin 4 × Bool, min (F.singleNeighborCount v a : ℤ) (F.singleNeighborCount w a) := by
  exact_mod_cast F.zero_case_row_common_upper h hz hne hno

#print axioms zero_case_row_degree
#print axioms zero_case_row_moment
#print axioms zero_case_row_common_budget
#print axioms zero_case_row_common_upper
#print axioms zero_case_row_common_budget_int
#print axioms zero_case_row_common_upper_int

end FourDirectionSystem
end Conway99
