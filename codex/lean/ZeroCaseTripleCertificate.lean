import Mathlib.Tactic

/-! A short counting replacement for the singleton-intersection DP in
the two non-residual surviving high arrays. No LP or Python result is trusted. -/

namespace Conway99.ZeroCaseTriple

open scoped BigOperators

def pairs : Finset (Fin 4 × Fin 4) :=
  (Finset.univ.product Finset.univ).filter (fun p => p.1 < p.2)

private theorem point_bound : ∀ (b : Fin 4 → Bool) (excluded : Fin 4),
    (∑ i ∈ (Finset.univ : Finset (Fin 4)).erase excluded, if b i then 1 else 0) ≤
      1 + ∑ p ∈ pairs, if b p.1 && b p.2 then 1 else 0 := by decide

variable {V : Type*} [DecidableEq V]

theorem group_bound (T : Finset V) (A : Fin 4 → Finset V) (excluded : Fin 4) :
    (∑ i ∈ (Finset.univ : Finset (Fin 4)).erase excluded, (T ∩ A i).card) ≤
      T.card + ∑ p ∈ pairs, (T ∩ A p.1 ∩ A p.2).card := by
  have hp (u : V) := point_bound (fun i => decide (u ∈ A i)) excluded
  have hh := Finset.sum_le_sum (s := T) (fun u _ => hp u)
  rw [Finset.sum_add_distrib] at hh
  have hleft :
      (∑ u ∈ T, ∑ i ∈ (Finset.univ : Finset (Fin 4)).erase excluded,
        if decide (u ∈ A i) then 1 else 0) =
      ∑ i ∈ (Finset.univ : Finset (Fin 4)).erase excluded, (T ∩ A i).card := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.sum_ite, Finset.filter_mem_eq_inter]
  have hright :
      (∑ u ∈ T, ∑ p ∈ pairs, if decide (u ∈ A p.1) && decide (u ∈ A p.2) then 1 else 0) =
      ∑ p ∈ pairs, (T ∩ A p.1 ∩ A p.2).card := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    have heq : T.filter (fun u => u ∈ A p.1 ∧ u ∈ A p.2) = T ∩ A p.1 ∩ A p.2 := by
      ext u
      simp [and_assoc]
    simpa only [Bool.and_eq_true, decide_eq_true_eq, Finset.sum_boole] using
      congrArg Finset.card heq
  rw [hleft, hright] at hh
  simpa using hh

theorem four_group_bound (T A : Fin 4 → Finset V)
    (hd : Pairwise (fun i j => Disjoint (T i) (T j))) :
    (∑ j : Fin 4, ∑ i ∈ (Finset.univ : Finset (Fin 4)).erase (Fin.rev j), (T j ∩ A i).card) ≤
      (∑ j : Fin 4, (T j).card) +
        ∑ p ∈ pairs, ((Finset.univ.biUnion T) ∩ A p.1 ∩ A p.2).card := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => group_bound (T j) A (Fin.rev j))
  rw [Finset.sum_add_distrib, Finset.sum_comm (s := Finset.univ) (t := pairs)] at hh
  have hc (p : Fin 4 × Fin 4) :
      (∑ j : Fin 4, (T j ∩ A p.1 ∩ A p.2).card) =
        ((Finset.univ.biUnion T) ∩ A p.1 ∩ A p.2).card := by
    have heq : ((Finset.univ.biUnion T) ∩ A p.1 ∩ A p.2) =
        Finset.univ.biUnion (fun j => T j ∩ A p.1 ∩ A p.2) := by
      ext u
      simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨⟨j, hj⟩, h1⟩, h2⟩
        exact ⟨j, ⟨⟨hj, h1⟩, h2⟩⟩
      · rintro ⟨j, ⟨⟨hj, h1⟩, h2⟩⟩
        exact ⟨⟨⟨j, hj⟩, h1⟩, h2⟩
    rw [heq, Finset.card_biUnion]
    intro i hi j hj hij
    exact Finset.disjoint_of_subset_left (Finset.inter_subset_left.trans Finset.inter_subset_left)
      (Finset.disjoint_of_subset_right (Finset.inter_subset_left.trans Finset.inter_subset_left) (hd hij))
  simpa only [hc] using hh

def marginsOne : Fin 4 → Fin 4 → ℕ :=
  ![![3,3,1,0], ![3,1,0,3], ![3,0,3,1], ![0,2,2,2]]

def marginsThree : Fin 4 → Fin 4 → ℕ :=
  ![![3,3,1,0], ![3,1,0,3], ![1,0,3,3], ![0,3,3,1]]

def sizesOne : Fin 4 → ℕ := ![4,4,4,3]
def sizesThree : Fin 4 → ℕ := ![4,4,4,4]

def budgetsOne : Fin 4 → Fin 4 → ℕ :=
  ![![0,2,2,2], ![0,0,1,1], ![0,0,0,1], ![0,0,0,0]]

def budgetsThree : Fin 4 → Fin 4 → ℕ :=
  ![![0,2,1,2], ![0,0,2,1], ![0,0,0,2], ![0,0,0,0]]

theorem orbit_one_singletons_impossible (T A : Fin 4 → Finset V)
    (hd : Pairwise (fun i j => Disjoint (T i) (T j)))
    (hs : ∀ j, (T j).card = sizesOne j)
    (hm : ∀ j i, (T j ∩ A i).card = marginsOne j i)
    (hb : ∀ p ∈ pairs, ((Finset.univ.biUnion T) ∩ A p.1 ∩ A p.2).card ≤ budgetsOne p.1 p.2) : False := by
  have hh := four_group_bound T A hd
  have hsum := Finset.sum_le_sum hb
  simp_rw [hm, hs] at hh
  have hmarg : (∑ j : Fin 4, ∑ i ∈ (Finset.univ : Finset (Fin 4)).erase (Fin.rev j), marginsOne j i) = 27 := by decide
  have hsize : (∑ j : Fin 4, sizesOne j) = 15 := by decide
  have hbudget : (∑ p ∈ pairs, budgetsOne p.1 p.2) = 9 := by decide
  rw [hmarg, hsize] at hh
  rw [hbudget] at hsum
  omega

theorem orbit_three_singletons_impossible (T A : Fin 4 → Finset V)
    (hd : Pairwise (fun i j => Disjoint (T i) (T j)))
    (hs : ∀ j, (T j).card = sizesThree j)
    (hm : ∀ j i, (T j ∩ A i).card = marginsThree j i)
    (hb : ∀ p ∈ pairs, ((Finset.univ.biUnion T) ∩ A p.1 ∩ A p.2).card ≤ budgetsThree p.1 p.2) : False := by
  have hh := four_group_bound T A hd
  have hsum := Finset.sum_le_sum hb
  simp_rw [hm, hs] at hh
  have hmarg : (∑ j : Fin 4, ∑ i ∈ (Finset.univ : Finset (Fin 4)).erase (Fin.rev j), marginsThree j i) = 28 := by decide
  have hsize : (∑ j : Fin 4, sizesThree j) = 16 := by decide
  have hbudget : (∑ p ∈ pairs, budgetsThree p.1 p.2) = 10 := by decide
  rw [hmarg, hsize] at hh
  rw [hbudget] at hsum
  omega

#print axioms orbit_one_singletons_impossible
#print axioms orbit_three_singletons_impossible

end Conway99.ZeroCaseTriple
