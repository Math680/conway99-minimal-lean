import ProfileBudget
import FourDirections

/-! Global saturation of the six profile edge budgets. All budget terms are
cardinalities of actual edge finsets, and saturation is proved by incidence
double counting. -/

namespace Conway99

open scoped BigOperators

variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]

theorem finite_family_budget_saturated (S : Finset ι) (A : ι → Finset α) (E : Finset α)
    (hcard : E.card = ∑ i ∈ S, (A i).card)
    (howner : ∀ e ∈ E, (S.filter (fun i => e ∈ A i)).card = 1) :
    ∀ i ∈ S, A i ⊆ E := by
  have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun i e => e ∈ A i) (s := S) (t := E)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hdouble
  rw [Finset.sum_congr rfl howner] at hdouble
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hcard] at hdouble
  have hle (i : ι) (_hi : i ∈ S) : (E.filter (fun e => e ∈ A i)).card ≤ (A i).card := by
    apply Finset.card_le_card
    intro e he
    exact (Finset.mem_filter.mp he).2
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp hdouble
  intro i hi e he
  have hset : E.filter (fun e => e ∈ A i) = A i :=
    Finset.eq_of_subset_of_card_le (by intro e he; exact (Finset.mem_filter.mp he).2)
      (by rw [heq i hi])
  exact (Finset.mem_filter.mp (hset.symm ▸ he)).1

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem profile_global_budget_saturated (S : Finset ι) (B : ι → Finset V)
    (E : Finset (Sym2 V)) (hcard : E.card = ∑ i ∈ S, profileEdgeCount G (B i))
    (howner : ∀ e ∈ E,
      (S.filter (fun i => e ∈ (profileRestrictedGraph G (B i)).edgeFinset)).card = 1) :
    ∀ i ∈ S, (profileRestrictedGraph G (B i)).edgeFinset ⊆ E :=
  finite_family_budget_saturated S (fun i => (profileRestrictedGraph G (B i)).edgeFinset)
    E hcard howner

theorem profile_six_budget_saturated (S : Finset ι) (hS : S.card = 6)
    (B : ι → Finset V) (he : ∀ i ∈ S, profileEdgeCount G (B i) = 2)
    (E : Finset (Sym2 V)) (hE : E.card = 12)
    (howner : ∀ e ∈ E,
      (S.filter (fun i => e ∈ (profileRestrictedGraph G (B i)).edgeFinset)).card = 1) :
    ∀ i ∈ S, (profileRestrictedGraph G (B i)).edgeFinset ⊆ E := by
  apply profile_global_budget_saturated G S B E _ howner
  rw [Finset.sum_congr rfl he]
  simp [hE, hS]

theorem profile_six_all_budget_saturated (B : Fin 6 → Finset V)
    (he : ∀ i, profileEdgeCount G (B i) = 2)
    (E : Finset (Sym2 V)) (hE : E.card = 12)
    (howner : ∀ e ∈ E,
      (Finset.univ.filter (fun i => e ∈ (profileRestrictedGraph G (B i)).edgeFinset)).card = 1) :
    ∀ i, (profileRestrictedGraph G (B i)).edgeFinset ⊆ E := by
  intro i
  exact profile_six_budget_saturated G Finset.univ (by simp) B (fun i _ => he i)
    E hE howner i (Finset.mem_univ _)

theorem profile_six_structural_budget_saturated (h : G.IsSRGWith 99 14 1 2)
    (S : Finset ι) (hS : S.card = 6) (P B : ι → Finset V)
    (hP : ∀ i ∈ S, (P i).card = 6) (hB : ∀ i ∈ S, (B i).card = 17)
    (hp : ∀ i ∈ S, ∀ p ∈ P i, profileDegree G (B i) p = profileDegree G (P i) p + 6)
    (hb : ∀ i ∈ S, ∀ b ∈ B i, profileDegree G (P i) b = profileDegree G (B i) b + 2)
    (u v : V) (ha : G.Adj u v) (hu : ∀ i ∈ S, u ∈ P i) (hv : ∀ i ∈ S, v ∈ P i)
    (E : Finset (Sym2 V)) (hE : E.card = 12)
    (howner : ∀ e ∈ E,
      (S.filter (fun i => e ∈ (profileRestrictedGraph G (B i)).edgeFinset)).card = 1) :
    ∀ i ∈ S, (profileRestrictedGraph G (B i)).edgeFinset ⊆ E := by
  apply profile_six_budget_saturated G S hS B _ E hE howner
  intro i hi
  exact (profile_six_seventeen_saturated_of_edge G h (P i) (B i) (hP i hi) (hB i hi)
    (hp i hi) (hb i hi) u v (hu i hi) (hv i hi) ha).2

theorem profile_six_no_extra_negative_edge (S : Finset ι) (hS : S.card = 6)
    (B : ι → Finset V) (he : ∀ i ∈ S, profileEdgeCount G (B i) = 2)
    (E : Finset (Sym2 V)) (hE : E.card = 12)
    (howner : ∀ e ∈ E,
      (S.filter (fun i => e ∈ (profileRestrictedGraph G (B i)).edgeFinset)).card = 1)
    (u v : V) (ha : G.Adj u v) (hnot : s(u, v) ∉ E) :
    ∀ i ∈ S, ¬ (u ∈ B i ∧ v ∈ B i) := by
  intro i hi huv
  exact hnot (profile_six_budget_saturated G S hS B he E hE howner i hi
    (SimpleGraph.mem_edgeFinset.mpr ⟨huv.1, huv.2, ha⟩))

namespace FourDirections

theorem profile_V_internal_owner_count
    (B : Finset Label → Finset V) (u v : V) (i j : Label) (hij : i ≠ j)
    (ha : G.Adj u v)
    (hu : ∀ D ∈ Profiles, u ∈ B D ↔ negV D i)
    (hv : ∀ D ∈ Profiles, v ∈ B D ↔ negV D j) :
    (Profiles.filter (fun D => s(u, v) ∈ (profileRestrictedGraph G (B D)).edgeFinset)).card = 1 := by
  have heq : Profiles.filter (fun D => s(u, v) ∈ (profileRestrictedGraph G (B D)).edgeFinset) =
      Profiles.filter (fun D => negV D i ∧ negV D j) := by
    ext D
    by_cases hD : D ∈ Profiles
    · simp only [Finset.mem_filter, hD, true_and, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet]
      change (u ∈ B D ∧ v ∈ B D ∧ G.Adj u v) ↔ _
      simp [hu D hD, hv D hD, ha]
    · simp [hD]
  rw [heq]
  exact V_internal_profile_count i j hij

theorem profile_W_internal_owner_count
    (B : Finset Label → Finset V) (u v : V) (i j : Label) (hij : i ≠ j)
    (ha : G.Adj u v)
    (hu : ∀ D ∈ Profiles, u ∈ B D ↔ negW D i)
    (hv : ∀ D ∈ Profiles, v ∈ B D ↔ negW D j) :
    (Profiles.filter (fun D => s(u, v) ∈ (profileRestrictedGraph G (B D)).edgeFinset)).card = 1 := by
  have heq : Profiles.filter (fun D => s(u, v) ∈ (profileRestrictedGraph G (B D)).edgeFinset) =
      Profiles.filter (fun D => negW D i ∧ negW D j) := by
    ext D
    by_cases hD : D ∈ Profiles
    · simp only [Finset.mem_filter, hD, true_and, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet]
      change (u ∈ B D ∧ v ∈ B D ∧ G.Adj u v) ↔ _
      simp [hu D hD, hv D hD, ha]
    · simp [hD]
  rw [heq]
  exact W_internal_profile_count i j hij

theorem global_profile_V_W_restriction
    (B : Finset Label → Finset V) (he : ∀ D ∈ Profiles, profileEdgeCount G (B D) = 2)
    (E : Finset (Sym2 V)) (hE : E.card = 12)
    (howner : ∀ e ∈ E,
      (Profiles.filter (fun D => e ∈ (profileRestrictedGraph G (B D)).edgeFinset)).card = 1)
    (u v : V) (i j : Label) (ha : G.Adj u v) (hnot : s(u, v) ∉ E)
    (hu : ∀ D ∈ Profiles, negV D i → u ∈ B D)
    (hv : ∀ D ∈ Profiles, negW D j → v ∈ B D) : i = j := by
  apply (V_W_restriction i j).mp
  intro D hD hh
  exact profile_six_no_extra_negative_edge G Profiles six_profiles B he E hE howner
    u v ha hnot D hD ⟨hu D hD hh.1, hv D hD hh.2⟩

theorem global_profile_V_R_restriction
    (B : Finset Label → Finset V) (he : ∀ D ∈ Profiles, profileEdgeCount G (B D) = 2)
    (E : Finset (Sym2 V)) (hE : E.card = 12)
    (howner : ∀ e ∈ E,
      (Profiles.filter (fun D => e ∈ (profileRestrictedGraph G (B D)).edgeFinset)).card = 1)
    (u v : V) (i : Label) (a : Arc) (ha : G.Adj u v) (hnot : s(u, v) ∉ E)
    (hu : ∀ D ∈ Profiles, negV D i → u ∈ B D)
    (hv : ∀ D ∈ Profiles, negR D a → v ∈ B D) : i = src a := by
  apply (V_R_restriction i a).mp
  intro D hD hh
  exact profile_six_no_extra_negative_edge G Profiles six_profiles B he E hE howner
    u v ha hnot D hD ⟨hu D hD hh.1, hv D hD hh.2⟩

theorem global_profile_W_R_restriction
    (B : Finset Label → Finset V) (he : ∀ D ∈ Profiles, profileEdgeCount G (B D) = 2)
    (E : Finset (Sym2 V)) (hE : E.card = 12)
    (howner : ∀ e ∈ E,
      (Profiles.filter (fun D => e ∈ (profileRestrictedGraph G (B D)).edgeFinset)).card = 1)
    (u v : V) (i : Label) (a : Arc) (ha : G.Adj u v) (hnot : s(u, v) ∉ E)
    (hu : ∀ D ∈ Profiles, negW D i → u ∈ B D)
    (hv : ∀ D ∈ Profiles, negR D a → v ∈ B D) : i = dst a := by
  apply (W_R_restriction i a).mp
  intro D hD hh
  exact profile_six_no_extra_negative_edge G Profiles six_profiles B he E hE howner
    u v ha hnot D hD ⟨hu D hD hh.1, hv D hD hh.2⟩

theorem global_profile_R_R_restriction
    (B : Finset Label → Finset V) (he : ∀ D ∈ Profiles, profileEdgeCount G (B D) = 2)
    (E : Finset (Sym2 V)) (hE : E.card = 12)
    (howner : ∀ e ∈ E,
      (Profiles.filter (fun D => e ∈ (profileRestrictedGraph G (B D)).edgeFinset)).card = 1)
    (u v : V) (a b : Arc) (ha : G.Adj u v) (hnot : s(u, v) ∉ E)
    (hu : ∀ D ∈ Profiles, negR D a → u ∈ B D)
    (hv : ∀ D ∈ Profiles, negR D b → v ∈ B D) :
    dst a = src b ∨ dst b = src a := by
  apply (R_R_restriction a b).mp
  intro D hD hh
  exact profile_six_no_extra_negative_edge G Profiles six_profiles B he E hE howner
    u v ha hnot D hD ⟨hu D hD hh.1, hv D hD hh.2⟩

end FourDirections

#print axioms finite_family_budget_saturated
#print axioms profile_six_budget_saturated
#print axioms profile_six_all_budget_saturated
#print axioms profile_six_structural_budget_saturated
#print axioms FourDirections.profile_V_internal_owner_count
#print axioms FourDirections.profile_W_internal_owner_count
#print axioms FourDirections.global_profile_R_R_restriction

end Conway99
