import FourDirectionProfileNorm
import FourDirectionOnePartition
import FourDirections

/-! Ternarity and actual six/seventeen support sizes of the profiles in the
one-zero configuration. The proof uses two unique signed cells, not enumeration. -/

namespace Conway99

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem ternary_sign_product (a b : ℤ) (ha : a = -1 ∨ a = 1)
    (hb : b = -1 ∨ b = 0 ∨ b = 1) :
    (-1 ≤ a * b ∧ a * b ≤ 1) ∧ (a * b = 1 ↔ b = a) ∧ (a * b = -1 ↔ b = -a) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb | hb <;> norm_num [ha, hb]

namespace OnePointConfiguration

variable {F : FourDirectionSystem G} (C : OnePointConfiguration F)

theorem profile_code_square (i : Fin 4) : F.code i C.v ^ 2 = 1 := by
  rcases (F.biplane i).signs C.v with hi | hi | hi
  · simp [hi]
  · exact (C.v_code_ne i hi).elim
  · simp [hi]

theorem profile_code_product (i : Fin 4) (u : V) :
    (-1 ≤ F.code i C.v * F.code i u ∧ F.code i C.v * F.code i u ≤ 1) ∧
    (F.code i C.v * F.code i u = 1 ↔ F.code i u = F.code i C.v) ∧
    (F.code i C.v * F.code i u = -1 ↔ F.code i u = -F.code i C.v) := by
  apply ternary_sign_product
  · rcases (F.biplane i).signs C.v with hi | hi | hi
    · exact Or.inl hi
    · exact (C.v_code_ne i hi).elim
    · exact Or.inr hi
  · exact (F.biplane i).signs u

theorem profile_at_v (D : Finset (Fin 4)) (hD : D.card = 2) : F.profile C.v D C.v = 1 := by
  have he (i : Fin 4) : F.code i C.v * F.code i C.v = 1 := by
    simpa only [pow_two] using C.profile_code_square i
  simp [FourDirectionSystem.profile, profileVertexBase, he, hD]

theorem profile_at_w (D : Finset (Fin 4)) (hD : D.card = 2) : F.profile C.v D C.w = 1 := by
  have he (i : Fin 4) : F.code i C.v * F.code i C.w = -1 := by
    apply (C.profile_code_product i C.w).2.2.mpr
    have hop := C.opposite i
    omega
  simp [FourDirectionSystem.profile, profileVertexBase, Ne.symm C.vw_ne, C.vw_adj, he, hD]

theorem profile_ternary (D : Finset (Fin 4)) (hD : D.card = 2) (u : V) :
    F.profile C.v D u = -1 ∨ F.profile C.v D u = 0 ∨ F.profile C.v D u = 1 := by
  by_cases huv : u = C.v
  · subst u
    exact Or.inr (Or.inr (C.profile_at_v D hD))
  by_cases huw : u = C.w
  · subst u
    exact Or.inr (Or.inr (C.profile_at_w D hD))
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hD
  have hi := C.profile_code_product i u
  have hj := C.profile_code_product j u
  have hform : F.profile C.v {i,j} u =
      (if G.Adj C.v u then (-1 : ℤ) else 0) -
        (F.code i C.v * F.code i u + F.code j C.v * F.code j u) := by
    by_cases ha : G.Adj C.v u <;>
      simp [FourDirectionSystem.profile, profileVertexBase, huv, hij, ha]
  rw [hform]
  by_cases ha : G.Adj C.v u
  · have hni : F.code i C.v * F.code i u ≤ 0 := by
      have hnot : F.code i C.v * F.code i u ≠ 1 := by
        intro hh
        exact F.same_nonzero_coordinate_not_adj i (C.v_code_ne i) (hi.2.1.mp hh).symm ha
      omega
    have hnj : F.code j C.v * F.code j u ≤ 0 := by
      have hnot : F.code j C.v * F.code j u ≠ 1 := by
        intro hh
        exact F.same_nonzero_coordinate_not_adj j (C.v_code_ne j) (hj.2.1.mp hh).symm ha
      omega
    simp only [if_pos ha]
    omega
  · have hpos : ¬ (F.code i C.v * F.code i u = 1 ∧ F.code j C.v * F.code j u = 1) := by
      rintro ⟨hpi, hpj⟩
      have heq : C.v = u := F.equal_nonzero_coordinates_unique C.signedCells i j hij
        (C.v_code_ne i) (C.v_code_ne j) (hi.2.1.mp hpi).symm (hj.2.1.mp hpj).symm
      exact huv heq.symm
    have hneg : ¬ (F.code i C.v * F.code i u = -1 ∧ F.code j C.v * F.code j u = -1) := by
      rintro ⟨hmi, hmj⟩
      have hei : F.code i C.w = F.code i u := by
        have hp := hi.2.2.mp hmi
        have ho := C.opposite i
        omega
      have hej : F.code j C.w = F.code j u := by
        have hp := hj.2.2.mp hmj
        have ho := C.opposite j
        omega
      have heq : C.w = u := F.equal_nonzero_coordinates_unique C.signedCells i j hij
        (C.w_code_ne i) (C.w_code_ne j) hei hej
      exact huw heq.symm
    simp only [if_neg ha]
    omega

theorem profile_cardinalities (D : Finset (Fin 4)) (hD : D.card = 2) :
    (positiveCodeSupport (F.profile C.v D)).card = 6 ∧
      (negativeCodeSupport (F.profile C.v D)).card = 17 :=
  F.profile_cardinalities_of_ternary C.srg C.signedCells C.v C.v_weight D (C.profile_ternary D hD)

theorem profile_edge_counts (D : Finset (Fin 4)) (hD : D.card = 2) :
    profileEdgeCount G (positiveCodeSupport (F.profile C.v D)) = 1 ∧
      profileEdgeCount G (negativeCodeSupport (F.profile C.v D)) = 2 := by
  have hcard := C.profile_cardinalities D hD
  have hdegree := ternary_affine_profile_degrees G _ (C.profile_ternary D hD)
    (F.profile_affine_eigen C.srg C.v D)
  apply profile_six_seventeen_saturated_of_edge G C.srg _ _ hcard.1 hcard.2
    hdegree.1 hdegree.2 C.v C.w _ _ C.vw_adj
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.profile_at_v D hD⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.profile_at_w D hD⟩

theorem six_profile_negative_edge_counts :
    ∀ D ∈ FourDirections.Profiles,
      profileEdgeCount G (negativeCodeSupport (F.profile C.v D)) = 2 := by
  intro D hD
  exact (C.profile_edge_counts D (Finset.mem_filter.mp hD).2).2

end OnePointConfiguration

#print axioms OnePointConfiguration.profile_ternary
#print axioms OnePointConfiguration.profile_cardinalities
#print axioms OnePointConfiguration.profile_edge_counts
#print axioms OnePointConfiguration.six_profile_negative_edge_counts

end Conway99
