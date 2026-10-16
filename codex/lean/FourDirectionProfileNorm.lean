import FourDirectionProfiles
import FourDirectionOneTriangle

/-! Exact norm 23 for each profile, from the SRG row and the orthogonal
signed-cell Gram. No profile support cardinalities are assumed. -/

namespace Conway99

open scoped BigOperators Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem profileVertexBase_norm (h : G.IsSRGWith 99 14 1 2) (v : V) :
    (∑ u, profileVertexBase G v u ^ 2) = 23 := by
  have hp (u : V) : profileVertexBase G v u ^ 2 =
      (if u = v then (9 : ℤ) else 0) + (if G.Adj v u then 1 else 0) := by
    by_cases huv : u = v
    · subst u
      simp [profileVertexBase]
    · by_cases ha : G.Adj v u <;> simp [profileVertexBase, huv, ha]
  simp_rw [hp, Finset.sum_add_distrib]
  have hd : (Finset.univ.filter (G.Adj v)).card = 14 := by
    simpa [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter] using h.regular.degree_eq v
  simp [Finset.sum_ite, hd]

theorem profileVertexBase_code_product (b : V → ℤ)
    (he : ∀ u, (∑ w, if G.Adj u w then b w else 0) = -4 * b u) (v : V) :
    (∑ u, profileVertexBase G v u * b u) = 7 * b v := by
  have hp (u : V) : profileVertexBase G v u * b u =
      (if u = v then 3 * b v else 0) - (if G.Adj v u then b u else 0) := by
    by_cases huv : u = v
    · subst u
      simp [profileVertexBase]
    · by_cases ha : G.Adj v u <;> simp [profileVertexBase, huv, ha]
  simp_rw [hp]
  rw [Finset.sum_sub_distrib, he v]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

namespace FourDirectionSystem

variable {G} (F : FourDirectionSystem G)

theorem code_norm (i : Fin 4) : (∑ u, F.code i u ^ 2) = 14 := by
  rw [sign_code_norm _ (F.biplane i).signs, (F.biplane i).positive_card,
    (F.biplane i).negative_card]
  norm_num

theorem signed_cells_code_orthogonal (hc : F.HasSignedCells) (i j : Fin 4) (hij : i ≠ j) :
    (∑ u, F.code i u * F.code j u) = 0 := by
  have hp (u : V) : F.code i u * F.code j u =
      (if u ∈ positiveCodeSupport (F.code i) ∩ positiveCodeSupport (F.code j) then (1 : ℤ) else 0) +
      (if u ∈ negativeCodeSupport (F.code i) ∩ negativeCodeSupport (F.code j) then 1 else 0) -
      (if u ∈ positiveCodeSupport (F.code i) ∩ negativeCodeSupport (F.code j) then 1 else 0) -
      (if u ∈ negativeCodeSupport (F.code i) ∩ positiveCodeSupport (F.code j) then 1 else 0) := by
    rcases (F.biplane i).signs u with hi | hi | hi <;>
      rcases (F.biplane j).signs u with hj | hj | hj <;>
      simp [positiveCodeSupport, negativeCodeSupport, hi, hj]
  have hpp := hc i j hij true true
  have hnn := hc i j hij false false
  have hpn := hc i j hij true false
  have hnp := hc i j hij false true
  simp only [signedCodeSupport, ite_true, Bool.false_eq_true, ite_false] at hpp hnn hpn hnp
  simp_rw [hp, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hind (T : Finset V) : (∑ u, if u ∈ T then (1 : ℤ) else 0) = (T.card : ℤ) := by
    simp only [Finset.sum_boole, Finset.filter_univ_mem]
  rw [hind, hind, hind, hind, hpp, hnn, hpn, hnp]
  norm_num

theorem signed_cells_code_gram (hc : F.HasSignedCells) (i j : Fin 4) :
    (∑ u, F.code i u * F.code j u) = if i = j then 14 else 0 := by
  by_cases hij : i = j
  · subst j
    simpa [pow_two] using F.code_norm i
  · simpa [hij] using F.signed_cells_code_orthogonal hc i j hij

theorem profile_norm (h : G.IsSRGWith 99 14 1 2) (hc : F.HasSignedCells)
    (v : V) (hv : F.weight v = 4) (D : Finset (Fin 4)) :
    (∑ u, F.profile v D u ^ 2) = 23 := by
  let a := profileVertexBase G v
  let t : V → ℤ := fun u => ∑ i ∈ D, F.code i v * F.code i u
  have heps (i : Fin 4) : F.code i v ^ 2 = 1 := by
    have hn := (F.weight_four_iff v).mp hv i
    rcases (F.biplane i).signs v with hi | hi | hi
    · simp [hi]
    · exact (hn hi).elim
    · simp [hi]
  have hat : a ⬝ᵥ t = 7 * (D.card : ℤ) := by
    change (∑ u, a u * ∑ i ∈ D, F.code i v * F.code i u) = _
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have ht (i : Fin 4) : (∑ u, a u * (F.code i v * F.code i u)) = 7 := by
      have hb := profileVertexBase_code_product G (F.code i) (F.eigen i) v
      change (∑ u, profileVertexBase G v u * (F.code i v * F.code i u)) = _
      calc
        _ = F.code i v * ∑ u, profileVertexBase G v u * F.code i u := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u _
          ring
        _ = 7 := by rw [hb]; nlinarith [heps i]
    simp_rw [ht]
    simp [mul_comm]
  have htt : t ⬝ᵥ t = 14 * (D.card : ℤ) := by
    change (∑ u, (∑ i ∈ D, F.code i v * F.code i u) *
      ∑ j ∈ D, F.code j v * F.code j u) = _
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hi (i : Fin 4) :
        (∑ u, ∑ j ∈ D, F.code i v * F.code i u * (F.code j v * F.code j u)) =
          ∑ j ∈ D, if i = j then (14 : ℤ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = (F.code i v * F.code j v) * ∑ u, F.code i u * F.code j u := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u _
          ring
        _ = if i = j then 14 else 0 := by
          rw [F.signed_cells_code_gram hc i j]
          by_cases hij : i = j
          · subst j
            simp only [if_true]
            nlinarith [heps i]
          · simp [hij]
    simp_rw [hi]
    simp [mul_comm]
  have haa : a ⬝ᵥ a = 23 := by
    simpa only [a, dotProduct, ← pow_two] using profileVertexBase_norm G h v
  have hta : t ⬝ᵥ a = 7 * (D.card : ℤ) := by rw [dotProduct_comm]; exact hat
  simp only [pow_two]
  change (a - t) ⬝ᵥ (a - t) = 23
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, haa, hat, hta, htt]
  ring

theorem profile_cardinalities_of_ternary (h : G.IsSRGWith 99 14 1 2) (hc : F.HasSignedCells)
    (v : V) (hv : F.weight v = 4) (D : Finset (Fin 4))
    (hs : ∀ u, F.profile v D u = -1 ∨ F.profile v D u = 0 ∨ F.profile v D u = 1) :
    (positiveCodeSupport (F.profile v D)).card = 6 ∧
      (negativeCodeSupport (F.profile v D)).card = 17 :=
  ternary_affine_profile_cardinalities_of_norm G h _ hs (F.profile_affine_eigen h v D)
    (F.profile_norm h hc v hv D)

end FourDirectionSystem

#print axioms profileVertexBase_norm
#print axioms profileVertexBase_code_product
#print axioms FourDirectionSystem.signed_cells_code_gram
#print axioms FourDirectionSystem.profile_norm
#print axioms FourDirectionSystem.profile_cardinalities_of_ternary

end Conway99
