import HoffmanCocliques
import RootEquitable

/-! Orthogonal Hoffman cocliques meet each signed half once and avoid the isolated cell. -/

namespace Conway99

open scoped BigOperators Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem hoffman_equal_sign_intersections_le_one
    (b : V → ℤ) (hb : SignedBiplaneCode G b)
    (H : Finset V) (hH : G.IsIndepSet (H : Set V))
    (heq : (H ∩ positiveCodeSupport b).card = (H ∩ negativeCodeSupport b).card) :
    (H ∩ positiveCodeSupport b).card ≤ 1 := by
  by_contra hn
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp
    (by omega : 1 < (H ∩ positiveCodeSupport b).card)
  have hpH := (Finset.mem_inter.mp hp).1
  have hqH := (Finset.mem_inter.mp hq).1
  have hpP := (Finset.mem_inter.mp hp).2
  have hqP := (Finset.mem_inter.mp hq).2
  let A := (negativeCodeSupport b).filter (G.Adj p)
  let B := (negativeCodeSupport b).filter (G.Adj q)
  have hA : A.card = 4 := hb.positive_cross p hpP
  have hB : B.card = 4 := hb.positive_cross q hqP
  have hAB : (A ∩ B).card = 2 := by
    have hu : A ∩ B = (negativeCodeSupport b).filter
        (fun v => G.Adj p v ∧ G.Adj q v) := by
      ext v
      simp [A, B, and_assoc, and_left_comm, and_comm]
    rw [hu]
    exact hb.positive_pairs p hpP q hqP hpq
  have hU : (A ∪ B).card = 6 := by
    have hh := Finset.card_union_add_card_inter A B
    omega
  have hd : Disjoint (H ∩ negativeCodeSupport b) (A ∪ B) := by
    apply Finset.disjoint_left.mpr
    intro v hv hvU
    have hvH := (Finset.mem_inter.mp hv).1
    rcases Finset.mem_union.mp hvU with hvA | hvB
    · have ha := (Finset.mem_filter.mp hvA).2
      exact ((G.isIndepSet_iff.mp hH) hpH hvH (G.ne_of_adj ha)) ha
    · have ha := (Finset.mem_filter.mp hvB).2
      exact ((G.isIndepSet_iff.mp hH) hqH hvH (G.ne_of_adj ha)) ha
  have hs : (H ∩ negativeCodeSupport b) ∪ (A ∪ B) ⊆ negativeCodeSupport b := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact (Finset.mem_inter.mp hv).2
    · rcases Finset.mem_union.mp hv with hv | hv <;> exact (Finset.mem_filter.mp hv).1
  have hh := Finset.card_le_card hs
  rw [Finset.card_union_of_disjoint hd, hU, hb.negative_card] at hh
  omega

theorem finiteIndicator_dot_intersection (T U : Finset V) :
    finiteIndicator T ⬝ᵥ finiteIndicator U = ((T ∩ U).card : ℚ) := by
  simpa only [dotProduct, finiteIndicator, cocliqueIndicator] using
    cocliqueIndicator_intersection T U

theorem finiteIndicator_dot_one (T : Finset V) :
    finiteIndicator T ⬝ᵥ (fun _ => (1 : ℚ)) = (T.card : ℚ) := by
  simpa only [dotProduct, mul_one] using finiteIndicator_sum T

theorem finiteIndicator_adjacency_swap (T U : Finset V) :
    finiteIndicator T ⬝ᵥ (G.adjMatrix ℚ *ᵥ finiteIndicator U) =
      finiteIndicator U ⬝ᵥ (G.adjMatrix ℚ *ᵥ finiteIndicator T) := by
  have ht : (G.adjMatrix ℚ).transpose = G.adjMatrix ℚ := by
    ext u v
    simp [Matrix.transpose_apply, SimpleGraph.adjMatrix_apply, SimpleGraph.adj_comm]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ht, dotProduct_comm]

theorem hoffman_finiteIndicator_dot_adjacency
    (h : G.IsSRGWith 99 14 1 2) (H : Finset V)
    (hH : G.IsIndepSet (H : Set V)) (hc : H.card = 22) (T : Finset V) :
    finiteIndicator T ⬝ᵥ (G.adjMatrix ℚ *ᵥ finiteIndicator H) =
      4 * ((T.card : ℚ) - ((T ∩ H).card : ℚ)) := by
  have hn : G.adjMatrix ℚ *ᵥ finiteIndicator H =
      (4 : ℚ) • ((fun _ => (1 : ℚ)) - finiteIndicator H) := by
    simpa only [finiteIndicator, cocliqueIndicator, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      using hoffman_coclique_nexus G h hH hc
  rw [hn, dotProduct_smul, dotProduct_sub, finiteIndicator_dot_one,
    finiteIndicator_dot_intersection]
  rfl

theorem hoffman_orthogonal_intersections
    (h : G.IsSRGWith 99 14 1 2) (b : V → ℤ) (hb : SignedBiplaneCode G b)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u)
    (H : Finset V) (hH : G.IsIndepSet (H : Set V)) (hc : H.card = 22)
    (heq : (H ∩ positiveCodeSupport b).card = (H ∩ negativeCodeSupport b).card) :
    (H ∩ positiveCodeSupport b).card = 1 ∧
      (H ∩ negativeCodeSupport b).card = 1 ∧ H ∩ rootIsolated G b = ∅ := by
  have ht := hoffman_equal_sign_intersections_le_one G b hb H hH heq
  have hdis : Disjoint (positiveCodeSupport b) (negativeCodeSupport b) := by
    apply Finset.disjoint_left.mpr
    intro v hp hn
    have hp' := (Finset.mem_filter.mp hp).2
    have hn' := (Finset.mem_filter.mp hn).2
    omega
  have hC : (H ∩ rootSupport b).card =
      (H ∩ positiveCodeSupport b).card + (H ∩ negativeCodeSupport b).card := by
    rw [rootSupport, Finset.inter_union_distrib_left,
      Finset.card_union_of_disjoint (Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right hdis))]
  have hbound : (H ∩ rootSupport b).card ≤ 2 := by omega
  have hA := congrArg (fun x => finiteIndicator H ⬝ᵥ x)
    (signed_biplane_support_adjacency G h b hb he)
  simp only [dotProduct_add, dotProduct_smul, finiteIndicator_dot_intersection, smul_eq_mul] at hA
  rw [finiteIndicator_adjacency_swap, hoffman_finiteIndicator_dot_adjacency G h H hH hc,
    signed_biplane_support_card G b hb] at hA
  rw [Finset.inter_comm (rootSupport b) H] at hA
  have hpart := congrArg (fun x => finiteIndicator H ⬝ᵥ x)
    (signed_biplane_indicator_partition G h b hb he)
  simp only [dotProduct_add, finiteIndicator_dot_intersection, finiteIndicator_dot_one, hc] at hpart
  have hcz : (0 : ℚ) ≤ (H ∩ rootSupport b).card := Nat.cast_nonneg _
  have haz : (0 : ℚ) ≤ (H ∩ rootShell G b).card := Nat.cast_nonneg _
  have hdz : (0 : ℚ) ≤ (H ∩ rootIsolated G b).card := Nat.cast_nonneg _
  have hcb : ((H ∩ rootSupport b).card : ℚ) ≤ 2 := by exact_mod_cast hbound
  have hc2 : ((H ∩ rootSupport b).card : ℚ) = 2 := by
    norm_num only [Nat.cast_ofNat] at hA hpart
    linarith
  have hc2n : (H ∩ rootSupport b).card = 2 := by exact_mod_cast hc2
  have hd0 : ((H ∩ rootIsolated G b).card : ℚ) = 0 := by
    norm_num only [Nat.cast_ofNat] at hA hpart
    linarith
  have hd0n : (H ∩ rootIsolated G b).card = 0 := by exact_mod_cast hd0
  refine ⟨by omega, by omega, Finset.card_eq_zero.mp hd0n⟩

theorem coclique_signed_sum (b : V → ℤ)
    (hsigns : ∀ u, b u = -1 ∨ b u = 0 ∨ b u = 1) (H : Finset V) :
    ∑ u, (b u : ℚ) * cocliqueIndicator H u =
      ((H ∩ positiveCodeSupport b).card : ℚ) - ((H ∩ negativeCodeSupport b).card : ℚ) := by
  have hp (u : V) : (b u : ℚ) * cocliqueIndicator H u =
      cocliqueIndicator H u * cocliqueIndicator (positiveCodeSupport b) u -
        cocliqueIndicator H u * cocliqueIndicator (negativeCodeSupport b) u := by
    rcases hsigns u with hu | hu | hu <;>
      by_cases hv : u ∈ H <;>
      simp [cocliqueIndicator, positiveCodeSupport, negativeCodeSupport, hu, hv]
  simp_rw [hp]
  rw [Finset.sum_sub_distrib, cocliqueIndicator_intersection, cocliqueIndicator_intersection]

theorem hoffmanCocliqueCode_signed_root_pair (h : G.IsSRGWith 99 14 1 2)
    (b : V → ℤ) (hE : (fun u => (b u : ℚ)) ∈ rationalAmbient G)
    (hsigns : ∀ u, b u = -1 ∨ b u = 0 ∨ b u = 1) (H : Finset V) :
    codePair (hoffmanCocliqueCode G H) ((3 : ℚ) • (fun u => (b u : ℚ))) =
      (((H ∩ positiveCodeSupport b).card : ℚ) - ((H ∩ negativeCodeSupport b).card : ℚ)) / 7 := by
  rw [codePair_symm]
  change codePair ((3 : ℚ) • (fun u => (b u : ℚ)))
    ((1 / 7 : ℚ) • coefficientCode G (cocliqueCoefficients H)) = _
  rw [codePair_smul_right,
    codePair_coefficientCode G h ((rationalAmbient G).smul_mem (3 : ℚ) hE)]
  have he : (∑ u, ((3 : ℚ) • (fun u => (b u : ℚ))) u * (cocliqueCoefficients H u : ℚ)) =
      3 * ∑ u, (b u : ℚ) * cocliqueIndicator H u := by
    simp only [Pi.smul_apply, smul_eq_mul, cocliqueCoefficients, Int.cast_ite,
      Int.cast_one, Int.cast_zero, cocliqueIndicator, Finset.mul_sum, mul_assoc]
  rw [he, coclique_signed_sum b hsigns H]
  ring

theorem hoffman_orthogonal_root_intersections
    (h : G.IsSRGWith 99 14 1 2) (b : V → ℤ) (hb : SignedBiplaneCode G b)
    (hE : (fun u => (b u : ℚ)) ∈ rationalAmbient G)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u)
    (H : Finset V) (hH : G.IsIndepSet (H : Set V)) (hc : H.card = 22)
    (ho : codePair (hoffmanCocliqueCode G H) ((3 : ℚ) • (fun u => (b u : ℚ))) = 0) :
    (H ∩ positiveCodeSupport b).card = 1 ∧
      (H ∩ negativeCodeSupport b).card = 1 ∧ H ∩ rootIsolated G b = ∅ := by
  have hp := hoffmanCocliqueCode_signed_root_pair G h b hE hb.signs H
  rw [ho] at hp
  have heq : ((H ∩ positiveCodeSupport b).card : ℚ) =
      ((H ∩ negativeCodeSupport b).card : ℚ) := by linarith
  have heq' : (H ∩ positiveCodeSupport b).card = (H ∩ negativeCodeSupport b).card := by
    exact_mod_cast heq
  exact hoffman_orthogonal_intersections G h b hb he H hH hc heq'

#print axioms hoffman_equal_sign_intersections_le_one
#print axioms hoffman_orthogonal_intersections
#print axioms hoffmanCocliqueCode_signed_root_pair
#print axioms hoffman_orthogonal_root_intersections

end Conway99
