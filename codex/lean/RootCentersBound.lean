import RootHoffman
import HoffmanOrthogonalIntersection

/-! Gram of root centres and the first bound of four root directions. -/

namespace Conway99

open scoped BigOperators Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def rootSignedHoffman (b : V → ℤ) (s : Bool) : Finset V :=
  if s then rootPositiveHoffman G b else rootNegativeHoffman G b

def rootCenterCode (b : V → ℤ) : V → ℚ :=
  (1 / 2 : ℚ) • (hoffmanCocliqueCode G (rootPositiveHoffman G b) +
    hoffmanCocliqueCode G (rootNegativeHoffman G b))

theorem rootSignedHoffman_specs (h : G.IsSRGWith 99 14 1 2)
    (b : V → ℤ) (hb : SignedBiplaneCode G b)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u) (s : Bool) :
    (rootSignedHoffman G b s).card = 22 ∧
      G.IsIndepSet (rootSignedHoffman G b s : Set V) := by
  obtain ⟨hp, hpI, hn, hnI⟩ := signed_biplane_canonical_hoffman G h b hb he
  cases s <;> simp [rootSignedHoffman, hp, hpI, hn, hnI]

theorem root_canonical_hoffman_intersection (b : V → ℤ) :
    rootPositiveHoffman G b ∩ rootNegativeHoffman G b = rootIsolated G b := by
  ext u
  simp only [Finset.mem_inter, rootPositiveHoffman, rootNegativeHoffman, Finset.mem_union]
  constructor
  · rintro ⟨hp | hi, hn | hi'⟩
    · have hp' := (Finset.mem_filter.mp hp).2
      have hn' := (Finset.mem_filter.mp hn).2
      omega
    · exact hi'
    · exact hi
    · exact hi
  · exact fun hi => ⟨Or.inr hi, Or.inr hi⟩

theorem orthogonal_canonical_hoffman_intersection
    (h : G.IsSRGWith 99 14 1 2) (b : V → ℤ) (hb : SignedBiplaneCode G b)
    (hE : (fun u => (b u : ℚ)) ∈ rationalAmbient G)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u)
    (H : Finset V) (hH : G.IsIndepSet (H : Set V)) (hc : H.card = 22)
    (ho : codePair (hoffmanCocliqueCode G H) ((3 : ℚ) • (fun u => (b u : ℚ))) = 0)
    (s : Bool) : (H ∩ rootSignedHoffman G b s).card = 1 := by
  obtain ⟨hp, hn, hi⟩ := hoffman_orthogonal_root_intersections G h b hb hE he H hH hc ho
  cases s
  · simpa only [rootSignedHoffman, Bool.false_eq_true, ite_false, rootNegativeHoffman,
      Finset.inter_union_distrib_left, hi, Finset.union_empty] using hn
  · simpa only [rootSignedHoffman, ite_true, rootPositiveHoffman,
      Finset.inter_union_distrib_left, hi, Finset.union_empty] using hp

theorem rootCenterCode_norm (h : G.IsSRGWith 99 14 1 2)
    (b : V → ℤ) (hb : SignedBiplaneCode G b)
    (he : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u) :
    codePair (rootCenterCode G b) (rootCenterCode G b) = 35 / 18 := by
  obtain ⟨hp, hpI, hn, hnI⟩ := signed_biplane_canonical_hoffman G h b hb he
  have hpp := hoffmanCocliqueCode_norm G h hpI hp
  have hnn := hoffmanCocliqueCode_norm G h hnI hn
  have hpn := hoffmanCocliqueCode_pair G h hpI hp hnI hn
  rw [root_canonical_hoffman_intersection, signed_biplane_isolated_card G h b hb he] at hpn
  norm_num at hpn
  have hnp : codePair (hoffmanCocliqueCode G (rootNegativeHoffman G b))
      (hoffmanCocliqueCode G (rootPositiveHoffman G b)) = 13 / 9 := by
    rw [codePair_symm]
    exact hpn
  simp only [rootCenterCode, codePair_smul_left, codePair_smul_right,
    codePair_add_left, codePair_add_right]
  rw [hpp, hnn, hpn, hnp]
  norm_num

theorem rootCenterCode_cross_pair
    (h : G.IsSRGWith 99 14 1 2) (b c : V → ℤ)
    (hb : SignedBiplaneCode G b) (hc : SignedBiplaneCode G c)
    (hE : (fun u => (c u : ℚ)) ∈ rationalAmbient G)
    (heb : ∀ u, (∑ v, if G.Adj u v then b v else 0) = -4 * b u)
    (hec : ∀ u, (∑ v, if G.Adj u v then c v else 0) = -4 * c u)
    (ho : ∀ s : Bool, codePair (hoffmanCocliqueCode G (rootSignedHoffman G b s))
      ((3 : ℚ) • (fun u => (c u : ℚ))) = 0) :
    codePair (rootCenterCode G b) (rootCenterCode G c) = -5 / 9 := by
  have hi (s t : Bool) :
      (rootSignedHoffman G b s ∩ rootSignedHoffman G c t).card = 1 :=
    orthogonal_canonical_hoffman_intersection G h c hc hE hec _
      (rootSignedHoffman_specs G h b hb heb s).2
      (rootSignedHoffman_specs G h b hb heb s).1 (ho s) t
  have hp (s t : Bool) : codePair (hoffmanCocliqueCode G (rootSignedHoffman G b s))
      (hoffmanCocliqueCode G (rootSignedHoffman G c t)) = -5 / 9 := by
    rw [hoffmanCocliqueCode_pair G h (rootSignedHoffman_specs G h b hb heb s).2
      (rootSignedHoffman_specs G h b hb heb s).1
      (rootSignedHoffman_specs G h c hc hec t).2
      (rootSignedHoffman_specs G h c hc hec t).1, hi]
    norm_num
  have hpp := hp true true
  have hpn := hp true false
  have hnp := hp false true
  have hnn := hp false false
  simp only [rootSignedHoffman, Bool.false_eq_true, ite_true, ite_false] at hpp hpn hnp hnn
  simp only [rootCenterCode, codePair_smul_left, codePair_smul_right,
    codePair_add_left, codePair_add_right]
  rw [hpp, hpn, hnp, hnn]
  norm_num

theorem codePair_sum_left {ι : Type*} [Fintype ι] (x : ι → V → ℚ) (y : V → ℚ) :
    codePair (∑ i, x i) y = ∑ i, codePair (x i) y := by
  simp only [codePair, sum_dotProduct, Finset.sum_div]

theorem codePair_sum_right {ι : Type*} [Fintype ι] (x : V → ℚ) (y : ι → V → ℚ) :
    codePair x (∑ i, y i) = ∑ i, codePair x (y i) := by
  simp only [codePair, dotProduct_sum, Finset.sum_div]

theorem codePair_nonneg (x : V → ℚ) : 0 ≤ codePair x x :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)) (by norm_num)

theorem root_centers_gram_card_le_four {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → V → ℚ)
    (hz : ∀ i j, codePair (z i) (z j) = if i = j then 35 / 18 else -5 / 9) :
    Fintype.card ι ≤ 4 := by
  have he (i j : ι) : codePair (z i) (z j) = (if i = j then (5 / 2 : ℚ) else 0) - 5 / 9 := by
    rw [hz]
    by_cases hij : i = j <;> norm_num [hij]
  have hn := codePair_nonneg (∑ i, z i)
  rw [codePair_sum_left] at hn
  simp_rw [codePair_sum_right, he] at hn
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hn
  have hc : (0 : ℚ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hl : (Fintype.card ι : ℚ) < 5 := by nlinarith
  have hl' : Fintype.card ι < 5 := by exact_mod_cast hl
  omega

theorem root_centers_card_le_four (h : G.IsSRGWith 99 14 1 2)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → V → ℤ)
    (hb : ∀ i, SignedBiplaneCode G (b i))
    (hE : ∀ i, (fun u => (b i u : ℚ)) ∈ rationalAmbient G)
    (he : ∀ i u, (∑ v, if G.Adj u v then b i v else 0) = -4 * b i u)
    (ho : ∀ i j, i ≠ j → ∀ s : Bool,
      codePair (hoffmanCocliqueCode G (rootSignedHoffman G (b i) s))
        ((3 : ℚ) • (fun u => (b j u : ℚ))) = 0) :
    Fintype.card ι ≤ 4 := by
  apply root_centers_gram_card_le_four (fun i => rootCenterCode G (b i))
  intro i j
  by_cases hij : i = j
  · subst j
    simpa using rootCenterCode_norm G h (b i) (hb i) (he i)
  · simpa only [if_neg hij] using
      rootCenterCode_cross_pair G h (b i) (b j) (hb i) (hb j) (hE j) (he i) (he j) (ho i j hij)

#print axioms orthogonal_canonical_hoffman_intersection
#print axioms rootCenterCode_norm
#print axioms rootCenterCode_cross_pair
#print axioms root_centers_card_le_four

end Conway99
