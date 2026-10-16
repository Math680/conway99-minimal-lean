import LatticeQuadratic

/-! Hoffman bound and its equality case, from the SRG equations alone. -/

namespace Conway99

open scoped BigOperators Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def hoffmanPositiveMatrix : Matrix V V ℚ :=
  G.adjMatrix ℚ + (4 : ℚ) • 1 - (2 / 11 : ℚ) • allOnes

theorem hoffmanPositiveMatrix_square (h : G.IsSRGWith 99 14 1 2) :
    hoffmanPositiveMatrix G * hoffmanPositiveMatrix G =
      (7 : ℚ) • hoffmanPositiveMatrix G := by
  unfold hoffmanPositiveMatrix
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
  rw [adjacency_square G h, adjacency_mul_ones G h, ones_mul_adjacency G h,
    ones_square G h]
  module

theorem hoffmanPositiveMatrix_transpose :
    (hoffmanPositiveMatrix G).transpose = hoffmanPositiveMatrix G := by
  ext u v
  simp [hoffmanPositiveMatrix, Matrix.transpose_apply, Matrix.one_apply,
    SimpleGraph.adjMatrix_apply, allOnes, eq_comm, SimpleGraph.adj_comm]

theorem hoffmanPositiveMatrix_posSemidef (h : G.IsSRGWith 99 14 1 2) :
    (hoffmanPositiveMatrix G).PosSemidef := by
  refine ⟨?_, ?_⟩
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hoffmanPositiveMatrix_transpose G
  · intro x
    have hx : 0 ≤ x ⬝ᵥ ((hoffmanPositiveMatrix G * hoffmanPositiveMatrix G) *ᵥ x) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
        hoffmanPositiveMatrix_transpose]
      exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
    rw [hoffmanPositiveMatrix_square G h, Matrix.smul_mulVec, dotProduct_smul] at hx
    simp only [smul_eq_mul, star_trivial]
    norm_num at hx
    linarith

def cocliqueIndicator (H : Finset V) : V → ℚ := fun u => if u ∈ H then 1 else 0

def cocliqueCoefficients (H : Finset V) : V → ℤ := fun u => if u ∈ H then 1 else 0

theorem cocliqueIndicator_sum (H : Finset V) :
    ∑ u, cocliqueIndicator H u = (H.card : ℚ) := by
  simp [cocliqueIndicator]

theorem cocliqueIndicator_dot (H : Finset V) :
    cocliqueIndicator H ⬝ᵥ cocliqueIndicator H = (H.card : ℚ) := by
  simp [dotProduct, cocliqueIndicator]

theorem coclique_adjacency_zero {H : Finset V} (hH : G.IsIndepSet (H : Set V))
    {u : V} (hu : u ∈ H) :
    (G.adjMatrix ℚ *ᵥ cocliqueIndicator H) u = 0 := by
  unfold Matrix.mulVec dotProduct
  apply Finset.sum_eq_zero
  intro v _
  by_cases hv : v ∈ H
  · have hn : ¬G.Adj u v := by
      by_cases huv : u = v
      · subst v; exact G.loopless u
      · exact (G.isIndepSet_iff.mp hH) hu hv huv
    simp [SimpleGraph.adjMatrix_apply, hn, cocliqueIndicator, hv]
  · simp [cocliqueIndicator, hv]

theorem coclique_adjacency_dot_zero {H : Finset V} (hH : G.IsIndepSet (H : Set V)) :
    cocliqueIndicator H ⬝ᵥ (G.adjMatrix ℚ *ᵥ cocliqueIndicator H) = 0 := by
  unfold dotProduct
  apply Finset.sum_eq_zero
  intro u _
  by_cases hu : u ∈ H
  · rw [coclique_adjacency_zero G hH hu, mul_zero]
  · simp [cocliqueIndicator, hu]

theorem coclique_positive_dot {H : Finset V} (hH : G.IsIndepSet (H : Set V)) :
    cocliqueIndicator H ⬝ᵥ (hoffmanPositiveMatrix G *ᵥ cocliqueIndicator H) =
      4 * (H.card : ℚ) - (2 / 11 : ℚ) * (H.card : ℚ) ^ 2 := by
  unfold hoffmanPositiveMatrix
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_add, dotProduct_smul, dotProduct_smul,
    coclique_adjacency_dot_zero G hH, cocliqueIndicator_dot]
  have hj : (allOnes : Matrix V V ℚ) *ᵥ cocliqueIndicator H =
      fun _ => (H.card : ℚ) := by
    ext u
    simpa only [Matrix.mulVec, dotProduct, allOnes, one_mul] using cocliqueIndicator_sum H
  rw [hj]
  have hd : cocliqueIndicator H ⬝ᵥ (fun _ => (H.card : ℚ)) = (H.card : ℚ) ^ 2 := by
    simp only [dotProduct, ← Finset.sum_mul, cocliqueIndicator_sum]
    ring
  rw [hd]
  simp only [smul_eq_mul]
  ring

theorem hoffman_coclique_card_le (h : G.IsSRGWith 99 14 1 2)
    {H : Finset V} (hH : G.IsIndepSet (H : Set V)) : H.card ≤ 22 := by
  have hp := (hoffmanPositiveMatrix_posSemidef G h).2 (cocliqueIndicator H)
  simp only [star_trivial] at hp
  rw [coclique_positive_dot G hH] at hp
  have hc : (0 : ℚ) ≤ H.card := Nat.cast_nonneg _
  have he : (H.card : ℚ) ≤ 22 := by nlinarith
  exact_mod_cast he

theorem hoffmanPositiveMatrix_zero_of_dot_zero (h : G.IsSRGWith 99 14 1 2)
    (x : V → ℚ) (hx : x ⬝ᵥ (hoffmanPositiveMatrix G *ᵥ x) = 0) :
    hoffmanPositiveMatrix G *ᵥ x = 0 := by
  have hn : x ⬝ᵥ ((hoffmanPositiveMatrix G * hoffmanPositiveMatrix G) *ᵥ x) =
      (hoffmanPositiveMatrix G *ᵥ x) ⬝ᵥ (hoffmanPositiveMatrix G *ᵥ x) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      hoffmanPositiveMatrix_transpose]
  have hz : x ⬝ᵥ ((hoffmanPositiveMatrix G * hoffmanPositiveMatrix G) *ᵥ x) = 0 := by
    rw [hoffmanPositiveMatrix_square G h, Matrix.smul_mulVec, dotProduct_smul, hx]
    simp
  rw [hn] at hz
  change ∑ u, (hoffmanPositiveMatrix G *ᵥ x) u * (hoffmanPositiveMatrix G *ᵥ x) u = 0 at hz
  ext u
  exact (Finset.sum_mul_self_eq_zero_iff Finset.univ _).mp hz u (Finset.mem_univ u)

theorem hoffmanPositiveMatrix_mulVec (x : V → ℚ) (u : V) :
    (hoffmanPositiveMatrix G *ᵥ x) u =
      (G.adjMatrix ℚ *ᵥ x) u + 4 * x u - (2 / 11 : ℚ) * ∑ v, x v := by
  simp only [hoffmanPositiveMatrix, Matrix.sub_mulVec, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  simp only [Matrix.mulVec, dotProduct, allOnes, one_mul]

theorem hoffman_coclique_nexus (h : G.IsSRGWith 99 14 1 2)
    {H : Finset V} (hH : G.IsIndepSet (H : Set V)) (hc : H.card = 22) :
    G.adjMatrix ℚ *ᵥ cocliqueIndicator H = fun u => 4 * (1 - cocliqueIndicator H u) := by
  have hd : cocliqueIndicator H ⬝ᵥ (hoffmanPositiveMatrix G *ᵥ cocliqueIndicator H) = 0 := by
    rw [coclique_positive_dot G hH, hc]
    norm_num
  have hz := hoffmanPositiveMatrix_zero_of_dot_zero G h (cocliqueIndicator H) hd
  ext u
  have he := congrFun hz u
  rw [hoffmanPositiveMatrix_mulVec, cocliqueIndicator_sum, hc] at he
  norm_num only [Nat.cast_ofNat, Pi.zero_apply] at he
  linarith

theorem cocliqueIndicator_adjacency_count (H : Finset V) (u : V) :
    (G.adjMatrix ℚ *ᵥ cocliqueIndicator H) u = ((H.filter (G.Adj u)).card : ℚ) := by
  simp [Matrix.mulVec, dotProduct, cocliqueIndicator, SimpleGraph.adjMatrix_apply,
    Finset.sum_filter, mul_ite]

theorem hoffman_coclique_neighbor_count (h : G.IsSRGWith 99 14 1 2)
    {H : Finset V} (hH : G.IsIndepSet (H : Set V)) (hc : H.card = 22)
    {u : V} (hu : u ∉ H) : (H.filter (G.Adj u)).card = 4 := by
  have he := congrFun (hoffman_coclique_nexus G h hH hc) u
  rw [cocliqueIndicator_adjacency_count] at he
  simp only [cocliqueIndicator, if_neg hu] at he
  norm_num at he
  exact_mod_cast he

def hoffmanCocliqueCode (H : Finset V) : V → ℚ :=
  (1 / 7 : ℚ) • coefficientCode G (cocliqueCoefficients H)

theorem coefficientCode_coclique (H : Finset V) :
    coefficientCode G (cocliqueCoefficients H) =
      (1 / 3 : ℚ) • (vertexGram G *ᵥ cocliqueIndicator H) := by
  simp only [coefficientCode, LinearMap.coe_mk, AddHom.coe_mk,
    cocliqueCoefficients, Int.cast_ite, Int.cast_one, Int.cast_zero, cocliqueIndicator]
  rfl

theorem hoffmanCocliqueCode_mem_ambient (H : Finset V) :
    hoffmanCocliqueCode G H ∈ rationalAmbient G :=
  (rationalAmbient G).smul_mem _ (coefficientCode_mem_ambient G (cocliqueCoefficients H))

theorem hoffmanCocliqueCode_apply (h : G.IsSRGWith 99 14 1 2)
    {H : Finset V} (hH : G.IsIndepSet (H : Set V)) (hc : H.card = 22) (u : V) :
    hoffmanCocliqueCode G H u = 3 * cocliqueIndicator H u - 2 / 3 := by
  have hj : (allOnes : Matrix V V ℚ) *ᵥ cocliqueIndicator H = fun _ => (22 : ℚ) := by
    ext v
    simpa only [Matrix.mulVec, dotProduct, allOnes, one_mul, hc] using cocliqueIndicator_sum H
  rw [hoffmanCocliqueCode, coefficientCode_coclique, vertexGram_eq, Matrix.add_mulVec,
    Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    hoffman_coclique_nexus G h hH hc, hj]
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem hoffmanCocliqueCode_pair_y_vertex (h : G.IsSRGWith 99 14 1 2)
    {H : Finset V} (hH : G.IsIndepSet (H : Set V)) (hc : H.card = 22) (u : V) :
    codePair (hoffmanCocliqueCode G H) ((1 / 3 : ℚ) • vertexCode G u) =
      cocliqueIndicator H u - 2 / 9 := by
  rw [codePair_smul_right, codePair_vertexCode G h (hoffmanCocliqueCode_mem_ambient G H),
    hoffmanCocliqueCode_apply G h hH hc]
  ring

theorem cocliqueIndicator_intersection (H K : Finset V) :
    ∑ u, cocliqueIndicator H u * cocliqueIndicator K u = ((H ∩ K).card : ℚ) := by
  simp [cocliqueIndicator, mul_ite, Finset.inter_comm]

theorem hoffmanCocliqueCode_pair (h : G.IsSRGWith 99 14 1 2)
    {H K : Finset V} (hH : G.IsIndepSet (H : Set V)) (hc : H.card = 22)
    (hK : G.IsIndepSet (K : Set V)) (kc : K.card = 22) :
    codePair (hoffmanCocliqueCode G H) (hoffmanCocliqueCode G K) =
      (9 * ((H ∩ K).card : ℚ) - 44) / 63 := by
  change codePair (hoffmanCocliqueCode G H)
    ((1 / 7 : ℚ) • coefficientCode G (cocliqueCoefficients K)) = _
  rw [codePair_smul_right,
    codePair_coefficientCode G h (hoffmanCocliqueCode_mem_ambient G H)]
  have he : ∑ u, hoffmanCocliqueCode G H u * (cocliqueCoefficients K u : ℚ) =
      3 * ((H ∩ K).card : ℚ) - (2 / 3 : ℚ) * K.card := by
    simp only [hoffmanCocliqueCode_apply G h hH hc, cocliqueCoefficients,
      Int.cast_ite, Int.cast_one, Int.cast_zero]
    change (∑ u, (3 * cocliqueIndicator H u - 2 / 3) * cocliqueIndicator K u) = _
    simp only [sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum,
      cocliqueIndicator_intersection, cocliqueIndicator_sum]
  rw [he, kc]
  norm_num
  ring

theorem hoffmanCocliqueCode_norm (h : G.IsSRGWith 99 14 1 2)
    {H : Finset V} (hH : G.IsIndepSet (H : Set V)) (hc : H.card = 22) :
    codePair (hoffmanCocliqueCode G H) (hoffmanCocliqueCode G H) = 22 / 9 := by
  rw [hoffmanCocliqueCode_pair G h hH hc hH hc, Finset.inter_self, hc]
  norm_num

theorem coclique_sum_y_norm (h : G.IsSRGWith 99 14 1 2)
    {H : Finset V} (hH : G.IsIndepSet (H : Set V)) (hc : H.card = 22) :
    codePair (coefficientCode G (cocliqueCoefficients H))
      (coefficientCode G (cocliqueCoefficients H)) = 1078 / 9 := by
  have hn := hoffmanCocliqueCode_norm G h hH hc
  rw [hoffmanCocliqueCode, codePair_smul_left, codePair_smul_right] at hn
  linarith

#print axioms hoffman_coclique_card_le
#print axioms hoffman_coclique_nexus
#print axioms hoffman_coclique_neighbor_count
#print axioms hoffmanCocliqueCode_pair
#print axioms hoffmanCocliqueCode_norm

end Conway99
