import Conway99Audit.Frame

/-!
# Quadratic form of the triangle frame, parity, and the congruence lemma 3.1

`Q x = Σ_{L,M} x_L S_{LM} x_M` is the norm of `Σ x_L x_L` in the triangle lattice `Λ`.
* `21 Q x = |S x|²` (from `S² = 21 S`), so `Q ≥ 0` and `Q x = 0 → S x = 0`;
* `Q x` is even (diagonal of `S` is `4`);
* Lemma 3.1 of the minimal proof: `Q x = 2 → 3 ∣ (P x)_u` for all `u`.
-/

open Finset SimpleGraph Matrix

namespace Conway99

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Parity of a symmetric double sum: off-diagonal terms pair up. -/
lemma sum_symm_offdiag_even {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ι → ℤ)
    (hf : ∀ i j, f i j = f j i) : Even ((∑ i, ∑ j, f i j) - ∑ i, f i i) := by
  have hsplit : (∑ i, ∑ j, f i j) - ∑ i, f i i = ∑ p ∈ (univ : Finset ι).offDiag, f p.1 p.2 := by
    rw [← Finset.sum_product', ← Finset.diag_union_offDiag,
      Finset.sum_union (Finset.disjoint_diag_offDiag univ), Finset.sum_diag]
    ring
  rw [hsplit, even_iff_two_dvd]
  have h0 : ((∑ p ∈ (univ : Finset ι).offDiag, f p.1 p.2 : ℤ) : ZMod 2) = 0 := by
    push_cast
    apply Finset.sum_involution (fun p _ => (p.2, p.1))
    · intro p _
      simp only
      rw [hf p.2 p.1]
      exact CharTwo.add_self_eq_zero _
    · intro p hp _ h
      rw [Finset.mem_offDiag] at hp
      exact hp.2.2 (by simpa using (Prod.ext_iff.1 h).2)
    · intro p hp
      rw [Finset.mem_offDiag] at hp ⊢
      exact ⟨hp.2.1, hp.1, Ne.symm hp.2.2⟩
    · intro p _
      rfl
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 h0

variable (G) in
/-- The quadratic form `xᵀ S x`. -/
def Q (x : Tr G → ℤ) : ℤ := ∑ L, ∑ M, x L * S G L M * x M

lemma Q_eq_dot (x : Tr G → ℤ) : Q G x = x ⬝ᵥ (S G *ᵥ x) := by
  simp only [Q, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

section SRG

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

lemma S_symm_apply (L M : Tr G) : S G L M = S G M L := by
  have h := congrFun (congrFun (S_symm hG) M) L
  simpa [Matrix.transpose_apply] using h

lemma S_diag (L : Tr G) : S G L L = 4 := by
  simp only [S, Matrix.of_apply, inter_self, T_card3 L.2]
  have : eLM G L.1 L.1 = 6 := by
    unfold eLM nb
    rw [Finset.sum_congr rfl (fun u hu => T_card_filter_adj_mem L.2 hu), sum_const, T_card3 L.2]
    rfl
  rw [this]; norm_num

lemma S_sq_apply (M N : Tr G) : ∑ L, S G M L * S G L N = 21 * S G M N := by
  have h := congrFun (congrFun (S_sq hG) M) N
  simpa [Matrix.mul_apply, Matrix.smul_apply] using h

lemma PtP_apply (L M : Tr G) : ∑ u, P G u L * P G u M = 63 * S G L M := by
  have h := congrFun (congrFun (Pt_mul_P hG) L) M
  simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply] using h

lemma BS_apply (u : V) (M : Tr G) : ∑ L, B G u L * S G L M = P G u M := by
  have h := congrFun (congrFun (B_mul_S hG) u) M
  simpa [Matrix.mul_apply] using h

lemma AP_apply (u : V) (L : Tr G) : ∑ v, A G u v * P G v L = -4 * P G u L := by
  have h := congrFun (congrFun (A_mul_P hG) u) L
  simpa [Matrix.mul_apply, Matrix.smul_apply] using h

lemma PS_apply (u : V) (J : Tr G) : ∑ L, P G u L * S G L J = 21 * P G u J := by
  have h := congrFun (congrFun (P_mul_S hG) u) J
  simpa [Matrix.mul_apply, Matrix.smul_apply] using h

lemma nonempty_V : Nonempty V := by
  rw [← Fintype.card_pos_iff, card_V hG]; norm_num

lemma sum_P_col (L : Tr G) : ∑ u, P G u L = 0 := by
  obtain ⟨w⟩ := nonempty_V hG
  have h := congrFun (congrFun (J_mul_P hG) w) L
  simpa [Matrix.mul_apply, J_apply] using h

lemma sum_B_row (u : V) : ∑ L : Tr G, B G u L = 7 := by
  simp only [B_apply]
  rw [Finset.sum_coe_sort (T (G := G)) (fun t => if u ∈ t then (1 : ℤ) else 0)]
  rw [Finset.sum_boole, T_through_vertex hG u]
  rfl

lemma sum_S_col (J : Tr G) : ∑ L, S G L J = 0 := by
  have h3 : ∀ L, 3 * S G L J = ∑ u, B G u L * P G u J := by
    intro L
    have h := congrFun (congrFun (Bt_mul_P (G := G)) L) J
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul] at h
    exact h.symm
  have : 3 * ∑ L, S G L J = 0 := by
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun L _ => h3 L), Finset.sum_comm]
    simp only [← Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun u _ => by rw [sum_B_row hG u])]
    rw [← Finset.mul_sum, sum_P_col hG, mul_zero]
  linarith

lemma Q_mul_21 (x : Tr G → ℤ) : 21 * Q G x = (S G *ᵥ x) ⬝ᵥ (S G *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, S_symm hG, Matrix.mulVec_mulVec,
    S_sq hG, Matrix.smul_mulVec, smul_dotProduct, dotProduct_comm, ← Q_eq_dot, smul_eq_mul]

lemma Q_nonneg (x : Tr G → ℤ) : 0 ≤ Q G x := by
  have h := Q_mul_21 hG x
  have : 0 ≤ (S G *ᵥ x) ⬝ᵥ (S G *ᵥ x) := by
    simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  linarith

lemma S_mulVec_eq_zero (x : Tr G → ℤ) (h0 : Q G x = 0) : S G *ᵥ x = 0 := by
  have h := Q_mul_21 hG x
  rw [h0, mul_zero] at h
  have hsum : ∑ i, (S G *ᵥ x) i * (S G *ᵥ x) i = 0 := by
    simpa [dotProduct] using h.symm
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg ((S G *ᵥ x) j))).1
    hsum i (mem_univ i)
  simpa using this

lemma Q_even (x : Tr G → ℤ) : Even (Q G x) := by
  have h := sum_symm_offdiag_even (fun L M => x L * S G L M * x M)
    (fun L M => by rw [S_symm_apply hG L M]; ring)
  have hdiag : ∑ L, x L * S G L L * x L = 2 * ∑ L, 2 * x L * x L := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro L _; rw [S_diag hG]; ring
  have : Q G x = ((∑ L, ∑ M, x L * S G L M * x M) - ∑ L, x L * S G L L * x L)
        + 2 * ∑ L, 2 * x L * x L := by rw [← hdiag, Q]; ring
  rw [this]
  exact h.add (even_two_mul _)

/-! ### Lemma 3.1 in coordinates -/

lemma P_eq (u : V) (L : Tr G) :
    P G u L = 1 + 3 * (3 * (if u ∈ L.1 then 1 else 0) - (nb G u L.1 : ℤ)) := by
  simp only [P, Matrix.of_apply]; ring

lemma Pvec_sum (x : Tr G → ℤ) : ∑ u, (P G *ᵥ x) u = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro L _
  rw [← Finset.sum_mul, sum_P_col hG, zero_mul]

lemma Pvec_sq (x : Tr G → ℤ) : (P G *ᵥ x) ⬝ᵥ (P G *ᵥ x) = 63 * Q G x := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, Pt_mul_P hG,
    Matrix.smul_mulVec, smul_dotProduct, dotProduct_comm, ← Q_eq_dot, smul_eq_mul]

lemma Pvec_mod3 (x : Tr G → ℤ) (u : V) : (P G *ᵥ x) u % 3 = (∑ L, x L) % 3 := by
  have : (P G *ᵥ x) u = ∑ L, x L
      + 3 * ∑ L, (3 * (if u ∈ L.1 then 1 else 0) - (nb G u L.1 : ℤ)) * x L := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro L _; rw [P_eq hG]; ring
  rw [this, Int.add_mul_emod_self_left]

/-- Lemma 3.1 of the minimal proof, in coordinates. -/
lemma lemma31 (x : Tr G → ℤ) (h2 : Q G x = 2) (u : V) : 3 ∣ (P G *ᵥ x) u := by
  set z := P G *ᵥ x with hz
  have hsum : ∑ v, z v = 0 := Pvec_sum hG x
  have hsq : ∑ v, z v * z v = 126 := by
    have := Pvec_sq hG x; rw [h2] at this; simpa [dotProduct, hz] using this
  have hres : ∀ v, z v % 3 = (∑ L, x L) % 3 := fun v => Pvec_mod3 hG x v
  have hcard := card_V hG
  by_contra hnd
  have hr : (∑ L, x L) % 3 ≠ 0 := by
    rw [← hres u]; intro h0; exact hnd (Int.dvd_of_emod_eq_zero h0)
  have hr' : (∑ L, x L) % 3 = 1 ∨ (∑ L, x L) % 3 = 2 := by omega
  rcases hr' with h1 | h1
  · have hb : ∀ v, 2 ≤ z v * z v + z v := by
      intro v
      have hv := hres v; rw [h1] at hv
      obtain ⟨k, hk⟩ : ∃ k, z v = 3 * k + 1 := ⟨z v / 3, by omega⟩
      have hkk : 0 ≤ k * (k + 1) := by
        rcases le_or_gt 0 k with h | h
        · positivity
        · nlinarith
      rw [hk]; nlinarith
    have : ∑ v : V, (2 : ℤ) ≤ ∑ v, (z v * z v + z v) := Finset.sum_le_sum (fun v _ => hb v)
    rw [Finset.sum_add_distrib, hsq, hsum, sum_const, card_univ, hcard] at this
    norm_num at this
  · have hb : ∀ v, 2 ≤ z v * z v - z v := by
      intro v
      have hv := hres v; rw [h1] at hv
      obtain ⟨k, hk⟩ : ∃ k, z v = 3 * k + 2 := ⟨z v / 3, by omega⟩
      have hkk : 0 ≤ k * (k + 1) := by
        rcases le_or_gt 0 k with h | h
        · positivity
        · nlinarith
      rw [hk]; nlinarith
    have : ∑ v : V, (2 : ℤ) ≤ ∑ v, (z v * z v - z v) := Finset.sum_le_sum (fun v _ => hb v)
    rw [Finset.sum_sub_distrib, hsq, hsum, sum_const, card_univ, hcard] at this
    norm_num at this

end SRG

end Conway99
