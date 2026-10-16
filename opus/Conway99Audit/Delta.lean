import Conway99Audit.Quad

/-!
# Part A: `N₂ + 3 N₃ = 4158`, `δ ∈ 3ℤ` and `δ ≥ 165`

Minimal proof, §§2.1, 2.3, 3.  Notation: `K J = Σ_{L,M} S_JL S_JM S_LM²` (= `‖U_{x_J}‖²_HS`).
* Lemma 2.1: `4 ∣ K J`;
* §3.2–3.3: the vectors `c = c(u,J)` (coordinates of `M_u x_J` in `Λ`) satisfy
  `(P c)_u = P_{uJ} ≢ 0 (mod 3)`, hence `Q c ≥ 4`, and `Σ_u Q c(u,J) = 7 K J`;
  so `K J ≥ 60`;
* §2.1/§2.3: `Σ_J K J = 84 δ` with `δ = N₂ - 693`.
-/

open Finset SimpleGraph Matrix

namespace Conway99

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
def K (J : Tr G) : ℤ := ∑ L, ∑ M, S G J L * S G J M * S G L M ^ 2

lemma even_mul_pred (n : ℤ) : Even (n * (n - 1)) := by
  rcases Int.even_or_odd n with h | h
  · exact h.mul_right _
  · exact (h.sub_odd odd_one).mul_left _

section SRG

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

/-- Lemma 2.1: `K J ≡ 0 (mod 4)`. -/
lemma K_mod4 (J : Tr G) : 4 ∣ K G J := by
  -- first part: Σ S_JL S_JM S_LM = (S³)_JJ = 1764
  have hT1 : ∑ L, ∑ M, S G J L * S G J M * S G L M = 1764 := by
    have : ∀ L, ∑ M, S G J L * S G J M * S G L M = S G J L * (21 * S G L J) := by
      intro L
      rw [← S_sq_apply hG L J, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro M _
      rw [S_symm_apply hG J M]; ring
    rw [Finset.sum_congr rfl (fun L _ => this L)]
    have h2 : ∑ L, S G J L * (21 * S G L J) = 21 * (21 * S G J J) := by
      rw [← S_sq_apply hG J J, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro L _; ring
    rw [h2, S_diag hG]; norm_num
  -- second part: f = 2 g with g symmetric, diagonal of g = 6 S_JL²
  set g : Tr G → Tr G → ℤ := fun L M => S G J L * S G J M * (S G L M * (S G L M - 1) / 2) with hg
  have hf2 : ∀ L M, S G J L * S G J M * (S G L M ^ 2 - S G L M) = 2 * g L M := by
    intro L M
    simp only [hg]
    obtain ⟨w, hw⟩ := even_mul_pred (S G L M)
    have hdiv : S G L M * (S G L M - 1) / 2 = w := by rw [hw]; omega
    have hsq : S G L M ^ 2 - S G L M = w + w := by rw [← hw]; ring
    rw [hdiv, hsq]; ring
  have hgsym : ∀ L M, g L M = g M L := by
    intro L M; simp only [hg]; rw [S_symm_apply hG L M]; ring
  have hgdiag : ∀ L, g L L = 2 * (3 * S G J L ^ 2) := by
    intro L; simp only [hg]; rw [S_diag hG]; norm_num; ring
  have hev := sum_symm_offdiag_even g hgsym
  have hsumg : Even (∑ L, ∑ M, g L M) := by
    have : (∑ L, ∑ M, g L M) = ((∑ L, ∑ M, g L M) - ∑ L, g L L) + 2 * ∑ L, 3 * S G J L ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_congr rfl (fun L _ => (hgdiag L).symm)]; ring
    rw [this]; exact hev.add (even_two_mul _)
  have hK : K G J = 1764 + 2 * ∑ L, ∑ M, g L M := by
    have : K G J = ∑ L, ∑ M, S G J L * S G J M * S G L M
        + ∑ L, ∑ M, S G J L * S G J M * (S G L M ^ 2 - S G L M) := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro L _
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro M _; ring
    rw [this, hT1]
    congr 1
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro L _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro M _
    exact hf2 L M
  obtain ⟨k, hk⟩ := hsumg
  rw [hK, hk]
  exact ⟨441 + k, by ring⟩

/-! ### The vectors `c(u,J)` = coordinates of `M_u x_J` -/

variable (G) in
def cvec (u : V) (J : Tr G) : Tr G → ℤ := fun L =>
  -7 * (if L = J then 1 else 0) - (3 * (if u ∈ L.1 then 1 else 0) - (nb G u L.1 : ℤ)) * S G L J

lemma P_sq (u : V) (L : Tr G) :
    P G u L ^ 2 = 1 + 9 * (if u ∈ L.1 then 1 else 0) + 3 * (nb G u L.1 : ℤ) := by
  rcases n_le_one_or_two hG L.2 u with ⟨hu, hn⟩ | ⟨hu, hn⟩
  · simp only [P, Matrix.of_apply, nb, hu, if_true, hn]; norm_num
  · have hn' : nb G u L.1 = 0 ∨ nb G u L.1 = 1 := by unfold nb; omega
    rcases hn' with h0 | h1
    · simp only [P, Matrix.of_apply, hu, if_false, h0]; norm_num
    · simp only [P, Matrix.of_apply, hu, if_false, h1]; norm_num

lemma sum_nb_S (u : V) (J : Tr G) : ∑ L, (nb G u L.1 : ℤ) * S G L J = -4 * P G u J := by
  have : ∀ L : Tr G, (nb G u L.1 : ℤ) = ∑ v, A G u v * B G v L := by
    intro L; rw [← sum_A_indicator]; rfl
  simp_rw [this, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [← AP_apply hG u J]
  apply Finset.sum_congr rfl; intro v _
  rw [← BS_apply hG v J, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro L _; ring

lemma sum_r_S (u : V) (J : Tr G) :
    ∑ L, (if u ∈ L.1 then (1 : ℤ) else 0) * S G L J = P G u J := by
  rw [← BS_apply hG u J]; rfl

lemma sum_Psq_S (u : V) (J : Tr G) : ∑ L, P G u L ^ 2 * S G L J = -3 * P G u J := by
  simp_rw [P_sq hG, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [one_mul, sum_S_col hG, sum_r_S hG, sum_nb_S hG]; ring

lemma Pc (u : V) (J : Tr G) : (P G *ᵥ cvec G u J) u = P G u J := by
  have h3 : 3 * (P G *ᵥ cvec G u J) u = 3 * P G u J := by
    simp only [Matrix.mulVec, dotProduct, cvec, Finset.mul_sum]
    have : ∀ L, 3 * (P G u L * (-7 * (if L = J then 1 else 0)
        - (3 * (if u ∈ L.1 then 1 else 0) - (nb G u L.1 : ℤ)) * S G L J))
        = -21 * P G u L * (if L = J then 1 else 0)
          - (P G u L ^ 2 * S G L J - P G u L * S G L J) := by
      intro L; rw [P_eq hG u L]; ring
    rw [Finset.sum_congr rfl (fun L _ => this L), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      sum_Psq_S hG, PS_apply hG]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ, if_true]
    ring
  linarith

lemma Pc_mod3 (u : V) (J : Tr G) : (P G *ᵥ cvec G u J) u % 3 = 1 := by
  rw [Pc hG, P_eq hG, Int.add_mul_emod_self_left]; norm_num

/-- `Q (c(u,J)) ≥ 4`: norm of `M_u x_J` in the even lattice `Λ`. -/
lemma Qc_ge4 (u : V) (J : Tr G) : 4 ≤ Q G (cvec G u J) := by
  set c := cvec G u J
  have hnn := Q_nonneg hG c
  have hev := Q_even hG c
  have h0 : Q G c ≠ 0 := by
    intro h
    have hS := S_mulVec_eq_zero hG c h
    have : (P G *ᵥ c) u = 0 := by
      rw [← B_mul_S hG, ← Matrix.mulVec_mulVec, hS, Matrix.mulVec_zero]; rfl
    have := Pc_mod3 hG u J
    rw [show (P G *ᵥ cvec G u J) u = (P G *ᵥ c) u from rfl, ‹(P G *ᵥ c) u = 0›] at this
    norm_num at this
  have h2 : Q G c ≠ 2 := by
    intro h
    have hd := lemma31 hG c h u
    have h3 : (P G *ᵥ c) u % 3 = 1 := Pc_mod3 hG u J
    omega
  obtain ⟨k, hk⟩ := hev
  omega

/-- `9 Q(c) = Q(d)` with `d_L = P_uL S_LJ`. -/
lemma nine_Qc (u : V) (J : Tr G) :
    9 * Q G (cvec G u J) = Q G (fun L => P G u L * S G L J) := by
  set c := cvec G u J
  set d : Tr G → ℤ := fun L => P G u L * S G L J
  have hS : S G *ᵥ ((3 : ℤ) • c) = -(S G *ᵥ d) := by
    funext M
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, c, d, cvec]
    have : ∀ L, S G M L * (3 * (-7 * (if L = J then 1 else 0)
        - (3 * (if u ∈ L.1 then 1 else 0) - (nb G u L.1 : ℤ)) * S G L J))
        = -21 * (S G M L * (if L = J then 1 else 0)) + S G M L * S G L J
          - S G M L * (P G u L * S G L J) := by
      intro L; rw [P_eq hG u L]; ring
    rw [Finset.sum_congr rfl (fun L _ => this L), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, S_sq_apply hG]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ, if_true]
    ring
  have h1 := Q_mul_21 hG ((3 : ℤ) • c)
  have h2 := Q_mul_21 hG d
  rw [hS, neg_dotProduct, dotProduct_neg, neg_neg, ← h2] at h1
  have h3 : Q G ((3 : ℤ) • c) = 9 * Q G c := by
    simp only [Q, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro L _; apply Finset.sum_congr rfl; intro M _; ring
  linarith

lemma sum_Qd (J : Tr G) : ∑ u, Q G (fun L => P G u L * S G L J) = 63 * K G J := by
  simp only [Q, K]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro L _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro M _
  have : ∀ u, P G u L * S G L J * S G L M * (P G u M * S G M J)
      = (P G u L * P G u M) * (S G L J * S G L M * S G M J) := by intro u; ring
  rw [Finset.sum_congr rfl (fun u _ => this u), ← Finset.sum_mul, PtP_apply hG,
    S_symm_apply hG L J, S_symm_apply hG M J]
  ring

lemma sum_Qc (J : Tr G) : ∑ u, Q G (cvec G u J) = 7 * K G J := by
  have h := sum_Qd hG J
  rw [← Finset.sum_congr rfl (fun u _ => nine_Qc hG u J), ← Finset.mul_sum] at h
  linarith

/-- `K J ≥ 60` for every triangle `J`. -/
lemma K_ge60 (J : Tr G) : 60 ≤ K G J := by
  have h := sum_Qc hG J
  have hle : ∑ u : V, (4 : ℤ) ≤ ∑ u, Q G (cvec G u J) :=
    Finset.sum_le_sum (fun u _ => Qc_ge4 hG u J)
  rw [sum_const, card_univ, card_V hG, h] at hle
  norm_num at hle
  have h4 := K_mod4 hG J
  obtain ⟨k, hk⟩ := h4
  omega

end SRG

end Conway99
