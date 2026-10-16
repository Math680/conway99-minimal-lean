import Conway99Audit.Count

/-!
# Part B, step 1: integer eigenvectors of eigenvalue `-4` (minimal proof, Lemma 5.1)

`IsM4 b` means `A b = -4 b`.  We prove: a nonzero integer such `b` has `b·b ≥ 14`; at equality
`b ∈ {0,±1}^V`, both sign classes have seven elements, are cocliques, every vertex of a sign
class has exactly four neighbours in the other class, and two distinct vertices of the same
class have all their common neighbours in the other class.
-/

open Finset SimpleGraph Matrix

namespace Conway99

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
def IsM4 (b : V → ℤ) : Prop := A G *ᵥ b = (-4 : ℤ) • b

def pos (b : V → ℤ) : Finset V := univ.filter (fun u => b u = 1)
def neg (b : V → ℤ) : Finset V := univ.filter (fun u => b u = -1)

lemma mem_pos {b : V → ℤ} {u : V} : u ∈ pos b ↔ b u = 1 := by simp [pos]
lemma mem_neg {b : V → ℤ} {u : V} : u ∈ neg b ↔ b u = -1 := by simp [neg]

lemma Av_apply (b : V → ℤ) (u : V) : (A G *ᵥ b) u = ∑ v ∈ G.neighborFinset u, b v := by
  rw [A, adjMatrix_mulVec_apply]

lemma IsM4.apply {b : V → ℤ} (hb : IsM4 G b) (u : V) :
    ∑ v ∈ G.neighborFinset u, b v = -4 * b u := by
  have := congrFun hb u
  rw [Av_apply] at this
  simpa using this

lemma IsM4.neg {b : V → ℤ} (hb : IsM4 G b) : IsM4 G (-b) := by
  unfold IsM4 at *; rw [Matrix.mulVec_neg, hb]; simp

/-- `G0` is positive semidefinite (from `G0² = 63 G0`). -/
lemma G0_psd (hG : G.IsSRGWith 99 14 1 2) (x : V → ℤ) : 0 ≤ x ⬝ᵥ (G0 G *ᵥ x) := by
  have h : (G0 G *ᵥ x) ⬝ᵥ (G0 G *ᵥ x) = 63 * (x ⬝ᵥ (G0 G *ᵥ x)) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, G0_symm, Matrix.mulVec_mulVec,
      hG0G0 hG, Matrix.smul_mulVec, smul_dotProduct, dotProduct_comm, smul_eq_mul]
  have : 0 ≤ (G0 G *ᵥ x) ⬝ᵥ (G0 G *ᵥ x) := by
    simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  linarith

lemma G0_quad (x : V → ℤ) :
    x ⬝ᵥ (G0 G *ᵥ x) = 27 * (x ⬝ᵥ x) - 9 * (x ⬝ᵥ (A G *ᵥ x)) + (∑ u, x u) ^ 2 := by
  have hJ : (J : Matrix V V ℤ) *ᵥ x = fun _ => ∑ u, x u := by
    funext v; simp [Matrix.mulVec, dotProduct, J_apply]
  simp only [G0, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hJ,
    dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have : x ⬝ᵥ (fun _ => ∑ u, x u) = (∑ u, x u) ^ 2 := by
    simp only [dotProduct, ← Finset.sum_mul]; ring
  rw [this]

lemma abs_le_mul_self (x : ℤ) : |x| ≤ x * x := by
  rcases le_or_gt x 0 with h | h
  · rw [abs_of_nonpos h]; nlinarith
  · rw [abs_of_pos h]; nlinarith

section SRG

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

lemma colsum_A (v : V) : ∑ u, A G u v = 14 := by
  have : ∀ u, A G u v = if G.Adj v u then 1 else 0 := by
    intro u; rw [A_apply]; simp [adj_comm]
  simp_rw [this]
  rw [Finset.sum_boole, ← neighborFinset_eq_filter, degree_eq hG]
  rfl

lemma IsM4.sum_zero {b : V → ℤ} (hb : IsM4 G b) : ∑ u, b u = 0 := by
  have h1 : ∑ u, ∑ v ∈ G.neighborFinset u, b v = 14 * ∑ u, b u := by
    have : ∀ u, ∑ v ∈ G.neighborFinset u, b v = ∑ v, A G u v * b v := by
      intro u; rw [← Av_apply]; rfl
    simp_rw [this]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro v _
    rw [← Finset.sum_mul, colsum_A hG]
  have h2 : ∑ u, ∑ v ∈ G.neighborFinset u, b v = -4 * ∑ u, b u := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun u _ => hb.apply u)
  linarith

/-- The sum of `b` over non-neighbours of `u` (other than `u`) is `3 b u`. -/
lemma IsM4.far_sum {b : V → ℤ} (hb : IsM4 G b) (u : V) :
    ∑ v ∈ (univ.erase u).filter (fun v => ¬ G.Adj u v), b v = 3 * b u := by
  have hs := hb.sum_zero hG
  have hsplit : ∑ v, b v = b u + (∑ v ∈ G.neighborFinset u, b v
      + ∑ v ∈ (univ.erase u).filter (fun v => ¬ G.Adj u v), b v) := by
    rw [← Finset.add_sum_erase _ _ (mem_univ u)]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not (univ.erase u) (fun v => G.Adj u v)]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext v; simp only [mem_filter, mem_erase, mem_univ, and_true, mem_neighborFinset]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨(G.ne_of_adj h).symm, h⟩
  rw [hb.apply u] at hsplit
  linarith

/-- Lemma A: if `b u0` is a maximum of `b` and `≥ 1`, the positive mass is at least `4 b u0`. -/
lemma IsM4.posmass {b : V → ℤ} (hb : IsM4 G b) (u0 : V) (hmax : ∀ v, b v ≤ b u0)
    (h1 : 1 ≤ b u0) : 4 * b u0 ≤ ∑ v, max (b v) 0 := by
  have hfar := hb.far_sum hG u0
  have hle : ∑ v ∈ (univ.erase u0).filter (fun v => ¬ G.Adj u0 v), b v
      ≤ ∑ v ∈ univ.erase u0, max (b v) 0 := by
    calc _ ≤ ∑ v ∈ (univ.erase u0).filter (fun v => ¬ G.Adj u0 v), max (b v) 0 :=
          Finset.sum_le_sum (fun v _ => le_max_left _ _)
      _ ≤ ∑ v ∈ univ.erase u0, max (b v) 0 :=
          Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun v _ _ => le_max_right _ _)
  have hsplit := Finset.add_sum_erase (univ : Finset V) (fun v => max (b v) 0) (mem_univ u0)
  have hm : max (b u0) 0 = b u0 := max_eq_left (by linarith)
  rw [hm] at hsplit
  linarith

lemma IsM4.norm_ge {b : V → ℤ} (hb : IsM4 G b) (u0 : V) (hmax : ∀ v, b v ≤ b u0)
    (h1 : 1 ≤ b u0) : 8 * b u0 + (b u0 * b u0 - b u0) ≤ b ⬝ᵥ b := by
  have hpm := hb.posmass hG u0 hmax h1
  have hs := hb.sum_zero hG
  -- Σ |b| = 2 Σ max(b,0)
  have habs : ∑ v, |b v| = 2 * ∑ v, max (b v) 0 := by
    have e1 : ∀ v, |b v| = 2 * max (b v) 0 - b v := by
      intro v; rcases le_or_gt (b v) 0 with h | h
      · rw [abs_of_nonpos h, max_eq_right h]; ring
      · rw [abs_of_pos h, max_eq_left h.le]; ring
    simp_rw [e1]
    rw [Finset.sum_sub_distrib, hs, ← Finset.mul_sum]; ring
  have hterm : ∀ v, 0 ≤ b v * b v - |b v| := fun v => by linarith [abs_le_mul_self (b v)]
  have hsingle : b u0 * b u0 - |b u0| ≤ ∑ v, (b v * b v - |b v|) :=
    Finset.single_le_sum (f := fun v => b v * b v - |b v|) (fun v _ => hterm v) (mem_univ u0)
  have hu0 : |b u0| = b u0 := abs_of_pos (by linarith)
  rw [hu0, Finset.sum_sub_distrib] at hsingle
  have : b ⬝ᵥ b = ∑ v, b v * b v := rfl
  linarith

/-- All entries of a short `-4` eigenvector are in `{-1,0,1}`. -/
lemma IsM4.entries {b : V → ℤ} (hb : IsM4 G b) (h14 : b ⬝ᵥ b ≤ 14) (v : V) : |b v| ≤ 1 := by
  by_contra hv
  push_neg at hv
  obtain ⟨u0, -, hu0⟩ := Finset.exists_max_image univ b ⟨v, mem_univ v⟩
  obtain ⟨u1, -, hu1⟩ := Finset.exists_max_image univ (-b) ⟨v, mem_univ v⟩
  rcases le_or_gt 2 (b u0) with h2 | h2
  · have := hb.norm_ge hG u0 (fun w => hu0 w (mem_univ w)) (by linarith)
    nlinarith
  · -- then b v ≤ 1, so b v ≤ -2 and (-b) u1 ≥ 2
    have hbv : b v ≤ -2 := by
      have := hu0 v (mem_univ v); rcases abs_cases (b v) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    have hu1' : 2 ≤ (-b) u1 := by
      have := hu1 v (mem_univ v); simp only [Pi.neg_apply] at this ⊢; linarith
    have := (hb.neg).norm_ge hG u1 (fun w => hu1 w (mem_univ w)) (by linarith)
    have hn : (-b) ⬝ᵥ (-b) = b ⬝ᵥ b := by simp
    rw [hn] at this
    nlinarith

end SRG

end Conway99
