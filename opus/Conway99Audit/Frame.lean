import Conway99Audit.Basic

/-!
# Conway 99-graph audit — the frames (minimal proof §2.2), in integer coordinates

Everything is expressed with integer matrices indexed by vertices `V` and by the
subtype `Tr` of triangles:
* `A` adjacency, `J` all-ones, `G0 = 27 I - 9 A + J` (the Gram `63 E` of the `w_u`);
* `B` vertex–triangle incidence;
* `P u L = 9 [u ∈ L] - 3 |N(u) ∩ L| + 1` (= `w_u · x_L`), with `3 P = G0 B`;
* `S L M = 3 |L ∩ M| - e(L,M) + 1` (= `x_L · x_M`), with `3 S = Bᵀ P`, `9 S = Bᵀ G0 B`.
-/

open Finset SimpleGraph Matrix

namespace Conway99

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The type of triangles. -/
abbrev Tr (G : SimpleGraph V) [DecidableRel G.Adj] := {t : Finset V // t ∈ T (G := G)}

variable (G)

def A : Matrix V V ℤ := G.adjMatrix ℤ
def J : Matrix V V ℤ := Matrix.of fun _ _ => 1
def G0 : Matrix V V ℤ := (27 : ℤ) • (1 : Matrix V V ℤ) - (9 : ℤ) • A G + J
def B : Matrix V (Tr G) ℤ := Matrix.of fun u t => if u ∈ t.1 then 1 else 0

/-- number of neighbours of `u` in a finset `t`. -/
def nb (u : V) (t : Finset V) : ℕ := (t.filter (G.Adj u)).card

/-- ordered adjacent pairs between `L` and `M`. -/
def eLM (L M : Finset V) : ℕ := ∑ u ∈ L, nb G u M

def P : Matrix V (Tr G) ℤ := Matrix.of fun u t =>
  9 * (if u ∈ t.1 then 1 else 0) - 3 * (nb G u t.1 : ℤ) + 1

def S : Matrix (Tr G) (Tr G) ℤ := Matrix.of fun L M =>
  3 * ((L.1 ∩ M.1).card : ℤ) - (eLM G L.1 M.1 : ℤ) + 1

variable {G}

/-! ### Entry formulas -/

lemma A_apply (u v : V) : A G u v = if G.Adj u v then 1 else 0 := by
  simp [A, adjMatrix_apply]

lemma sum_A_indicator (u : V) (t : Finset V) :
    ∑ v, A G u v * (if v ∈ t then 1 else 0) = (nb G u t : ℤ) := by
  have h : ∀ v, A G u v * (if v ∈ t then (1 : ℤ) else 0)
      = if (v ∈ t ∧ G.Adj u v) then 1 else 0 := by
    intro v; rw [A_apply]
    by_cases h1 : G.Adj u v <;> by_cases h2 : v ∈ t <;> simp [h1, h2]
  rw [Finset.sum_congr rfl (fun v _ => h v), Finset.sum_boole, nb]
  norm_cast
  congr 1
  ext v; simp

lemma G0_mul_B : G0 G * B G = (3 : ℤ) • P G := by
  ext u t
  simp only [G0, B, P, Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.of_apply, J, smul_eq_mul]
  have h1 : ∑ v, ((27 : ℤ) * (if u = v then 1 else 0) - 9 * A G u v + 1) *
      (if v ∈ t.1 then 1 else 0)
      = 27 * (if u ∈ t.1 then 1 else 0) - 9 * (nb G u t.1 : ℤ) + (t.1.card : ℤ) := by
    simp only [sub_mul, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_A_indicator]
    congr 1
    · congr 1
      simp
    · simp
  rw [h1, T_card3 t.2]
  push_cast
  ring

lemma B_apply (u : V) (t : Tr G) : B G u t = if u ∈ t.1 then 1 else 0 := rfl

lemma J_apply (u v : V) : (J : Matrix V V ℤ) u v = 1 := rfl

lemma A_symm : (A G)ᵀ = A G := by simp [A]

lemma J_symm : (J : Matrix V V ℤ)ᵀ = J := by ext; simp [J]

lemma G0_symm : (G0 G)ᵀ = G0 G := by
  ext u v
  simp only [G0, Matrix.transpose_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, A_apply, J_apply, smul_eq_mul]
  by_cases h : u = v
  · subst h; simp
  · simp [h, Ne.symm h, adj_comm]

section SRG

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

lemma AA_apply (u v : V) : (A G * A G) u v = ((cn G u v).card : ℤ) := by
  rw [A, adjMatrix_mul_apply]
  simp only [adjMatrix_apply]
  rw [Finset.sum_boole]
  norm_cast
  congr 1
  ext w
  simp [cn, mem_neighborFinset, adj_comm]

lemma hA2 : A G * A G = (12 : ℤ) • (1 : Matrix V V ℤ) - A G + (2 : ℤ) • J := by
  ext u v
  rw [AA_apply hG]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, J_apply,
    A_apply, smul_eq_mul]
  by_cases huv : u = v
  · subst huv
    have : cn G u u = G.neighborFinset u := by ext w; simp [cn]
    rw [this, degree_eq hG]; simp
  · by_cases ha : G.Adj u v
    · rw [cn_adj hG ha]; simp [huv, ha]
    · rw [cn_nadj hG huv ha]; simp [huv, ha]

lemma hAJ : A G * (J : Matrix V V ℤ) = (14 : ℤ) • J := by
  ext u v
  rw [A, adjMatrix_mul_apply]
  simp [J_apply, degree_eq hG]

lemma hJA : (J : Matrix V V ℤ) * A G = (14 : ℤ) • J := by
  ext u v
  rw [A, mul_adjMatrix_apply]
  simp [J_apply, degree_eq hG]

lemma hJJ : (J : Matrix V V ℤ) * J = (99 : ℤ) • J := by
  ext u v
  simp [Matrix.mul_apply, J_apply, card_V hG]

lemma hG0A : G0 G * A G = (-4 : ℤ) • G0 G := by
  simp only [G0, Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hA2 hG, hJA hG]
  module

lemma hAG0 : A G * G0 G = (-4 : ℤ) • G0 G := by
  simp only [G0, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, hA2 hG, hAJ hG]
  module

lemma hG0J : G0 G * (J : Matrix V V ℤ) = 0 := by
  simp only [G0, Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hAJ hG, hJJ hG]
  module

lemma hG0G0 : G0 G * G0 G = (63 : ℤ) • G0 G := by
  calc G0 G * G0 G = G0 G * ((27 : ℤ) • (1 : Matrix V V ℤ) - (9 : ℤ) • A G + J) := rfl
    _ = (27 : ℤ) • G0 G - (9 : ℤ) • (G0 G * A G) + G0 G * J := by
        rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
    _ = (63 : ℤ) • G0 G := by rw [hG0A hG, hG0J hG]; module

lemma BBt : B G * (B G)ᵀ = (7 : ℤ) • (1 : Matrix V V ℤ) + A G := by
  ext u v
  simp only [Matrix.mul_apply, Matrix.transpose_apply, B_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, A_apply, smul_eq_mul]
  have hs : ∑ t : Tr G, (if u ∈ t.1 then (1 : ℤ) else 0) * (if v ∈ t.1 then 1 else 0)
      = (((T (G := G)).filter (fun t => u ∈ t ∧ v ∈ t)).card : ℤ) := by
    rw [Finset.sum_coe_sort (T (G := G))
      (fun t => (if u ∈ t then (1 : ℤ) else 0) * (if v ∈ t then 1 else 0))]
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro t _
    by_cases h1 : u ∈ t <;> by_cases h2 : v ∈ t <;> simp [h1, h2]
  rw [hs]
  by_cases huv : u = v
  · subst huv
    simp only [and_self, if_true, G.loopless.irrefl, if_false]
    rw [T_through_vertex hG u]; simp
  · by_cases ha : G.Adj u v
    · rw [T_through_edge hG ha]; simp [huv, ha]
    · rw [T_through_nonedge huv ha]; simp [huv, ha]

lemma BBtG0 : B G * (B G)ᵀ * G0 G = (3 : ℤ) • G0 G := by
  rw [BBt hG, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hAG0 hG]
  module

end SRG

/-! ### `S` from `P`, and the frame identities -/

lemma sum_B_mul (L : Tr G) (f : V → ℤ) : ∑ u, B G u L * f u = ∑ u ∈ L.1, f u := by
  simp only [B_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma Bt_mul_P : (B G)ᵀ * P G = (3 : ℤ) • S G := by
  ext L M
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  rw [sum_B_mul]
  simp only [P, S, Matrix.of_apply]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : ∑ u ∈ L.1, (if u ∈ M.1 then (1 : ℤ) else 0) = ((L.1 ∩ M.1).card : ℤ) := by
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter]
  have h2 : ∑ u ∈ L.1, (nb G u M.1 : ℤ) = (eLM G L.1 M.1 : ℤ) := by
    simp [eLM]
  rw [h1, h2, Finset.sum_const, T_card3 L.2]
  simp only [nsmul_eq_mul]
  push_cast
  ring

section SRG2

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

lemma nine_S : (9 : ℤ) • S G = (B G)ᵀ * G0 G * B G := by
  rw [Matrix.mul_assoc, G0_mul_B, Matrix.mul_smul, Bt_mul_P, smul_smul]
  norm_num

lemma S_symm : (S G)ᵀ = S G := by
  apply smul_right_injective (Matrix (Tr G) (Tr G) ℤ) (show (9 : ℤ) ≠ 0 by norm_num)
  try simp only []
  rw [← Matrix.transpose_smul, nine_S hG, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, G0_symm, Matrix.mul_assoc]

lemma S_sq : S G * S G = (21 : ℤ) • S G := by
  apply smul_right_injective (Matrix (Tr G) (Tr G) ℤ) (show (81 : ℤ) ≠ 0 by norm_num)
  try simp only []
  have e1 : (81 : ℤ) • (S G * S G) = ((9 : ℤ) • S G) * ((9 : ℤ) • S G) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; norm_num
  rw [e1, nine_S hG]
  have e2 : (B G)ᵀ * G0 G * B G * ((B G)ᵀ * G0 G * B G)
      = (B G)ᵀ * (G0 G * (B G * (B G)ᵀ * G0 G)) * B G := by
    simp only [Matrix.mul_assoc]
  rw [e2, BBtG0 hG, Matrix.mul_smul, hG0G0 hG]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [← nine_S hG, smul_smul]
  norm_num

lemma B_mul_S : B G * S G = P G := by
  apply smul_right_injective (Matrix V (Tr G) ℤ) (show (9 : ℤ) ≠ 0 by norm_num)
  try simp only []
  rw [← Matrix.mul_smul, nine_S hG]
  have : B G * ((B G)ᵀ * G0 G * B G) = (B G * (B G)ᵀ * G0 G) * B G := by
    simp only [Matrix.mul_assoc]
  rw [this, BBtG0 hG, Matrix.smul_mul, G0_mul_B, smul_smul]
  norm_num

lemma Pt_mul_P : (P G)ᵀ * P G = (63 : ℤ) • S G := by
  apply smul_right_injective (Matrix (Tr G) (Tr G) ℤ) (show (9 : ℤ) ≠ 0 by norm_num)
  try simp only []
  have e1 : (9 : ℤ) • ((P G)ᵀ * P G) = ((3 : ℤ) • P G)ᵀ * ((3 : ℤ) • P G) := by
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]; norm_num
  rw [e1, ← G0_mul_B, Matrix.transpose_mul, G0_symm]
  have : (B G)ᵀ * G0 G * (G0 G * B G) = (B G)ᵀ * (G0 G * G0 G) * B G := by
    simp only [Matrix.mul_assoc]
  rw [this, hG0G0 hG, Matrix.mul_smul, Matrix.smul_mul, ← nine_S hG, smul_smul, smul_smul]
  norm_num

lemma A_mul_P : A G * P G = (-4 : ℤ) • P G := by
  apply smul_right_injective (Matrix V (Tr G) ℤ) (show (3 : ℤ) ≠ 0 by norm_num)
  try simp only []
  rw [← Matrix.mul_smul, ← G0_mul_B, ← Matrix.mul_assoc, hAG0 hG, Matrix.smul_mul, G0_mul_B,
    smul_smul, smul_smul]
  norm_num

lemma J_mul_P : (J : Matrix V V ℤ) * P G = 0 := by
  apply smul_right_injective (Matrix V (Tr G) ℤ) (show (3 : ℤ) ≠ 0 by norm_num)
  try simp only []
  rw [← Matrix.mul_smul, ← G0_mul_B, ← Matrix.mul_assoc]
  have hJG0 : (J : Matrix V V ℤ) * G0 G = 0 := by
    rw [← Matrix.transpose_transpose ((J : Matrix V V ℤ) * G0 G), Matrix.transpose_mul, G0_symm,
      J_symm, hG0J hG, Matrix.transpose_zero]
  rw [hJG0, Matrix.zero_mul, smul_zero]

lemma P_mul_S : P G * S G = (21 : ℤ) • P G := by
  rw [← B_mul_S hG, Matrix.mul_assoc, S_sq hG, Matrix.mul_smul]

end SRG2

end Conway99
