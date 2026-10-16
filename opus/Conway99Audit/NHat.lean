import Conway99Audit.Zero
import Conway99Audit.Iso

/-!
# Part C, step 6: the lattices `N`, `N*` and the overlattice `N̂` of determinant 49 (§4)

In profile coordinates (see `Roots.lean`):
* `Nsub G = {Nvec c : 3 ∣ Σ c}` is the lattice `N`; it is even and integral (§4.1);
* `Ndual G = {z : A z = -4 z, z_u ≡ z_v (mod 3)}` is `N*` (`(16)` of the paper);
* `7 N* ⊆ N` (`seven_Ndual`): this replaces the 3-adic Smith computation of §4.2 — the
  discriminant group of every even overlattice of `N` is killed by `7`.
-/

open Finset SimpleGraph Matrix

namespace Conway99

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma J_mulVec (z : V → ℤ) (u : V) : ((J : Matrix V V ℤ) *ᵥ z) u = ∑ v, z v := by
  simp [J, mulVec, dotProduct]

/-- `cᵀ A c` is even. -/
lemma even_cAc (c : V → ℤ) : Even (c ⬝ᵥ (A G *ᵥ c)) := by
  have h := sum_symm_offdiag_even (fun u v => c u * A G u v * c v) (fun u v => by
    rw [show A G u v = A G v u from by
      have := congrFun (congrFun (A_symm (G := G)) v) u; rwa [transpose_apply] at this]; ring)
  have hdiag : ∑ u, c u * A G u u * c u = 0 := by
    apply Finset.sum_eq_zero; intro u _; rw [A_apply]; simp
  rw [hdiag, sub_zero] at h
  have e : c ⬝ᵥ (A G *ᵥ c) = ∑ u, ∑ v, c u * A G u v * c v := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro v _; ring
  rw [e]; exact h

variable (G) in
/-- The lattice `N` in profile coordinates. -/
def Nsub : AddSubgroup (V → ℤ) where
  carrier := {z | ∃ c : V → ℤ, 3 ∣ ∑ v, c v ∧ z = Nvec G c}
  zero_mem' := ⟨0, by simp, by funext u; simp [Nvec]⟩
  add_mem' := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    refine ⟨c + c', by simp only [Pi.add_apply, Finset.sum_add_distrib]; exact dvd_add hc hc', ?_⟩
    funext u
    simp only [Nvec, Pi.add_apply, mulVec_add, Finset.sum_add_distrib]
    rw [Int.add_ediv_of_dvd_left hc]; ring
  neg_mem' := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨-c, by simp only [Pi.neg_apply, Finset.sum_neg_distrib]; exact (dvd_neg).2 hc, ?_⟩
    funext u
    simp only [Nvec, Pi.neg_apply, mulVec_neg, Finset.sum_neg_distrib]
    rw [Int.neg_ediv_of_dvd hc]; ring

variable (G) in
/-- The dual lattice `N*` in profile coordinates. -/
def Ndual : AddSubgroup (V → ℤ) where
  carrier := {z | IsM4 G z ∧ ∀ u v, 3 ∣ z u - z v}
  zero_mem' := ⟨by simp [IsM4], by simp⟩
  add_mem' := by
    rintro z z' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨?_, fun u v => ?_⟩
    · unfold IsM4 at *; rw [mulVec_add, h1, h1', smul_add]
    · have := dvd_add (h2 u v) (h2' u v); simp only [Pi.add_apply]
      convert this using 1; ring
  neg_mem' := by
    rintro z ⟨h1, h2⟩
    refine ⟨?_, fun u v => ?_⟩
    · unfold IsM4 at *; rw [mulVec_neg, h1, smul_neg]
    · have := (dvd_neg).2 (h2 u v); simp only [Pi.neg_apply]
      convert this using 1; ring

lemma mem_Nsub {z : V → ℤ} : z ∈ Nsub G ↔ ∃ c : V → ℤ, 3 ∣ ∑ v, c v ∧ z = Nvec G c := Iff.rfl

lemma mem_Ndual {z : V → ℤ} : z ∈ Ndual G ↔ IsM4 G z ∧ ∀ u v, 3 ∣ z u - z v := Iff.rfl

section SRG

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

/-- `G₀ z = 63 z` for a `-4` eigenvector. -/
lemma G0_mulVec_M4 {z : V → ℤ} (hz : IsM4 G z) : G0 G *ᵥ z = (63 : ℤ) • z := by
  have hs := hz.sum_zero hG
  funext u
  have hA : (A G *ᵥ z) u = -4 * z u := by
    have := congrFun hz u; simpa using this
  simp only [G0, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hA, J_mulVec, hs]; ring

/-- `3 Nvec c = G₀ c` when `3 ∣ Σ c`. -/
lemma three_Nvec {c : V → ℤ} (hc : 3 ∣ ∑ v, c v) : (3 : ℤ) • Nvec G c = G0 G *ᵥ c := by
  obtain ⟨k, hk⟩ := hc
  funext u
  simp only [Nvec, G0, Pi.smul_apply, smul_eq_mul, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply]
  rw [J_mulVec, hk, Int.mul_ediv_cancel_left _ (by norm_num : (3 : ℤ) ≠ 0)]; ring

lemma Nvec_M4 {c : V → ℤ} (hc : 3 ∣ ∑ v, c v) : IsM4 G (Nvec G c) := by
  have h3 := three_Nvec hG hc
  have key : A G *ᵥ (G0 G *ᵥ c) = (-4 : ℤ) • (G0 G *ᵥ c) := by
    rw [mulVec_mulVec, hAG0 hG, smul_mulVec]
  rw [← h3, mulVec_smul] at key
  unfold IsM4
  funext u
  have := congrFun key u
  simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
  omega

lemma Nvec_dot {c c' : V → ℤ} (hc : 3 ∣ ∑ v, c v) (hc' : 3 ∣ ∑ v, c' v) :
    Nvec G c ⬝ᵥ Nvec G c' = 7 * (c ⬝ᵥ (G0 G *ᵥ c')) := by
  have h3 := three_Nvec hG hc
  have h3' := three_Nvec hG hc'
  have e : (9 : ℤ) * (Nvec G c ⬝ᵥ Nvec G c') = (G0 G *ᵥ c) ⬝ᵥ (G0 G *ᵥ c') := by
    rw [← h3, ← h3', smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
  have e2 : (G0 G *ᵥ c) ⬝ᵥ (G0 G *ᵥ c') = 63 * (c ⬝ᵥ (G0 G *ᵥ c')) := by
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, G0_symm, mulVec_mulVec,
      hG0G0 hG, smul_mulVec, dotProduct_comm, dotProduct_smul, smul_eq_mul]
  rw [e2] at e
  linarith

lemma cG0c (c c' : V → ℤ) :
    c ⬝ᵥ (G0 G *ᵥ c') = 27 * (c ⬝ᵥ c') - 9 * (c ⬝ᵥ (A G *ᵥ c')) + (∑ v, c v) * ∑ v, c' v := by
  simp only [G0, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have : c ⬝ᵥ ((J : Matrix V V ℤ) *ᵥ c') = (∑ v, c v) * ∑ v, c' v := by
    simp only [dotProduct, J_mulVec, Finset.sum_mul]
  rw [this]

variable (G) in
/-- `N` is an even integral overlattice of itself. -/
def Nlat : EvenOverlattice G where
  L := Nsub G
  eig := by
    rintro _ ⟨c, hc, rfl⟩; exact Nvec_M4 hG hc
  contains := fun c hc => ⟨c, hc, rfl⟩
  integral := by
    rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩
    rw [Nvec_dot hG hc hc', cG0c hG]
    obtain ⟨k, hk⟩ := hc
    obtain ⟨k', hk'⟩ := hc'
    rw [hk, hk']
    exact ⟨3 * (c ⬝ᵥ c') - c ⬝ᵥ (A G *ᵥ c') + k * k', by ring⟩
  even := by
    rintro _ ⟨c, hc, rfl⟩
    rw [Nvec_dot hG hc hc, cG0c hG]
    obtain ⟨k, hk⟩ := hc
    obtain ⟨m, hm⟩ := even_cAc (G := G) c
    obtain ⟨a, ha⟩ : Even (c ⬝ᵥ c - ∑ v, c v) := by
      have : c ⬝ᵥ c - ∑ v, c v = ∑ v, c v * (c v - 1) := by
        simp only [dotProduct, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro v _; ring
      rw [this]
      exact Finset.even_sum _ (fun v _ => Int.even_mul_pred_self _)
    obtain ⟨b, hb⟩ := Int.even_mul_pred_self k
    rw [hk] at ha ⊢
    rw [hm]
    exact ⟨3 * a + 5 * k - m + b, by linear_combination (189 : ℤ) * ha + 63 * hb⟩

/-- Elements of an even overlattice lie in `N*`. -/
lemma le_Ndual (L : EvenOverlattice G) : L.L ≤ Ndual G :=
  fun _ hz => ⟨L.eig _ hz, L.res hG hz⟩

lemma Nsub_le (L : EvenOverlattice G) : Nsub G ≤ L.L := by
  rintro _ ⟨c, hc, rfl⟩; exact L.contains c hc

lemma A_rowsum (u : V) : ∑ v, A G u v = 14 := by
  rw [← colsum_A hG u]
  apply Finset.sum_congr rfl; intro v _
  have := congrFun (congrFun (A_symm (G := G)) v) u; rwa [transpose_apply] at this

/-- `G₀ 𝟏 = 0`. -/
lemma G0_const (r : ℤ) : G0 G *ᵥ (fun _ => r) = 0 := by
  funext u
  simp only [G0, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  rw [J_mulVec]
  have hA : (A G *ᵥ fun _ => r) u = 14 * r := by
    simp only [mulVec, dotProduct]
    rw [← Finset.sum_mul, A_rowsum hG]
  rw [hA, Finset.sum_const, card_univ, card_V hG]
  simp; ring

/-- **`7 N* ⊆ N`** (replaces the 3-adic Smith computation of §4.2). -/
theorem seven_Ndual {z : V → ℤ} (hz : z ∈ Ndual G) : (7 : ℤ) • z ∈ Nsub G := by
  obtain ⟨hM, hres⟩ := hz
  obtain ⟨u0⟩ := nonempty_V hG
  set r := z u0 with hr
  let y : V → ℤ := fun u => (z u - r) / 3
  have hy : ∀ u, 3 * y u = z u - r := fun u => Int.mul_ediv_cancel' (hres u u0)
  have hsum : ∑ u, y u = 3 * (-11 * r) := by
    have hs := hM.sum_zero hG
    have h3 : 3 * ∑ u, y u = ∑ u, (z u - r) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun u _ => hy u)
    rw [Finset.sum_sub_distrib, hs, Finset.sum_const, card_univ, card_V hG] at h3
    simp at h3; linarith
  have hyd : 3 ∣ ∑ u, y u := ⟨-11 * r, hsum⟩
  refine ⟨y, hyd, ?_⟩
  have h3 := three_Nvec hG hyd
  have hG0z := G0_mulVec_M4 hG hM
  have h3y : (3 : ℤ) • y = z - (fun _ => r) := by
    funext u; simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]; exact hy u
  have h9 : (9 : ℤ) • Nvec G y = (63 : ℤ) • z := by
    calc (9 : ℤ) • Nvec G y = (3 : ℤ) • ((3 : ℤ) • Nvec G y) := by rw [smul_smul]; norm_num
      _ = (3 : ℤ) • (G0 G *ᵥ y) := by rw [h3]
      _ = G0 G *ᵥ ((3 : ℤ) • y) := by rw [mulVec_smul]
      _ = G0 G *ᵥ z - G0 G *ᵥ (fun _ => r) := by rw [h3y, mulVec_sub]
      _ = (63 : ℤ) • z := by rw [hG0z, G0_const hG, sub_zero]
  funext u
  have := congrFun h9 u
  simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
  omega


/-! ### A basis of an even overlattice, its Gram matrix and its dual basis -/

/-- The columns `G₀ e_u = Nvec (3 e_u)` lie in `N`. -/
lemma G0col_mem (u : V) : G0 G *ᵥ Pi.single u 1 ∈ Nsub G := by
  have hc : 3 ∣ ∑ v, ((3 : ℤ) • Pi.single u (1 : ℤ)) v := ⟨1, by
    simp only [Pi.smul_apply, smul_eq_mul]; rw [← Finset.mul_sum]; simp⟩
  refine ⟨(3 : ℤ) • Pi.single u 1, hc, ?_⟩
  have h3 := three_Nvec hG hc
  rw [mulVec_smul] at h3
  funext v
  have := congrFun h3 v
  simp only [Pi.smul_apply, smul_eq_mul] at this
  omega


end SRG

noncomputable section Gram

variable (hG : G.IsSRGWith 99 14 1 2)

variable (L : EvenOverlattice G) {ι : Type} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι ℤ L.L.toIntSubmodule)

/-- The basis vectors, as profiles. -/
def bv (j : ι) : V → ℤ := (b j : V → ℤ)

lemma bv_mem (j : ι) : bv L b j ∈ L.L := (b j).2

lemma sum_bv_eq (x : ι → ℤ) : ∑ j, x j • bv L b j = ((∑ j, x j • b j : L.L.toIntSubmodule) : V → ℤ) := by
  simp [bv, Submodule.coe_sum]

/-- Coefficients in the basis are unique. -/
lemma coef_unique {x x' : ι → ℤ} (h : ∑ j, x j • bv L b j = ∑ j, x' j • bv L b j) : x = x' := by
  rw [sum_bv_eq, sum_bv_eq] at h
  have h' := Subtype.ext h
  apply b.equivFun.symm.injective
  rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply]
  exact h'

/-- Every element of `L` is an integral combination of the basis. -/
lemma exists_coef {z : V → ℤ} (hz : z ∈ L.L) : ∃ x : ι → ℤ, z = ∑ j, x j • bv L b j := by
  refine ⟨b.equivFun ⟨z, hz⟩, ?_⟩
  rw [sum_bv_eq]
  have := b.sum_equivFun ⟨z, hz⟩
  rw [this]

/-- The coordinates of the columns of `G₀`: `G₀ e_u = Σ_j C j u • b_j`. -/
def Cmat : Matrix ι V ℤ := Matrix.of fun j u =>
  b.equivFun ⟨G0 G *ᵥ Pi.single u 1, Nsub_le hG L (G0col_mem hG u)⟩ j

lemma G0col_eq (u : V) : G0 G *ᵥ Pi.single u 1 = ∑ j, Cmat hG L b j u • bv L b j := by
  rw [sum_bv_eq]
  simp only [Cmat, Matrix.of_apply]
  rw [b.sum_equivFun]

/-- Gram matrix (scaled by `1/63`). -/
def gram : Matrix ι ι ℤ := Matrix.of fun i j => (bv L b i ⬝ᵥ bv L b j) / 63

lemma gram_spec (i j : ι) : 63 * gram L b i j = bv L b i ⬝ᵥ bv L b j := by
  simp only [gram, Matrix.of_apply]
  exact Int.mul_ediv_cancel' (L.integral _ (bv_mem L b i) _ (bv_mem L b j))

lemma gram_symm : (gram L b)ᵀ = gram L b := by
  ext i j; simp only [transpose_apply, gram, Matrix.of_apply, dotProduct_comm]

lemma gram_even (i : ι) : Even (gram L b i i) := by
  have h := gram_spec L b i i
  obtain ⟨k, hk⟩ := L.even _ (bv_mem L b i)
  exact ⟨k, by omega⟩

/-- `63 b_i = Σ_u ...`: the profile of `b_k` from the columns of `G₀`. -/
lemma bv_apply (k : ι) (u : V) : bv L b k u = ∑ l, Cmat hG L b l u * gram L b k l := by
  have hM := L.eig _ (bv_mem L b k)
  have h1 : (63 : ℤ) * bv L b k u = bv L b k ⬝ᵥ (G0 G *ᵥ Pi.single u 1) := by
    have e0 := congrFun (G0_mulVec_M4 hG hM) u
    simp only [Pi.smul_apply, smul_eq_mul] at e0
    rw [← e0]
    simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    apply Finset.sum_congr rfl; intro v _
    rw [show G0 G v u = G0 G u v from by
      have := congrFun (congrFun (G0_symm (G := G)) u) v; rwa [transpose_apply] at this]
    ring
  rw [G0col_eq hG L b, dotProduct_sum] at h1
  simp only [dotProduct_smul, smul_eq_mul, ← gram_spec L b] at h1
  have : (63 : ℤ) * bv L b k u = 63 * ∑ l, Cmat hG L b l u * gram L b k l := by
    rw [h1, Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring
  omega

/-- `C B = 63 I`. -/
lemma CB (j k : ι) : ∑ u, Cmat hG L b j u * bv L b k u = if j = k then 63 else 0 := by
  have hM := L.eig _ (bv_mem L b k)
  have h1 := G0_mulVec_M4 hG hM
  -- `G₀ b_k = Σ_u (b_k)_u G₀ e_u`
  have h2 : G0 G *ᵥ bv L b k = ∑ u, bv L b k u • (G0 G *ᵥ Pi.single u 1) := by
    conv_lhs => rw [show bv L b k = ∑ u, bv L b k u • Pi.single u (1 : ℤ) by
      funext v; simp [Finset.sum_apply, Pi.single_apply]]
    rw [mulVec_sum]
    simp only [mulVec_smul]
  simp only [G0col_eq hG L b, Finset.smul_sum, smul_smul] at h2
  rw [Finset.sum_comm] at h2
  simp only [← Finset.sum_smul] at h2
  rw [h1] at h2
  have h3 : (63 : ℤ) • bv L b k = ∑ j, (if j = k then (63 : ℤ) else 0) • bv L b j := by
    simp [ite_smul]
  rw [h3] at h2
  have := coef_unique L b h2.symm
  have := congrFun this j
  rw [← this]
  apply Finset.sum_congr rfl; intro u _; ring

lemma gram_det_ne_zero : (gram L b).det ≠ 0 := by
  intro h0
  obtain ⟨x, hx, hQx⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
  apply hx
  -- `Σ x_j b_j` is orthogonal to every `b_i`, hence to itself
  set w := ∑ j, x j • bv L b j with hw
  have hdot : ∀ i, bv L b i ⬝ᵥ w = 0 := by
    intro i
    rw [hw, dotProduct_sum]
    simp only [dotProduct_smul, smul_eq_mul, ← gram_spec L b]
    have := congrFun hQx i
    simp only [mulVec, dotProduct, Pi.zero_apply] at this
    rw [show ∑ j, x j * (63 * gram L b i j) = 63 * ∑ j, gram L b i j * x j by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring, this, mul_zero]
  have hww : w ⬝ᵥ w = 0 := by
    have : (∑ j, x j • bv L b j) ⬝ᵥ w = 0 := by
      rw [sum_dotProduct]
      simp only [smul_dotProduct, smul_eq_mul, hdot, mul_zero, Finset.sum_const_zero]
    rwa [← hw] at this
  have hw0 : w = 0 := dotProduct_self_eq_zero.1 hww
  have : ∑ j, x j • bv L b j = ∑ j, (0 : ι → ℤ) j • bv L b j := by rw [← hw, hw0]; simp
  exact coef_unique L b this

/-- The dual basis: `w_j = (C j ·)`, with `w_j · b_i = 63 δ_ij`. -/
def wv (j : ι) : V → ℤ := fun u => Cmat hG L b j u

lemma wv_dot (j i : ι) : wv hG L b j ⬝ᵥ bv L b i = if j = i then 63 else 0 := by
  rw [← CB hG L b j i]; rfl

lemma det_wv (j : ι) :
    (gram L b).det • wv hG L b j = ∑ k, (gram L b).adjugate j k • bv L b k := by
  funext u
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, wv, bv_apply hG L b, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hadj := congrFun (congrFun (adjugate_mul (gram L b)) j)
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at hadj
  rw [← Finset.sum_congr rfl (fun l _ => by
      rw [show (∑ k, (gram L b).adjugate j k * (Cmat hG L b l u * gram L b k l))
        = Cmat hG L b l u * ∑ k, (gram L b).adjugate j k * gram L b k l by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring, hadj l])]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

lemma wv_M4 (j : ι) : IsM4 G (wv hG L b j) := by
  have hd := gram_det_ne_zero L b
  have h := det_wv hG L b j
  have hA : A G *ᵥ ((gram L b).det • wv hG L b j) = (-4 : ℤ) • ((gram L b).det • wv hG L b j) := by
    rw [h, mulVec_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [mulVec_smul, L.eig _ (bv_mem L b k), smul_comm]
  rw [mulVec_smul] at hA
  unfold IsM4
  funext u
  have := congrFun hA u
  simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
  have : (gram L b).det * ((A G *ᵥ wv hG L b j) u - (-4) * wv hG L b j u) = 0 := by linarith
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 hd
  · linarith

lemma wv_Ndual (j : ι) : wv hG L b j ∈ Ndual G := by
  refine ⟨wv_M4 hG L b j, fun u v => ?_⟩
  have hc : 3 ∣ ∑ x, ediff u v x := ⟨0, by rw [sum_ediff]; ring⟩
  have hN := Nsub_le hG L ⟨ediff u v, hc, rfl⟩
  obtain ⟨x, hx⟩ := exists_coef L b hN
  have h1 := dot_Nvec_diff hG (wv_M4 hG L b j) u v
  rw [hx, dotProduct_sum] at h1
  simp only [dotProduct_smul, smul_eq_mul, wv_dot hG L b, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
  omega

/-- The integer matrix `R` with `Gram · R = 7 I` (coordinates of `7 w_j`). -/
def Rmat : Matrix ι ι ℤ := Matrix.of fun k j =>
  b.equivFun ⟨(7 : ℤ) • wv hG L b j, Nsub_le hG L (seven_Ndual hG (wv_Ndual hG L b j))⟩ k

lemma seven_wv (j : ι) : (7 : ℤ) • wv hG L b j = ∑ k, Rmat hG L b k j • bv L b k := by
  rw [sum_bv_eq]
  simp only [Rmat, Matrix.of_apply]
  rw [b.sum_equivFun]

lemma gram_R : gram L b * Rmat hG L b = (7 : ℤ) • (1 : Matrix ι ι ℤ) := by
  ext i j
  have h := congrArg (fun z => bv L b i ⬝ᵥ z) (seven_wv hG L b j)
  simp only [dotProduct_smul, smul_eq_mul, dotProduct_sum] at h
  rw [dotProduct_comm, wv_dot hG L b] at h
  simp only [← gram_spec L b] at h
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have : (63 : ℤ) * ∑ k, gram L b i k * Rmat hG L b k j = 63 * (7 * if i = j then 1 else 0) := by
    rw [Finset.mul_sum]
    rw [show ∑ k, 63 * (gram L b i k * Rmat hG L b k j) = ∑ k, Rmat hG L b k j * (63 * gram L b i k) by
      apply Finset.sum_congr rfl; intro k _; ring, ← h]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  omega

end Gram

end Conway99
