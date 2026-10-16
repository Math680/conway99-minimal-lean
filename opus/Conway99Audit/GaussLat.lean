import Conway99Audit.Gauss1
import Conway99Audit.Quad

/-!
# Part C, step 2: Gauss sums of integral lattices, in coordinates

For `Q : Matrix (Fin n) (Fin n) ℤ` with `det Q ≠ 0`, the discriminant group of the lattice
`(ℤⁿ, Q)` is identified with `DQ Q = ℤⁿ / Q ℤⁿ` (a vector `y` represents `Q⁻¹ y ∈ L*`), with
quadratic form `qf Q y = yᵀ Q⁻¹ y` (rational).  We prove `|DQ Q| = |det Q|` and set
`gauss Q = ∑_{y ∈ DQ Q} exp (π i · yᵀ Q⁻¹ y)` (well defined for symmetric `Q` with even diagonal).
-/

open Complex Real Matrix Finset

namespace Conway99

noncomputable section

variable {n : ℕ}

/-- The sublattice `M ℤⁿ`. -/
def lat (M : Matrix (Fin n) (Fin n) ℤ) : Submodule ℤ (Fin n → ℤ) := LinearMap.range M.mulVecLin

lemma mem_lat {M : Matrix (Fin n) (Fin n) ℤ} {y : Fin n → ℤ} : y ∈ lat M ↔ ∃ x, M *ᵥ x = y := by
  simp [lat]

lemma mulVec_mem_lat (M : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) : M *ᵥ x ∈ lat M :=
  mem_lat.2 ⟨x, rfl⟩

lemma mulVec_injective_of_det {M : Matrix (Fin n) (Fin n) ℤ} (h : M.det ≠ 0) :
    Function.Injective M.mulVec := by
  intro x y hxy
  have h2 : M.adjugate *ᵥ (M *ᵥ x) = M.adjugate *ᵥ (M *ᵥ y) := by rw [hxy]
  rw [mulVec_mulVec, mulVec_mulVec, adjugate_mul, smul_mulVec, smul_mulVec, one_mulVec,
    one_mulVec] at h2
  funext i
  have := congrFun h2 i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ h this

/-- The discriminant group `ℤⁿ / M ℤⁿ`. -/
abbrev DQ (M : Matrix (Fin n) (Fin n) ℤ) := (Fin n → ℤ) ⧸ lat M

/-- `|ℤⁿ / M ℤⁿ| = |det M|`. -/
theorem card_DQ {M : Matrix (Fin n) (Fin n) ℤ} (h : M.det ≠ 0) :
    Nat.card (DQ M) = M.det.natAbs := by
  let e : (Fin n → ℤ) ≃ₗ[ℤ] lat M := LinearEquiv.ofInjective M.mulVecLin (mulVec_injective_of_det h)
  let bN : Module.Basis (Fin n) ℤ (lat M) := (Pi.basisFun ℤ (Fin n)).map e
  rw [← Submodule.natAbs_det_basis_change (Pi.basisFun ℤ (Fin n)) (lat M) bN]
  congr 1
  rw [Module.Basis.det_apply]
  have : (Pi.basisFun ℤ (Fin n)).toMatrix ((↑) ∘ bN) = M := by
    ext i j
    rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    show (M.mulVecLin (Pi.basisFun ℤ (Fin n) j)) i = M i j
    simp [Matrix.mulVec_single_one]
  rw [this]

lemma finite_DQ {M : Matrix (Fin n) (Fin n) ℤ} (h : M.det ≠ 0) : Finite (DQ M) :=
  Nat.finite_of_card_ne_zero (by rw [card_DQ h]; exact Int.natAbs_ne_zero.2 h)

/-! ### The rational quadratic form `yᵀ Q⁻¹ y` -/

/-- `Q` over `ℚ`. -/
def Qq (Q : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℚ := Q.map (Int.cast : ℤ → ℚ)

/-- An integer vector over `ℚ`. -/
def vq (y : Fin n → ℤ) : Fin n → ℚ := fun i => (y i : ℚ)

/-- `xᵀ Q⁻¹ y`. -/
def bf (Q : Matrix (Fin n) (Fin n) ℤ) (x y : Fin n → ℤ) : ℚ := vq x ⬝ᵥ ((Qq Q)⁻¹ *ᵥ vq y)

/-- `yᵀ Q⁻¹ y`. -/
def qf (Q : Matrix (Fin n) (Fin n) ℤ) (y : Fin n → ℤ) : ℚ := bf Q y y

lemma vq_add (x y : Fin n → ℤ) : vq (x + y) = vq x + vq y := by
  funext i; simp [vq]

lemma vq_mulVec (M : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) : vq (M *ᵥ x) = Qq M *ᵥ vq x := by
  funext i
  simp only [vq, Qq, mulVec, dotProduct, Matrix.map_apply]
  push_cast; rfl

lemma Qq_det (Q : Matrix (Fin n) (Fin n) ℤ) : (Qq Q).det = (Q.det : ℚ) := by
  have := RingHom.map_det (Int.castRingHom ℚ) Q
  simpa [Qq] using this.symm

lemma Qq_transpose (Q : Matrix (Fin n) (Fin n) ℤ) : (Qq Q)ᵀ = Qq Qᵀ := by
  ext i j; simp [Qq]

lemma Qq_mul (A B : Matrix (Fin n) (Fin n) ℤ) : Qq (A * B) = Qq A * Qq B := by
  ext i j; simp only [Qq, Matrix.map_apply, Matrix.mul_apply]; push_cast; rfl

lemma isUnit_Qq_det {Q : Matrix (Fin n) (Fin n) ℤ} (h : Q.det ≠ 0) : IsUnit (Qq Q).det := by
  rw [Qq_det]; exact isUnit_iff_ne_zero.2 (by exact_mod_cast h)

lemma vq_dot (x y : Fin n → ℤ) : vq x ⬝ᵥ vq y = ((x ⬝ᵥ y : ℤ) : ℚ) := by
  simp [vq, dotProduct]

section Sym

variable {Q : Matrix (Fin n) (Fin n) ℤ} (hs : Qᵀ = Q) (hd : Q.det ≠ 0)
include hs hd

lemma bf_symm (x y : Fin n → ℤ) : bf Q x y = bf Q y x := by
  have hinvT : ((Qq Q)⁻¹)ᵀ = (Qq Q)⁻¹ := by rw [transpose_nonsing_inv, Qq_transpose, hs]
  unfold bf
  rw [dotProduct_mulVec, ← mulVec_transpose, hinvT, dotProduct_comm]

lemma bf_add_right (x y z : Fin n → ℤ) : bf Q x (y + z) = bf Q x y + bf Q x z := by
  unfold bf; rw [vq_add, mulVec_add, dotProduct_add]

lemma bf_add_left (x y z : Fin n → ℤ) : bf Q (x + y) z = bf Q x z + bf Q y z := by
  rw [bf_symm hs hd, bf_add_right hs hd, bf_symm hs hd y, bf_symm hs hd x]

lemma qf_add (x y : Fin n → ℤ) : qf Q (x + y) = qf Q x + qf Q y + 2 * bf Q x y := by
  unfold qf
  rw [bf_add_left hs hd, bf_add_right hs hd, bf_add_right hs hd, bf_symm hs hd y x]; ring

/-- `(Q m)ᵀ Q⁻¹ y = mᵀ y`. -/
lemma bf_lat_left (m y : Fin n → ℤ) : bf Q (Q *ᵥ m) y = ((m ⬝ᵥ y : ℤ) : ℚ) := by
  unfold bf
  have hT : (Qq Q)ᵀ = Qq Q := by rw [Qq_transpose, hs]
  calc vq (Q *ᵥ m) ⬝ᵥ ((Qq Q)⁻¹ *ᵥ vq y) = (Qq Q *ᵥ vq m) ⬝ᵥ ((Qq Q)⁻¹ *ᵥ vq y) := by
        rw [vq_mulVec]
    _ = ((Qq Q)⁻¹ *ᵥ vq y) ⬝ᵥ (Qq Q *ᵥ vq m) := dotProduct_comm _ _
    _ = (((Qq Q)⁻¹ *ᵥ vq y) ᵥ* Qq Q) ⬝ᵥ vq m := dotProduct_mulVec _ _ _
    _ = ((Qq Q)ᵀ *ᵥ ((Qq Q)⁻¹ *ᵥ vq y)) ⬝ᵥ vq m := by rw [mulVec_transpose]
    _ = vq y ⬝ᵥ vq m := by
        rw [hT, mulVec_mulVec, mul_nonsing_inv _ (isUnit_Qq_det hd), one_mulVec]
    _ = ((m ⬝ᵥ y : ℤ) : ℚ) := by rw [vq_dot, dotProduct_comm]

lemma bf_lat_right (m y : Fin n → ℤ) : bf Q y (Q *ᵥ m) = ((m ⬝ᵥ y : ℤ) : ℚ) := by
  rw [bf_symm hs hd, bf_lat_left hs hd]

lemma qf_lat (m : Fin n → ℤ) : qf Q (Q *ᵥ m) = ((m ⬝ᵥ (Q *ᵥ m) : ℤ) : ℚ) := by
  unfold qf; rw [bf_lat_left hs hd]

end Sym

/-- Even lattice: `mᵀ Q m` is even when `Q` is symmetric with even diagonal. -/
lemma even_quad {Q : Matrix (Fin n) (Fin n) ℤ} (hs : Qᵀ = Q) (he : ∀ i, Even (Q i i))
    (m : Fin n → ℤ) : Even (m ⬝ᵥ (Q *ᵥ m)) := by
  have h := sum_symm_offdiag_even (fun i j => m i * Q i j * m j) (fun i j => by
    have : Q i j = Q j i := by
      have h := congrFun (congrFun hs j) i; rwa [transpose_apply] at h
    rw [this]; ring)
  have hdiag : Even (∑ i, m i * Q i i * m i) := by
    apply Finset.even_sum; intro i _
    obtain ⟨k, hk⟩ := he i
    exact ⟨m i * k * m i, by rw [hk]; ring⟩
  have e : m ⬝ᵥ (Q *ᵥ m) = ∑ i, ∑ j, m i * Q i j * m j := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  rw [e]
  have := h.add hdiag
  simpa using this

/-! ### The Gauss sum -/

/-- `exp (π i yᵀ Q⁻¹ y)`. -/
def phi (Q : Matrix (Fin n) (Fin n) ℤ) (y : Fin n → ℤ) : ℂ := cexp (π * I * (qf Q y : ℂ))

lemma exp_pi_I_even (k : ℤ) (hk : Even k) : cexp (π * I * (k : ℂ)) = 1 := by
  obtain ⟨j, hj⟩ := hk
  rw [show π * I * (k : ℂ) = (j : ℂ) * (2 * π * I) by rw [hj]; push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I j

section Even

variable {Q : Matrix (Fin n) (Fin n) ℤ} (hs : Qᵀ = Q) (hd : Q.det ≠ 0) (he : ∀ i, Even (Q i i))
include hs hd he

lemma phi_add_lat (y m : Fin n → ℤ) : phi Q (y + Q *ᵥ m) = phi Q y := by
  unfold phi
  rw [qf_add hs hd, qf_lat hs hd, bf_lat_right hs hd]
  have hev : Even (2 * (m ⬝ᵥ y) + m ⬝ᵥ (Q *ᵥ m)) :=
    (even_two_mul _).add (even_quad hs he m)
  rw [show (π : ℂ) * I * (((qf Q y + ((m ⬝ᵥ (Q *ᵥ m) : ℤ) : ℚ) + 2 * ((m ⬝ᵥ y : ℤ) : ℚ)) : ℚ) : ℂ)
      = π * I * (qf Q y : ℂ) + π * I * (((2 * (m ⬝ᵥ y) + m ⬝ᵥ (Q *ᵥ m) : ℤ)) : ℂ) by
    push_cast; ring, Complex.exp_add, exp_pi_I_even _ hev, mul_one]

end Even

end

end Conway99
