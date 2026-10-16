import Conway99Audit.Milgram

/-!
# Part C, step 5: discriminant forms killed by 7

Setting: `Q` symmetric, positive definite, even diagonal, with an integer `R`, `Q R = 7 I`
(the discriminant group `ℤⁿ / Q ℤⁿ` is killed by `7`).

* `exists_isotropic`: if `det Q ≥ 7³`, some class `y ∉ Q ℤⁿ` is isotropic (`yᵀ Q⁻¹ y ∈ 2ℤ`):
  an anisotropic quadratic form over `𝔽₇` has dimension at most `2` (pigeonhole on squares).
* `det_ne_one_seven`: for `n = 44`, Milgram's formula excludes `det Q = 1` and `det Q = 7`.
-/

open Complex Real Matrix Finset

namespace Conway99

noncomputable section

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ### An abstract lemma on finite quadratic modules over `𝔽₇` -/

lemma pigeonhole7 : ∀ p q r : ZMod 7, p ≠ 0 → q ≠ 0 → r ≠ 0 →
    ∃ a b : ZMod 7, a ^ 2 * p + b ^ 2 * q + r = 0 := by decide

lemma card_ker_ge {D : Type*} [AddCommGroup D] [Fintype D] [DecidableEq D]
    (f : D →+ ZMod 7) (S : AddSubgroup D) [Fintype S] [DecidablePred (· ∈ S ⊓ f.ker)] :
    Fintype.card S ≤ 7 * Fintype.card (S ⊓ f.ker : AddSubgroup D) := by
  classical
  -- `S ⊓ ker f` is the kernel of `f` restricted to `S`
  let g : S →+ ZMod 7 := f.comp S.subtype
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker
  have h2 : Nat.card (S ⧸ g.ker) ≤ 7 := by
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv]
    calc Nat.card g.range ≤ Nat.card (ZMod 7) := Finite.card_subtype_le _
      _ = 7 := by simp
  have h3 : Nat.card g.ker = Fintype.card (S ⊓ f.ker : AddSubgroup D) := by
    rw [← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    exact {
      toFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  rw [← Nat.card_eq_fintype_card, h1, ← h3]
  calc Nat.card (S ⧸ g.ker) * Nat.card g.ker ≤ 7 * Nat.card g.ker :=
        Nat.mul_le_mul_right _ h2

/-- A finite quadratic module over `𝔽₇` of order at least `7³` has a nonzero isotropic vector. -/
theorem exists_isotropic_abstract {D : Type*} [AddCommGroup D] [Fintype D] [DecidableEq D]
    (κ : D → ZMod 7) (β : D →+ D →+ ZMod 7)
    (hsymm : ∀ x y, β x y = β y x)
    (hκadd : ∀ x y, κ (x + y) = κ x + κ y + β x y)
    (hκβ : ∀ x, β x x = 2 * κ x)
    (hcard : 343 ≤ Fintype.card D) :
    ∃ v : D, v ≠ 0 ∧ κ v = 0 := by
  classical
  have hκ0 : κ 0 = 0 := by
    have := hκadd 0 0; simp at this; linear_combination this
  have hκsmul : ∀ (k : ℕ) x, κ (k • x) = (k : ZMod 7) ^ 2 * κ x := by
    intro k x
    induction k with
    | zero => simp [hκ0]
    | succ k ih =>
      rw [succ_nsmul, hκadd, ih, map_nsmul, AddMonoidHom.nsmul_apply, hsymm, hκβ]
      push_cast; ring
  have h2ne : ∀ c : ZMod 7, c ≠ 0 → 2 * c ≠ 0 := by decide
  -- a nonzero vector
  have hD1 : 1 < Fintype.card D := by omega
  obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card hD1 0
  by_cases hκx : κ x = 0
  · exact ⟨x, hx, hκx⟩
  -- its orthogonal
  let K1 : AddSubgroup D := ⊤ ⊓ (β x).ker
  have hK1 : Fintype.card (⊤ : AddSubgroup D) ≤ 7 * Fintype.card K1 :=
    card_ker_ge (β x) ⊤
  have htop : Fintype.card (⊤ : AddSubgroup D) = Fintype.card D := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, AddSubgroup.card_top]
  rw [htop] at hK1
  have hK1' : 1 < Fintype.card K1 := by omega
  obtain ⟨⟨y, hyK⟩, hy⟩ := Fintype.exists_ne_of_one_lt_card hK1' 0
  have hy0 : y ≠ 0 := fun h => hy (by ext; simpa using h)
  have hxy : β x y = 0 := (AddSubgroup.mem_inf.1 hyK).2
  by_cases hκy : κ y = 0
  · exact ⟨y, hy0, hκy⟩
  let K2 : AddSubgroup D := K1 ⊓ (β y).ker
  have hK2 : Fintype.card K1 ≤ 7 * Fintype.card K2 := card_ker_ge (β y) K1
  have hK2' : 1 < Fintype.card K2 := by omega
  obtain ⟨⟨w, hwK⟩, hw⟩ := Fintype.exists_ne_of_one_lt_card hK2' 0
  have hw0 : w ≠ 0 := fun h => hw (by ext; simpa using h)
  have hxw : β x w = 0 := (AddSubgroup.mem_inf.1 (AddSubgroup.mem_inf.1 hwK).1).2
  have hyw : β y w = 0 := (AddSubgroup.mem_inf.1 hwK).2
  by_cases hκw : κ w = 0
  · exact ⟨w, hw0, hκw⟩
  obtain ⟨a, b, hab⟩ := pigeonhole7 (κ x) (κ y) (κ w) hκx hκy hκw
  refine ⟨a.val • x + b.val • y + w, ?_, ?_⟩
  · intro hv
    have h1 : β x (a.val • x + b.val • y + w) = 0 := by rw [hv, map_zero]
    rw [map_add, map_add, map_nsmul, map_nsmul, hκβ, hxy, hxw] at h1
    simp only [nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id', id_eq, mul_zero, add_zero] at h1
    have ha : a = 0 := by
      rcases mul_eq_zero.1 (show a * (2 * κ x) = 0 by linear_combination h1) with h | h
      · exact h
      · exact absurd h (h2ne _ hκx)
    have h2 : β y (a.val • x + b.val • y + w) = 0 := by rw [hv, map_zero]
    rw [map_add, map_add, map_nsmul, map_nsmul, hκβ, hyw, hsymm y x, hxy] at h2
    simp only [nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id', id_eq, mul_zero, zero_add,
      add_zero] at h2
    have hb : b = 0 := by
      rcases mul_eq_zero.1 (show b * (2 * κ y) = 0 by linear_combination h2) with h | h
      · exact h
      · exact absurd h (h2ne _ hκy)
    rw [ha, hb] at hv
    simp at hv
    exact hw0 hv
  · rw [hκadd, hκadd, hκsmul, hκsmul]
    simp only [map_add, map_nsmul, AddMonoidHom.add_apply, AddMonoidHom.nsmul_apply, hxy, hxw,
      hyw, smul_zero, add_zero, ZMod.natCast_val, ZMod.cast_id', id_eq]
    linear_combination hab

/-! ### The sum of seventh roots of unity, and quadratic sums modulo 7 -/

/-- `ψ a = exp(2πi a / 7)`. -/
def psi7 (a : ZMod 7) : ℂ := cexp (2 * π * I * (a.val : ℂ) / 7)

lemma exp_int_seven (m : ℤ) : cexp (2 * π * I * (m : ℂ) / 7) = psi7 (m : ZMod 7) := by
  unfold psi7
  have h := ZMod.val_intCast (n := 7) m
  -- `m = val + 7 q`
  obtain ⟨q, hq⟩ : ∃ q : ℤ, m = ((m : ZMod 7).val : ℤ) + 7 * q := by
    refine ⟨m / 7, ?_⟩
    rw [h]; push_cast; omega
  conv_lhs => rw [hq]
  rw [show 2 * π * I * ((((m : ZMod 7).val : ℤ) + 7 * q : ℤ) : ℂ) / 7
      = 2 * π * I * (((m : ZMod 7).val : ℕ) : ℂ) / 7 + q * (2 * π * I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma psi7_conj (a : ZMod 7) : (starRingEnd ℂ) (psi7 a) = psi7 (-a) := by
  unfold psi7
  rw [← Complex.exp_conj]
  have : (starRingEnd ℂ) (2 * π * I * (a.val : ℂ) / 7) = 2 * π * I * ((-(a.val : ℤ) : ℤ) : ℂ) / 7 := by
    rw [map_div₀, map_mul, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I, map_natCast,
      map_ofNat, map_ofNat]
    push_cast; ring
  rw [this, exp_int_seven]
  congr 1
  simp

lemma sum_zmod7 (f : ZMod 7 → ℂ) : ∑ a : ZMod 7, f a = ∑ i ∈ range 7, f (i : ZMod 7) := by
  refine Finset.sum_nbij' (fun a => a.val) (fun i => (i : ZMod 7)) ?_ ?_ ?_ ?_ ?_
  · intro a _; simp only [Finset.mem_coe, Finset.mem_range]; exact ZMod.val_lt a
  · intro i _; simp
  · intro a _; simp [ZMod.natCast_zmod_val]
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_range] at hi
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  · intro a _; simp [ZMod.natCast_zmod_val]

lemma sum_psi7 : ∑ a : ZMod 7, psi7 a = 0 := by
  have hζ := Complex.isPrimitiveRoot_exp 7 (by norm_num)
  have h := hζ.geom_sum_eq_zero (by norm_num)
  rw [← h, sum_zmod7]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  unfold psi7
  rw [← Complex.exp_nat_mul]
  congr 1
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  push_cast; ring

lemma count_seven : ∀ s a : ZMod 7, s ≠ 0 →
    (univ.filter (fun k : ZMod 7 => s * k ^ 2 = a)).card +
      (univ.filter (fun k : ZMod 7 => -(s * k ^ 2) = a)).card = 2 := by
  decide

lemma sum_square_seven (s : ZMod 7) (hs : s ≠ 0) (f : ZMod 7 → ℂ) :
    ∑ k : ZMod 7, (f (s * k ^ 2) + f (-(s * k ^ 2))) = 2 * ∑ a : ZMod 7, f a := by
  classical
  rw [Finset.sum_add_distrib,
    ← Finset.sum_fiberwise univ (fun k => s * k ^ 2) (fun k => f (s * k ^ 2)),
    ← Finset.sum_fiberwise univ (fun k => -(s * k ^ 2)) (fun k => f (-(s * k ^ 2))),
    ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have e1 : ∑ k ∈ univ.filter (fun k : ZMod 7 => s * k ^ 2 = a), f (s * k ^ 2)
      = ∑ k ∈ univ.filter (fun k : ZMod 7 => s * k ^ 2 = a), f a :=
    Finset.sum_congr rfl (fun k hk => by rw [(Finset.mem_filter.1 hk).2])
  have e2 : ∑ k ∈ univ.filter (fun k : ZMod 7 => -(s * k ^ 2) = a), f (-(s * k ^ 2))
      = ∑ k ∈ univ.filter (fun k : ZMod 7 => -(s * k ^ 2) = a), f a :=
    Finset.sum_congr rfl (fun k hk => by rw [(Finset.mem_filter.1 hk).2])
  rw [e1, e2, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, ← add_mul]
  have := count_seven s a hs
  rw [show ((univ.filter (fun k : ZMod 7 => s * k ^ 2 = a)).card : ℂ) +
      ((univ.filter (fun k : ZMod 7 => -(s * k ^ 2) = a)).card : ℂ) = 2 by exact_mod_cast this]

/-- A quadratic sum modulo `7` is never `-√7`. -/
lemma gauss7_ne (s : ℤ) :
    ∑ k : Fin 7, cexp (2 * π * I * ((s * (k : ℤ) ^ 2 : ℤ) : ℂ) / 7) ≠ -(Real.sqrt 7 : ℂ) := by
  intro hG
  have hterm : ∀ k : Fin 7, cexp (2 * π * I * ((s * (k : ℤ) ^ 2 : ℤ) : ℂ) / 7)
      = psi7 ((s : ZMod 7) * ((k : ℕ) : ZMod 7) ^ 2) := by
    intro k; rw [exp_int_seven]; push_cast; rfl
  simp_rw [hterm] at hG
  have hG' : ∑ k : ZMod 7, psi7 ((s : ZMod 7) * k ^ 2) = -(Real.sqrt 7 : ℂ) := by
    rw [← hG]; rfl
  by_cases hs : (s : ZMod 7) = 0
  · simp only [hs, zero_mul] at hG'
    rw [sum_const, card_univ, ZMod.card] at hG'
    have h1 : psi7 0 = 1 := by simp [psi7]
    rw [h1] at hG'
    have h7 : (0 : ℝ) < Real.sqrt 7 := Real.sqrt_pos.2 (by norm_num)
    have := congrArg Complex.re hG'
    simp at this <;> linarith
  · have hsum := sum_square_seven (s : ZMod 7) hs psi7
    rw [sum_psi7, mul_zero, Finset.sum_add_distrib, hG'] at hsum
    have hconj : ∑ k : ZMod 7, psi7 (-((s : ZMod 7) * k ^ 2)) = -(Real.sqrt 7 : ℂ) := by
      have := congrArg (starRingEnd ℂ) hG'
      rw [map_sum] at this
      simp_rw [psi7_conj] at this
      rw [this]; simp [Complex.conj_ofReal]
    rw [hconj] at hsum
    have h7 : (0 : ℝ) < Real.sqrt 7 := Real.sqrt_pos.2 (by norm_num)
    have := congrArg Complex.re hsum
    simp at this <;> linarith

/-! ### Lattices whose discriminant group is killed by `7` -/

variable {n : ℕ}

section Seven

variable {Q R : Matrix (Fin n) (Fin n) ℤ}

lemma Qq_seven : Qq ((7 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) = (7 : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
  ext i j
  rw [Qq, Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

lemma det_ne_zero_of_QR (hQR : Q * R = (7 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) : Q.det ≠ 0 := by
  have h := congrArg det hQR
  rw [det_mul, det_smul, det_one, mul_one, Fintype.card_fin] at h
  intro h0; rw [h0, zero_mul] at h
  exact (pow_ne_zero n (by norm_num : (7 : ℤ) ≠ 0)) h.symm

lemma RQ_of_QR (hQR : Q * R = (7 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) :
    R * Q = (7 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) := by
  have hq : Qq Q * ((1 / 7 : ℚ) • Qq R) = 1 := by
    rw [Matrix.mul_smul, ← Qq_mul, hQR, Qq_seven, smul_smul]; norm_num
  have hq' := mul_eq_one_comm.1 hq
  rw [Matrix.smul_mul, ← Qq_mul] at hq'
  ext i j
  have := congrFun (congrFun hq' i) j
  simp only [Matrix.smul_apply, Qq, Matrix.map_apply, smul_eq_mul, Matrix.one_apply] at this
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  split_ifs at this ⊢ with h
  · have : ((R * Q) i j : ℚ) = 7 := by linarith
    exact_mod_cast this
  · have : ((R * Q) i j : ℚ) = 0 := by linarith
    exact_mod_cast this

lemma R_symm (hs : Qᵀ = Q) (hQR : Q * R = (7 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) : Rᵀ = R := by
  have hRQ := RQ_of_QR hQR
  have h1 : Rᵀ * Q = (7 : ℤ) • 1 := by
    have := congrArg transpose hQR
    rw [transpose_mul, hs, transpose_smul, transpose_one] at this
    exact this
  -- `(Rᵀ - R) Q R = 7 (Rᵀ - R) = 0`
  have h2 : (Rᵀ - R) * (Q * R) = (7 : ℤ) • (Rᵀ - R) := by
    rw [hQR, Matrix.mul_smul, Matrix.mul_one]
  have h3 : (Rᵀ - R) * (Q * R) = 0 := by
    rw [← Matrix.mul_assoc, Matrix.sub_mul, h1, hRQ, sub_self, Matrix.zero_mul]
  rw [h3] at h2
  have h4 : Rᵀ - R = 0 := by
    ext i j
    have := congrFun (congrFun h2 i) j
    simp only [Matrix.zero_apply, Matrix.smul_apply, smul_eq_mul] at this
    simp only [Matrix.zero_apply]
    omega
  exact sub_eq_zero.1 h4

/-- `ρ(y, y') = yᵀ R y'` (so that `yᵀ Q⁻¹ y' = ρ(y, y') / 7`). -/
def rho (R : Matrix (Fin n) (Fin n) ℤ) (y y' : Fin n → ℤ) : ℤ := y ⬝ᵥ (R *ᵥ y')

variable (hs : Qᵀ = Q) (he : ∀ i, Even (Q i i))
  (hQR : Q * R = (7 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ))
include hs he hQR

lemma rho_symm (y y' : Fin n → ℤ) : rho R y y' = rho R y' y := by
  unfold rho
  rw [dotProduct_mulVec, ← mulVec_transpose, R_symm hs hQR, dotProduct_comm]

lemma rho_lat (y m : Fin n → ℤ) : rho R y (Q *ᵥ m) = 7 * (y ⬝ᵥ m) := by
  unfold rho
  rw [mulVec_mulVec, RQ_of_QR hQR, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]

lemma rho_even (y : Fin n → ℤ) : Even (rho R y y) := by
  have h := even_quad hs he (R *ᵥ y)
  rw [mulVec_mulVec, hQR, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul,
    dotProduct_comm] at h
  have : Even (7 * rho R y y) := by unfold rho; exact h
  rcases Int.even_mul.1 this with h7 | h7
  · exact absurd h7 (by decide)
  · exact h7

lemma qf_eq_rho (y : Fin n → ℤ) : qf Q y = (rho R y y : ℚ) / 7 := by
  have hinv : (Qq Q)⁻¹ = (1 / 7 : ℚ) • Qq R := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.mul_smul, ← Qq_mul, hQR, Qq_seven, smul_smul]; norm_num
  unfold qf bf rho
  rw [hinv, smul_mulVec, dotProduct_smul, ← vq_mulVec, vq_dot, smul_eq_mul]
  ring

lemma bf_eq_rho (y y' : Fin n → ℤ) : bf Q y y' = (rho R y y' : ℚ) / 7 := by
  have hinv : (Qq Q)⁻¹ = (1 / 7 : ℚ) • Qq R := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.mul_smul, ← Qq_mul, hQR, Qq_seven, smul_smul]; norm_num
  unfold bf rho
  rw [hinv, smul_mulVec, dotProduct_smul, ← vq_mulVec, vq_dot, smul_eq_mul]
  ring

lemma seven_mem_lat (y : Fin n → ℤ) : (7 : ℤ) • y ∈ lat Q :=
  mem_lat.2 ⟨R *ᵥ y, by rw [mulVec_mulVec, hQR, smul_mulVec, one_mulVec]⟩

/-- The `𝔽₇`-valued bilinear form on the discriminant group. -/
def betaR (R : Matrix (Fin n) (Fin n) ℤ) (Q : Matrix (Fin n) (Fin n) ℤ) (d d' : DQ Q) : ZMod 7 :=
  (rho R (rep Q d) (rep Q d') : ZMod 7)

/-- The `𝔽₇`-valued quadratic form (`κ = ρ(y,y)/2 = 4 ρ(y,y)` in `𝔽₇`). -/
def kappaR (R : Matrix (Fin n) (Fin n) ℤ) (Q : Matrix (Fin n) (Fin n) ℤ) (d : DQ Q) : ZMod 7 :=
  4 * (rho R (rep Q d) (rep Q d) : ZMod 7)

lemma rho_add_left (a b c : Fin n → ℤ) : rho R (a + b) c = rho R a c + rho R b c := by
  unfold rho; rw [add_dotProduct]

lemma rho_add_right (a b c : Fin n → ℤ) : rho R a (b + c) = rho R a b + rho R a c := by
  unfold rho; rw [mulVec_add, dotProduct_add]

lemma rho_mod (y y' m m' : Fin n → ℤ) :
    ((rho R (y + Q *ᵥ m) (y' + Q *ᵥ m') : ℤ) : ZMod 7) = (rho R y y' : ZMod 7) := by
  rw [rho_add_left hs he hQR, rho_add_right hs he hQR, rho_add_right hs he hQR,
    rho_lat hs he hQR, rho_symm hs he hQR (Q *ᵥ m), rho_lat hs he hQR,
    rho_symm hs he hQR (Q *ᵥ m), rho_lat hs he hQR]
  push_cast
  rw [show (7 : ZMod 7) = 0 by decide]
  ring

lemma betaR_mk (y y' : Fin n → ℤ) :
    betaR R Q (Submodule.Quotient.mk y) (Submodule.Quotient.mk y') = (rho R y y' : ZMod 7) := by
  obtain ⟨m, hm⟩ := rep_mk Q y
  obtain ⟨m', hm'⟩ := rep_mk Q y'
  unfold betaR; rw [hm, hm', rho_mod hs he hQR]

lemma kappaR_mk (y : Fin n → ℤ) :
    kappaR R Q (Submodule.Quotient.mk y) = 4 * (rho R y y : ZMod 7) := by
  obtain ⟨m, hm⟩ := rep_mk Q y
  unfold kappaR; rw [hm, rho_mod hs he hQR]

/-- **Isotropic vectors**: if `det Q ≥ 7³`, some `y ∉ Q ℤⁿ` has `14 ∣ yᵀ R y`
(i.e. `yᵀ Q⁻¹ y ∈ 2ℤ`). -/
theorem exists_isotropic (hdet : 343 ≤ Q.det) :
    ∃ y : Fin n → ℤ, y ∉ lat Q ∧ 14 ∣ rho R y y := by
  classical
  have hd := det_ne_zero_of_QR hQR
  haveI := finite_DQ hd
  letI : Fintype (DQ Q) := Fintype.ofFinite _
  have hcard : 343 ≤ Fintype.card (DQ Q) := by
    rw [← Nat.card_eq_fintype_card, card_DQ hd]; omega
  let β : DQ Q →+ DQ Q →+ ZMod 7 :=
    { toFun := fun d =>
        { toFun := fun d' => betaR R Q d d'
          map_zero' := by
            obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ d
            rw [← Submodule.Quotient.mk_zero, betaR_mk hs he hQR]; simp [rho]
          map_add' := by
            intro x y
            obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ d
            obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
            obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
            rw [← Submodule.Quotient.mk_add, betaR_mk hs he hQR, betaR_mk hs he hQR,
              betaR_mk hs he hQR, rho_add_right hs he hQR]; push_cast; ring }
      map_zero' := by
        ext d'
        obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ d'
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.zero_apply]
        rw [← Submodule.Quotient.mk_zero, betaR_mk hs he hQR]; simp [rho]
      map_add' := by
        intro x y
        ext d'
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ d'
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply]
        rw [← Submodule.Quotient.mk_add, betaR_mk hs he hQR, betaR_mk hs he hQR,
          betaR_mk hs he hQR, rho_add_left hs he hQR]; push_cast; ring }
  have hβ : ∀ x y, β x y = betaR R Q x y := fun x y => rfl
  obtain ⟨v, hv, hκv⟩ := exists_isotropic_abstract (kappaR R Q) β
    (by
      intro x y
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [hβ, hβ, betaR_mk hs he hQR, betaR_mk hs he hQR, rho_symm hs he hQR])
    (by
      intro x y
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [hβ, ← Submodule.Quotient.mk_add, kappaR_mk hs he hQR, kappaR_mk hs he hQR,
        kappaR_mk hs he hQR, betaR_mk hs he hQR, rho_add_left hs he hQR,
        rho_add_right hs he hQR, rho_add_right hs he hQR, rho_symm hs he hQR b a]
      push_cast
      have h7 : (7 : ZMod 7) = 0 := by decide
      linear_combination (rho R a b : ZMod 7) * h7)
    (by
      intro x
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [hβ, kappaR_mk hs he hQR, betaR_mk hs he hQR]
      have h7 : (7 : ZMod 7) = 0 := by decide
      linear_combination (-(rho R a a : ZMod 7)) * h7)
    hcard
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  refine ⟨y, ?_, ?_⟩
  · intro hy; apply hv; rw [Submodule.Quotient.mk_eq_zero]; exact hy
  · rw [kappaR_mk hs he hQR] at hκv
    have h7 : (7 : ℤ) ∣ rho R y y := by
      have : ((rho R y y : ℤ) : ZMod 7) = 0 := by
        have h2 : (2 : ZMod 7) * (4 * (rho R y y : ZMod 7)) = 0 := by rw [hκv, mul_zero]
        rw [← mul_assoc, show (2 : ZMod 7) * 4 = 1 by decide, one_mul] at h2
        exact h2
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).1 this
    obtain ⟨k, hk⟩ := rho_even hs he hQR y
    omega

end Seven

lemma qf_nsmul {Q : Matrix (Fin n) (Fin n) ℤ} (k : ℕ) (y : Fin n → ℤ) :
    qf Q (k • y) = (k : ℚ) ^ 2 * qf Q y := by
  unfold qf bf
  have : vq (k • y) = (k : ℚ) • vq y := by funext i; simp [vq]
  rw [this, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring

lemma exp_eleven : cexp (π * I * (44 : ℕ) / 4) = -1 := by
  rw [show (π : ℂ) * I * ((44 : ℕ) : ℂ) / 4 = π * I + (5 : ℤ) * (2 * π * I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_pi_mul_I]

/-- **Milgram in rank 44** excludes the determinants `1` and `7` when `7` kills the
discriminant group. -/
theorem det_ne_one_seven {Q R : Matrix (Fin 44) (Fin 44) ℤ} (hs : Qᵀ = Q) (he : ∀ i, Even (Q i i))
    (hQR : Q * R = (7 : ℤ) • (1 : Matrix (Fin 44) (Fin 44) ℤ))
    (hpos : ∀ x : Fin 44 → ℤ, x ≠ 0 → 0 < x ⬝ᵥ (Q *ᵥ x)) :
    Q.det ≠ 1 ∧ Q.det ≠ 7 := by
  classical
  obtain ⟨hdpos, hg⟩ := milgram hs he hpos
  rw [exp_eleven] at hg
  have hd := det_ne_zero_of_QR hQR
  haveI := finite_DQ hd
  letI : Fintype (DQ Q) := Fintype.ofFinite _
  have hcard : Fintype.card (DQ Q) = Q.det.natAbs := by
    rw [← Nat.card_eq_fintype_card, card_DQ hd]
  unfold gauss at hg
  rw [finsum_eq_sum_of_fintype] at hg
  constructor
  · intro h1
    rw [h1] at hcard hg
    simp only [Int.natAbs_one] at hcard
    obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.1 hcard
    rw [Fintype.sum_eq_single x (fun y hy => absurd (hx y) hy)] at hg
    have h0 : x = Submodule.Quotient.mk 0 := (hx _).symm
    rw [h0, phiQ_mk hs hd he] at hg
    have hv0 : vq (0 : Fin 44 → ℤ) = 0 := by funext i; simp [vq]
    simp only [phi, qf, bf, hv0, zero_dotProduct, Rat.cast_zero, mul_zero, Complex.exp_zero] at hg
    norm_num at hg
  · intro h7
    rw [h7] at hcard hg
    simp only [show (7 : ℤ).natAbs = 7 from rfl] at hcard
    obtain ⟨d0, hd0⟩ := Fintype.exists_ne_of_one_lt_card (by rw [hcard]; norm_num) (0 : DQ Q)
    have h7d : (7 : ℕ) • d0 = 0 := by
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ d0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      have := seven_mem_lat hs he hQR y
      simpa using this
    have hord : addOrderOf d0 = 7 := by
      have hdvd := addOrderOf_dvd_of_nsmul_eq_zero h7d
      rcases (Nat.dvd_prime (by norm_num)).1 hdvd with h | h
      · exact absurd (AddMonoid.addOrderOf_eq_one_iff.1 h) hd0
      · exact h
    let f : Fin 7 → DQ Q := fun k => (k : ℕ) • d0
    have hinj : Function.Injective f := by
      intro k k' hkk
      have := nsmul_injOn_Iio_addOrderOf (x := d0) (by rw [hord]; exact k.2)
        (by rw [hord]; exact k'.2) hkk
      exact Fin.ext this
    have hbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, by rw [hcard]; simp⟩
    rw [← Fintype.sum_bijective f hbij (fun k => phiQ Q (f k)) _ (fun k => rfl)] at hg
    obtain ⟨y0, rfl⟩ := Submodule.Quotient.mk_surjective _ d0
    obtain ⟨t, ht⟩ := rho_even hs he hQR y0
    have hterm : ∀ k : Fin 7, phiQ Q (f k)
        = cexp (2 * π * I * ((t * (k : ℤ) ^ 2 : ℤ) : ℂ) / 7) := by
      intro k
      simp only [f]
      rw [← Submodule.Quotient.mk_smul, phiQ_mk hs hd he]
      unfold phi
      rw [qf_nsmul, qf_eq_rho hs he hQR, ht]
      congr 1
      push_cast; ring
    simp_rw [hterm] at hg
    exact gauss7_ne t (by rw [hg]; simp)

end

end Conway99
