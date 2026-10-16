import Conway99Audit.GaussLat
import Conway99Audit.FinGauss

/-!
# Part C, step 4: Milgram's formula

For `Q` symmetric, positive definite, with even diagonal (an even positive lattice of rank `n`):
`∑_{y ∈ ℤⁿ/Qℤⁿ} exp(π i yᵀQ⁻¹y) = √(det Q) · exp(π i n / 4)`.

Proof (algebraic reduction to rank one):
* `gauss_sub`: for `det P ≠ 0`, `gauss (Pᵀ Q P) = |det P| · gauss Q`
  (the sublattice `P ℤⁿ`; character orthogonality on the isotropic subgroup `L/L'`);
* `gauss_diag`: for a diagonal `Q`, the Gauss sum is a product of one-dimensional sums;
* `exists_diag`: some `Pᵀ Q P` is diagonal (orthogonal basis over `ℚ`, denominators cleared);
* `gauss_sum_even` (theta functions) evaluates the one-dimensional sums.
-/

open Complex Real Matrix Finset

namespace Conway99

noncomputable section

variable {n : ℕ}

/-- A chosen representative of a class. -/
def rep (M : Matrix (Fin n) (Fin n) ℤ) (d : DQ M) : Fin n → ℤ :=
  Classical.choose (Submodule.Quotient.mk_surjective (lat M) d)

lemma mk_rep (M : Matrix (Fin n) (Fin n) ℤ) (d : DQ M) :
    (Submodule.Quotient.mk (rep M d) : DQ M) = d :=
  Classical.choose_spec (Submodule.Quotient.mk_surjective (lat M) d)

lemma rep_mk (M : Matrix (Fin n) (Fin n) ℤ) (y : Fin n → ℤ) :
    ∃ m, rep M (Submodule.Quotient.mk y) = y + M *ᵥ m := by
  have h := mk_rep M (Submodule.Quotient.mk y)
  rw [Submodule.Quotient.eq] at h
  obtain ⟨m, hm⟩ := mem_lat.1 h
  exact ⟨m, by rw [hm]; abel⟩

/-- The quadratic character on the discriminant group. -/
def phiQ (Q : Matrix (Fin n) (Fin n) ℤ) (d : DQ Q) : ℂ := phi Q (rep Q d)

/-- The bilinear character. -/
def betaQ (Q : Matrix (Fin n) (Fin n) ℤ) (d e : DQ Q) : ℂ :=
  cexp (2 * π * I * (bf Q (rep Q d) (rep Q e) : ℂ))

/-- The Gauss sum of the lattice `(ℤⁿ, Q)`. -/
def gauss (Q : Matrix (Fin n) (Fin n) ℤ) : ℂ := ∑ᶠ d : DQ Q, phiQ Q d

lemma exp_two_pi_int (k : ℤ) : cexp (2 * π * I * (k : ℂ)) = 1 := by
  rw [show 2 * π * I * (k : ℂ) = k * (2 * π * I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

lemma exp_two_pi_eq_one {q : ℚ} (h : cexp (2 * π * I * (q : ℂ)) = 1) : ∃ k : ℤ, q = k := by
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have : (q : ℂ) = (k : ℂ) := by
    apply mul_left_cancel₀ h2; rw [hk]; ring
  exact_mod_cast this

section Basic

variable {Q : Matrix (Fin n) (Fin n) ℤ} (hs : Qᵀ = Q) (hd : Q.det ≠ 0) (he : ∀ i, Even (Q i i))
include hs hd he

lemma phiQ_mk (y : Fin n → ℤ) : phiQ Q (Submodule.Quotient.mk y) = phi Q y := by
  obtain ⟨m, hm⟩ := rep_mk Q y
  rw [phiQ, hm, phi_add_lat hs hd he]

lemma betaQ_mk (x y : Fin n → ℤ) :
    betaQ Q (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = cexp (2 * π * I * (bf Q x y : ℂ)) := by
  obtain ⟨m, hm⟩ := rep_mk Q x
  obtain ⟨m', hm'⟩ := rep_mk Q y
  rw [betaQ, hm, hm', bf_add_left hs hd, bf_add_right hs hd, bf_add_right hs hd,
    bf_lat_left hs hd, bf_lat_right hs hd, bf_lat_left hs hd]
  rw [show (2 * π * I * (((bf Q x y + ((m' ⬝ᵥ x : ℤ) : ℚ) +
      (((m ⬝ᵥ y : ℤ) : ℚ) + ((m ⬝ᵥ (Q *ᵥ m') : ℤ) : ℚ)) : ℚ)) : ℂ))
      = 2 * π * I * (bf Q x y : ℂ) + 2 * π * I * ((m' ⬝ᵥ x + m ⬝ᵥ y + m ⬝ᵥ (Q *ᵥ m') : ℤ) : ℂ) by
    push_cast; ring, Complex.exp_add, exp_two_pi_int, mul_one]

end Basic

/-! ### The sublattice `P ℤⁿ` -/

section Sub

variable {Q P : Matrix (Fin n) (Fin n) ℤ}

lemma vq_injective : Function.Injective (vq : (Fin n → ℤ) → (Fin n → ℚ)) := by
  intro x y h; funext i; have := congrFun h i; simp only [vq] at this; exact_mod_cast this

lemma transpose_sym (hs : Qᵀ = Q) : (Pᵀ * Q * P)ᵀ = Pᵀ * Q * P := by
  rw [transpose_mul, transpose_mul, transpose_transpose, hs, Matrix.mul_assoc]

lemma det_PQP : (Pᵀ * Q * P).det = P.det * Q.det * P.det := by
  rw [det_mul, det_mul, det_transpose]

lemma diag_PQP (hs : Qᵀ = Q) (he : ∀ i, Even (Q i i)) (i : Fin n) : Even ((Pᵀ * Q * P) i i) := by
  have e : (Pᵀ * Q * P) i i = (fun k => P k i) ⬝ᵥ (Q *ᵥ fun k => P k i) := by
    simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro k _; ring
  rw [e]; exact even_quad hs he _

lemma isUnit_Pq (hP : P.det ≠ 0) : IsUnit (Qq P).det := isUnit_Qq_det hP

lemma isUnit_PqT (hP : P.det ≠ 0) : IsUnit (Qq P)ᵀ.det := by
  rw [det_transpose]; exact isUnit_Qq_det hP

lemma inv_PQP (hd : Q.det ≠ 0) (hP : P.det ≠ 0) :
    ((Qq P)ᵀ * Qq Q * Qq P)⁻¹ = (Qq P)⁻¹ * (Qq Q)⁻¹ * ((Qq P)ᵀ)⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]

lemma key_PT (hd : Q.det ≠ 0) (hP : P.det ≠ 0) :
    Qq P * ((Qq P)⁻¹ * (Qq Q)⁻¹ * ((Qq P)ᵀ)⁻¹) * (Qq P)ᵀ = (Qq Q)⁻¹ := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_Pq hP), Matrix.one_mul,
    Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_PqT hP), Matrix.mul_one]

/-- `(Pᵀu)ᵀ (PᵀQP)⁻¹ (Pᵀv) = uᵀ Q⁻¹ v`. -/
lemma bf_PT (hd : Q.det ≠ 0) (hP : P.det ≠ 0) (u v : Fin n → ℤ) :
    bf (Pᵀ * Q * P) (Pᵀ *ᵥ u) (Pᵀ *ᵥ v) = bf Q u v := by
  unfold bf
  rw [vq_mulVec, vq_mulVec, Qq_mul, Qq_mul, ← Qq_transpose, inv_PQP hd hP]
  rw [mulVec_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, key_PT hd hP]

/-- `aᵀ (PᵀQP)⁻¹ PᵀQ k = aᵀ P⁻¹ k`. -/
lemma bf_PT_lat (hd : Q.det ≠ 0) (hP : P.det ≠ 0) (a k : Fin n → ℤ) :
    bf (Pᵀ * Q * P) a (Pᵀ *ᵥ (Q *ᵥ k)) = vq a ⬝ᵥ ((Qq P)⁻¹ *ᵥ vq k) := by
  unfold bf
  rw [vq_mulVec, vq_mulVec, Qq_mul, Qq_mul, ← Qq_transpose, inv_PQP hd hP,
    mulVec_mulVec, mulVec_mulVec]
  have : (Qq P)⁻¹ * (Qq Q)⁻¹ * ((Qq P)ᵀ)⁻¹ * (Qq P)ᵀ * Qq Q = (Qq P)⁻¹ := by
    rw [Matrix.mul_assoc ((Qq P)⁻¹ * (Qq Q)⁻¹), nonsing_inv_mul _ (isUnit_PqT hP), Matrix.mul_one,
      Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_Qq_det hd), Matrix.mul_one]
  rw [this]

end Sub

lemma vq_single (i : Fin n) : vq (Pi.single i (1 : ℤ)) = Pi.single i (1 : ℚ) := by
  funext j; simp only [vq, Pi.single_apply]; split_ifs <;> simp

/-- **Sublattice invariance**: `gauss (Pᵀ Q P) = |det P| · gauss Q`. -/
theorem gauss_sub {Q P : Matrix (Fin n) (Fin n) ℤ} (hs : Qᵀ = Q) (hd : Q.det ≠ 0)
    (he : ∀ i, Even (Q i i)) (hP : P.det ≠ 0) :
    gauss (Pᵀ * Q * P) = (P.det.natAbs : ℂ) * gauss Q := by
  classical
  have hs' := transpose_sym (P := P) hs
  have hd' : (Pᵀ * Q * P).det ≠ 0 := by
    rw [det_PQP]; exact mul_ne_zero (mul_ne_zero hP hd) hP
  have he' := diag_PQP (P := P) hs he
  have hdQP : (Q * P).det ≠ 0 := by rw [det_mul]; exact mul_ne_zero hd hP
  haveI := finite_DQ hd
  haveI := finite_DQ hd'
  haveI := finite_DQ hdQP
  letI : Fintype (DQ Q) := Fintype.ofFinite _
  letI : Fintype (DQ (Pᵀ * Q * P)) := Fintype.ofFinite _
  letI : Fintype (DQ (Q * P)) := Fintype.ofFinite _
  set Q' := Pᵀ * Q * P with hQ'
  suffices main : ∑ x : DQ Q', phiQ Q' x = (P.det.natAbs : ℂ) * ∑ x : DQ Q, phiQ Q x by
    unfold gauss
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    convert main using 3
  -- the isotropic subgroup `L / L'`
  let H : AddSubgroup (DQ Q') := ((lat (Pᵀ * Q)).map (lat Q').mkQ).toAddSubgroup
  have hmemH : ∀ h ∈ H, ∃ k, h = Submodule.Quotient.mk (Pᵀ *ᵥ (Q *ᵥ k)) := by
    intro h hh
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hh
    obtain ⟨k, rfl⟩ := mem_lat.1 hy
    exact ⟨k, by rw [mulVec_mulVec]; rfl⟩
  haveI : Fintype H := Fintype.ofFinite _
  have hβ : ∀ x h1 h2, betaQ Q' x (h1 + h2) = betaQ Q' x h1 * betaQ Q' x h2 := by
    intro x h1 h2
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨b1, rfl⟩ := Submodule.Quotient.mk_surjective _ h1
    obtain ⟨b2, rfl⟩ := Submodule.Quotient.mk_surjective _ h2
    rw [← Submodule.Quotient.mk_add, betaQ_mk hs' hd' he', betaQ_mk hs' hd' he',
      betaQ_mk hs' hd' he', bf_add_right hs' hd', ← Complex.exp_add]
    congr 1; push_cast; ring
  have hφ : ∀ x, ∀ h ∈ H, phiQ Q' (x + h) = phiQ Q' x * betaQ Q' x h := by
    intro x h hh
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨k, rfl⟩ := hmemH h hh
    rw [← Submodule.Quotient.mk_add, phiQ_mk hs' hd' he', phiQ_mk hs' hd' he',
      betaQ_mk hs' hd' he']
    unfold phi
    rw [qf_add hs' hd']
    have hq : qf Q' (Pᵀ *ᵥ (Q *ᵥ k)) = ((k ⬝ᵥ (Q *ᵥ k) : ℤ) : ℚ) := by
      unfold qf; rw [bf_PT hd hP]; exact qf_lat hs hd k
    rw [hq, ← Complex.exp_add]
    rw [show (π : ℂ) * I * (((qf Q' a + ((k ⬝ᵥ (Q *ᵥ k) : ℤ) : ℚ) +
          2 * bf Q' a (Pᵀ *ᵥ (Q *ᵥ k)) : ℚ)) : ℂ)
        = (π * I * (qf Q' a : ℂ) + 2 * π * I * (bf Q' a (Pᵀ *ᵥ (Q *ᵥ k)) : ℂ)) +
          π * I * ((k ⬝ᵥ (Q *ᵥ k) : ℤ) : ℂ) by push_cast; ring]
    rw [Complex.exp_add, exp_pi_I_even _ (even_quad hs he k), mul_one]
  rw [sum_eq_sum_good (phiQ Q') (betaQ Q') H hβ hφ]
  -- the embedding `ι : L*/L' ⊇ L*/... `, `[y] ↦ [Pᵀ y]`
  have hle : lat (Q * P) ≤ (lat Q').comap Pᵀ.mulVecLin := by
    intro y hy
    obtain ⟨m, rfl⟩ := mem_lat.1 hy
    rw [Submodule.mem_comap, mulVecLin_apply]
    exact mem_lat.2 ⟨m, by rw [hQ', mulVec_mulVec, Matrix.mul_assoc]⟩
  let ι := (lat (Q * P)).mapQ (lat Q') Pᵀ.mulVecLin hle
  have hι : ∀ y, ι (Submodule.Quotient.mk y) = Submodule.Quotient.mk (Pᵀ *ᵥ y) := by
    intro y; rw [Submodule.mapQ_apply]; rfl
  have hPT : Function.Injective (Pᵀ).mulVec :=
    mulVec_injective_of_det (by rw [det_transpose]; exact hP)
  have hι_inj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [hι, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨m, hm⟩ := mem_lat.1 hx
    rw [Submodule.Quotient.mk_eq_zero]
    refine mem_lat.2 ⟨m, ?_⟩
    apply hPT
    rw [← hm, mulVec_mulVec, hQ', Matrix.mul_assoc]
  have hgood : univ.filter (fun x => ∀ h ∈ H, betaQ Q' x h = 1) = univ.map ⟨ι, hι_inj⟩ := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro hx
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have hint : ∀ i, ∃ z : ℤ, (vq a ⬝ᵥ ((Qq P)⁻¹ *ᵥ vq (Pi.single i 1))) = z := by
        intro i
        have h1 := hx (Submodule.Quotient.mk (Pᵀ *ᵥ (Q *ᵥ Pi.single i 1)))
          (Submodule.mem_map.2 ⟨_, mulVec_mem_lat _ (Pi.single i 1), by
            rw [← mulVec_mulVec]; rfl⟩)
        rw [betaQ_mk hs' hd' he', bf_PT_lat hd hP] at h1
        exact exp_two_pi_eq_one h1
      choose z hz using hint
      refine ⟨Submodule.Quotient.mk z, ?_⟩
      rw [hι]
      congr 1
      apply vq_injective
      have hvz : vq z = vq a ᵥ* (Qq P)⁻¹ := by
        funext i
        have h1 := hz i
        rw [vq_single, mulVec_single_one] at h1
        show (z i : ℚ) = _
        rw [← h1]
        simp only [vecMul, dotProduct]
        rfl
      rw [vq_mulVec, ← Qq_transpose, mulVec_transpose, hvz, vecMul_vecMul,
        nonsing_inv_mul _ (isUnit_Pq hP), vecMul_one]
    · rintro ⟨y', rfl⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y'
      intro h hh
      obtain ⟨k, rfl⟩ := hmemH h hh
      rw [hι, betaQ_mk hs' hd' he', bf_PT hd hP, bf_lat_right hs hd, Rat.cast_intCast]
      exact exp_two_pi_int _
  rw [hgood, Finset.sum_map]
  -- the projection `π : L*/L' → L*/L`
  have hle2 : lat (Q * P) ≤ lat Q := by
    intro y hy
    obtain ⟨m, rfl⟩ := mem_lat.1 hy
    exact mem_lat.2 ⟨P *ᵥ m, by rw [mulVec_mulVec]⟩
  let πm := Submodule.factor hle2
  have hπ : ∀ y, πm (Submodule.Quotient.mk y) = Submodule.Quotient.mk y := by
    intro y; exact Submodule.factor_mk hle2 y
  have hπs : Function.Surjective πm := by
    intro b
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    exact ⟨_, hπ y⟩
  have hcompat : ∀ a, phiQ Q' (ι a) = phiQ Q (πm a) := by
    intro a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    rw [hι, hπ, phiQ_mk hs' hd' he', phiQ_mk hs hd he]
    unfold phi qf; rw [bf_PT hd hP]
  simp only [Function.Embedding.coeFn_mk, hcompat]
  have key := sum_comp_surj πm.toAddMonoidHom hπs (phiQ Q)
  have c1 : Fintype.card (DQ Q) = Q.det.natAbs := by
    rw [← Nat.card_eq_fintype_card, card_DQ hd]
  have c2 : Fintype.card (DQ (Q * P)) = Q.det.natAbs * P.det.natAbs := by
    rw [← Nat.card_eq_fintype_card, card_DQ hdQP, det_mul, Int.natAbs_mul]
  rw [c1, c2] at key
  have hQn : (Q.det.natAbs : ℂ) ≠ 0 := by exact_mod_cast Int.natAbs_ne_zero.2 hd
  apply mul_left_cancel₀ hQn
  simp only [LinearMap.toAddMonoidHom_coe] at key
  push_cast at key ⊢
  linear_combination key

/-! ### Diagonal lattices -/

section Diag

variable (d : Fin n → ℤ)

lemma qf_diag (hd0 : ∀ i, d i ≠ 0) (y : Fin n → ℤ) :
    qf (diagonal d) y = ∑ i, (y i : ℚ) ^ 2 / (d i : ℚ) := by
  have hQq : Qq (diagonal d) = diagonal (fun i => (d i : ℚ)) := by
    ext i j; simp only [Qq, Matrix.map_apply, diagonal_apply]; split_ifs <;> simp
  have hinv : (Qq (diagonal d))⁻¹ = diagonal (fun i => ((d i : ℚ))⁻¹) := by
    rw [hQq]
    apply Matrix.inv_eq_right_inv
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have : (d i : ℚ) ≠ 0 := by exact_mod_cast hd0 i
    field_simp
  unfold qf bf
  rw [hinv]
  simp only [dotProduct, mulVec_diagonal, vq]
  apply Finset.sum_congr rfl; intro i _
  field_simp

/-- Gauss sum of a diagonal even positive lattice: a product of one-dimensional sums. -/
theorem gauss_diag (hpos : ∀ i, 0 < d i) (hev : ∀ i, Even (d i)) :
    gauss (diagonal d) = ∏ i, ((Real.sqrt (d i) : ℂ) * cexp (π * I / 4)) := by
  classical
  have hd0 : ∀ i, d i ≠ 0 := fun i => (hpos i).ne'
  have hs : (diagonal d)ᵀ = diagonal d := diagonal_transpose d
  have hdet : (diagonal d).det ≠ 0 := by
    rw [det_diagonal]; exact Finset.prod_ne_zero_iff.2 (fun i _ => hd0 i)
  have he : ∀ i, Even ((diagonal d) i i) := fun i => by rw [diagonal_apply_eq]; exact hev i
  haveI := finite_DQ hdet
  letI : Fintype (DQ (diagonal d)) := Fintype.ofFinite _
  -- the box of representatives
  let f : ((i : Fin n) → Fin (d i).toNat) → DQ (diagonal d) :=
    fun x => Submodule.Quotient.mk (fun i => ((x i : ℕ) : ℤ))
  have hf : Function.Bijective f := by
    constructor
    · intro x x' hxx
      simp only [f, Submodule.Quotient.eq] at hxx
      obtain ⟨m, hm⟩ := mem_lat.1 hxx
      funext i
      have hi := congrFun hm i
      rw [mulVec_diagonal] at hi
      simp only [Pi.sub_apply] at hi
      have hn1 : (0 : ℤ) ≤ ((x i : ℕ) : ℤ) := Int.natCast_nonneg _
      have hn2 : (0 : ℤ) ≤ ((x' i : ℕ) : ℤ) := Int.natCast_nonneg _
      have h1 := (x i).2
      have h2 := (x' i).2
      have hpi := hpos i
      have hx1 : ((x i : ℕ) : ℤ) < d i := by
        have := Int.toNat_of_nonneg hpi.le; omega
      have hx2 : ((x' i : ℕ) : ℤ) < d i := by
        have := Int.toNat_of_nonneg hpi.le; omega
      have hm0 : m i = 0 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · have : d i * m i ≤ d i * (-1) := mul_le_mul_of_nonneg_left (by omega) hpi.le
          linarith
        · have : d i * 1 ≤ d i * m i := mul_le_mul_of_nonneg_left (by omega) hpi.le
          linarith
      rw [hm0, mul_zero] at hi
      ext; omega
    · intro q
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      refine ⟨fun i => ⟨(y i % d i).toNat, ?_⟩, ?_⟩
      · have h1 := Int.emod_nonneg (y i) (hd0 i)
        have h2 := Int.emod_lt_of_pos (y i) (hpos i)
        omega
      · simp only [f, Submodule.Quotient.eq]
        refine mem_lat.2 ⟨fun i => -(y i / d i), ?_⟩
        funext i
        rw [mulVec_diagonal]
        have h1 := Int.emod_nonneg (y i) (hd0 i)
        simp only [Pi.sub_apply, Int.toNat_of_nonneg h1]
        have := Int.emod_add_mul_ediv (y i) (d i)
        linarith
  unfold gauss
  rw [finsum_eq_sum_of_fintype]
  rw [← Fintype.sum_equiv (Equiv.ofBijective f hf) (fun x => phiQ (diagonal d) (f x)) _
    (fun x => rfl)]
  simp only [f, phiQ_mk hs hdet he]
  have hphi : ∀ x : ((i : Fin n) → Fin (d i).toNat),
      phi (diagonal d) (fun i => ((x i : ℕ) : ℤ))
        = ∏ i, cexp (π * I * ((x i : ℕ) : ℂ) ^ 2 / (d i : ℂ)) := by
    intro x
    unfold phi
    rw [qf_diag d hd0, ← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; ring
  simp only [hphi]
  rw [← Fintype.prod_sum (fun i (j : Fin (d i).toNat) => cexp (π * I * ((j : ℕ) : ℂ) ^ 2 / (d i : ℂ)))]
  apply Finset.prod_congr rfl
  intro i _
  have hc : 0 < (d i).toNat := by have := hpos i; omega
  have hce : Even (d i).toNat := by
    obtain ⟨k, hk⟩ := hev i
    refine ⟨k.toNat, ?_⟩
    have := hpos i
    omega
  have hcast : (((d i).toNat : ℕ) : ℂ) = (d i : ℂ) := by
    have := Int.toNat_of_nonneg (hpos i).le
    exact_mod_cast this
  have hcastR : (((d i).toNat : ℕ) : ℝ) = (d i : ℝ) := by
    have := Int.toNat_of_nonneg (hpos i).le
    exact_mod_cast this
  have h := gauss_sum_even (d i).toNat hc hce
  rw [hcast, hcastR] at h
  rw [← h, ← Fin.sum_univ_eq_sum_range (fun x => cexp (π * I * (x : ℂ) ^ 2 / (d i : ℂ)))]

end Diag

/-! ### Diagonalisation over `ℤ` -/

lemma clear_denominators (u : Fin n → ℚ) :
    ∃ (c : ℕ) (w : Fin n → ℤ), 0 < c ∧ ∀ i, (w i : ℚ) = c * u i := by
  refine ⟨∏ i, (u i).den, fun i => (u i).num * ∏ k ∈ univ.erase i, ((u k).den : ℤ), ?_, ?_⟩
  · exact Finset.prod_pos (fun i _ => (u i).den_pos)
  · intro i
    push_cast
    rw [← Finset.mul_prod_erase univ (fun k => ((u k).den : ℚ)) (mem_univ i)]
    rw [show ((u i).den : ℚ) * (∏ k ∈ univ.erase i, ((u k).den : ℚ)) * u i
        = (∏ k ∈ univ.erase i, ((u k).den : ℚ)) * (u i * (u i).den) by ring, Rat.mul_den_eq_num]
    ring

/-- There is an integer matrix `P`, `det P ≠ 0`, with `Pᵀ Q P` diagonal. -/
theorem exists_diag {Q : Matrix (Fin n) (Fin n) ℤ} (hs : Qᵀ = Q) :
    ∃ P : Matrix (Fin n) (Fin n) ℤ, P.det ≠ 0 ∧ ∀ i j, i ≠ j → (Pᵀ * Q * P) i j = 0 := by
  classical
  let B : LinearMap.BilinForm ℚ (Fin n → ℚ) := Matrix.toBilin' (Qq Q)
  have hB : B.IsSymm := by
    refine ⟨fun x y => ?_⟩
    simp only [B, Matrix.toBilin'_apply']
    rw [dotProduct_mulVec, ← mulVec_transpose, Qq_transpose, hs, dotProduct_comm]
  haveI : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
  obtain ⟨v0, hv0⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.1 hB)
  have hfr : Module.finrank ℚ (Fin n → ℚ) = n := Module.finrank_fin_fun ℚ
  let v := v0.reindex (finCongr hfr)
  have hv : ∀ i j, i ≠ j → B (v i) (v j) = 0 := by
    intro i j hij
    simp only [v, Module.Basis.reindex_apply]
    exact hv0 (fun h => hij (by simpa using congrArg (finCongr hfr) h))
  choose c w hc hw using fun j => clear_denominators (v j)
  let P : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => w j i
  have hPq : Qq P = (Pi.basisFun ℚ (Fin n)).toMatrix v * diagonal (fun j => (c j : ℚ)) := by
    ext i j
    simp only [Qq, P, Matrix.map_apply, Matrix.of_apply, Matrix.mul_diagonal,
      Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [hw j i]; ring
  refine ⟨P, ?_, ?_⟩
  · intro h0
    have h1 : (Qq P).det = 0 := by rw [Qq_det, h0]; simp
    rw [hPq, det_mul, det_diagonal] at h1
    rcases mul_eq_zero.1 h1 with h | h
    · rw [← Module.Basis.det_apply] at h
      exact (Module.Basis.isUnit_det _ v).ne_zero h
    · rw [Finset.prod_eq_zero_iff] at h
      obtain ⟨j, _, hj⟩ := h
      exact (Nat.cast_ne_zero.2 (hc j).ne') hj
  · intro i j hij
    have h1 : (Qq (Pᵀ * Q * P)) i j = 0 := by
      rw [Qq_mul, Qq_mul, ← Qq_transpose]
      have : ((Qq P)ᵀ * Qq Q * Qq P) i j = (c i : ℚ) * c j * B (v i) (v j) := by
        simp only [B, Matrix.toBilin'_apply', Matrix.mul_apply, transpose_apply, dotProduct,
          mulVec, Qq, P, Matrix.map_apply, Matrix.of_apply, hw]
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro l _
        ring
      rw [this, hv i j hij, mul_zero]
    simpa [Qq] using h1

/-! ### Milgram -/

/-- **Milgram's formula** for an even positive definite lattice `(ℤⁿ, Q)`:
`gauss Q = √(det Q) · exp (π i n / 4)`, and `det Q > 0`. -/
theorem milgram {Q : Matrix (Fin n) (Fin n) ℤ} (hs : Qᵀ = Q) (he : ∀ i, Even (Q i i))
    (hpos : ∀ x : Fin n → ℤ, x ≠ 0 → 0 < x ⬝ᵥ (Q *ᵥ x)) :
    0 < Q.det ∧ gauss Q = (Real.sqrt (Q.det : ℝ) : ℂ) * cexp (π * I * n / 4) := by
  obtain ⟨P, hP, hdiag⟩ := exists_diag hs
  set D := Pᵀ * Q * P with hD
  have hcol : ∀ i, (fun k => P k i) ≠ 0 := by
    intro i h0
    apply hP
    apply Matrix.det_eq_zero_of_column_eq_zero i
    intro k; exact congrFun h0 k
  have hDii : ∀ i, D i i = (fun k => P k i) ⬝ᵥ (Q *ᵥ fun k => P k i) := by
    intro i
    simp only [hD, Matrix.mul_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro k _; ring
  have hDpos : ∀ i, 0 < D i i := fun i => by rw [hDii]; exact hpos _ (hcol i)
  have hDev : ∀ i, Even (D i i) := fun i => diag_PQP hs he i
  have hDdiag : D = diagonal (fun i => D i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [diagonal_apply_ne _ hij]; exact hdiag i j hij
  have hdetD : D.det = ∏ i, D i i := by rw [hDdiag, det_diagonal]; simp
  have hdetD' : D.det = P.det * Q.det * P.det := det_PQP
  have hDdet_pos : 0 < D.det := by rw [hdetD]; exact Finset.prod_pos (fun i _ => hDpos i)
  have hQpos : 0 < Q.det := by
    rw [hdetD'] at hDdet_pos
    have hPP : 0 < P.det * P.det := mul_self_pos.2 hP
    have : 0 < (P.det * P.det) * Q.det := by linarith [hDdet_pos]
    exact pos_of_mul_pos_right this hPP.le
  refine ⟨hQpos, ?_⟩
  have hsub := gauss_sub hs hQpos.ne' he hP
  have hdg := gauss_diag (fun i => D i i) hDpos hDev
  rw [← hDdiag] at hdg
  rw [hdg, Finset.prod_mul_distrib, Finset.prod_const, card_univ, Fintype.card_fin,
    ← Complex.exp_nat_mul] at hsub
  have hsqrt : ∏ i, (Real.sqrt (D i i : ℝ) : ℂ) = (P.det.natAbs : ℂ) * Real.sqrt (Q.det : ℝ) := by
    rw [← Complex.ofReal_prod, ← Real.sqrt_prod _ (fun i _ => by exact_mod_cast (hDpos i).le)]
    have : (∏ i, (D i i : ℝ)) = ((P.det.natAbs : ℝ)) ^ 2 * (Q.det : ℝ) := by
      have h1 : (∏ i, (D i i : ℝ)) = ((D.det : ℤ) : ℝ) := by rw [hdetD]; push_cast; rfl
      rw [h1, hdetD', Int.cast_mul, Int.cast_mul, Nat.cast_natAbs, Int.cast_abs, sq_abs]; ring
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    push_cast; ring
  rw [hsqrt] at hsub
  have hPn : (P.det.natAbs : ℂ) ≠ 0 := by exact_mod_cast Int.natAbs_ne_zero.2 hP
  apply mul_left_cancel₀ hPn
  rw [← hsub]
  rw [show (n : ℂ) * (π * I / 4) = π * I * n / 4 by ring]
  ring

end

end Conway99
