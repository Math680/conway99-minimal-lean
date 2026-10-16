import Conway99Audit.NHat

/-!
# Part C, step 7: rank 44, the overlattice `N̂` of determinant 49, and Theorem 1.1

* `card_basis`: every `ℤ`-basis of an even overlattice of `N` has `44` elements
  (`G₀ = B C`, `C B = 63 I`, and `G₀ / 63` is an idempotent of trace `44`).
* `extend`: if the Gram determinant is `≥ 7³`, an isotropic vector of the discriminant group
  (`exists_isotropic`) gives a strictly larger even overlattice with smaller determinant.
* `exists_det49`: starting from `N`, one reaches an even overlattice `N̂` whose Gram determinant
  is `49`: it is `7^k` (`Gram · R = 7 I`), `k ≤ 2` at the end, and Milgram excludes `k = 0, 1`.
* `theorem_1_1`: the full statement of Theorem 1.1 of the minimal proof.
-/

open Finset SimpleGraph Matrix

namespace Conway99

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

variable (G) in
/-- `G₀` over `ℚ`. -/
def G0q : Matrix V V ℚ := (G0 G).map (Int.cast : ℤ → ℚ)

lemma G0_diag (u : V) : G0 G u u = 28 := by
  simp only [G0, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    A_apply, J_apply, smul_eq_mul, G.loopless.irrefl u, if_false]
  norm_num

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

/-- `rank G₀ = 44`. -/
lemma rank_G0q : (G0q G).rank = 44 := by
  set E : Matrix V V ℚ := (1 / 63 : ℚ) • G0q G with hE
  have hG0q2 : G0q G * G0q G = (63 : ℚ) • G0q G := by
    have h := hG0G0 hG
    ext u v
    have h' := congrFun (congrFun h u) v
    simp only [G0q, Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at h' ⊢
    exact_mod_cast h'
  have hEE : E * E = E := by
    rw [hE, Matrix.smul_mul, Matrix.mul_smul, hG0q2, smul_smul, smul_smul]; norm_num
  have hidem : IsIdempotentElem (Matrix.toLin' E) := by
    show Matrix.toLin' E * Matrix.toLin' E = Matrix.toLin' E
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hEE]
  have htr := ((LinearMap.isProj_range_iff_isIdempotentElem _).2 hidem).trace
  have htrace : LinearMap.trace ℚ _ (Matrix.toLin' E) = Matrix.trace E := by
    rw [LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ V), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin']
  have htE : Matrix.trace E = 44 := by
    simp only [Matrix.trace, Matrix.diag, hE, Matrix.smul_apply, G0q, Matrix.map_apply, G0_diag,
      smul_eq_mul]
    rw [Finset.sum_const, card_univ, card_V hG]; norm_num
  have hrE : E.rank = 44 := by
    have : (E.rank : ℚ) = 44 := by
      rw [Matrix.rank, ← Matrix.toLin'_apply', ← htr, htrace, htE]
    exact_mod_cast this
  have h1 : E.rank ≤ (G0q G).rank := by
    rw [show E = G0q G * ((1 / 63 : ℚ) • (1 : Matrix V V ℚ)) by
      rw [hE, Matrix.mul_smul, Matrix.mul_one]]
    exact rank_mul_le_left _ _
  have h2 : (G0q G).rank ≤ E.rank := by
    rw [show G0q G = E * ((63 : ℚ) • (1 : Matrix V V ℚ)) by
      rw [hE, Matrix.mul_smul, Matrix.mul_one, smul_smul]; norm_num]
    exact rank_mul_le_left _ _
  omega

/-- **Rank 44**: every `ℤ`-basis of an even overlattice of `N` has `44` elements. -/
theorem card_basis (L : EvenOverlattice G) {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ L.L.toIntSubmodule) : Fintype.card ι = 44 := by
  set Bq : Matrix V ι ℚ := Matrix.of fun u j => (bv L b j u : ℚ) with hBq
  set Cq : Matrix ι V ℚ := Matrix.of fun j u => (Cmat hG L b j u : ℚ) with hCq
  have hBC : G0q G = Bq * Cq := by
    ext v u
    have h := congrFun (G0col_eq hG L b u) v
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
    simp only [G0q, Matrix.map_apply, Matrix.mul_apply, hBq, hCq, Matrix.of_apply]
    rw [h]; push_cast; apply Finset.sum_congr rfl; intro j _; ring
  have hCB : Cq * Bq = (63 : ℚ) • (1 : Matrix ι ι ℚ) := by
    ext j k
    have h := CB hG L b j k
    simp only [Matrix.mul_apply, hCq, hBq, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    split_ifs at h ⊢ with hjk
    · rw [mul_one]; exact_mod_cast h
    · rw [mul_zero]; exact_mod_cast h
  have hunit : IsUnit ((63 : ℚ) • (1 : Matrix ι ι ℚ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, det_smul, det_one, mul_one]
    exact isUnit_iff_ne_zero.2 (pow_ne_zero _ (by norm_num))
  have r1 : Fintype.card ι ≤ Bq.rank := by
    rw [← rank_of_isUnit _ hunit, ← hCB]; exact rank_mul_le_right _ _
  have r2 : Bq.rank ≤ Fintype.card ι := rank_le_card_width _
  have r3 : (G0q G).rank ≤ Bq.rank := by rw [hBC]; exact rank_mul_le_left _ _
  have r4 : Bq.rank ≤ (G0q G).rank := by
    rw [show Bq = G0q G * ((1 / 63 : ℚ) • Bq) by
      rw [Matrix.mul_smul, hBC, Matrix.mul_assoc, hCB, Matrix.mul_smul, Matrix.mul_one, smul_smul]
      norm_num]
    exact rank_mul_le_left _ _
  have := rank_G0q hG
  omega

omit hG in
/-- The Gram matrix is positive definite. -/
lemma gram_pos (L : EvenOverlattice G) {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ L.L.toIntSubmodule) (x : ι → ℤ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ (gram L b *ᵥ x) := by
  set w := ∑ j, x j • bv L b j with hw
  have hw0 : w ≠ 0 := by
    intro h; apply hx
    have : ∑ j, x j • bv L b j = ∑ j, (0 : ι → ℤ) j • bv L b j := by rw [← hw, h]; simp
    exact coef_unique L b this
  have h63 : 63 * (x ⬝ᵥ (gram L b *ᵥ x)) = w ⬝ᵥ w := by
    have e1 : w ⬝ᵥ w = ∑ i, ∑ j, x i * (x j * (63 * gram L b i j)) := by
      rw [hw, sum_dotProduct]
      simp only [smul_dotProduct, dotProduct_sum, dotProduct_smul, smul_eq_mul, ← gram_spec L b,
        Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
    have e2 : 63 * (x ⬝ᵥ (gram L b *ᵥ x)) = ∑ i, ∑ j, x i * (x j * (63 * gram L b i j)) := by
      simp only [dotProduct, mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
    rw [e1, e2]
  have hpos : 0 < w ⬝ᵥ w := by
    have hnn : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exact absurd (dotProduct_self_eq_zero.1 h.symm) hw0
  omega

/-- A basis of an even overlattice, indexed by `Fin 44`. -/
lemma exists_basis44 (L : EvenOverlattice G) :
    Nonempty (Module.Basis (Fin 44) ℤ L.L.toIntSubmodule) := by
  obtain ⟨r, b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ V) L.L.toIntSubmodule
  have hr := card_basis hG L b
  rw [Fintype.card_fin] at hr
  subst hr
  exact ⟨b⟩

/-- The Gram determinant is a positive power of... a power of `7`. -/
lemma gram_det_pow (L : EvenOverlattice G) (b : Module.Basis (Fin 44) ℤ L.L.toIntSubmodule) :
    ∃ k : ℕ, (gram L b).det = 7 ^ k := by
  have hs := gram_symm L b
  have he := gram_even L b
  have hpos := gram_pos L b
  obtain ⟨hdpos, -⟩ := milgram hs he hpos
  have h := congrArg det (gram_R hG L b)
  rw [det_mul, det_smul, det_one, mul_one, Fintype.card_fin] at h
  have hdvd : (gram L b).det.natAbs ∣ 7 ^ 44 := by
    have : (gram L b).det ∣ (7 : ℤ) ^ 44 := ⟨_, h.symm⟩
    have := Int.natAbs_dvd_natAbs.2 this
    simpa using this
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).1 hdvd
  refine ⟨k, ?_⟩
  have : ((gram L b).det.natAbs : ℤ) = (gram L b).det := Int.natAbs_of_nonneg hdpos.le
  rw [← this, hk]; push_cast; rfl

/-- **Extension step**: a Gram determinant `≥ 7³` can be decreased by a larger even
overlattice. -/
theorem extend (L : EvenOverlattice G) (b : Module.Basis (Fin 44) ℤ L.L.toIntSubmodule)
    (hdet : 343 ≤ (gram L b).det) :
    ∃ (L' : EvenOverlattice G) (b' : Module.Basis (Fin 44) ℤ L'.L.toIntSubmodule),
      L.L ≤ L'.L ∧ (gram L' b').det < (gram L b).det := by
  classical
  set Q := gram L b with hQ
  set R := Rmat hG L b with hR
  have hs : Qᵀ = Q := gram_symm L b
  have he : ∀ i, Even (Q i i) := gram_even L b
  have hQR : Q * R = (7 : ℤ) • (1 : Matrix (Fin 44) (Fin 44) ℤ) := gram_R hG L b
  obtain ⟨y, hy, h14⟩ := exists_isotropic hs he hQR hdet
  set z : V → ℤ := ∑ j, y j • wv hG L b j with hz
  have hzN : z ∈ Ndual G :=
    AddSubgroup.sum_mem _ (fun j _ => AddSubgroup.zsmul_mem _ (wv_Ndual hG L b j) _)
  have hzb : ∀ i, z ⬝ᵥ bv L b i = 63 * y i := by
    intro i
    rw [hz, sum_dotProduct]
    simp only [smul_dotProduct, wv_dot hG L b, smul_eq_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  have hzL : ∀ m ∈ L.L, 63 ∣ z ⬝ᵥ m := by
    intro m hm
    obtain ⟨x, rfl⟩ := exists_coef L b hm
    rw [dotProduct_sum]
    apply Finset.dvd_sum; intro k _
    rw [dotProduct_smul, hzb, smul_eq_mul]
    exact ⟨x k * y k, by ring⟩
  have h7z : (7 : ℤ) • z = ∑ k, (R *ᵥ y) k • bv L b k := by
    rw [hz, Finset.smul_sum]
    simp only [smul_comm (7 : ℤ) (y _), seven_wv hG L b, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    rw [← Finset.sum_smul]
    congr 1
    simp only [mulVec, dotProduct, hR]
    apply Finset.sum_congr rfl; intro j _; ring
  have hzz : z ⬝ᵥ z = 9 * rho R y y := by
    have h1 : z ⬝ᵥ ((7 : ℤ) • z) = 7 * (z ⬝ᵥ z) := by rw [dotProduct_smul, smul_eq_mul]
    rw [h7z, dotProduct_sum] at h1
    simp only [dotProduct_smul, hzb, smul_eq_mul] at h1
    have h2 : ∑ k, (R *ᵥ y) k * (63 * y k) = 63 * rho R y y := by
      unfold rho
      rw [dotProduct_comm, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _; ring
    omega
  have hz_notin : z ∉ L.L := by
    intro hzL'
    obtain ⟨x, hx⟩ := exists_coef L b hzL'
    apply hy
    refine mem_lat.2 ⟨x, ?_⟩
    funext i
    have h := hzb i
    rw [hx, sum_dotProduct] at h
    simp only [smul_dotProduct, smul_eq_mul] at h
    simp only [← gram_spec L b] at h
    have hsym : ∀ k, gram L b k i = gram L b i k := fun k => by
      have := congrFun (congrFun (gram_symm L b) i) k; rwa [transpose_apply] at this
    have : ∑ k, x k * (63 * gram L b k i) = 63 * (Q *ᵥ x) i := by
      simp only [hQ, mulVec, dotProduct, Finset.mul_sum, hsym]
      apply Finset.sum_congr rfl; intro k _; ring
    omega
  -- the larger lattice
  let L' : EvenOverlattice G :=
    { L := L.L ⊔ AddSubgroup.zmultiples z
      eig := by
        intro x hx
        have hle : L.L ⊔ AddSubgroup.zmultiples z ≤ Ndual G :=
          sup_le (le_Ndual hG L) ((AddSubgroup.zmultiples_le).2 hzN)
        exact (hle hx).1
      contains := fun c hc => (le_sup_left : L.L ≤ L.L ⊔ AddSubgroup.zmultiples z) (L.contains c hc)
      integral := by
        intro x hx x' hx'
        obtain ⟨l, hl, w, hw, rfl⟩ := AddSubgroup.mem_sup.1 hx
        obtain ⟨l', hl', w', hw', rfl⟩ := AddSubgroup.mem_sup.1 hx'
        obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hw
        obtain ⟨n', rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hw'
        obtain ⟨a1, ha1⟩ := L.integral l hl l' hl'
        obtain ⟨a2, ha2⟩ := hzL l hl
        obtain ⟨a3, ha3⟩ := hzL l' hl'
        obtain ⟨t, ht⟩ := h14
        have e : (l + n • z) ⬝ᵥ (l' + n' • z)
            = l ⬝ᵥ l' + n' * (z ⬝ᵥ l) + n * (z ⬝ᵥ l') + n * n' * (z ⬝ᵥ z) := by
          simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
          rw [dotProduct_comm l z]; ring
        rw [e, ha1, ha2, ha3, hzz, ht]
        exact ⟨a1 + n' * a2 + n * a3 + 2 * n * n' * t, by ring⟩
      even := by
        intro x hx
        obtain ⟨l, hl, w, hw, rfl⟩ := AddSubgroup.mem_sup.1 hx
        obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hw
        obtain ⟨u, hu⟩ := L.even l hl
        obtain ⟨a2, ha2⟩ := hzL l hl
        obtain ⟨t, ht⟩ := h14
        have e : (l + n • z) ⬝ᵥ (l + n • z)
            = l ⬝ᵥ l + 2 * n * (z ⬝ᵥ l) + n * n * (z ⬝ᵥ z) := by
          simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
          rw [dotProduct_comm l z]; ring
        rw [e, hu, ha2, hzz, ht]
        exact ⟨u + n * a2 + n * n * t, by ring⟩ }
  have hle : L.L ≤ L'.L := le_sup_left
  obtain ⟨b'⟩ := exists_basis44 hG L'
  refine ⟨L', b', hle, ?_⟩
  -- change of basis
  have hT : ∀ j, ∃ x : Fin 44 → ℤ, bv L b j = ∑ i, x i • bv L' b' i :=
    fun j => exists_coef L' b' (hle (bv_mem L b j))
  choose T hT using hT
  set Tm : Matrix (Fin 44) (Fin 44) ℤ := Matrix.of fun i j => T j i with hTm
  have hTij : ∀ i j, Tm i j = T j i := fun i j => rfl
  have hgram : Q = Tmᵀ * gram L' b' * Tm := by
    ext j k
    have h := gram_spec L b j k
    rw [hT j, hT k, sum_dotProduct] at h
    simp only [dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      ← gram_spec L' b'] at h
    simp only [Matrix.mul_apply, transpose_apply, hTm, Matrix.of_apply]
    have : (63 : ℤ) * Q j k = 63 * ∑ l, (∑ i, T j i * gram L' b' i l) * T k l := by
      rw [hQ, h, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro l _
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _; ring
    omega
  have hdetQ : Q.det = Tm.det * (gram L' b').det * Tm.det := by
    rw [hgram, det_mul, det_mul, det_transpose]
  -- `Tm` is not unimodular, otherwise `z ∈ L`
  have hTne : Tm.det ≠ 1 ∧ Tm.det ≠ -1 := by
    have key : ∀ k, Tm.det • bv L' b' k ∈ L.L := by
      intro k
      have : Tm.det • bv L' b' k = ∑ j, (Tm.adjugate j k) • bv L b j := by
        simp only [hT, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        rw [show Tm.det • bv L' b' k = ∑ i, (Tm.det * if i = k then 1 else 0) • bv L' b' i by
          simp [ite_smul]]
        apply Finset.sum_congr rfl; intro i _
        rw [← Finset.sum_smul]
        congr 1
        have hma := congrFun (congrFun (mul_adjugate Tm) i) k
        simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
          hTij] at hma
        rw [← hma]
        apply Finset.sum_congr rfl; intro j _; ring
      rw [this]
      exact AddSubgroup.sum_mem _ (fun j _ => AddSubgroup.zsmul_mem _ (bv_mem L b j) _)
    have hall : (∀ k, bv L' b' k ∈ L.L) → False := by
      intro hk
      apply hz_notin
      have hzL' : z ∈ L'.L :=
        (le_sup_right : AddSubgroup.zmultiples z ≤ L.L ⊔ AddSubgroup.zmultiples z)
          (AddSubgroup.mem_zmultiples z)
      obtain ⟨x, hx⟩ := exists_coef L' b' hzL'
      rw [hx]
      exact AddSubgroup.sum_mem _ (fun k _ => AddSubgroup.zsmul_mem _ (hk k) _)
    constructor
    · intro h1; apply hall; intro k; have := key k; rwa [h1, one_smul] at this
    · intro h1; apply hall; intro k; have := key k
      rw [h1, neg_one_smul] at this; exact neg_mem_iff.1 this
  have hQ'pos : 0 < (gram L' b').det :=
    (milgram (gram_symm L' b') (gram_even L' b') (gram_pos L' b')).1
  have hsq : 4 ≤ Tm.det * Tm.det := by
    rcases le_or_gt 2 Tm.det with h | h
    · nlinarith
    · rcases le_or_gt Tm.det (-2) with h' | h'
      · nlinarith
      · exfalso
        have h0 : Tm.det ≠ 0 := by
          intro h0; rw [h0] at hdetQ; simp at hdetQ; omega
        omega
  rw [hdetQ]
  nlinarith

/-- **`N̂` of determinant 49**: every even overlattice of `N` lies in one whose Gram
determinant is `49`. -/
theorem exists_det49 :
    ∀ (d : ℕ) (L : EvenOverlattice G) (b : Module.Basis (Fin 44) ℤ L.L.toIntSubmodule),
      (gram L b).det = d → ∃ (L' : EvenOverlattice G) (b' : Module.Basis (Fin 44) ℤ L'.L.toIntSubmodule),
        L.L ≤ L'.L ∧ (gram L' b').det = 49 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro L b hd
    by_cases h343 : 343 ≤ (gram L b).det
    · obtain ⟨L', b', hle, hlt⟩ := extend hG L b h343
      have hpos' := (milgram (gram_symm L' b') (gram_even L' b') (gram_pos L' b')).1
      obtain ⟨L'', b'', hle', h49⟩ := ih ((gram L' b').det.toNat) (by omega) L' b'
        (by rw [Int.toNat_of_nonneg hpos'.le])
      exact ⟨L'', b'', hle.trans hle', h49⟩
    · obtain ⟨k, hk⟩ := gram_det_pow hG L b
      have h17 := det_ne_one_seven (gram_symm L b) (gram_even L b) (gram_R hG L b) (gram_pos L b)
      refine ⟨L, b, le_rfl, ?_⟩
      rw [hk] at h343 h17 ⊢
      have hk3 : k < 3 := by
        by_contra h3
        apply h343
        calc (343 : ℤ) = 7 ^ 3 := by norm_num
          _ ≤ 7 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
      interval_cases k
      · exact absurd (by norm_num) h17.1
      · exact absurd (by norm_num) h17.2
      · norm_num

/-- The columns of `P` (the triangle vectors `x_L`, profile coordinates) lie in `N`. -/
lemma Pcol_mem (t : Tr G) : (fun u => P G u t) ∈ Nsub G := by
  have hcard : ((t.1.card : ℕ) : ℤ) = 3 := by exact_mod_cast T_card3 t.2
  have hsum : ∑ v, B G v t = 3 := by
    simp only [B_apply, Finset.sum_boole]
    rw [Finset.filter_mem_eq_inter, univ_inter]
    exact hcard
  refine ⟨fun v => B G v t, ⟨1, by rw [hsum]; norm_num⟩, ?_⟩
  funext u
  simp only [Nvec, P, Matrix.of_apply, mulVec, dotProduct, B_apply, sum_A_indicator]
  rw [show (∑ v, if v ∈ t.1 then (1 : ℤ) else 0) = 3 by
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, univ_inter]; exact hcard]
  norm_num

/-- **Theorem 1.1 (lattice part), fully formal**: there is an even integral lattice `N̂`
(profile coordinates) containing `N` and the triangle lattice `Λ`, every basis of which has
`44` elements, whose Gram determinant is `49`, with `min N̂* ≥ 2`, roots `= 3 ×` biplanes,
`Φ(N̂) = A₁^ρ` and `ρ ≤ 3`. -/
theorem theorem_1_1_lattice :
    ∃ L : EvenOverlattice G,
      (∀ t : Tr G, (fun u => P G u t) ∈ L.L) ∧
      (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ L.L.toIntSubmodule),
        Fintype.card ι = 44) ∧
      (∃ b : Module.Basis (Fin 44) ℤ L.L.toIntSubmodule, (gram L b).det = 49) ∧
      (∀ z ∈ L.L, z ≠ 0 → 126 ≤ z ⬝ᵥ z) ∧
      (∀ z ∈ L.L, z ⬝ᵥ z = 126 → ∃ b : V → ℤ, z = (3 : ℤ) • b ∧ IsM4 G b ∧ Biplane G b) ∧
      (∀ z ∈ L.L, ∀ z' ∈ L.L, z ⬝ᵥ z = 126 → z' ⬝ᵥ z' = 126 → z' ≠ z → z' ≠ -z →
        z ⬝ᵥ z' = 0) ∧
      (∀ z : Fin 4 → V → ℤ, (∀ i, z i ∈ L.L) → (∀ i, z i ⬝ᵥ z i = 126) →
        (∀ i j, i ≠ j → z j ≠ z i ∧ z j ≠ -z i) → False) := by
  obtain ⟨b0⟩ := exists_basis44 hG (Nlat G hG)
  have hpos0 := (milgram (gram_symm _ b0) (gram_even _ b0) (gram_pos _ b0)).1
  obtain ⟨L, b, hle, h49⟩ := exists_det49 hG ((gram (Nlat G hG) b0).det.toNat) (Nlat G hG) b0
    (by rw [Int.toNat_of_nonneg hpos0.le])
  refine ⟨L, fun t => hle (Pcol_mem hG t), fun b => card_basis hG L b, ⟨b, h49⟩, ?_⟩
  exact partB_full hG L

end

end Conway99
