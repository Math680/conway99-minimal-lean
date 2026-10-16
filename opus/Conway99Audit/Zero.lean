import Conway99Audit.Final

/-!
# Part B, step 10: the case `z = 0` (§8) without enumeration

A short argument replaces the finite certificate of §8.

For `t ∈ I_k` (four orthogonal roots): `t` has no neighbour in `C_k ∪ I_k`, and for `c ≠ k`
it lies in `S_c`, hence has three neighbours in `I_c` and exactly two in `C_c` (one on each
side).  So `t` has `5` neighbours in `W`, whose weights add up to `6`.

If `z = 0` every point of `W` has weight `≥ 1`, so a neighbour of `t` in `W` has weight `≤ 2`.
A point `h` of weight `3` has three neighbours in `I_k` (`k` its zero direction): contradiction,
so `n₃ = 0`.  Then `Σ_W (wt-1)(wt-2) = 14` reads `6 n₄ = 14`: impossible.  Hence `z ≠ 0`,
which is exactly `Sec8`.
-/

open Finset SimpleGraph Matrix

namespace Conway99

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma wt_le_four (b : Fin 4 → V → ℤ) (u : V) : wt b u ≤ 4 := by
  simp only [wt, Fin.sum_univ_four]; split_ifs <;> norm_num

section SRG

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

namespace Quad

variable {b : Fin 4 → V → ℤ}

/-- A point of `I_k` has no neighbour in `C_k` and two in each `C_c`, `c ≠ k`. -/
lemma I_nbC (hQ : Quad G b) {k : Fin 4} {t : V} (ht : t ∈ Iset G (b k)) (c : Fin 4) :
    (G.neighborFinset t ∩ Cset (b c)).card = if c = k then 0 else 2 := by
  split_ifs with hck
  · subst hck; exact I_no_C hG (hQ.m4 c) (hQ.bip c) ht
  · have hnC : t ∉ Cset (b c) := fun h => Finset.disjoint_left.1 (hQ.C_disj_I hG c k) h ht
    have hnI : t ∉ Iset G (b c) := fun h => Finset.disjoint_left.1 (hQ.I_disj hG hck) h ht
    rw [nbC_card hG (hQ.m4 c) (hQ.bip c), if_neg hnC]
    rcases mem_S_or_I hG (hQ.bip c) hnC with ⟨hS, _⟩ | ⟨hI, _⟩
    · simp only [Sset, mem_filter] at hS; rw [hS.2.2]
    · exact absurd hI hnI

/-- A point of `I_k` has exactly five neighbours in `W`. -/
lemma I_degW (hQ : Quad G b) {k : Fin 4} {t : V} (ht : t ∈ Iset G (b k)) :
    (G.neighborFinset t ∩ Wset G b).card = 5 := by
  have hsplit := card_nb_split hG (b := b) t
  have hcoc := (Hp_props hG (hQ.m4 k) (hQ.bip k)).2.1
  have hI : ∀ c, (G.neighborFinset t ∩ Iset G (b c)).card = if c = k then 0 else 3 := by
    intro c
    split_ifs with hck
    · subst hck
      rw [card_eq_zero, eq_empty_iff_forall_notMem]
      intro x hx; rw [mem_inter, mem_neighborFinset] at hx
      exact hcoc t (mem_union_right _ ht) x (mem_union_right _ hx.2) hx.1
    · have hnC : t ∉ Cset (b c) := fun h => Finset.disjoint_left.1 (hQ.C_disj_I hG c k) h ht
      have hnI : t ∉ Iset G (b c) := fun h => Finset.disjoint_left.1 (hQ.I_disj hG hck) h ht
      rw [nbI hG (hQ.m4 c) (hQ.bip c) hnC]
      rcases mem_S_or_I hG (hQ.bip c) hnC with ⟨h, _⟩ | ⟨h, _⟩
      · rw [if_pos h]
      · exact absurd h hnI
  rw [hQ.nbIall hG t, Finset.sum_congr rfl (fun c _ => hI c)] at hsplit
  have : ∑ c : Fin 4, (if c = k then 0 else 3) = 9 := by fin_cases k <;> simp [Fin.sum_univ_four]
  omega

/-- The weights of the five `W`-neighbours of a point of `I_k` add up to `6`. -/
lemma I_wt_sum (hQ : Quad G b) {k : Fin 4} {t : V} (ht : t ∈ Iset G (b k)) :
    ∑ x ∈ G.neighborFinset t ∩ Wset G b, wt b x = 6 := by
  simp only [wt]
  rw [Finset.sum_comm]
  have e : ∀ c, ∑ x ∈ G.neighborFinset t ∩ Wset G b, (if x ∈ Cset (b c) then (1 : ℤ) else 0)
      = ((G.neighborFinset t ∩ Cset (b c)).card : ℤ) := by
    intro c
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter]
    congr 2
    ext x; simp only [mem_inter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, hQ.mem_W_of_C hG h3⟩, h3⟩
  simp only [e, hQ.I_nbC hG ht]
  fin_cases k <;> simp [Fin.sum_univ_four]

/-- **§8: `z ≠ 0`.**  Four pairwise orthogonal roots always leave a zero point in `W`. -/
theorem zero_exists (hQ : Quad G b) : ∃ o ∈ Wset G b, ∀ i, b i o = 0 := by
  by_contra hno
  push Not at hno
  have hwt1 : ∀ u ∈ Wset G b, 1 ≤ wt b u := by
    intro u hu
    obtain ⟨i, hi⟩ := hno u hu
    have := wt_ge (b := b) (x := u) {i} (by
      intro j hj; rw [mem_singleton] at hj; subst hj
      exact (mem_C_iff (hQ.bip j) u).2 hi)
    simpa using this
  -- no point of weight three
  have hno3 : ∀ h ∈ Wset G b, wt b h ≠ 3 := by
    intro h hh h3
    obtain ⟨k, hk⟩ : ∃ k, h ∉ Cset (b k) := by
      by_contra hall; push Not at hall
      rw [wt_eq_four hall] at h3; norm_num at h3
    have hI3 := hQ.nbI_W hG hh k
    rw [if_neg hk] at hI3
    obtain ⟨t, ht⟩ := card_pos.1 (by rw [hI3]; norm_num)
    rw [mem_inter, mem_neighborFinset] at ht
    have hs := hQ.I_wt_sum hG ht.2
    have hc := hQ.I_degW hG ht.2
    have hhN : h ∈ G.neighborFinset t ∩ Wset G b :=
      mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 ht.1.symm, hh⟩
    rw [← Finset.add_sum_erase _ _ hhN, h3] at hs
    have hle : ∑ x ∈ (G.neighborFinset t ∩ Wset G b).erase h, (1 : ℤ)
        ≤ ∑ x ∈ (G.neighborFinset t ∩ Wset G b).erase h, wt b x :=
      Finset.sum_le_sum (fun x hx => hwt1 x (mem_inter.1 (mem_of_mem_erase hx)).2)
    rw [sum_const, card_erase_of_mem hhN, hc] at hle
    norm_num at hle
    linarith
  -- then every term of Σ (wt-1)(wt-2) = 14 is 0 or 6
  have hs := hQ.sum_f hG
  have hdiv : ∀ u ∈ Wset G b, (6 : ℤ) ∣ (wt b u - 1) * (wt b u - 2) := by
    intro u hu
    have h1 := hwt1 u hu
    have h4 := wt_le_four b u
    have h3 := hno3 u hu
    have : wt b u = 1 ∨ wt b u = 2 ∨ wt b u = 4 := by omega
    rcases this with h | h | h <;> rw [h] <;> norm_num
  have := Finset.dvd_sum hdiv
  rw [hs] at this
  norm_num at this

end Quad

/-- The statement of §8 holds. -/
theorem sec8 : Sec8 G := fun _ hQ => hQ.zero_exists hG

/-- **No four pairwise orthogonal roots**, unconditionally. -/
theorem no_quad' {b : Fin 4 → V → ℤ} (hQ : Quad G b) : False := no_quad hG (sec8 hG) hQ

/-- **Part B of Theorem 1.1, unconditional**: for every even integral overlattice `L ⊇ N`
(profile coordinates), the dual minimum, the root shape, `Φ = A₁^ρ`, and `ρ ≤ 3`. -/
theorem partB_full (L : EvenOverlattice G) :
    (∀ z ∈ L.L, z ≠ 0 → 126 ≤ z ⬝ᵥ z) ∧
    (∀ z ∈ L.L, z ⬝ᵥ z = 126 → ∃ b : V → ℤ, z = (3 : ℤ) • b ∧ IsM4 G b ∧ Biplane G b) ∧
    (∀ z ∈ L.L, ∀ z' ∈ L.L, z ⬝ᵥ z = 126 → z' ⬝ᵥ z' = 126 → z' ≠ z → z' ≠ -z → z ⬝ᵥ z' = 0) ∧
    (∀ z : Fin 4 → V → ℤ, (∀ i, z i ∈ L.L) → (∀ i, z i ⬝ᵥ z i = 126) →
      (∀ i j, i ≠ j → z j ≠ z i ∧ z j ≠ -z i) → False) :=
  partB hG (sec8 hG) L

end SRG

end Conway99
