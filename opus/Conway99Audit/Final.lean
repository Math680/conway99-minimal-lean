import Conway99Audit.One3

/-!
# Part B, final assembly (§10)

* `Quad.no_zero_point`: four orthogonal roots admit no zero-signature point in `W` (§§7, 9).
* `Sec8 G`: the statement of §8 (`z ≠ 0`, i.e. a zero point exists), the only finite
  enumeration of the paper.  It is an explicit hypothesis here.
* `rho_le_three`: with `Sec8`, an even integral overlattice of `N` has no four roots that are
  pairwise neither equal nor opposite, i.e. `ρ ≤ 3`.
-/

open Finset SimpleGraph Matrix

namespace Conway99

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Cset_neg (b : V → ℤ) : Cset (-b) = Cset b := by
  rw [Cset, Cset, pos_neg_neg, neg_neg_pos, union_comm]

variable (G) in
/-- The statement proved by the finite certificate of §8: for four pairwise orthogonal roots,
`W` contains a point of zero signature (`z ≠ 0`). -/
def Sec8 : Prop := ∀ b : Fin 4 → V → ℤ, Quad G b → ∃ o ∈ Wset G b, ∀ i, b i o = 0

section SRG

variable (hG : G.IsSRGWith 99 14 1 2)
include hG

/-- §§7 and 9: no zero point.  (Orient the roots so that the first neighbour of `o` is
positive, then apply `OneCfg.contra`.) -/
theorem Quad.no_zero_point {b : Fin 4 → V → ℤ} (hQ : Quad G b) {o : V} (ho : o ∈ Wset G b)
    (hz : ∀ i, b i o = 0) : False := by
  obtain ⟨x, y, hxy, hset, hsig⟩ := hQ.zero_nbrs hG ho hz
  have hcov := hQ.cover hG ho hz hxy hset hsig
  set b' : Fin 4 → V → ℤ := fun i => if b i x = 1 then b i else -b i with hb'
  have hcase : ∀ i, (b' i = b i) ∨ (b' i = -b i) := by
    intro i; by_cases h : b i x = 1
    · left; simp [hb', h]
    · right; simp [hb', h]
  have hQ' : Quad G b' := by
    refine ⟨fun i => ?_, fun i => ?_, fun i j hij => ?_⟩
    · rcases hcase i with h | h <;> rw [h]
      · exact hQ.m4 i
      · exact (hQ.m4 i).neg
    · rcases hcase i with h | h <;> rw [h]
      · exact hQ.bip i
      · exact (hQ.bip i).neg'
    · have := hQ.orth i j hij
      rcases hcase i with h | h <;> rcases hcase j with h' | h' <;> rw [h, h'] <;>
        simp [dotProduct_neg, neg_dotProduct, this]
  have hI : ∀ i, Iset G (b' i) = Iset G (b i) := by
    intro i; rcases hcase i with h | h <;> rw [h]
    exact Iset_neg hG (hQ.m4 i) (hQ.bip i)
  have hW : Wset G b' = Wset G b := by
    rw [Wset, Wset, Iall, Iall]; simp only [hI]
  have hC : ∀ i, Cset (b' i) = Cset (b i) := by
    intro i; rcases hcase i with h | h <;> rw [h]
    exact Cset_neg (b i)
  have hwt : ∀ u, wt b' u = wt b u := by intro u; simp only [wt, hC]
  have hx1 : ∀ i, b' i x = 1 := by
    intro i; rcases hsig i with h | h
    · simp [hb', h.1]
    · simp [hb', h.1]
  have hy1 : ∀ i, b' i y = -1 := by
    intro i; rcases hsig i with h | h
    · simp [hb', h.1, h.2]
    · simp [hb', h.1, h.2]
  have ho' : ∀ i, b' i o = 0 := by
    intro i; rcases hcase i with h | h <;> rw [h]
    · exact hz i
    · simp [hz i]
  have hR : ∀ i j : Fin 4, ∃ r : V, i ≠ j → b' i r = 1 ∧ b' j r = -1 := by
    intro i j
    by_cases hij : i = j
    · exact ⟨o, fun h => absurd hij h⟩
    · have hc := (rel31 hG (hQ'.m4 i) (hQ'.bip i) (hQ'.m4 j) (hQ'.bip j) (hQ'.orth i j hij)).2.2.2.1
      obtain ⟨r, hr⟩ := card_pos.1 (by rw [hc]; norm_num)
      rw [mem_inter, mem_pos, mem_neg] at hr
      exact ⟨r, fun _ => hr⟩
  choose R hR using hR
  have C : OneCfg G b' o x y R :=
    { Q := hQ'
      oW := by rw [hW]; exact ho
      oz := ho'
      vw := hxy
      onb := by rw [hW]; exact hset
      v1 := hx1
      w1 := hy1
      cov := by
        intro u hu h1 h2 h3
        rw [hwt]; rw [hW] at hu; exact hcov u hu h1 h2 h3
      R1 := hR }
  exact C.contra hG

/-- With §8, there are no four pairwise orthogonal roots. -/
theorem no_quad (h8 : Sec8 G) {b : Fin 4 → V → ℤ} (hQ : Quad G b) : False := by
  obtain ⟨o, ho, hz⟩ := h8 b hQ
  exact hQ.no_zero_point hG ho hz

/-- **ρ ≤ 3.**  In every even integral overlattice of `N` (profile coordinates), there are no
four roots that are pairwise neither equal nor opposite, given the finite statement `Sec8`. -/
theorem rho_le_three (h8 : Sec8 G) (L : EvenOverlattice G) (z : Fin 4 → V → ℤ)
    (hz : ∀ i, z i ∈ L.L) (hn : ∀ i, z i ⬝ᵥ z i = 126)
    (hd : ∀ i j, i ≠ j → z j ≠ z i ∧ z j ≠ -z i) : False := by
  have hb : ∀ i, ∃ c : V → ℤ, z i = (3 : ℤ) • c ∧ IsM4 G c ∧ Biplane G c :=
    fun i => root_struct hG L (hz i) (hn i)
  choose b hb using hb
  have hQ : Quad G b :=
    { m4 := fun i => (hb i).2.1
      bip := fun i => (hb i).2.2
      orth := fun i j hij => by
        have h := roots_orth hG L (hz i) (hz j) (hn i) (hn j) (hd i j hij).1 (hd i j hij).2
        rw [(hb i).1, (hb j).1, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h
        linarith }
  exact no_quad hG h8 hQ

/-- **Part B summary** (Theorem 1.1, root part), for any even integral overlattice `L ⊇ N`:
(i) `min L* ≥ 2` in the form: nonzero `-4` eigenvectors with all coordinates congruent mod 3
have norm `≥ 126`; (ii) every root is `3b` with `b` a biplane vector; (iii) two roots are
orthogonal unless equal or opposite (`Φ = A₁^ρ`); (iv) given `Sec8`, `ρ ≤ 3`. -/
theorem partB (h8 : Sec8 G) (L : EvenOverlattice G) :
    (∀ z ∈ L.L, z ≠ 0 → 126 ≤ z ⬝ᵥ z) ∧
    (∀ z ∈ L.L, z ⬝ᵥ z = 126 → ∃ b : V → ℤ, z = (3 : ℤ) • b ∧ IsM4 G b ∧ Biplane G b) ∧
    (∀ z ∈ L.L, ∀ z' ∈ L.L, z ⬝ᵥ z = 126 → z' ⬝ᵥ z' = 126 → z' ≠ z → z' ≠ -z → z ⬝ᵥ z' = 0) ∧
    (∀ z : Fin 4 → V → ℤ, (∀ i, z i ∈ L.L) → (∀ i, z i ⬝ᵥ z i = 126) →
      (∀ i j, i ≠ j → z j ≠ z i ∧ z j ≠ -z i) → False) :=
  ⟨fun _ hz hne => min_dual hG (L.eig _ hz) (L.res hG hz) hne,
   fun _ hz hn => root_struct hG L hz hn,
   fun _ hz _ hz' hn hn' h1 h2 => roots_orth hG L hz hz' hn hn' h1 h2,
   fun z hz hn hd => rho_le_three hG h8 L z hz hn hd⟩

end SRG

end Conway99
