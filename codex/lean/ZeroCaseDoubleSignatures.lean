import ZeroCaseSupportSizes

/-! Actual double signatures are exactly the signed pair cells not occupied by a
high signature. Thus the entire core and all eight simple-class sizes are
determined by the high packing. No zero-case enumeration is recomputed here. -/

namespace Conway99

def doubleCandidates (high : Finset RootSignature) : Finset RootSignature :=
  Finset.univ.filter (fun w => signatureWeight w = 2 ∧
    ∀ z ∈ high, Disjoint (signatureCells w) (signatureCells z))

private theorem signature_pair_weight_lower (w : RootSignature) (i j : Fin 4)
    (hij : i ≠ j) (hi : w i ≠ 1) (hj : w j ≠ 1) : 2 ≤ signatureWeight w := by
  have hs : ({i, j} : Finset (Fin 4)) ⊆ Finset.univ.filter (fun k => w k ≠ 1) := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · simp [hi]
    · rw [Finset.mem_singleton] at hk
      subst k
      simp [hj]
  have hh := Finset.card_le_card hs
  simpa [signatureWeight, hij] using hh

private theorem signature_double_pair (w : RootSignature) (hw : signatureWeight w = 2) :
    ∃ i j : Fin 4, i < j ∧ w i ≠ 1 ∧ w j ≠ 1 := by
  have hh : 1 < (Finset.univ.filter (fun k => w k ≠ 1)).card := by
    change 1 < signatureWeight w
    omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hh
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ⟨i, j, hlt, hi', hj'⟩
  · exact ⟨j, i, hgt, hj', hi'⟩

private theorem signature_double_other (w : RootSignature) (hw : signatureWeight w = 2)
    (i j : Fin 4) (hij : i ≠ j) (hi : w i ≠ 1) (hj : w j ≠ 1)
    (k : Fin 4) (hki : k ≠ i) (hkj : k ≠ j) : w k = 1 := by
  by_contra hk
  have hs : ({i, j, k} : Finset (Fin 4)) ⊆ Finset.univ.filter (fun l => w l ≠ 1) := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl <;> simp [hi, hj, hk]
  have hh := Finset.card_le_card hs
  have hc : ({i, j, k} : Finset (Fin 4)).card = 3 := by
    simp [hij, hki, hkj, Ne.symm hki, Ne.symm hkj]
  change ({i, j, k} : Finset (Fin 4)).card ≤ signatureWeight w at hh
  omega

private theorem signature_double_unique (w z : RootSignature)
    (hw : signatureWeight w = 2) (hz : signatureWeight z = 2)
    (i j : Fin 4) (hij : i ≠ j) (hi : w i ≠ 1) (hj : w j ≠ 1)
    (hei : z i = w i) (hej : z j = w j) : z = w := by
  funext k
  by_cases hki : k = i
  · simpa only [hki] using hei
  by_cases hkj : k = j
  · simpa only [hkj] using hej
  rw [signature_double_other w hw i j hij hi hj k hki hkj,
    signature_double_other z hz i j hij (hei ▸ hi) (hej ▸ hj) k hki hkj]

private theorem signature_pair_cell_mem (w : RootSignature) (i j : Fin 4)
    (hij : i < j) (hi : w i ≠ 1) (hj : w j ≠ 1) :
    (i, j, w i, w j) ∈ signatureCells w := by
  apply Finset.mem_image.mpr
  exact ⟨(i,j), Finset.mem_filter.mpr ⟨by simp, hij, hi, hj⟩, rfl⟩

private theorem signature_active_sign (a : Fin 3) (ha : a ≠ 1) :
    ∃ s : Bool, (a.val : ℤ) = (if s then 1 else -1) + 1 := by
  fin_cases a
  · exact ⟨false, by norm_num⟩
  · exact (ha rfl).elim
  · exact ⟨true, by norm_num⟩

namespace FourDirectionSystem

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (F : FourDirectionSystem G)

theorem doubleCandidate_realized (hc : F.HasSignedCells) {w : RootSignature}
    (hw : w ∈ doubleCandidates F.highSignatures) : w ∈ F.coreSignatures := by
  obtain ⟨_, hwt, hdis⟩ := Finset.mem_filter.mp hw
  obtain ⟨i, j, hij, hi, hj⟩ := signature_double_pair w hwt
  obtain ⟨s, hs⟩ := signature_active_sign (w i) hi
  obtain ⟨t, ht⟩ := signature_active_sign (w j) hj
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp (hc i j (ne_of_lt hij) s t)
  have hucell : u ∈ signedCodeSupport (F.code i) s ∩ signedCodeSupport (F.code j) t := by
    rw [hu]
    exact Finset.mem_singleton_self u
  have hui := (signedCodeSupport_mem _ _ _).mp (Finset.mem_inter.mp hucell).1
  have huj := (signedCodeSupport_mem _ _ _).mp (Finset.mem_inter.mp hucell).2
  have hei : F.signature u i = w i := by
    apply Fin.ext
    have hv := F.signature_val u i
    rw [hui] at hv
    omega
  have hej : F.signature u j = w j := by
    apply Fin.ext
    have hv := F.signature_val u j
    rw [huj] at hv
    omega
  have huW : u ∈ F.W := F.support_subset_W i
    (signedCodeSupport_subset _ _ (Finset.mem_inter.mp hucell).1)
  have hsig : (signatureWeight (F.signature u) : ℤ) = F.weight u := F.signature_active_card u
  have htwo : 2 ≤ signatureWeight (F.signature u) :=
    signature_pair_weight_lower _ i j (ne_of_lt hij) (hei ▸ hi) (hej ▸ hj)
  have hnotHigh : ¬3 ≤ F.weight u := by
    intro hhigh
    have hhighmem : F.signature u ∈ F.highSignatures :=
      Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨huW, hhigh⟩, rfl⟩
    have hwcell := signature_pair_cell_mem w i j hij hi hj
    have huc := signature_pair_cell_mem (F.signature u) i j hij (hei ▸ hi) (hej ▸ hj)
    rw [hei, hej] at huc
    exact Finset.disjoint_left.mp (hdis _ hhighmem) hwcell huc
  have hutwo : signatureWeight (F.signature u) = 2 := by omega
  have heq : F.signature u = w := signature_double_unique w (F.signature u)
    hwt hutwo i j (ne_of_lt hij) hi hj hei hej
  exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨huW, by omega⟩, heq⟩

theorem coreSignatures_eq_high_union_double (hc : F.HasSignedCells) :
    F.coreSignatures = F.highSignatures ∪ doubleCandidates F.highSignatures := by
  ext w
  constructor
  · intro hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨huW, hu2⟩ := Finset.mem_filter.mp hu
    by_cases hu3 : 3 ≤ F.weight u
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨u, Finset.mem_filter.mpr ⟨huW, hu3⟩, rfl⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      have hsig : (signatureWeight (F.signature u) : ℤ) = F.weight u := F.signature_active_card u
      have hwt : F.weight u = 2 := by omega
      refine ⟨Finset.mem_univ _, by omega, ?_⟩
      intro z hz
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
      have hv3 := (Finset.mem_filter.mp hv).2
      apply F.distinct_signature_cells_disjoint hc
      intro he
      subst v
      omega
  · intro hw
    rcases Finset.mem_union.mp hw with hh | hd
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hh
      obtain ⟨huW, hu3⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨huW, by omega⟩, rfl⟩
    · exact F.doubleCandidate_realized hc hd

theorem singleClass_card_from_high (hc : F.HasSignedCells) (a : Fin 4 × Bool) :
    (F.singleClass a).card =
      7 - ((F.highSignatures ∪ doubleCandidates F.highSignatures).filter
        (fun w => w a.1 = if a.2 then 2 else 0)).card := by
  rw [F.singleClass_card_from_signatures hc, F.coreSignatures_eq_high_union_double hc]

#print axioms doubleCandidate_realized
#print axioms coreSignatures_eq_high_union_double
#print axioms singleClass_card_from_high

end FourDirectionSystem
end Conway99
