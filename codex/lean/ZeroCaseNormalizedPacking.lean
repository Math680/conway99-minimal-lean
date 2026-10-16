import ZeroCaseSymmetry

/-! Any nonempty full-signature part can be normalized to contain ++++.
The remaining packing belongs to a small, complete pruning search. -/

namespace Conway99

def allPlusSignature : RootSignature := fun _ => 2

theorem allPlusSignature_weight : signatureWeight allPlusSignature = 4 := by decide

def IsZeroCaseHighPacking (S : Finset RootSignature) (n : ℕ) : Prop :=
  (∀ w ∈ S, signatureWeight w = 3 ∨ signatureWeight w = 4) ∧
  (S.filter (fun w => signatureWeight w = 4)).card = n ∧
  (S.filter (fun w => signatureWeight w = 3)).card = 7 - 3 * n ∧
  (S : Set RootSignature).Pairwise (fun w z => Disjoint (signatureCells w) (signatureCells z))

theorem signatureSetAct_filter_weight (g : SignatureSymmetry) (S : Finset RootSignature) (k : ℕ) :
    (signatureSetAct g S).filter (fun w => signatureWeight w = k) =
      signatureSetAct g (S.filter (fun w => signatureWeight w = k)) := by
  ext w
  simp only [signatureSetAct,Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨⟨z,hz,rfl⟩,hk⟩
    exact ⟨z,⟨hz,(signatureAct_weight g z) ▸ hk⟩,rfl⟩
  · rintro ⟨z,⟨hz,hk⟩,rfl⟩
    exact ⟨⟨z,hz,rfl⟩,by rwa [signatureAct_weight]⟩

theorem IsZeroCaseHighPacking.act {S : Finset RootSignature} {n : ℕ}
    (hS : IsZeroCaseHighPacking S n) (g : SignatureSymmetry) :
    IsZeroCaseHighPacking (signatureSetAct g S) n := by
  refine ⟨?_,?_,?_,signatureSetAct_packing g S hS.2.2.2⟩
  · intro w hw
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hw
    rw [signatureAct_weight]
    exact hS.1 z hz
  · rw [signatureSetAct_filter_weight,signatureSetAct_card]
    exact hS.2.1
  · rw [signatureSetAct_filter_weight,signatureSetAct_card]
    exact hS.2.2.1

theorem signatureWeight_four_nonzero {w : RootSignature} (hw : signatureWeight w = 4)
    (i : Fin 4) : w i ≠ 1 := by
  have hh : (Finset.univ.filter (fun j : Fin 4 => w j ≠ 1)).card = Fintype.card (Fin 4) := hw
  have he := Finset.eq_univ_of_card _ hh
  have hm : i ∈ Finset.univ.filter (fun j : Fin 4 => w j ≠ 1) := by rw [he]; exact Finset.mem_univ _
  exact (Finset.mem_filter.mp hm).2

theorem exists_full_normalization {S : Finset RootSignature} {n : ℕ}
    (hS : IsZeroCaseHighPacking S n) (hn : 0 < n) :
    ∃ g : SignatureSymmetry, allPlusSignature ∈ signatureSetAct g S := by
  have hp : 0 < (S.filter (fun w => signatureWeight w = 4)).card := by rwa [hS.2.1]
  obtain ⟨b,hb⟩ := Finset.card_pos.mp hp
  let g : SignatureSymmetry := (Equiv.refl _, fun i => b i == 0)
  have he : signatureAct g b = allPlusSignature := by
    funext i
    have hh : ∀ x : Fin 3, x ≠ 1 → signatureFlip (x == 0) x = 2 := by decide
    exact hh (b i) (signatureWeight_four_nonzero (Finset.mem_filter.mp hb).2 i)
  exact ⟨g,Finset.mem_image.mpr ⟨b,(Finset.mem_filter.mp hb).1,he⟩⟩

def normalizedHighPackings (n : ℕ) : Finset (Finset RootSignature) :=
  (FinitePacking.search signatureCells (n - 1) fullSignatureList
    (signatureCells allPlusSignature)).biUnion (fun A =>
    (FinitePacking.search signatureCells (7 - 3 * n) tripleSignatureList
      (signatureCells allPlusSignature ∪ A.biUnion signatureCells)).image
      (fun B => insert allPlusSignature (A ∪ B)))

theorem normalizedHighPackings_complete {S : Finset RootSignature} {n : ℕ}
    (hS : IsZeroCaseHighPacking S n) (hplus : allPlusSignature ∈ S) :
    S ∈ normalizedHighPackings n := by
  let A := (S.filter (fun w => signatureWeight w = 4)).erase allPlusSignature
  let B := S.filter (fun w => signatureWeight w = 3)
  have hplus4 : allPlusSignature ∈ S.filter (fun w => signatureWeight w = 4) :=
    Finset.mem_filter.mpr ⟨hplus,allPlusSignature_weight⟩
  have hA (w : RootSignature) (hw : w ∈ A) : w ∈ S ∧ signatureWeight w = 4 ∧ w ≠ allPlusSignature := by
    have hh := Finset.mem_erase.mp hw
    exact ⟨(Finset.mem_filter.mp hh.2).1,(Finset.mem_filter.mp hh.2).2,hh.1⟩
  have hB (w : RootSignature) (hw : w ∈ B) : w ∈ S ∧ signatureWeight w = 3 := Finset.mem_filter.mp hw
  have hma : A ∈ FinitePacking.search signatureCells (n - 1) fullSignatureList
      (signatureCells allPlusSignature) := by
    apply FinitePacking.search_complete signatureCells fullSignatureList (n - 1)
      (signatureCells allPlusSignature) A
    · intro w hw
      exact (mem_fullSignatureList w).mpr (hA w hw).2.1
    · dsimp only [A]
      rw [Finset.card_erase_of_mem hplus4,hS.2.1]
    · intro w hw z hz hwz
      exact hS.2.2.2 (hA w hw).1 (hA z hz).1 hwz
    · intro w hw
      exact hS.2.2.2 (hA w hw).1 hplus (hA w hw).2.2
  have hmb : B ∈ FinitePacking.search signatureCells (7 - 3 * n) tripleSignatureList
      (signatureCells allPlusSignature ∪ A.biUnion signatureCells) := by
    apply FinitePacking.search_complete signatureCells tripleSignatureList (7 - 3 * n)
      (signatureCells allPlusSignature ∪ A.biUnion signatureCells) B
    · intro w hw
      exact (mem_tripleSignatureList w).mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hB w hw).2⟩)
    · exact hS.2.2.1
    · intro w hw z hz hwz
      exact hS.2.2.2 (hB w hw).1 (hB z hz).1 hwz
    · intro w hw
      rw [Finset.disjoint_union_right]
      constructor
      · apply hS.2.2.2 (hB w hw).1 hplus
        intro he
        have hh := (hB w hw).2
        rw [he,allPlusSignature_weight] at hh
        omega
      · apply (Finset.disjoint_biUnion_right _ _ _).mpr
        intro z hz
        apply hS.2.2.2 (hB w hw).1 (hA z hz).1
        intro he
        have h3 := (hB w hw).2
        have h4 := (hA z hz).2.1
        rw [he] at h3
        omega
  have he : insert allPlusSignature (A ∪ B) = S := by
    ext w
    simp only [Finset.mem_insert,Finset.mem_union]
    constructor
    · rintro (rfl | hw | hw)
      · exact hplus
      · exact (hA w hw).1
      · exact (hB w hw).1
    · intro hw
      by_cases he : w = allPlusSignature
      · exact Or.inl he
      · rcases hS.1 w hw with h3 | h4
        · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨hw,h3⟩))
        · exact Or.inr (Or.inl (Finset.mem_erase.mpr ⟨he,Finset.mem_filter.mpr ⟨hw,h4⟩⟩))
  exact Finset.mem_biUnion.mpr ⟨A,hma,Finset.mem_image.mpr ⟨B,hmb,he⟩⟩

def signatureSymmetryComp (g h : SignatureSymmetry) : SignatureSymmetry :=
  (g.1.trans h.1, fun i => Bool.xor (g.2 i) (h.2 (g.1 i)))

theorem signatureAct_comp (g h : SignatureSymmetry) (w : RootSignature) :
    signatureAct (signatureSymmetryComp g h) w = signatureAct g (signatureAct h w) := by
  funext i
  have hh : ∀ a b : Bool, ∀ x : Fin 3,
      signatureFlip (Bool.xor a b) x = signatureFlip a (signatureFlip b x) := by decide
  exact hh _ _ _

theorem signatureSetAct_comp (g h : SignatureSymmetry) (S : Finset RootSignature) :
    signatureSetAct (signatureSymmetryComp g h) S = signatureSetAct g (signatureSetAct h S) := by
  unfold signatureSetAct
  rw [Finset.image_image]
  apply Finset.image_congr
  intro w _
  exact signatureAct_comp g h w

#print axioms normalizedHighPackings_complete
#print axioms exists_full_normalization

end Conway99
