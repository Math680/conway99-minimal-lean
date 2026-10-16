import Mathlib.Tactic

/-! Exhaustive finite row search with pairwise compatibility, and its
completeness theorem for an arbitrary prescribed assignment. -/

namespace Conway99.FiniteRowSearch

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

def search (options : ι → Finset α) (compatible : ι → α → ι → α → Prop)
    [∀ i a j b, Decidable (compatible i a j b)] :
    List ι → List (ι × α) → Finset (List (ι × α))
  | [], chosen => {chosen}
  | i :: rest, chosen => (options i).biUnion fun a =>
      if ∀ p ∈ chosen, compatible i a p.1 p.2 then search options compatible rest ((i,a)::chosen) else ∅

theorem search_complete (options : ι → Finset α) (compatible : ι → α → ι → α → Prop)
    [∀ i a j b, Decidable (compatible i a j b)]
    (f : ι → α) (hf : ∀ i, f i ∈ options i) (hc : ∀ i j, compatible i (f i) j (f j))
    (indices : List ι) (chosen : List (ι × α)) (hchosen : ∀ p ∈ chosen, p.2 = f p.1) :
    (indices.map (fun i => (i,f i))).reverse ++ chosen ∈ search options compatible indices chosen := by
  induction indices generalizing chosen with
  | nil => simp [search]
  | cons i rest ih =>
      have hgood : ∀ p ∈ chosen, compatible i (f i) p.1 p.2 := by
        intro p hp
        rw [hchosen p hp]
        exact hc i p.1
      apply Finset.mem_biUnion.mpr
      refine ⟨f i,hf i,?_⟩
      rw [if_pos hgood]
      have hnew : ∀ p ∈ (i,f i)::chosen, p.2 = f p.1 := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · rfl
        · exact hchosen p hp
      simpa [List.map_cons,List.reverse_cons,List.append_assoc] using ih ((i,f i)::chosen) hnew

#print axioms search_complete

end Conway99.FiniteRowSearch
