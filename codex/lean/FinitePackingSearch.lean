import SignaturePacking

/-! A pruning search whose completeness is proved in the kernel.
This is an enumerator, not yet the exclusion certificate for the zero case. -/

namespace Conway99
namespace FinitePacking

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def search (cells : α → Finset β) (n : ℕ) (candidates : List α)
    (used : Finset β) : Finset (Finset α) :=
  match n, candidates with
  | 0, _ => {∅}
  | _ + 1, [] => ∅
  | k + 1, a :: rest =>
      search cells (k + 1) rest used ∪
        if Disjoint (cells a) used then
          (search cells k rest (used ∪ cells a)).image (insert a)
        else ∅
termination_by structural candidates

theorem search_complete (cells : α → Finset β) (candidates : List α)
    (n : ℕ) (used : Finset β) (S : Finset α)
    (hsub : ∀ a ∈ S, a ∈ candidates)
    (hcard : S.card = n)
    (hpack : (S : Set α).Pairwise (fun a b => Disjoint (cells a) (cells b)))
    (hused : ∀ a ∈ S, Disjoint (cells a) used) :
    S ∈ search cells n candidates used := by
  induction candidates generalizing n used S with
  | nil =>
      have hs : S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        simpa using hsub a ha
      subst S
      simp only [Finset.card_empty] at hcard
      subst n
      simp [search]
  | cons a rest ih =>
      cases n with
      | zero =>
          have hs := Finset.card_eq_zero.mp hcard
          simp [search, hs]
      | succ n =>
          rw [search]
          by_cases ha : a ∈ S
          · apply Finset.mem_union_right
            rw [if_pos (hused a ha)]
            apply Finset.mem_image.mpr
            refine ⟨S.erase a, ih n (used ∪ cells a) (S.erase a) ?_ ?_ ?_ ?_, ?_⟩
            · intro b hb
              have hh := hsub b (Finset.mem_erase.mp hb).2
              rcases List.mem_cons.mp hh with heq | hmem
              · exact ((Finset.mem_erase.mp hb).1 heq).elim
              · exact hmem
            · rw [Finset.card_erase_of_mem ha, hcard]
              omega
            · intro b hb c hc hbc
              exact hpack (Finset.mem_erase.mp hb).2 (Finset.mem_erase.mp hc).2 hbc
            · intro b hb
              rw [Finset.disjoint_union_right]
              exact ⟨hused b (Finset.mem_erase.mp hb).2,
                hpack (Finset.mem_erase.mp hb).2 ha (Finset.mem_erase.mp hb).1⟩
            · exact Finset.insert_erase ha
          · apply Finset.mem_union_left
            apply ih (n + 1) used S ?_ hcard hpack hused
            intro b hb
            rcases List.mem_cons.mp (hsub b hb) with heq | hmem
            · exact (ha (heq ▸ hb)).elim
            · exact hmem

#print axioms search_complete

attribute [irreducible] search

end FinitePacking
end Conway99
