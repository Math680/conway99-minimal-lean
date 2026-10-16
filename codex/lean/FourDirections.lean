import Mathlib.Tactic

/-!
Small finite lemmas from section 9, checked by kernel reduction (`decide`).
These prove the label combinatorics, NOT the reduction of an SRG to these labels.
No external solver or `native_decide` is used.
-/

namespace Conway99.FourDirections

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev Label := Fin 4
abbrev Arc := {p : Label × Label // p.1 ≠ p.2}

def src (a : Arc) : Label := a.val.1
def dst (a : Arc) : Label := a.val.2

def Profiles : Finset (Finset Label) := Finset.univ.powerset.filter (fun D => D.card = 2)

def negV (D : Finset Label) (i : Label) : Prop := i ∉ D
def negW (D : Finset Label) (i : Label) : Prop := i ∈ D
def negR (D : Finset Label) (a : Arc) : Prop := src a ∈ D ∧ dst a ∉ D

instance (D : Finset Label) (i : Label) : Decidable (negV D i) := inferInstanceAs (Decidable (i ∉ D))
instance (D : Finset Label) (i : Label) : Decidable (negW D i) := inferInstanceAs (Decidable (i ∈ D))
instance (D : Finset Label) (a : Arc) : Decidable (negR D a) :=
  inferInstanceAs (Decidable (src a ∈ D ∧ dst a ∉ D))

theorem six_profiles : Profiles.card = 6 := by decide
theorem twelve_arcs : Fintype.card Arc = 12 := by decide

theorem V_W_restriction : ∀ i j : Label,
    (∀ D ∈ Profiles, ¬ (negV D i ∧ negW D j)) ↔ i = j := by decide

theorem V_R_restriction : ∀ (i : Label) (a : Arc),
    (∀ D ∈ Profiles, ¬ (negV D i ∧ negR D a)) ↔ i = src a := by decide

theorem W_R_restriction : ∀ (i : Label) (a : Arc),
    (∀ D ∈ Profiles, ¬ (negW D i ∧ negR D a)) ↔ i = dst a := by decide

theorem R_R_restriction : ∀ a b : Arc,
    (∀ D ∈ Profiles, ¬ (negR D a ∧ negR D b)) ↔
      dst a = src b ∨ dst b = src a := by decide

theorem V_internal_profile_count : ∀ i j : Label, i ≠ j →
    (Profiles.filter (fun D => negV D i ∧ negV D j)).card = 1 := by decide

theorem W_internal_profile_count : ∀ i j : Label, i ≠ j →
    (Profiles.filter (fun D => negW D i ∧ negW D j)).card = 1 := by decide

def arcAdj (a b : Arc) : Prop :=
  (dst a = src b ∧ dst b ≠ src a) ∨ (dst b = src a ∧ src b ≠ dst a)

instance (a b : Arc) : Decidable (arcAdj a b) :=
  inferInstanceAs (Decidable
    ((dst a = src b ∧ dst b ≠ src a) ∨ (dst b = src a ∧ src b ≠ dst a)))

def commonArcs (a b : Arc) : Finset Arc :=
  Finset.univ.filter (fun c => arcAdj a c ∧ arcAdj b c)

theorem same_source_one_common_arc : ∀ a b : Arc,
    a ≠ b → src a = src b → (commonArcs a b).card = 1 := by decide

theorem same_destination_one_common_arc : ∀ a b : Arc,
    a ≠ b → dst a = dst b → (commonArcs a b).card = 1 := by decide

theorem adjacent_one_common_arc : ∀ a b : Arc,
    arcAdj a b → (commonArcs a b).card = 1 := by decide

/-- On three available labels, the only pair with distinct sources and
destinations, and no allowed arc-edge, is an inverse pair. -/
theorem three_labels_force_inverse : ∀ (a b : Arc) (excluded : Label),
    src a ≠ excluded → dst a ≠ excluded →
    src b ≠ excluded → dst b ≠ excluded →
    src a ≠ src b → dst a ≠ dst b → ¬ arcAdj a b →
      src a = dst b ∧ dst a = src b := by decide

theorem profile_edge_budget (eP eB : ℤ)
    (heP : 0 ≤ eP) (hrel : eB = eP + 1)
    (hcommon : 17 + 4 * eB ≤ 30 - eP) : eP ≤ 1 := by omega

theorem profile_binomial_bound (d : ℕ) :
    1 + 2 * d ≤ (d + 2) * (d + 1) / 2 := by
  have h : 2 + 4 * d ≤ (d + 2) * (d + 1) := by
    by_cases hd : d = 0
    · subst d; norm_num
    · have : 1 ≤ d := by omega
      nlinarith
  omega

#print axioms R_R_restriction
#print axioms V_W_restriction
#print axioms V_R_restriction
#print axioms W_R_restriction
#print axioms three_labels_force_inverse
#print axioms same_source_one_common_arc
#print axioms same_destination_one_common_arc
#print axioms adjacent_one_common_arc
#print axioms profile_edge_budget
#print axioms profile_binomial_bound

end Conway99.FourDirections
