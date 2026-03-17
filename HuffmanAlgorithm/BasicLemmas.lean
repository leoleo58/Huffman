import Mathlib.Tactic

/-!
# Basic Lemmas used for proof

This file contains basic lemmas about element of finset and their intersections

It provides results showing that if two sets are disjoint:
- An element cannot belong to both sets at the same time.
- Membership in one set means non-membership in the other.
-/

/--
If `A` and `B` are disjoint (their intersection is empty),
no element can belong to both sets at the same time.
-/
lemma mem_inter_empty {α} [DecidableEq α]
  (A B : Finset α) (a : α) (h : A ∩ B = ∅)
  (h1 : a ∈ A) (h2 : a ∈ B) : False := by
  have : a ∈ A ∩ B := Finset.mem_inter_of_mem h1 h2
  simp [h] at this

lemma not_mem_right {α} [DecidableEq α]
  {A B : Finset α} {a : α} :
  A ∩ B = ∅ → a ∈ A → a ∉ B := by
  intro h ha hb
  have : a ∈ A ∩ B := Finset.mem_inter.mpr ⟨ha, hb⟩
  simp [h] at this

lemma not_mem_left {α} [DecidableEq α]
  {A B : Finset α} {a : α} :
  A ∩ B = ∅ → a ∈ B → a ∉ A := by
  intro h ha hb
  have : a ∈ A ∩ B := Finset.mem_inter.mpr ⟨hb, ha⟩
  simp [h] at this

/--
If `A` and `B` are disjoint,
- `a` in `A` means `a` not in `B`
- `a` in `B` means `a` not in `A`.
-/
lemma not_mem_inter_empty {α} {A B : Finset α} {a : α} [DecidableEq α] :
  A ∩ B = ∅ → (a ∈ A → a ∉ B) ∧ (a ∈ B → a ∉ A) := by
  intro h
  constructor <;> grind[mem_inter_empty]
