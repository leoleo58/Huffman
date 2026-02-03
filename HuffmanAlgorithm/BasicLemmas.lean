import Mathlib.Tactic

/-!
# Basic Lemmas used for proof

This file contains basic lemmas about element and disjoint
-/
lemma mem_inter_empty {α} [DecidableEq α]
  (A B : Finset α) (a : α) (h : A ∩ B = ∅)
  (h1 : a ∈ A) (h2 : a ∈ B) : False := by
  have : a ∈ A ∩ B := Finset.mem_inter_of_mem h1 h2
  simp [h] at this

lemma not_mem_right_of_inter_empty {α} [DecidableEq α]
  {A B : Finset α} {a : α} :
  A ∩ B = ∅ → a ∈ A → a ∉ B := by
  intro h ha hb
  have : a ∈ A ∩ B := Finset.mem_inter.mpr ⟨ha, hb⟩
  simp [h] at this

lemma not_mem_left_of_inter_empty {α} [DecidableEq α]
  {A B : Finset α} {a : α} :
  A ∩ B = ∅ → a ∈ B → a ∉ A := by
  intro h ha hb
  have : a ∈ A ∩ B := Finset.mem_inter.mpr ⟨hb, ha⟩
  simp [h] at this

lemma not_mem_inter_empty {α} {A B : Finset α} {a : α} [DecidableEq α] :
  A ∩ B = ∅ → (a ∈ A → a ∉ B) ∧ (a ∈ B → a ∉ A) := by
  intro h
  constructor <;> intro ha hb
  · have : a ∈ A ∩ B := Finset.mem_inter.mpr ⟨ha, hb⟩
    simp [h] at this
  · have : a ∈ A ∩ B := Finset.mem_inter.mpr ⟨hb, ha⟩
    simp [h] at this
