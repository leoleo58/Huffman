import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Basic
import aesop

inductive HuffmanTree (α : Type) where
  | leaf (w : Nat) (a : α) : HuffmanTree α
  | node (w : Nat) (t1 : HuffmanTree α) (t2 : HuffmanTree α) : HuffmanTree α

abbrev Forest (α) := List (HuffmanTree α)

def cachedWeight {α} : HuffmanTree α → Nat
  | HuffmanTree.leaf w _ => w
  | HuffmanTree.node w _ _ => w

def uniteTrees {α} (t1 t2 : HuffmanTree α) : HuffmanTree α :=
  HuffmanTree.node (cachedWeight t1 + cachedWeight t2) t1 t2

def insortTree {α} (u : HuffmanTree α) : List (HuffmanTree α) → List (HuffmanTree α)
  | [] => [u]
  | t :: ts =>
      if cachedWeight u ≤ cachedWeight t then
        u :: t :: ts
      else
        t :: insortTree u ts

@[simp]
lemma insortTree_length {α} (u : HuffmanTree α) (ts : List (HuffmanTree α)) :
    (insortTree u ts).length = ts.length + 1 := by
  induction ts with
  | nil => rfl
  | cons t' ts' ih =>
      aesop (add norm[insortTree])

@[simp]
lemma insortTree_ne_nil {α} (u : HuffmanTree α) (ts : List (HuffmanTree α)) :
    insortTree u ts ≠ [] := by
  intro H
  have h := insortTree_length u ts
  simp [H] at h

/-
Huffman algorithm
-/
def huffman {α} (xs : Forest α) (h : xs ≠ []) : HuffmanTree α :=
  match xs with
  | [t]      => t
  | t1 :: t2 :: ts =>
      huffman (insortTree (uniteTrees t1 t2) ts) (insortTree_ne_nil _ _)
termination_by xs.length

def alphabet {α} [DecidableEq α] : HuffmanTree α → Finset α
  | HuffmanTree.leaf _ a => {a}
  | HuffmanTree.node _ t1 t2 => alphabet t1 ∪ alphabet t2

def alphabetF {α} [DecidableEq α] : Forest α → Finset α
  | [] => Finset.empty
  | t :: ts => alphabet t ∪ alphabetF ts

def consistent {α} [DecidableEq α] : HuffmanTree α → Prop
  | HuffmanTree.leaf _ _ => True
  | HuffmanTree.node _ t1 t2 => (alphabet t1 ∩ alphabet t2 = ∅) ∧ consistent t1 ∧ consistent t2

def consistentF {α} [DecidableEq α] : Forest α → Prop
  | [] => True
  | t :: ts => (alphabet t ∩ alphabetF ts = ∅) ∧ consistent t ∧ consistentF ts

def depth {α} [DecidableEq α] : HuffmanTree α → α → Nat
  | HuffmanTree.leaf _ _, _ => 0
  | HuffmanTree.node _ t1 t2, a =>
    if a ∈ alphabet t1 then depth t1 a + 1
    else if a ∈ alphabet t2 then depth t2 a + 1
    else 0

def height {α} : HuffmanTree α → Nat
  | HuffmanTree.leaf _ _ => 0
  | HuffmanTree.node _ t1 t2 => max (height t1) (height t2) + 1

def heightF {α} : Forest α → Nat
  | [] => 0
  | t :: ts => max (height t) (heightF ts)

def freq {α} [DecidableEq α] : HuffmanTree α → α → Nat
  | HuffmanTree.leaf w a, b => if b = a then w else 0
  | HuffmanTree.node _ t1 t2, b => freq t1 b + freq t2 b

def freqF {α} [DecidableEq α] : Forest α → α → Nat
  | [] , _ => 0
  | t :: ts , b => freq t b + freqF ts b

def weight {α} : HuffmanTree α → Nat
  | HuffmanTree.leaf w _ => w
  | HuffmanTree.node _ t1 t2 => weight t1 + weight t2

def cost {α} : HuffmanTree α → Nat
  | HuffmanTree.leaf _ _ => 0
  | HuffmanTree.node _ t1 t2 => weight t1 + cost t1 + weight t2 + cost t2

def optimum {α} [DecidableEq α] (t : HuffmanTree α) : Prop :=
  ∀ u : HuffmanTree α, consistent u →
    alphabet t = alphabet u →
    freq t = freq u →
    cost t ≤ cost u

-- Bool version
def consistentB {α : Type} [DecidableEq α] : HuffmanTree α → Bool
  | HuffmanTree.leaf _ _ => true
  | HuffmanTree.node _ t1 t2 => (alphabet t1 ∩ alphabet t2 = ∅) ∧ consistentB t1 ∧ consistentB t2

def consistentBF {α : Type} [DecidableEq α] : Forest α → Bool
  | [] => true
  | t :: ts => (alphabet t ∩ alphabetF ts = ∅) ∧ consistentB t ∧ consistentBF ts

def freqEqualB {α} [DecidableEq α] (t u : HuffmanTree α) : Bool :=
  ∀ a ∈ alphabet t ∪ alphabet u, freq t a == freq u a
/-
def optimumB {α} [DecidableEq α] (t : HuffmanTree α) : Bool :=
  ∀ u : HuffmanTree α,
    consistentB u &&
    (alphabet t == alphabet u : Bool) &&
    freqEqualB t u &&
    (cost t ≤ cost u : Bool)-/

-- Set Version
def alphabetS {α : Type} [DecidableEq α] : HuffmanTree α → Set α
  | HuffmanTree.leaf _ a => {a}
  | HuffmanTree.node _ t1 t2 => alphabetS t1 ∪ alphabetS t2

lemma finite_alp {α : Type} (t : HuffmanTree α) [DecidableEq α] : (alphabetS t).Finite := by
  induction t with
  | leaf _ a => apply Set.finite_singleton
  | node _ t1 t2 h1 h2 =>
      apply Set.Finite.union
      · exact h1
      · exact h2

lemma exists_in_al {α : Type} [Inhabited α] [DecidableEq α] (t : HuffmanTree α) :
∃ a, a ∈ alphabetS t := by
  induction t with
  | leaf w a => exact ⟨a, by simp [alphabetS]⟩
  | node w t1 t2 h1 h2 =>
      rcases h1 with ⟨a, ha⟩
      exact ⟨a, Set.mem_union_left _ ha⟩

def consistentS {α : Type} [DecidableEq α] : HuffmanTree α → Prop
  | HuffmanTree.leaf _ _ => true
  | HuffmanTree.node _ t1 t2 => (alphabetS t1 ∩ alphabetS t2 = ∅) ∧ consistentS t1 ∧ consistentS t2

/-
doesn't work
def depthS {α} [DecidableEq α] : HuffmanTree α → α → Nat
  | HuffmanTree.leaf _ _, _ => 0
  | HuffmanTree.node _ t1 t2, a =>
    if a ∈ alphabetS t1 then depth t1 a + 1
    else if a ∈ alphabetS t2 then depth t2 a + 1
    else 0-/
