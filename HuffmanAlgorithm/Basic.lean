import HuffmanAlgorithm.BasicLemmas
import aesop

/-!
# Basic Definitions for Huffman Trees

This file introduces the core definition used throughout the
formalization of Huffman’s algorithm. It defines the Huffman tree and
it's properties: which are alphabets, frequencies, depth, height, weight and cost.
Additionally, it introduces `minima` and `optimum`, which are used in later proofs.
For each definitions, this file also provides lemmas about their
properties and relationships.

## Definitions

- `HuffmanTree α`    : Datatype representing a Huffman tree with symbols of type `α`.
- `Forest α`         : A list of Huffman trees.
- `alphabet t`       : The set of symbols occurring in tree `t`.
- `consistent t`     : Condition stating that each symbol only appears in one leaf in tree `t`.
- `depth t a`        : Depth of symbol `a` in tree `t`.
- `height t`         : Height of the tree `t`.
- `freq t a`         : Frequency of symbol `a` in `t`.
- `weight t`         : Weight of the tree `t`.
- `cost t`           : Cost of tree `t`.
- `optimum t`        : Condition stating that tree `t` is optimal.
- `minima t a b`     : Condition stating that two symbols have the lowest frequencies in tree `t`.
-/

/-
Huffman Tree and Forest definition
-/
inductive HuffmanTree (α : Type) where
  | leaf (w : Nat) (a : α) : HuffmanTree α
  | node (w : Nat) (t1 : HuffmanTree α) (t2 : HuffmanTree α) : HuffmanTree α

abbrev Forest (α) := List (HuffmanTree α)

/-
Alphabet
Set of symbols appearing in a tree
-/
def alphabet {α} [DecidableEq α] : HuffmanTree α → Finset α
  | HuffmanTree.leaf _ a => {a}
  | HuffmanTree.node _ t1 t2 => alphabet t1 ∪ alphabet t2

def alphabetF {α} [DecidableEq α] : Forest α → Finset α
  | [] => Finset.empty
  | t :: ts => alphabet t ∪ alphabetF ts

lemma exists_in_alphabet {α} [DecidableEq α] (t : HuffmanTree α) :
  ∃ a, a ∈ alphabet t := by
  induction t <;> aesop(add norm[alphabet])

lemma alphabet_cases {α} [DecidableEq α]
  (a : α) (t1 t2 : HuffmanTree α)
  (hdis : alphabet t1 ∩ alphabet t2 = ∅) :
  (a ∈ alphabet t1 ∧ a ∉ alphabet t2) ∨
  (a ∉ alphabet t1 ∧ a ∈ alphabet t2) ∨
  (a ∉ alphabet t1 ∧ a ∉ alphabet t2) := by
  by_cases h1 : a ∈ alphabet t1 <;> grind[not_mem_inter_empty]

/-
Consistent
Each symbol only appears in one leaf in a tree

`huffmanTree_induct_consistent` is used as a custom induction rule
-/
def consistent {α} [DecidableEq α] : HuffmanTree α → Prop
  | HuffmanTree.leaf _ _ => True
  | HuffmanTree.node _ t1 t2 => (alphabet t1 ∩ alphabet t2 = ∅) ∧ consistent t1 ∧ consistent t2

def consistentF {α} [DecidableEq α] : Forest α → Prop
  | [] => True
  | t :: ts => (alphabet t ∩ alphabetF ts = ∅) ∧ consistent t ∧ consistentF ts

theorem huffmanTree_induct_consistent {α} [DecidableEq α]
{P : (t : HuffmanTree α) → α → consistent t → Prop}
  {t : HuffmanTree α} (a : α) (hc : consistent t)
    (leaf : ∀ wb b (hc : consistent (HuffmanTree.leaf wb b)),
      P (HuffmanTree.leaf wb b) a hc)
    (left : ∀ w t1 t2 (hc : consistent (HuffmanTree.node w t1 t2))
      (hc1 : consistent t1) (hc2 : consistent t2),
      alphabet t1 ∩ alphabet t2 = ∅ →
      a ∈ alphabet t1 → a ∉ alphabet t2 →
      P t1 a hc1 → P t2 a hc2 →
      P (HuffmanTree.node w t1 t2) a hc)
    (right : ∀ w t1 t2 (hc : consistent (HuffmanTree.node w t1 t2))
      (hc1 : consistent t1) (hc2 : consistent t2),
      alphabet t1 ∩ alphabet t2 = ∅ →
      a ∉ alphabet t1 → a ∈ alphabet t2 →
      P t1 a hc1 → P t2 a hc2 →
      P (HuffmanTree.node w t1 t2) a hc)
    (none : ∀ w t1 t2 (hc : consistent (HuffmanTree.node w t1 t2))
      (hc1 : consistent t1) (hc2 : consistent t2),
      alphabet t1 ∩ alphabet t2 = ∅ →
      a ∉ alphabet t1 → a ∉ alphabet t2 →
      P t1 a hc1 → P t2 a hc2 →
      P (HuffmanTree.node w t1 t2) a hc)
  : P t a hc := by
    induction t <;> grind[not_mem_inter_empty, consistent, alphabet_cases]

/-
Depth
Path length from root to leaf
-/
def depth {α} [DecidableEq α] : HuffmanTree α → α → Nat
  | HuffmanTree.leaf _ _, _ => 0
  | HuffmanTree.node _ t1 t2, a =>
    if a ∈ alphabet t1 then depth t1 a + 1
    else if a ∈ alphabet t2 then depth t2 a + 1
    else 0

/-
Height
Length of longest path from root to leaf
-/
def height {α} : HuffmanTree α → Nat
  | HuffmanTree.leaf _ _ => 0
  | HuffmanTree.node _ t1 t2 => max (height t1) (height t2) + 1

def heightF {α} : Forest α → Nat
  | [] => 0
  | t :: ts => max (height t) (heightF ts)

@[simp]
lemma depth_le_height {α} [DecidableEq α] (t : HuffmanTree α) (a : α) :
  depth t a ≤ height t := by
  induction t <;> aesop(add norm[depth, height])

@[simp]
lemma exists_at_height {α} [DecidableEq α] (t : HuffmanTree α) :
  consistent t → ∃a ∈ alphabet t, depth t a = height t := by
  intro h_consistent
  induction t with
  | leaf w x => aesop (add norm[depth,height, alphabet])
  | node w t1 t2 h1 h2 =>
      simp[alphabet,height,depth]
      grind[mem_inter_empty,consistent]

lemma depth_max_height_left {α} [DecidableEq α]
  (t1 t2 : HuffmanTree α) (a : α)
  (h1 : depth t1 a = max (height t1) (height t2))
  (hh : height t1 ≥ height t2) :
  depth t1 a = height t1 := by aesop

lemma depth_max_height_right {α} [DecidableEq α]
  {t1 t2 : HuffmanTree α} {a : α}
  (h1 : depth t2 a = max (height t1) (height t2))
  (hh : height t2 ≥ height t1) :
  depth t2 a = height t2 := by aesop

lemma height_gt_0_alphabet_eq_imp_height_gt_0 {α} [DecidableEq α] (t u : HuffmanTree α)
  (h_height : height t > 0) (h_consistent : consistent t)
  (h_alphabet_t_u : alphabet t = alphabet u)
  : height u > 0 := by
  cases t with
  | leaf w x => simp [height] at h_height
  | node w t1 t2 =>
      obtain ⟨b, h_b⟩ := exists_in_alphabet t1
      obtain ⟨c, h_c⟩ := exists_in_alphabet t2
      let ⟨h_disj, h_consistent_t1, h_consistent_t2⟩ := h_consistent
      have bc : b ≠ c := by
        intro h_bc
        have h_b_t2 : b ∈ alphabet t2 := by simpa [h_bc] using h_c
        have h_b_t1_t2 := Finset.mem_inter_of_mem h_b h_b_t2
        simp [h_disj] at h_b_t1_t2
      cases u with
      | leaf w a =>
          simp [alphabet] at h_alphabet_t_u
          have hba : b ∈ ({a} : Finset α) := by
            rw [← h_alphabet_t_u]
            exact Finset.mem_union_left _ h_b
          have hca : c ∈ ({a} : Finset α) := by
            rw [← h_alphabet_t_u]
            exact Finset.mem_union_right _ h_c
          grind
      | node w t3 t4 => simp [height]

/-
Frequency
Sum of weight from nodes
-/
def freq {α} [DecidableEq α] : HuffmanTree α → α → Nat
  | HuffmanTree.leaf w a, b => if b = a then w else 0
  | HuffmanTree.node _ t1 t2, b => freq t1 b + freq t2 b

def freqF {α} [DecidableEq α] : Forest α → α → Nat
  | [] , _ => 0
  | t :: ts , b => freq t b + freqF ts b

@[simp]
lemma notin_alphabet_imp_freq_0 {α} [DecidableEq α] (a : α) (t : HuffmanTree α) :
  a ∉ alphabet t → freq t a = 0 := by
  induction t <;> aesop (add norm [alphabet, freq])

@[simp]
lemma notin_alphabetF_imp_freqF_0 {α} [DecidableEq α] (a : α) (ts : Forest α) :
  a ∉ alphabetF ts → freqF ts a = 0 := by
  induction ts <;> aesop (add norm [alphabet, alphabetF, freq, freqF])

@[simp]
lemma freq_0_right {α} [DecidableEq α] (a : α) (t1 t2 : HuffmanTree α)
  (h_disj : alphabet t1 ∩ alphabet t2 = ∅) (h_a_t1 : a ∈ alphabet t1) :
  freq t2 a = 0 := by
  grind[notin_alphabet_imp_freq_0,not_mem_inter_empty]

@[simp]
lemma freq_0_left {α} [DecidableEq α] (a : α) (t1 t2 : HuffmanTree α)
  (h_disj : alphabet t1 ∩ alphabet t2 = ∅) (h_a_t2 : a ∈ alphabet t2) :
  freq t1 a = 0 := by
  grind[notin_alphabet_imp_freq_0, not_mem_inter_empty]

lemma heightF_0_imp_Leaf_freqF_in_set {α} [DecidableEq α] (ts : Forest α) (a : α) :
  consistentF ts →
  heightF ts = 0 →
  a ∈ alphabetF ts →
  HuffmanTree.leaf (freqF ts a) a ∈ ts := by
  intro h_consistent h_height h_alphabet
  induction ts with
  | nil =>
      simp [alphabetF] at h_alphabet
      contradiction
  | cons t ts ih =>
      cases t <;>
      grind[notin_alphabet_imp_freq_0, notin_alphabetF_imp_freqF_0,
            freq, freqF, alphabet, alphabetF, alphabet_cases,
            consistent, consistentF, height, heightF]

/-
Weight
Weight of the tree
-/
def weight {α} : HuffmanTree α → Nat
  | HuffmanTree.leaf w _ => w
  | HuffmanTree.node _ t1 t2 => weight t1 + weight t2

@[simp]
lemma weight_eq_Sum_freq {α} [DecidableEq α] (t : HuffmanTree α) :
  consistent t → weight t = (∑a ∈ alphabet t, freq t a) := by
  intro h_consistent
  induction t with
  | leaf w x => simp [weight, alphabet, freq]
  | node w t1 t2 ih1 ih2 =>
      let ⟨hd, h_consistent_t1, h_consistent_t2⟩ := h_consistent
      have h3 : Disjoint (alphabet t1) (alphabet t2) :=
        Finset.disjoint_iff_inter_eq_empty.mpr hd
      have h_sum_1 : (∑ a ∈ alphabet t1, freq t2 a) = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        exact freq_0_right a t1 t2 hd ha
      have h_sum_2 : (∑ a ∈ alphabet t2, freq t1 a) = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        exact freq_0_left a t1 t2 hd ha
      simp [weight, alphabet, freq]
      rw [ih1 h_consistent_t1, ih2 h_consistent_t2, Finset.sum_union h3]
      simp [Finset.sum_add_distrib, h_sum_1, h_sum_2]

/-
Cost
Sum of freq * depth
-/
def cost {α} : HuffmanTree α → Nat
  | HuffmanTree.leaf _ _ => 0
  | HuffmanTree.node _ t1 t2 => weight t1 + cost t1 + weight t2 + cost t2

theorem cost_eq_Sum_freq_mult_depth
  {α} [DecidableEq α] (t : HuffmanTree α) :
  consistent t →
  cost t = (∑ a ∈ alphabet t, freq t a * depth t a) := by
  induction t with
  | leaf w a => simp [cost, alphabet, freq, depth]
  | node w t1 t2 ih1 ih2 =>
      rintro ⟨h_disj, h_consistent_t1, h_consistent_t2⟩
      let t := HuffmanTree.node w t1 t2
      have w1 := weight_eq_Sum_freq t1 h_consistent_t1
      have w2 := weight_eq_Sum_freq t2 h_consistent_t2
      have h_weight : ∀ (u : HuffmanTree α), consistent u →
          weight u + ∑ a ∈ alphabet u, freq u a * depth u a =
          ∑ a ∈ alphabet u, freq u a * (depth u a + 1) := by
        intro u hu
        simp [weight_eq_Sum_freq, hu, Nat.mul_add, Finset.sum_add_distrib, Nat.add_comm]
      have d1 : ∀ a, a ∈ alphabet t1 → depth t a = depth t1 a + 1 := by
        grind[depth]
      have d2 : ∀ a, a ∈ alphabet t2 → depth t a = depth t2 a + 1 := by
        grind[not_mem_inter_empty,depth]
      calc
        cost (HuffmanTree.node w t1 t2)
            = weight t1 + cost t1 + weight t2 + cost t2 := by simp [cost]
        _ = weight t1 + (∑ a ∈ alphabet t1, freq t1 a * depth t1 a)
                + weight t2 + (∑ a ∈ alphabet t2, freq t2 a * depth t2 a) := by
              rw [ih1 h_consistent_t1, ih2 h_consistent_t2]
        _ = ∑ a ∈ alphabet t1, freq t1 a * (depth t1 a + 1)
            + ∑ a ∈ alphabet t2, freq t2 a * (depth t2 a + 1) := by
              grind
        _ = ∑ a ∈ alphabet t1, freq (HuffmanTree.node w t1 t2) a *
          depth (HuffmanTree.node w t1 t2) a
            + ∑ a ∈ alphabet t2, freq (HuffmanTree.node w t1 t2) a *
              depth (HuffmanTree.node w t1 t2) a := by
              have sum1 :
                ∑ a ∈ alphabet t1, freq t1 a * (depth t1 a + 1)
                  = ∑ a ∈ alphabet t1, freq t a * depth t a := by
                apply Finset.sum_congr rfl
                grind[freq_0_right,freq]
              have sum2 :
                ∑ a ∈ alphabet t2, freq t2 a * (depth t2 a + 1)
                  = ∑ a ∈ alphabet t2, freq (HuffmanTree.node w t1 t2) a *
                    depth (HuffmanTree.node w t1 t2) a := by
                apply Finset.sum_congr rfl
                grind[freq_0_left,freq]
              rw [sum1, sum2]
        _ = ∑ a ∈ alphabet t1 ∪ alphabet t2, freq (HuffmanTree.node w t1 t2) a *
              depth (HuffmanTree.node w t1 t2) a := by
              rw [Finset.sum_union]
              exact Finset.disjoint_iff_inter_eq_empty.mpr h_disj
        _ = ∑ a ∈ alphabet (HuffmanTree.node w t1 t2),
            freq (HuffmanTree.node w t1 t2) a *
            depth (HuffmanTree.node w t1 t2) a := by simp [alphabet]

@[simp]
lemma height_0_imp_cost_0 {α} (t : HuffmanTree α) :
  height t = 0 → cost t = 0 := by
  cases t <;> simp [height, cost]

/-
Optimum
The cost of tree is lower than other comparable tree
-/
def optimum {α} [DecidableEq α] (t : HuffmanTree α) : Prop :=
  ∀ u : HuffmanTree α, consistent u →
    alphabet t = alphabet u →
    freq t = freq u →
    cost t ≤ cost u

/-
Minima
Two symbols have the lowest frequencies in a tree
-/
def minima {α} [DecidableEq α]
  (t : HuffmanTree α) (a b : α) : Prop :=
    a ∈ alphabet t ∧
    b ∈ alphabet t ∧
    a ≠ b ∧
    ∀ c ∈ alphabet t,
      c ≠ a →
      c ≠ b →
      freq t a ≤ freq t c ∧
      freq t b ≤ freq t c

lemma twice_freq_le_imp_minima {α} [DecidableEq α]
  (t u : HuffmanTree α) (a b : α) (wa wb : ℕ)
  (h1 : ∀ c ∈ alphabet t, wa ≤ freq t c ∧ wb ≤ freq t c)
  (h2 : alphabet u = alphabet t ∪ {b})
  (h3 : a ∈ alphabet u)
  (h4 : a ≠ b)
  (h5 : freq u =
    fun c => if c = a then wa else if c = b then wb else freq t c) :
  minima u a b := by grind[minima,alphabet,freq]
