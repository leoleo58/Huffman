import HuffmanAlgorithm.Algorithm

/-!
# Structural properties and operations of Huffman trees

This file formalizes structural properties of Huffman trees.
It defines sibling relations, merging sibling nodes, and splitting leaf nodes,
as well as the condition `sortedByWeight`, which states that a forest
is sorted according to the weights of its trees.
Lemmas accompanying each definition formalize their structural properties.

## Main definitions

- `sibling t a`            : Returns the sibling of symbol `a` in tree `t`.
- `mergeSibling t a`       : Combines a pair of sibling nodes into a single node.
- `splitLeaf t wa a wb b`  : Splits a leaf into two leaves.
- `sortedByWeight ts`      : Predicate stating that a list of trees `ts` is sorted by weight.
-/

/--
Returns the label of the node that is the sibling (left or right) of the symbol `a`

- If `a` is not in the tree or the tree is a leaf, returns `a`.
- If `a` is in a node, returns its sibling in the left or right subtree.
-/
def sibling {α} [DecidableEq α] : HuffmanTree α → α → α
  | HuffmanTree.leaf _ _, a => a
  | HuffmanTree.node _ (HuffmanTree.leaf _ b) (HuffmanTree.leaf _ c), a =>
      if a = b then c else if a = c then b else a
  | HuffmanTree.node _ t1 t2, a =>
      if a ∈ alphabet t1 then sibling t1 a
      else if a ∈ alphabet t2 then sibling t2 a
      else a

@[simp]
lemma notin_alphabet_imp_sibling_id {α} [DecidableEq α] (t : HuffmanTree α) (a : α) :
  a ∉ alphabet t → sibling t a = a := by
  intro h_a
  cases t with
  | leaf w x => simp [sibling]
  | node w t1 t2 =>
    cases t1 <;> cases t2 <;> aesop (add norm[sibling,alphabet])

@[simp]
lemma height_0_imp_sibling_id {α} [DecidableEq α] (t : HuffmanTree α) (a : α) :
  height t = 0 → sibling t a = a := by
  cases t <;> simp[sibling,height]

@[simp]
lemma height_gt_0_in_alphabet_imp_sibling_left {α} [DecidableEq α]
  (t1 t2 : HuffmanTree α) (a : α) (w : ℕ) :
  height t1 > 0 → a ∈ alphabet t1 → sibling (HuffmanTree.node w t1 t2) a = sibling t1 a := by
  cases t1 <;> aesop (add norm [height,sibling])

@[simp]
lemma height_gt_0_in_alphabet_imp_sibling_right {α} [DecidableEq α]
  (t1 t2 : HuffmanTree α) (a : α) (w : ℕ) :
  height t2 > 0 → a ∈ alphabet t1 → sibling (HuffmanTree.node w t1 t2) a = sibling t1 a := by
  cases t2 <;> aesop (add norm [height,sibling])

@[simp]
lemma height_gt_0_notin_alphabet_imp_sibling_left {α} [DecidableEq α]
  (t1 t2 : HuffmanTree α) (a : α) (w : ℕ) :
  height t1 > 0 → a ∉ alphabet t1 → sibling (HuffmanTree.node w t1 t2) a = sibling t2 a := by
  cases t1 <;> aesop (add norm [height,sibling])

@[simp]
lemma height_gt_0_notin_alphabet_imp_sibling_right {α} [DecidableEq α]
  (t1 t2 : HuffmanTree α) (a : α) (w : ℕ) :
  height t2 > 0 → a ∉ alphabet t1 → sibling (HuffmanTree.node w t1 t2) a = sibling t2 a := by
  cases t2 <;> aesop (add norm [height,sibling])

@[simp]
lemma either_height_gt_0_imp_sibling {α} [DecidableEq α]
  (t1 t2 : HuffmanTree α) (a : α) (w : ℕ) :
  height t1 > 0 ∨ height t2 > 0 →
  sibling (HuffmanTree.node w t1 t2) a =
  (if a ∈ alphabet t1 then sibling t1 a else sibling t2 a) := by
  aesop

@[simp]
lemma in_alphabet_imp_sibling_in_alphabet {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α) :
  a ∈ alphabet t → sibling t a ∈ alphabet t := by
  induction t, a using sibling.induct <;> aesop (add norm [alphabet,sibling])

@[simp]
lemma sibling_ne_imp_sibling_in_alphabet {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α) :
  sibling t a ≠ a → sibling t a ∈ alphabet t := by
  by_cases h_a : a ∈ alphabet t <;> aesop

/--
A custom induction rule for Huffman trees using sibling and consistency.
It is used to simplify proofs.
-/
theorem sibling_induct_consistent {α} [DecidableEq α]
  {P : (t : HuffmanTree α) → α → consistent t → Prop}
  {t : HuffmanTree α} (a : α) (hc : consistent t)
  (leaf : ∀ w b (hc : consistent (HuffmanTree.leaf w b)),
    P (HuffmanTree.leaf w b) a hc)
  (step1 : ∀ w wb b wc c
  (hc : consistent (HuffmanTree.node w (HuffmanTree.leaf wb b) (HuffmanTree.leaf wc c))),
    b ≠ c → P (HuffmanTree.node w (HuffmanTree.leaf wb b) (HuffmanTree.leaf wc c)) a hc)
  (step21 : ∀ w t1 t2 (hc : consistent (HuffmanTree.node w t1 t2))
    (hc1 : consistent t1) (hc2 : consistent t2),
    alphabet t1 ∩ alphabet t2 = ∅ →
    (height t1 > 0 ∨ height t2 > 0) →
    a ∈ alphabet t1 →
    sibling t1 a ∈ alphabet t1 →
    a ∉ alphabet t2 →
    sibling t1 a ∉ alphabet t2 →
    P t1 a hc1 →
    P (HuffmanTree.node w t1 t2) a hc)
  (step22 : ∀ w t1 t2 (hc : consistent (HuffmanTree.node w t1 t2))
    (hc1 : consistent t1) (hc2 : consistent t2),
    alphabet t1 ∩ alphabet t2 = ∅ →
    (height t1 > 0 ∨ height t2 > 0) →
    a ∉ alphabet t1 →
    sibling t2 a ∉ alphabet t1 →
    a ∈ alphabet t2 →
    sibling t2 a ∈ alphabet t2 →
    P t2 a hc2 →
    P (HuffmanTree.node w t1 t2) a hc)
  (step23 : ∀ w t1 t2 (hc : consistent (HuffmanTree.node w t1 t2))
    (hc1 : consistent t1) (hc2 : consistent t2),
    alphabet t1 ∩ alphabet t2 = ∅ →
    (height t1 > 0 ∨ height t2 > 0) →
    a ∉ alphabet t1 →
    a ∉ alphabet t2 →
    P (HuffmanTree.node w t1 t2) a hc)
  : P t a hc := by
  induction t with
  | leaf w b => exact leaf w b hc
  | node w1 t1 t2 ih1 ih2 =>
      let ⟨h_disj, h_consistent_t1, h_consistent_t2⟩ := hc
      cases t1 <;> cases t2 <;>
      grind[mem_inter_empty, in_alphabet_imp_sibling_in_alphabet,
            alphabet_cases, height, alphabet, consistent]

/--
For a consistent tree, applying `sibling` twice returns the original symbol.
-/
@[simp]
lemma sibling_sibling_id {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α) :
  consistent t → sibling t (sibling t a) = a := by
  intro h_consistent
  induction a, h_consistent using sibling_induct_consistent <;> aesop (add norm [sibling])

/--
In a consistent tree, if `a` is the sibling of `b`, then `b` is the sibling of `a`.
-/
@[simp]
lemma sibling_reciprocal {α} [DecidableEq α]
  (t : HuffmanTree α) (a b : α) :
  consistent t → sibling t a = b → sibling t b = a := by aesop

lemma depth_height_imp_sibling_ne {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α)
  (h_consistent : consistent t) (h_depth_height : depth t a = height t)
  (h_height : height t > 0) (h_a_t : a ∈ alphabet t) :
  sibling t a ≠ a := by
  induction a, h_consistent using sibling_induct_consistent <;>
  simp[*] <;>
  grind[height, depth, alphabet, depth_le_height, sibling]

/--
Siblings have equal depth in a consistent tree.
-/
@[simp]
lemma depth_sibling {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α) :
  consistent t → depth t (sibling t a) = depth t a := by
  intro h_consistent
  induction a, h_consistent using sibling_induct_consistent <;>
  aesop (add norm [depth, alphabet, sibling])

/--
Merge a pair of sibling nodes into a single node.
-/
def mergeSibling {α} [DecidableEq α] : HuffmanTree α → α → HuffmanTree α
  | HuffmanTree.leaf wb b, _ => HuffmanTree.leaf wb b
  | HuffmanTree.node w (HuffmanTree.leaf wb b) (HuffmanTree.leaf wc c), a =>
      if a = b ∨ a = c then HuffmanTree.leaf (wb + wc) a
      else HuffmanTree.node w (HuffmanTree.leaf wb b) (HuffmanTree.leaf wc c)
  | HuffmanTree.node w (HuffmanTree.node v va vb) t2, a =>
      HuffmanTree.node w (mergeSibling (HuffmanTree.node v va vb) a) (mergeSibling t2 a)
  | HuffmanTree.node w t1 (HuffmanTree.node v va vb), a =>
      HuffmanTree.node w (mergeSibling t1 a) (mergeSibling (HuffmanTree.node v va vb) a)

@[simp]
lemma notin_alphabet_imp_mergeSibling_id {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α) :
  a ∉ alphabet t → mergeSibling t a = t := by
  induction t,a using mergeSibling.induct <;> grind[alphabet,mergeSibling]

@[simp]
lemma height_gt_0_imp_mergeSibling_left {α} [DecidableEq α]
  (t1 t2 : HuffmanTree α) (a : α) (w : ℕ) :
  height t1 > 0 → mergeSibling (HuffmanTree.node w t1 t2) a =
  HuffmanTree.node w (mergeSibling t1 a) (mergeSibling t2 a) := by
  cases t1 <;> aesop (add norm [mergeSibling, height])

@[simp]
lemma height_gt_0_imp_mergeSibling_right {α} [DecidableEq α]
  (t1 t2 : HuffmanTree α) (a : α) (w : ℕ) :
  height t2 > 0 → mergeSibling (HuffmanTree.node w t1 t2) a =
  HuffmanTree.node w (mergeSibling t1 a) (mergeSibling t2 a) := by
  cases t2 <;> cases t1 <;> aesop (add norm [mergeSibling, height])

@[simp]
lemma either_height_gt_0_imp_mergeSibling {α} [DecidableEq α]
  (t1 t2 : HuffmanTree α) (a : α) (w : ℕ) :
  height t1 > 0 ∨ height t2 > 0 → mergeSibling (HuffmanTree.node w t1 t2) a =
  HuffmanTree.node w (mergeSibling t1 a) (mergeSibling t2 a) := by aesop

/--
Merging siblings `a` updates the alphabet by replacing the original sibling with `a`.
-/
@[simp]
lemma alphabet_mergeSibling {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α)
  (h_consistent : consistent t) (h_a : a ∈ alphabet t) :
  alphabet (mergeSibling t a) = (alphabet t \ {sibling t a}) ∪ {a} := by
  induction a, h_consistent using sibling_induct_consistent
  <;> aesop (add norm [alphabet, mergeSibling, sibling])

@[simp]
lemma consistent_mergeSibling {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α) :
  consistent t → consistent (mergeSibling t a) := by
  intro hc
  induction a, hc using sibling_induct_consistent <;>
  grind[either_height_gt_0_imp_mergeSibling, alphabet_mergeSibling,
        notin_alphabet_imp_mergeSibling_id, consistent, mergeSibling, alphabet]

@[simp]
lemma freq_mergesibling {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α)
  (h_consistent : consistent t) (h_a : a ∈ alphabet t) (h_sib : sibling t a ≠ a) :
  freq (mergeSibling t a) =
  fun c => if c = a then freq t a + freq t (sibling t a)
            else if c = sibling t a then 0
            else freq t c := by
  induction a, h_consistent using sibling_induct_consistent <;>
    grind[freq, alphabet, consistent, mergeSibling, sibling,
          notin_alphabet_imp_freq_0,
          notin_alphabet_imp_mergeSibling_id,
          either_height_gt_0_imp_sibling,
          either_height_gt_0_imp_mergeSibling]

/--
Merging siblings does not change the weight of the tree.
-/
@[simp]
lemma weight_mergeSibling {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α) :
  weight (mergeSibling t a) = weight t := by
  induction t, a using mergeSibling.induct <;> grind[weight, mergeSibling]

/--
The cost of merged tree plus the frequencies of `a` and its
sibling equals the original cost.
-/
@[simp]
lemma cost_mergeSibling {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α)
  (h_consistent : consistent t) (h_sib : sibling t a ≠ a) :
  cost (mergeSibling t a) + freq t a + freq t (sibling t a) = cost t := by
  induction a, h_consistent using sibling_induct_consistent <;>
  grind[mergeSibling, cost, freq,weight, sibling, consistent, alphabet,
        weight_mergeSibling,notin_alphabet_imp_sibling_id,
        notin_alphabet_imp_mergeSibling_id,either_height_gt_0_imp_sibling,
        notin_alphabet_imp_freq_0,sibling,either_height_gt_0_imp_mergeSibling]

/--
Split a leaf node into two leaves `a` and `b` with
weights `wa` and `wb`. This undos the merging from mergeSibling.
-/
def splitLeaf {α} [DecidableEq α] : HuffmanTree α → Nat → α → Nat → α → HuffmanTree α
  | HuffmanTree.leaf wc c, wa, a, wb, b =>
      if c = a then HuffmanTree.node wc (HuffmanTree.leaf wa a) (HuffmanTree.leaf wb b)
      else HuffmanTree.leaf wc c
  | HuffmanTree.node w t1 t2, wa, a, wb, b =>
      HuffmanTree.node w (splitLeaf t1 wa a wb b) (splitLeaf t2 wa a wb b)

def splitLeafF {α} [DecidableEq α] : Forest α → Nat → α → Nat → α → Forest α
  | [] , _, _, _, _ => []
  | t :: ts , wa, a, wb, b => splitLeaf t wa a wb b :: splitLeafF ts wa a wb b

@[simp]
lemma notin_alphabet_imp_splitLeaf_id {α} [DecidableEq α]
(t : HuffmanTree α) (wa wb : Nat) (a b : α) :
  a ∉ alphabet t → splitLeaf t wa a wb b = t := by
  induction t <;> grind [alphabet, splitLeaf]

@[simp]
lemma notin_alphabetF_imp_splitLeafF_id {α} [DecidableEq α]
(ts : Forest α) (wa wb : Nat) (a b : α) :
  a ∉ alphabetF ts → splitLeafF ts wa a wb b = ts := by
  induction ts <;> aesop(add norm[alphabetF, splitLeafF,alphabet,splitLeaf])

/--
The alphabet after splitting a leaf into `a` and `b`.
Adds `b` to the alphabet if `a` is in the tree.
-/
@[simp]
lemma alphabet_splitLeaf {α} [DecidableEq α] (t : HuffmanTree α) (wa wb : Nat) (a b : α) :
    alphabet (splitLeaf t wa a wb b) = if a ∈ alphabet t then alphabet t ∪ {b} else alphabet t := by
  induction t <;> grind [splitLeaf, alphabet]

@[simp]
lemma consistent_splitLeaf {α} [DecidableEq α] (t : HuffmanTree α) (wa wb : Nat) (a b : α)
  (h_consistent : consistent t) (h_b : b ∉ alphabet t) : consistent (splitLeaf t wa a wb b) := by
  induction t with
  | leaf w x => grind [splitLeaf,consistent, alphabet]
  | node w t1 t2 ih1 ih2 =>
      grind[mem_inter_empty,alphabet,consistent,splitLeaf,alphabet_splitLeaf]

@[simp]
lemma freq_splitLeaf {α} [DecidableEq α] (t : HuffmanTree α)
  (wa wb : Nat) (a b c : α)
  (h_consistent : consistent t) (h_b : b ∉ alphabet t) :
  freq (splitLeaf t wa a wb b) c =
    if a ∈ alphabet t then
      if c = a then wa else if c = b then wb else freq t c
    else freq t c := by
    induction a, h_consistent using huffmanTree_induct_consistent <;>
      aesop (add norm [freq, alphabet, splitLeaf])

/--
Splitting a leaf preserves weight of the tree.
-/
@[simp]
lemma weight_splitLeaf {α} [DecidableEq α] (t : HuffmanTree α) (wa wb : Nat) (a b : α)
  (h_consistent : consistent t) (h_a : a ∈ alphabet t) (h_freq : freq t a = wa + wb) :
  weight (splitLeaf t wa a wb b) = weight t := by
  induction a, h_consistent using huffmanTree_induct_consistent <;>
    aesop (add norm [weight,splitLeaf,alphabet,freq])

/--
The cost of the tree after splitting a leaf into `a` and `b`
increases the cost of the tree by `wa + wb`.
-/
lemma cost_splitLeaf {α} [DecidableEq α] (t : HuffmanTree α) (wa wb : Nat) (a b : α) :
  consistent t → a ∈ alphabet t → freq t a = wa + wb →
  cost (splitLeaf t wa a wb b) = cost t + wa + wb := by
  intro h_consistent h_alphabet h_freq
  induction a, h_consistent using huffmanTree_induct_consistent with
  | leaf wb b h_consistent => grind [splitLeaf, cost, alphabet, freq,weight]
  | left w t1 t2 h_consistent h_consistent1 h_consistent2 hd h_alphabet1 h_alphabet2 h1 h2 =>
      have h3 := notin_alphabet_imp_freq_0 a t2 h_alphabet2
      simp [freq, h3] at h_freq
      simp [h_alphabet1, h_freq] at h1
      have h4 := weight_splitLeaf (HuffmanTree.node w t1 t2) wa wb a b h_consistent h_alphabet
      simp [freq, h3, h_freq, weight,splitLeaf] at h4
      simp [cost, splitLeaf, h1]
      calc
        weight (splitLeaf t1 wa a wb b) + (cost t1 + wa + wb) +
        weight (splitLeaf t2 wa a wb b) + cost (splitLeaf t2 wa a wb b) =
        weight (splitLeaf t1 wa a wb b) + weight (splitLeaf t2 wa a wb b) +
        cost t1 + wa + wb + cost (splitLeaf t2 wa a wb b) := by ring
        _ = weight t1 + weight t2 + cost t1 + wa + wb + cost t2 := by
            aesop (add norm [h4, cost, weight, splitLeaf])
        _ = weight t1 + cost t1 + weight t2 + cost t2 + wa + wb := by ring
  | right w t1 t2 h_consistent h_consistent1 h_consistent2 hd h_alphabet1 h_alphabet2 h1 h2 =>
      have h3 := notin_alphabet_imp_freq_0 a t1 h_alphabet1
      simp [freq, h3] at h_freq
      simp [h_alphabet2, h_freq] at h2
      have h4 := weight_splitLeaf (HuffmanTree.node w t1 t2) wa wb a b h_consistent h_alphabet
      simp [freq, h3, h_freq, weight,splitLeaf] at h4
      simp [cost, splitLeaf, h2]
      calc
        weight (splitLeaf t1 wa a wb b) + cost (splitLeaf t1 wa a wb b) +
        weight (splitLeaf t2 wa a wb b) + (cost t2 + wa + wb) =
        weight (splitLeaf t1 wa a wb b) + weight (splitLeaf t2 wa a wb b) +
        cost (splitLeaf t1 wa a wb b) + cost t2 + wa + wb := by ring
        _ = weight t1 + weight t2 + cost t1 + cost t2 + wa + wb := by
            aesop (add norm [h4, cost, weight, splitLeaf])
        _ = weight t1 + cost t1 + weight t2 + cost t2 + wa + wb := by ring
  | none w t1 t2 h_consistent h_consistent1 h_consistent2 hd h_alphabet1 h_alphabet2 h1 h2 =>
      aesop(add norm [alphabet])

@[simp]
lemma cachedWeight_splitLeaf {α : Type} [DecidableEq α]
(t : HuffmanTree α) (a b : α) (wa wb : Nat) :
  cachedWeight (splitLeaf t wa a wb b) = cachedWeight t := by
  cases t <;> grind [splitLeaf, cachedWeight]

@[simp]
lemma splitLeafF_insortTree_when_in_alphabet_left {α : Type} [DecidableEq α]
  (t : HuffmanTree α) (ts : Forest α) (a b : α) (wa wb : Nat)
  (h_a : a ∈ alphabet t) (h_consistent : consistent t)
  (h_a_ts : a ∉ alphabetF ts) (h_freq : freq t a = wa + wb) :
  splitLeafF (insortTree t ts) wa a wb b =
    insortTree (splitLeaf t wa a wb b) ts := by
  induction ts <;> aesop (add norm [splitLeaf, splitLeafF, insortTree,alphabetF,alphabet])

@[simp]
lemma splitLeafF_insortTree_when_in_alphabetF_tail {α : Type} [DecidableEq α]
  (t : HuffmanTree α) (ts : Forest α) (a b : α) (wa wb : Nat)
  (h_a_ts : a ∈ alphabetF ts) (h_consistent : consistentF ts)
  (h_a : a ∉ alphabet t) (h_freq : freqF ts a = wa + wb) :
  splitLeafF (insortTree t ts) wa a wb b =
    insortTree t (splitLeafF ts wa a wb b) := by
  induction ts with
  | nil => aesop (add norm[splitLeafF, insortTree])
  | cons u us ih =>
      simp [consistentF] at h_consistent
      by_cases hau : a ∈ alphabet u
      · have haus : a ∉ alphabetF us := by grind[not_mem_inter_empty]
        aesop (add norm [splitLeaf, splitLeafF, insortTree])
      · simp [alphabetF, hau] at h_a_ts
        simp [freqF, notin_alphabet_imp_freq_0 a u hau] at h_freq
        aesop (add norm [splitLeaf, splitLeafF, insortTree, freqF])

lemma splitLeafF_nonempty {α : Type} [DecidableEq α]
  {ts : Forest α} {wa wb : Nat} {a b : α} (hne : ts ≠ []) :
  splitLeafF ts wa a wb b ≠ [] := by
  cases ts <;> grind[splitLeafF]

/--
Condition stating that a forest `ts` is sorted by weight.
-/
def sortedByWeight {α} : Forest α → Prop
  | [] => true
  | [_] => true
  | t1 :: t2 :: ts => weight t1 ≤ weight t2 ∧ sortedByWeight (t2 :: ts)

@[simp]
lemma sortedByWeight_Cons_imp_sortedByWeight {α}
  (t : HuffmanTree α) (ts : Forest α) :
  sortedByWeight (t :: ts) → sortedByWeight ts := by
  cases ts <;> simp [sortedByWeight]

@[simp]
lemma sortedByWeight_Cons_imp_forall_weight_ge {α}
  (t : HuffmanTree α) (ts : Forest α) :
  sortedByWeight (t :: ts) → ∀u ∈ ts, weight u ≥ weight t := by
  induction ts generalizing t <;> grind[sortedByWeight]

/--
Inserting a tree into a forest that is sorted by weight preserves sorting.
-/
@[simp]
lemma sortedByWeight_insortTree {α}
  (t : HuffmanTree α) (ts : Forest α)
  (h_sbw : sortedByWeight ts) (h_height_t : height t = 0) (h_height_ts : heightF ts = 0) :
  sortedByWeight (insortTree t ts) := by
  induction ts using sortedByWeight.induct <;>
    grind[heightF, insortTree,height_0_imp_cachedWeight_eq_weight,sortedByWeight]
