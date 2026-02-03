import HuffmanAlgorithm.Basic

/-!
# Huffman Algorithm Construction

This file contains the algorithm of the Huffman Tree.
It defines functions used in the construction of Huffman trees,
such as cached weight, tree union, and insertion into tree.
Based on these functions, it formalizes the Huffman algorithm.
The file also includes lemmas that establish basic correctness and
structural properties of these constructions.

## Definitions

- `cachedWeight t`    : Computes the weight of tree `t`.
- `uniteTrees t1 t2`  : Combines two Huffman trees into a single tree with summed weight.
- `insortTree t ts`   : Inserts tree `t` into forest `ts`.
- `huffman ts h`      : Recursively constructs the Huffman tree from a non-empty forest `ts`.
-/

/-
cachedWeight
-/
def cachedWeight {α} : HuffmanTree α → Nat
  | HuffmanTree.leaf w _ => w
  | HuffmanTree.node w _ _ => w

@[simp]
lemma height_0_imp_cachedWeight_eq_weight {α} (t : HuffmanTree α) :
  height t = 0 → cachedWeight t = weight t := by
  aesop (add norm[weight, cachedWeight,height])

/-
uniteTrees
-/
def uniteTrees {α} (t1 t2 : HuffmanTree α) : HuffmanTree α :=
  HuffmanTree.node (cachedWeight t1 + cachedWeight t2) t1 t2

@[simp]
lemma alphabet_uniteTrees {α : Type} [DecidableEq α] (t1 t2 : HuffmanTree α) :
  alphabet (uniteTrees t1 t2) = alphabet t1 ∪ alphabet t2 := by simp [uniteTrees, alphabet]

@[simp]
lemma consistent_uniteTrees {α : Type} [DecidableEq α] (t1 t2 : HuffmanTree α)
  (h_consistent_t1 : consistent t1) (h_consisstent_t2 : consistent t2)
  (h_disj : alphabet t1 ∩ alphabet t2 = ∅) :
  consistent (uniteTrees t1 t2) := by simp_all [uniteTrees, consistent]

@[simp]
lemma freq_uniteTrees {α : Type} [DecidableEq α] (t1 t2 : HuffmanTree α) (a : α) :
  freq (uniteTrees t1 t2) a = freq t1 a + freq t2 a := by simp [uniteTrees, freq]

/-
insortTree
-/
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

@[simp]
lemma alphabetF_insortTree {α : Type} [DecidableEq α] (u : HuffmanTree α) (ts : Forest α) :
  alphabetF (insortTree u ts) = alphabet u ∪ alphabetF ts := by
  induction ts <;> aesop(add norm[insortTree, alphabetF,alphabet])

@[simp]
lemma consistentF_insortTree {α : Type} [DecidableEq α] (u : HuffmanTree α) (ts : Forest α) :
  consistentF (insortTree u ts) = consistentF ( u :: ts ):= by
  induction ts <;>
  simp[insortTree] ;
  grind[consistentF,alphabetF_insortTree, alphabetF]

@[simp]
lemma freqF_insortTree {α : Type} [DecidableEq α] (u : HuffmanTree α) (ts : Forest α) :
  freqF (insortTree u ts) = fun a => freq u a + freqF ts a := by
  ext a
  induction ts <;> aesop (add norm[insortTree, freqF,freq, add_left_comm])

@[simp]
lemma heightF_insortTree {α : Type} (u : HuffmanTree α) (ts : Forest α) :
  heightF (insortTree u ts) = max (height u) (heightF ts) := by
  induction ts <;> aesop (add norm[heightF, max_left_comm, height, insortTree])

/-
Huffman's algorithm
-/
def huffman {α} (xs : Forest α) (h : xs ≠ []) : HuffmanTree α :=
  match xs with
  | [t]      => t
  | t1 :: t2 :: ts =>
      huffman (insortTree (uniteTrees t1 t2) ts) (insortTree_ne_nil _ _)
termination_by xs.length

@[simp]
lemma alphabet_huffman {α} [DecidableEq α] (ts : Forest α) (h : ts ≠ []) :
  alphabet (huffman ts h) = alphabetF ts := by
  induction ts, h using huffman.induct with
  | case1 t h1 h2 =>
      simp [alphabetF, huffman]
      exact Finset.inter_eq_left.mp rfl
  | case2 t1 t2 ts h1 h2 ih =>
      simp [huffman, alphabetF, ih, Finset.union_left_comm, Finset.union_comm]

@[simp]
lemma consistent_huffman {α} [DecidableEq α] (ts : Forest α) (h : ts ≠ []) :
  consistentF ts → consistent (huffman ts h) := by
  induction ts, h using huffman.induct with
  | case1 t h1 h2 => simp [consistentF, huffman]
  | case2 t1 t2 ts h1 h2 ih =>
      simp [consistentF, alphabetF, Finset.inter_union_distrib_left] at ih ⊢
      grind[consistent_uniteTrees, consistent,huffman,consistentF]

@[simp]
lemma freq_huffman {α} [DecidableEq α] (ts : Forest α) (a : α) (h : ts ≠ []) :
  freq (huffman ts h) a = freqF ts a := by
  induction ts, h using huffman.induct <;> simp [freqF, huffman]
  rename_i ih
  simp [ih]
  linarith
