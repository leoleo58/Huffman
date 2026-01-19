import HuffmanAlgorithm.Huffman

def swapLeaves {α} [DecidableEq α] : HuffmanTree α → Nat → α → Nat → α → HuffmanTree α
  | HuffmanTree.leaf wc c, wa, a, wb, b =>
      if c = a then HuffmanTree.leaf wb b
      else if c = b then HuffmanTree.leaf wa a
      else HuffmanTree.leaf wc c
  | HuffmanTree.node w t1 t2, wa, a, wb, b =>
      HuffmanTree.node w (swapLeaves t1 wa a wb b) (swapLeaves t2 wa a wb b)

def swapSyms {α} [DecidableEq α] (t : HuffmanTree α) (a b : α) : HuffmanTree α :=
  swapLeaves t (freq t a) a (freq t b) b

def swapFourSyms {α} [DecidableEq α] (t : HuffmanTree α) (a b c d : α) : HuffmanTree α :=
  if a = d then swapSyms t b c
  else if b = c then swapSyms t a d
  else swapSyms (swapSyms t a c) b d

def mergeSibling {α} [DecidableEq α] : HuffmanTree α → α → HuffmanTree α
  | HuffmanTree.leaf wb b, _ => HuffmanTree.leaf wb b
  | HuffmanTree.node w (HuffmanTree.leaf wb b) (HuffmanTree.leaf wc c), a =>
      if a = b ∨ a = c then HuffmanTree.leaf (wb + wc) a
      else HuffmanTree.node w (HuffmanTree.leaf wb b) (HuffmanTree.leaf wc c)
  | HuffmanTree.node w (HuffmanTree.node v va vb) t2, a =>
      HuffmanTree.node w (mergeSibling (HuffmanTree.node v va vb) a) (mergeSibling t2 a)
  | HuffmanTree.node w t1 (HuffmanTree.node v va vb), a =>
      HuffmanTree.node w (mergeSibling t1 a) (mergeSibling (HuffmanTree.node v va vb) a)

def sibling {α} [DecidableEq α] : HuffmanTree α → α → α
  | HuffmanTree.leaf _ _, a => a
  | HuffmanTree.node _ (HuffmanTree.leaf _ b) (HuffmanTree.leaf _ c), a =>
      if a = b then c else if a = c then b else a
  | HuffmanTree.node _ t1 t2, a =>
      if a ∈ alphabet t1 then sibling t1 a
      else if a ∈ alphabet t2 then sibling t2 a
      else a

def splitLeaf {α} [DecidableEq α] : HuffmanTree α → Nat → α → Nat → α → HuffmanTree α
  | HuffmanTree.leaf wc c, wa, a, wb, b =>
      if c = a then HuffmanTree.node wc (HuffmanTree.leaf wa a) (HuffmanTree.leaf wb b)
      else HuffmanTree.leaf wc c
  | HuffmanTree.node w t1 t2, wa, a, wb, b =>
      HuffmanTree.node w (splitLeaf t1 wa a wb b) (splitLeaf t2 wa a wb b)

def splitLeafF {α} [DecidableEq α] : Forest α → Nat → α → Nat → α → Forest α
  | [] , _, _, _, _ => []
  | t :: ts , wa, a, wb, b => splitLeaf t wa a wb b :: splitLeafF ts wa a wb b

def sortedByWeight {α} : Forest α → Prop
  | [] => true
  | [_] => true
  | t1 :: t2 :: ts => weight t1 ≤ weight t2 ∧ sortedByWeight (t2 :: ts)

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
