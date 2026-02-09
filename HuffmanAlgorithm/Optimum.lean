import HuffmanAlgorithm.OptimalityLemmas

/-!
# Optimality of Huffman Trees

This file contains the main theorem proving the optimality of Huffman trees.

Huffman’s algorithm constructs a tree that minimizes the total cost
for a given set of symbol frequencies.

## Main Result

Theorem `optimum_huffman` : Shows that the Huffman tree built from any non-empty forest is optimal,
  no other tree with the same alphabet and frequencies has lower cost.
-/

/--
The Huffman tree constructed from a forest `ts` using the `huffman` function
is optimal.
-/
theorem optimum_huffman {α : Type} [d : DecidableEq α] (ts : Forest α)
  (hcf : consistentF ts)
  (hh : heightF ts = 0)
  (hs : sortedByWeight ts)
  (hne : ts ≠ []) :
  optimum (huffman ts hne) := by
  induction h : ts.length using Nat.strong_induction_on generalizing ts with
  | h n ih =>
    cases ts with
    | nil => exact False.elim (hne rfl)
    | cons ta ts' =>
        cases ts' with
          | nil =>
              grind [optimum,huffman,heightF,height_0_imp_cost_0]
          | cons tb ts'' =>
              cases ta with
              | leaf wa a =>
                  cases tb with
                  | leaf wb b =>
                    simp [consistentF] at hcf
                    let ⟨hcfd , hca, hdbf, hcb, hcfts ⟩ := hcf
                    let ta := HuffmanTree.leaf wa a
                    let tb := HuffmanTree.leaf wb b
                    let us := insortTree (uniteTrees ta tb) ts''
                    let us' := insortTree (HuffmanTree.leaf (wa + wb) a) ts''
                    have hus' : us' ≠ [] := by simp [us']
                    let ts := splitLeaf (huffman us' hus') wa a wb b
                    have e1 : huffman (HuffmanTree.leaf wa a
                      :: HuffmanTree.leaf wb b :: ts'') hne  =
                      huffman us (insortTree_ne_nil _ _) := by
                        aesop (add norm[huffman, us, uniteTrees])
                    -- hafts used in e2 and hopt1 case c = a
                    have hafts : a ∉ alphabetF ts'' := by aesop (add norm[alphabet, alphabetF])
                    have e2 : huffman us (insortTree_ne_nil _ _) = ts := by
                      aesop (add norm[splitLeaf, uniteTrees, freq, consistent, consistentF,
                                      alphabet, alphabetF])
                    have hoptus' : optimum (huffman us' hus') := by
                      have hconus : consistentF us' := by
                        aesop (add norm[consistentF, consistent, alphabet, alphabetF])
                      have hhus' : heightF us' = 0 := by aesop(add norm[heightF,height])
                      have hlenus'1 : us'.length < n := by aesop
                      grind[sortedByWeight_insortTree, heightF, height,
                            sortedByWeight_Cons_imp_sortedByWeight]
                    have hopt1 : optimum ts := by
                      have ho:= optimum_splitLeaf (huffman us' hus') a b wa wb
                      have ho1: ∀ c ∈ alphabetF us', wa ≤ freqF us' c ∧ wb ≤ freqF us' c := by
                        intro c hc
                        by_cases hca : c = a
                        · aesop(add norm[freq, freqF,alphabet, alphabetF])
                        · have hleaf : HuffmanTree.leaf (freqF us' c) c ∈ ts'' := by
                            aesop(add norm[heightF,freq,height,alphabet, alphabetF,
                                            heightF_0_imp_Leaf_freqF_in_set])
                          have hw := sortedByWeight_Cons_imp_forall_weight_ge tb ts''
                                      (sortedByWeight_Cons_imp_sortedByWeight ta (tb :: ts'') hs)
                          have hwafreq: wa ≤ freqF us' c := by
                            have hweighttatb : weight ta ≤ weight tb :=
                              sortedByWeight_Cons_imp_forall_weight_ge ta
                              (tb :: ts'') hs tb (by simp)
                            grind[height_0_imp_cachedWeight_eq_weight, weight]
                          grind[weight]
                      have hbus': b ∉ alphabetF us' := by
                        aesop(add norm[alphabet,alphabetF])
                      aesop(add norm[consistentF, consistent, alphabet, alphabetF,
                                      consistent_huffman,huffman,freq,freqF])
                    simpa [e1, e2] using hopt1
                  | node w t1 t2 => simp [heightF, height] at hh
              | node w t1 t2 => simp [heightF, height] at hh
