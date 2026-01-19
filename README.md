# Huffman's Algorithm in Lean4

This repository contains a formalization of the Huffman coding algorithm in Lean 4, including:

- A HuffmanTree datatype
- Functions for computing weights, frequencies, consistency,...
- The Huffman merging algorithm
- Supporting lemmas
- Huffman's optimality theorem

## Project Structure

```
HuffmanAlgorithm/
├─ Huffman.lean       # Huffman tree datatype, cachedWeight, uniteTrees, insortTree, huffman algorithm, Basic definitions: alphabet, consistent, depth, height, freq, weight, cost, optimum
├─ Function.lean      # Helper functions: swapSyms, swapLeaves, swapFourSyms, mergeSibling, splitLeaf
├─ Lemmas.lean        # Lemmas about Huffman
├─ Lemmas2.lean       # More lemmas about Huffman
HuffmanAlgorithm.lean # Optimum theorem
```
