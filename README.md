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
├─ BasicLemmas.lean       # Basic lemmas used for proof
├─ Basic.lean             # Huffman tree definition and properties
├─ Algorithm.lean         # Huffman's Algorithm and tree building operation
├─ TreeStructure.lean     # Structure of Huffman tree
├─ Transformations.lean   # Structural transformation operations
├─ OptimalityLemmas.lean  # Lemmas for Optimum Theorem
├─ Optimum.lean           # Optimum Theorem
HuffmanAlgorithm.lean     # Huffman's Algorithm encoding
```
