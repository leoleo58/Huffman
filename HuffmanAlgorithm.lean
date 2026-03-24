import HuffmanAlgorithm.Optimum

/-!
# Huffman Coding

This file provides function for applying the formalised Huffman's algorithm to sample inputs,
such as lists of symbols with their frequencies or strings to be encoded.
The main focus is to compute Huffman codes for symbols and encode strings
according to those codes.

## Main Function
- `codeList` : Turns a list of symbols and their frequencies
  into a list of symbols with their Huffman codes.
  Example:
  #eval codeList [('t', 4), ('e', 2), ('s', 3)]
  result: [('t', "0"), ('e', "10"), ('s', "11")]
- `encodeString` : Encodes a string into its Huffman-coded string,
  returning the encoded string and the Huffman code used.
  Example:
  #eval encodeString "test"
  result: ("101001", [('s', "00"), ('e', "01"), ('t', "1")])
-/

/--
`freqList` is a list of pairs of symbols and their frequencies.
-/
abbrev freqList (α) := List (α × Nat)

/--
Creates a Huffman tree of a single leaf node for symbol `a` and frequency `w`.
-/
def leaf {α} : α × Nat → HuffmanTree α
| (a, w) => HuffmanTree.leaf w a

/--
Converts a list of symbol and frequency into a Huffman forest.
-/
def forest {α} (fs : freqList α) : Forest α :=
  fs.map leaf

/--
Constructs a Huffman tree from a non-empty list of symbol-frequency pairs.
-/
def buildHuffmanTree {α} (fs : freqList α) (h : fs ≠ []) : HuffmanTree α :=
  huffman (forest fs) (by aesop(add norm[forest]))

/--
Encodes a Huffman tree into a list of symbol and Huffman code.
-/
def encode {α : Type} (t : HuffmanTree α) (p : String) : List (α × String) :=
  match t with
  | HuffmanTree.leaf _ a => [(a, p)]
  | HuffmanTree.node _ t1 t2 => encode t1 (p ++ "0") ++ encode t2 (p ++ "1")

/--
The Huffman codes for each symbol in tree `t`.
-/
def huffmanCode {α} (t : HuffmanTree α) : List (α × String) :=
   match t with
  | HuffmanTree.leaf _ a => [(a, "0")]
  | _ => encode t ""

/--
`codeList` creates a Huffman tree from the list and returns a list of each symbol
and its Huffman code.
-/
def codeList {α} [DecidableEq α]
(fs : freqList α) : List (α × String) :=
  let fs' := fs.mergeSort (fun x y => x.2 ≤ y.2)
  if h : fs' ≠ [] then
    let t := buildHuffmanTree fs' h
    huffmanCode t
  else []

/--
`encodeString` encodes the input string using Huffman coding.
It returns the encoded String and Huffman code list used.
-/
def encodeString (s : String) : String × List (Char × String) :=
  let freq := s.toList.foldl
    (fun fs x =>
      match fs.find? (fun (y, _) => y = x) with
      | some (_, n) => (x, n + 1) :: fs.erase (x, n)
      | none => (x, 1) :: fs
    ) []
  let code_list := codeList (freq)
  let encoded := s.toList.foldl
    (fun s' x =>
      match code_list.find? (fun (y, _) => y = x) with
      | some (_, code) => s' ++ code
      | none => s'
    ) ""
  (encoded, code_list)

#eval codeList [('t', 4), ('e', 2), ('s', 3)]
#eval encodeString "test"
