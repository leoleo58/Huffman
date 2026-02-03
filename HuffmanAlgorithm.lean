import HuffmanAlgorithm.Optimum

/-!
# Huffman Coding

This file serves for applying the formalized Huffman's algorithm to sample inputs.

## Main Function
- `Freq_to_Code`   : Turns list of symbols and frequencies to symbols and Huffman code
- `encode_String`  : Turn string to encoded String and Huffman code

Example use:
#eval Freq_to_Code [('t', 4), ('e', 2), ('s', 3)]
result: [('t', "0"), ('e', "10"), ('s', "11")]

#eval encode_String "test"
result: ("101001", [('s', "00"), ('e', "01"), ('t', "1")])
-/

abbrev Freq_List (α) := List (α × Nat)

def leaf {α} : α × Nat → HuffmanTree α
| (a, w) => HuffmanTree.leaf w a

def forest {α} (fs : Freq_List α) : Forest α :=
  fs.map leaf

def build_Huffman_Tree {α} (fs : Freq_List α) (h : fs ≠ []) : HuffmanTree α :=
  huffman (forest fs) (by aesop(add norm[forest]))

abbrev Bit := Nat

def encode {α : Type} (t : HuffmanTree α) (p : String) : List (α × String) :=
  match t with
  | HuffmanTree.leaf _ a => [(a, p)]
  | HuffmanTree.node _ t1 t2 => encode t1 (p ++ "0") ++ encode t2 (p ++ "1")

def huffmanCode {α} (t : HuffmanTree α) : List (α × String) :=
  encode t ""

def Freq_to_Code {α} [DecidableEq α]
(fs : Freq_List α) : List (α × String) :=
  let fs' := fs.mergeSort (fun x y => x.2 ≤ y.2)
  if h : fs' ≠ [] then
    let t := build_Huffman_Tree fs' h
    huffmanCode t
  else []

def encode_String (s : String) : String × List (Char × String) :=
  let freq := s.toList.foldl
    (fun fs x =>
      match fs.find? (fun (y, _) => y = x) with
      | some (_, n) => (x, n + 1) :: fs.erase (x, n)
      | none => (x, 1) :: fs
    ) []
  let code_List := Freq_to_Code (freq)
  let encoded := s.toList.foldl
    (fun s' x =>
      match code_List.find? (fun (y, _) => y = x) with
      | some (_, code) => s' ++ code
      | none => s'
    ) ""
  (encoded, code_List)

#eval Freq_to_Code [('t', 4), ('e', 2), ('s', 3)]
#eval encode_String "test"
