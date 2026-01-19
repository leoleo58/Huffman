import HuffmanAlgorithm.Function
set_option linter.flexible false

lemma mem_inter_empty {α} [DecidableEq α]
  (A B : Finset α) (a : α) (h : A ∩ B = ∅)
  (h1 : a ∈ A) (h2 : a ∈ B) : False := by
  have : a ∈ A ∩ B := Finset.mem_inter_of_mem h1 h2
  simp [h] at this

lemma not_mem_right_of_inter_empty {α : Type} [DecidableEq α]
  {A B : Finset α} {a : α} :
  A ∩ B = ∅ → a ∈ A → a ∉ B := by
  intro h ha hb
  have : a ∈ A ∩ B := Finset.mem_inter.mpr ⟨ha, hb⟩
  simp [h] at this

lemma not_mem_left_of_inter_empty {α : Type} [DecidableEq α]
  {A B : Finset α} {a : α} :
  A ∩ B = ∅ → a ∈ B → a ∉ A := by
  intro h ha hb
  have : a ∈ A ∩ B := Finset.mem_inter.mpr ⟨hb, ha⟩
  simp [h] at this

lemma not_mem_inter_empty {α} {A B : Finset α} {a : α} [DecidableEq α] :
  A ∩ B = ∅ → (a ∈ A → a ∉ B) ∧ (a ∈ B → a ∉ A) := by
  intro h
  constructor <;> intro ha hb
  · have : a ∈ A ∩ B := Finset.mem_inter.mpr ⟨ha, hb⟩
    simp [h] at this
  · have : a ∈ A ∩ B := Finset.mem_inter.mpr ⟨hb, ha⟩
    simp [h] at this

lemma alphabet_cases {α} [DecidableEq α]
  (a : α) (t1 t2 : HuffmanTree α)
  (hdis : alphabet t1 ∩ alphabet t2 = ∅) :
  (a ∈ alphabet t1 ∧ a ∉ alphabet t2) ∨
  (a ∉ alphabet t1 ∧ a ∈ alphabet t2) ∨
  (a ∉ alphabet t1 ∧ a ∉ alphabet t2) := by
  by_cases h1 : a ∈ alphabet t1 <;> grind[not_mem_inter_empty]

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
Alphabet lemma
-/
lemma exists_in_alphabet {α : Type} [DecidableEq α] (t : HuffmanTree α) :
  ∃ a, a ∈ alphabet t := by
  induction t <;> aesop(add norm[alphabet])

/-
Height lemma
-/
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
      grind[mem_inter_empty,consistent,alphabet,height,depth]

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
Freq lemmas
-/
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
  apply notin_alphabet_imp_freq_0
  intro h_a_t2
  have h := Finset.mem_inter_of_mem h_a_t1 h_a_t2
  simp [h_disj] at h

@[simp]
lemma freq_0_left {α} [DecidableEq α] (a : α) (t1 t2 : HuffmanTree α)
  (h_disj : alphabet t1 ∩ alphabet t2 = ∅) (h_a_t2 : a ∈ alphabet t2) :
  freq t1 a = 0 := by
  apply notin_alphabet_imp_freq_0
  intro h_a_t1
  have h := Finset.mem_inter_of_mem h_a_t1 h_a_t2
  simp [h_disj] at h

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
Weight lemmas
-/
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
Working cost_eq_Sum_freq_mult_depth
-/
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

theorem cost_eq_Sum_freq_mult_depth2 {α} [DecidableEq α] (t : HuffmanTree α) :
  consistent t → cost t = (∑a ∈ alphabet t, freq t a * depth t a) := by
  intro hc
  induction t with
  | leaf w x => simp [cost, alphabet, freq, depth]
  | node w t1 t2 h1 h2 =>
      let ⟨hc1, hc2, hc3⟩ := hc
      let t := HuffmanTree.node w t1 t2
      have d1 : ∀ a, a ∈ alphabet t1 → depth t a = depth t1 a + 1 := by
        grind[depth]
      have d2 : ∀ a, a ∈ alphabet t2 → depth t a = depth t2 a + 1 := by
        grind[not_mem_inter_empty,depth]
      have cost1 := h1 hc2
      have cost2 := h2 hc3
      calc
        cost t = weight t1 + cost t1 + weight t2 + cost t2 := by simp[t, cost]
        _ = weight t1 + (∑a ∈ alphabet t1, freq t1 a * depth t1 a) +
            weight t2 + (∑a ∈ alphabet t2, freq t2 a * depth t2 a) := by rw [cost1, cost2]
        _ = weight t1
            + (∑a ∈ alphabet t1, freq t1 a * (depth t a - 1)) +
            weight t2
            + (∑a ∈ alphabet t2, freq t2 a * (depth t a - 1)) := by
            simp_all
        _ = weight t1
            + (∑a ∈ alphabet t1, freq t1 a * depth t a)
            - (∑a ∈ alphabet t1, freq t1 a)
            + weight t2
            + (∑a ∈ alphabet t2, freq t2 a * depth t a)
            - (∑a ∈ alphabet t2, freq t2 a) := by
            -- using c d⇩2 by (simp add: sum.distrib)
            sorry
        _ = (∑a ∈ alphabet t1, freq t1 a * depth t a) +
            (∑a ∈ alphabet t2, freq t2 a * depth t a) := by
            grind[weight_eq_Sum_freq]
        _ = (∑a ∈ alphabet t1, freq t a * depth t a)
            + (∑a ∈ alphabet t2, freq t a  * depth t a) := by
            have h1 : ∑a ∈ alphabet t1, freq t1 a * depth t a =
              ∑a ∈ alphabet t1, freq t a * depth t a := by
              apply Finset.sum_congr rfl
              grind[freq,freq_0_right]
            have h2 : ∑a ∈ alphabet t2, freq t2 a * depth t a =
              ∑a ∈ alphabet t2, freq t a * depth t a := by
              apply Finset.sum_congr rfl
              grind[freq, freq_0_left]
            rw [h1, h2]
        _ = (∑a ∈ alphabet t1 ∪ alphabet t2, freq t a
            * depth t a) := by
            rw [Finset.sum_union]
            exact Finset.disjoint_iff_inter_eq_empty.mpr hc1
        _ = (∑a ∈ alphabet t, freq t a
            * depth t a) := by
            simp [t, alphabet]

@[simp]
lemma height_0_imp_cost_0 {α} (t : HuffmanTree α) :
  height t = 0 → cost t = 0 := by
  cases t <;> simp [height, cost]

/-
CachedWeight lemma
-/
@[simp]
lemma height_0_imp_cachedWeight_eq_weight {α} (t : HuffmanTree α) :
  height t = 0 → cachedWeight t = weight t := by
  aesop (add norm[weight, cachedWeight,height])

/-
UniteTree lemmas
-/
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
InsortTree lemmas
-/
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
Huffman lemmas
-/
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
      simp [consistentF] at ih
      simp [huffman, consistentF, alphabetF]
      intro h_disj h_consistent_t1 h_disj_2_ts h_consistent_t2 h_consistent_ts
      simp [Finset.inter_union_distrib_left] at h_disj
      grind[consistent_uniteTrees, consistent]

@[simp]
lemma freq_huffman {α} [DecidableEq α] (ts : Forest α) (a : α) (h : ts ≠ []) :
  freq (huffman ts h) a = freqF ts a := by
  induction ts, h using huffman.induct <;> simp [freqF, huffman]
  rename_i ih
  simp [ih]
  linarith

/-
Sibling lemma
-/
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
  --by_cases h_a: a ∈ alphabet t1 <;> aesop

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

@[simp]
lemma sibling_sibling_id {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α) :
  consistent t → sibling t (sibling t a) = a := by
  intro h_consistent
  induction a, h_consistent using sibling_induct_consistent <;> aesop (add norm [sibling])

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

@[simp]
lemma depth_sibling {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α) :
  consistent t → depth t (sibling t a) = depth t a := by
  intro h_consistent
  induction a, h_consistent using sibling_induct_consistent <;>
  aesop (add norm [depth, alphabet, sibling])

/-
Swap Leaf lemma
-/
@[simp]
lemma swapLeaves_id_when_notin_alphabet {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α) (wa wb : ℕ) :
  a ∉ alphabet t → swapLeaves t wa a wb a = t := by
  induction t <;> grind [alphabet, swapLeaves]

@[simp]
lemma swapLeaves_id {α : Type} [d : DecidableEq α]
  (t : HuffmanTree α) (a : α) :
  consistent t → swapLeaves t (freq t a) a (freq t a) a = t := by
  intro h_consistent
  induction a, h_consistent using huffmanTree_induct_consistent <;>
  aesop (add norm [freq, swapLeaves])

@[simp]
lemma alphabet_swapLeaves {α} [DecidableEq α]
  (t : HuffmanTree α) (wa : ℕ) (a : α) (wb : ℕ) (b : α) :
  alphabet (swapLeaves t wa a wb b) =
    (if a ∈ alphabet t then
        if b ∈ alphabet t then alphabet t else (alphabet t \ {a}) ∪ {b}
     else
        if b ∈ alphabet t then (alphabet t \ {b}) ∪ {a} else alphabet t) := by
  induction t <;> grind [alphabet, swapLeaves]

@[simp]
lemma consistent_swapLeaves {α} [DecidableEq α]
  (t : HuffmanTree α) (wa wb : ℕ) (a b : α) :
  consistent t → consistent (swapLeaves t wa a wb b) := by
  induction t with
  | leaf wc c =>
      aesop (add norm [swapLeaves])
  | node w t1 t2 ih1 ih2 =>
      intro h_consistent
      let ⟨h_disj, h_consistent_t1, h_consistent_t2⟩ := h_consistent
      simp [consistent, ih1, ih2, swapLeaves, h_consistent_t1, h_consistent_t2]
      grind [mem_inter_empty]

@[simp]
lemma depth_swapLeaves_neither {α} [DecidableEq α]
  (t : HuffmanTree α) (wa wb : ℕ) (a b c : α) :
  consistent t → c ≠ a → c ≠ b →
  depth (swapLeaves t wa a wb b) c = depth t c := by
  intro h_consistent
  induction a, h_consistent using huffmanTree_induct_consistent <;>
  aesop (add norm [depth, swapLeaves])

@[simp]
lemma height_swapLeaves {α} [DecidableEq α] (t : HuffmanTree α) (wa wb : ℕ) (a b : α) :
  height (swapLeaves t wa a wb b) = height t := by
  induction t <;> aesop (add norm [height, swapLeaves])

@[simp]
lemma freq_swapLeaves {α} [DecidableEq α]
  (t : HuffmanTree α) (wa wb : ℕ) (a b : α) :
  consistent t → a ≠ b →
  freq (swapLeaves t wa a wb b) =
  fun c =>  if c = a then if b ∈ alphabet t then wa else 0
            else if c = b then if a ∈ alphabet t then wb else 0
            else freq t c := by
  intro h_consistent h_a_b
  ext c
  induction t with
  | leaf w x => aesop (add norm [freq, alphabet, swapLeaves])
  | node w t1 t2 ih1 ih2 =>
      let ⟨h_disj, h_consistent_t1, h_consistent_t2⟩ := h_consistent
      simp [freq, swapLeaves, alphabet, ih1, ih2, h_consistent_t1, h_consistent_t2]
      grind[mem_inter_empty]

@[simp]
lemma weight_swapLeaves {α} [DecidableEq α]
  (t : HuffmanTree α) (wa wb : ℕ) (a b : α) :
  consistent t → a ≠ b →
  if a ∈ alphabet t then
    if b ∈ alphabet t then
      weight (swapLeaves t wa a wb b) + freq t a + freq t b =
        weight t + wa + wb
    else
      weight (swapLeaves t wa a wb b) + freq t a = weight t + wb
  else
    if b ∈ alphabet t then
      weight (swapLeaves t wa a wb b) + freq t b = weight t + wa
    else
      weight (swapLeaves t wa a wb b) = weight t := by
  intro h_consistent h_a_b
  induction a, h_consistent using huffmanTree_induct_consistent <;>
  grind[weight, alphabet, freq, swapLeaves, mem_inter_empty, notin_alphabet_imp_freq_0]

@[simp]
lemma cost_swapLeaves {α} [DecidableEq α]
  (t : HuffmanTree α) (wa wb : ℕ) (a b : α) :
  consistent t → a ≠ b →
  if a ∈ alphabet t then
    if b ∈ alphabet t then
      cost (swapLeaves t wa a wb b) + freq t a * depth t a
      + freq t b * depth t b =
        cost t + wa * depth t b + wb * depth t a
    else
      cost (swapLeaves t wa a wb b) + freq t a * depth t a =
        cost t + wb * depth t a
  else
    if b ∈ alphabet t then
      cost (swapLeaves t wa a wb b) + freq t b * depth t b =
        cost t + wa * depth t b
    else
      cost (swapLeaves t wa a wb b) = cost t := by
  intro h_consistent h_a_b
  induction t with
  | leaf w c => aesop (add norm [cost,alphabet,freq,depth, swapLeaves])
  | node w t1 t2 ih1 ih2 =>
      obtain ⟨h_disj, h_consistent_t1, h_consistent_t2⟩ := h_consistent
      simp [alphabet, cost, freq, depth, swapLeaves]
      have w1 := weight_swapLeaves t1 wa wb a b h_consistent_t1 h_a_b
      have w2 := weight_swapLeaves t2 wa wb a b h_consistent_t2 h_a_b
      by_cases h_a_t1 : a ∈ alphabet t1
      · have h_a_t2 : a ∉ alphabet t2 := by grind[not_mem_inter_empty]
        by_cases h_b_t1 : b ∈ alphabet t1
        · have h_b_t2 : b ∉ alphabet t2 := by grind[not_mem_inter_empty]
          simp [h_a_t1, h_a_t2, h_b_t1, h_b_t2]
          grind
        · by_cases h_b_t2 : b ∈ alphabet t2 <;> simp_all <;> grind
      · by_cases h_a_t2 : a ∈ alphabet t2
        · by_cases h_b_t1 : b ∈ alphabet t1
          · have h_b_t2 : b ∉ alphabet t2 := by grind[not_mem_inter_empty]
            simp [h_a_t1, h_a_t2, h_b_t1, h_b_t2]
            grind
          · by_cases h_b_t2 : b ∈ alphabet t2 <;> simp_all <;> grind
        · by_cases h_b_t1 : b ∈ alphabet t1
          · have h_b_t2 : b ∉ alphabet t2 := by grind[not_mem_inter_empty]
            simp [h_a_t1, h_a_t2, h_b_t1, h_b_t2]
            grind
          · by_cases h_b_t2 : b ∈ alphabet t2 <;> simp_all ; grind

set_option maxHeartbeats 300000
@[simp]
lemma sibling_swapLeaves_sibling {α} [DecidableEq α]
  (t : HuffmanTree α) (a b : α) (wa ws : ℕ) :
  consistent t → sibling t b ≠ b → a ≠ b → sibling (swapLeaves t wa a ws (sibling t b)) a = b := by
  intro h_consistent h_sib_b h_a_b
  induction t with
  | leaf w x => simp [sibling] at h_sib_b
  | node w t1 t2 ih1 ih2 =>
      let ⟨h_disj, h_consistent_t1, h_consistent_t2⟩ := h_consistent
      simp [h_consistent_t1, h_consistent_t2] at ih1 ih2
      by_cases h_height_t1 : height t1 = 0
      · cases t1 with
        | leaf wc c =>
            by_cases h_height_t2 : height t2 = 0
            · cases t2 <;> aesop (add norm [sibling, swapLeaves])
            · have h_height_t2_le : height t2 > 0 := Nat.pos_of_ne_zero h_height_t2
              by_cases h_b_c : b = c
              · aesop(add norm[alphabet])
              · have h_sib: sibling (HuffmanTree.node w (HuffmanTree.leaf wc c) t2) b
                  = sibling t2 b := by aesop
                rw [h_sib]
                have h_c_alp_t2 : c ∉ alphabet t2 := by
                  intro h1
                  have h2 : c ∈ alphabet (HuffmanTree.leaf wc c) ∩ alphabet t2 :=
                    Finset.mem_inter.mpr ⟨Finset.mem_singleton_self c, h1⟩
                  simp [h_disj] at h2
                simp [swapLeaves]
                split_ifs with h_a_c h_sib_c <;> aesop (add norm [sibling, alphabet])
        | node w t1 t2 => simp [height] at h_height_t1
      · have h_height_t1_le : height t1 > 0 := Nat.pos_of_ne_zero h_height_t1
        by_cases hb1 : b ∈ alphabet t1
        · simp [hb1, h_height_t1_le, swapLeaves]
          grind[height_gt_0_in_alphabet_imp_sibling_left,sibling_ne_imp_sibling_in_alphabet]
        · by_cases hb2 : b ∈ alphabet t2
          · have hsa1 : sibling t2 b ∉ alphabet t1 := by
              grind[in_alphabet_imp_sibling_in_alphabet,not_mem_inter_empty]
            simp [h_height_t1_le, swapLeaves]
            grind[height_gt_0_notin_alphabet_imp_sibling_left]
          · aesop (add norm [sibling, alphabet])
