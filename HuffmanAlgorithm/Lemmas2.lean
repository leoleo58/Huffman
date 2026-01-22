import HuffmanAlgorithm.Lemmas
set_option linter.flexible false

/-
swapSyms lemma
-/
@[simp]
lemma swapSyms_id {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α) :
  consistent t → swapSyms t a a = t := by aesop (add norm [swapSyms])

@[simp]
lemma alphabet_swapSyms {α} [DecidableEq α]
  (t : HuffmanTree α) (a b : α) :
  a ∈ alphabet t → b ∈ alphabet t →
  alphabet (swapSyms t a b) = alphabet t := by aesop (add norm [swapSyms])

@[simp]
lemma consistent_swapSyms {α} [DecidableEq α]
  (t : HuffmanTree α) (a b : α) :
  consistent t → consistent (swapSyms t a b) := by aesop (add norm [swapSyms])

@[simp]
lemma depth_swapSyms_neither {α} [DecidableEq α]
  (t : HuffmanTree α) (a b c : α) :
  consistent t → c ≠ a → c ≠ b →
  depth (swapSyms t a b) c = depth t c := by aesop (add norm [swapSyms])

@[simp]
lemma freq_swapSyms {α} [DecidableEq α]
  (t : HuffmanTree α) (a b : α) :
  consistent t → a ∈ alphabet t → b ∈ alphabet t →
  freq (swapSyms t a b) = freq t := by
    by_cases h_a_b : a = b <;> aesop (add norm [swapSyms])

@[simp]
lemma cost_swapSyms {α} [DecidableEq α]
  (t : HuffmanTree α) (a b : α) :
  consistent t → a ∈ alphabet t → b ∈ alphabet t →
  cost (swapSyms t a b) + freq t a * depth t a + freq t b * depth t b =
  cost t + freq t a * depth t b + freq t b * depth t a := by
    by_cases h_a_b : a = b
    · simp_all
    · grind[swapSyms,cost_swapLeaves]

@[simp]
lemma cost_swapSyms_le {α} [DecidableEq α]
  (t : HuffmanTree α) (a b : α)
  (h_consistent : consistent t) (h_a : a ∈ alphabet t) (h_b : b ∈ alphabet t)
  (h_freq : freq t a ≤ freq t b) (h_depth : depth t a ≤ depth t b) :
  cost (swapSyms t a b) ≤ cost t := by
    have h1 : freq t a * depth t b + freq t b * depth t a
              ≤ freq t a * depth t a + freq t b * depth t b := by nlinarith
    grind [cost_swapSyms]

@[simp]
lemma sibling_swapSyms_sibling {α} [DecidableEq α]
  (t : HuffmanTree α) (a b : α) :
  consistent t → sibling t b ≠ b → a ≠ b →
  sibling (swapSyms t a (sibling t b)) a = b := by aesop (add norm [swapSyms])

@[simp]
lemma sibling_swapSyms_other_sibling {α} [DecidableEq α]
  (t : HuffmanTree α) (a b : α)
  (h_consistent : consistent t) (h_sib_b_a : sibling t b ≠ a)
  (h_sib_b_b : sibling t b ≠ b) (h_a_b : a ≠ b) :
  sibling (swapSyms t a b) (sibling t b) = a := by
    set c := sibling t b with hc
    have hsbc := sibling_reciprocal t b c h_consistent (by rw [hc])
    grind[sibling_reciprocal,sibling_swapSyms_sibling,consistent_swapSyms, sibling]

/-
swapFourSyms Lemmas
-/
@[simp]
lemma alphabet_swapFourSyms {α} [DecidableEq α]
  (t : HuffmanTree α) (a b c d : α) :
  a ∈ alphabet t → b ∈ alphabet t → c ∈ alphabet t → d ∈ alphabet t →
  alphabet (swapFourSyms t a b c d) = alphabet t := by aesop (add norm[swapFourSyms])

@[simp]
lemma consistent_swapFourSyms {α} [DecidableEq α]
  (t : HuffmanTree α) (a b c d : α) :
  consistent t → consistent (swapFourSyms t a b c d) := by aesop (add norm[swapFourSyms])

@[simp]
lemma freq_swapFourSyms {α} [DecidableEq α]
  (t : HuffmanTree α) (a b c d : α)
  (h_consistent : consistent t) (h_a : a ∈ alphabet t) (h_b : b ∈ alphabet t)
  (h_c : c ∈ alphabet t) (h_d : d ∈ alphabet t) :
  freq (swapFourSyms t a b c d) = freq t := by
  simp [swapFourSyms]
  by_cases h_ad : a = d <;> by_cases h_bc : b = c
  · aesop(add norm[swapSyms])
  · aesop(add norm[swapSyms])
  · aesop(add norm[swapSyms])
  · simp [h_ad, swapSyms, h_bc]
    by_cases h_ac : a = c <;> by_cases h_bd : b = d
    · simp [h_ac, h_bd, swapLeaves_id, h_consistent]
    · aesop
    · simp [h_bd.symm]
      have h_consistent1 : consistent (swapLeaves t (freq t a) a (freq t c) c) := by
        simp [consistent_swapLeaves, h_consistent]
      rw [swapLeaves_id (swapLeaves t (freq t a) a (freq t c) c) b h_consistent1]
      aesop
    · ext x
      aesop

/-
lemma sibling_swapFourSyms_when_4th_is_sibling:
-/
lemma sibling_swapFourSyms_when_4th_is_sibling {α} [DecidableEq α]
  (t : HuffmanTree α) (a b c d : α)
  (h_consistent : consistent t) (h_a: a ∈ alphabet t) (h_b : b ∈ alphabet t)
  (h_c : c ∈ alphabet t) (h_d : d ∈ alphabet t)
  (h_a_b : a ≠ b) (h_sib_c : sibling t c ≠ c) :
  sibling (swapFourSyms t a b c (sibling t c)) a = b := by
  by_cases h : a ≠ sibling t c ∧ b ≠ c
  · let d' := sibling t c
    let ts := swapFourSyms t a b c d'
    have h_consistent1 := consistent_swapFourSyms t a b c d' h_consistent
    have h_consistent2: consistent (swapSyms t a c) := by simp [h_consistent]
    have abba : (sibling ts a = b) = (sibling ts b = a) := by
      grind[sibling_reciprocal]
    have s : sibling t c = sibling (swapSyms t a c) a := by
      grind[sibling_swapSyms_other_sibling, sibling_reciprocal,
            swapSyms, swapLeaves_id]
    have h : sibling ts b = a := by
      calc
        sibling ts b = sibling (swapSyms t a c) d' := by
          have := freq_swapLeaves t (freq t a) (freq t c) a c h_consistent
          by_cases hac : a = c
          · simp [ts, swapFourSyms, d', h]
            aesop (add norm [swapLeaves, sibling,swapSyms])
          · set t1 := swapLeaves t (freq t a) a (freq t c) c with ht1
            have h_consistent1 : consistent t1 := by simp [t1, h_consistent]
            by_cases hsib1b : sibling t1 a = b
            · have h_freq1 : freq t1 b = freq t b := by grind[freq_swapLeaves]
              grind[swapLeaves_id, sibling_sibling_id,swapSyms,swapFourSyms]
            · have htemp : sibling (swapSyms t1 b (sibling t1 a)) (sibling t1 (sibling t1 a)) = b :=
                sibling_swapSyms_other_sibling t1 b (sibling t1 a)
                  h_consistent1 ?_ ?_ (Ne.symm hsib1b)
              <;> aesop (add norm [sibling, swapSyms,swapLeaves,swapFourSyms])
        _ = a := by aesop
    aesop (add norm [swapLeaves, swapSyms, sibling])
  · simp [swapFourSyms]
    split
    · by_cases hbc : b = c <;> aesop
    · aesop (add norm [swapLeaves, swapSyms, sibling])

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

@[simp]
lemma weight_mergeSibling {α} [DecidableEq α]
  (t : HuffmanTree α) (a : α) :
  weight (mergeSibling t a) = weight t := by
  induction t, a using mergeSibling.induct <;> grind[weight, mergeSibling]

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

/-
SplitLeaf
-/
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

@[simp]
lemma weight_splitLeaf {α} [DecidableEq α] (t : HuffmanTree α) (wa wb : Nat) (a b : α)
  (h_consistent : consistent t) (h_a : a ∈ alphabet t) (h_freq : freq t a = wa + wb) :
  weight (splitLeaf t wa a wb b) = weight t := by
  induction a, h_consistent using huffmanTree_induct_consistent <;>
    aesop (add norm [weight,splitLeaf,alphabet,freq])

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

lemma cost_splitLeaf2 {α} [DecidableEq α] (t : HuffmanTree α) (wa wb : Nat) (a b : α) :
  consistent t → a ∈ alphabet t → freq t a = wa + wb →
  cost (splitLeaf t wa a wb b) = cost t + wa + wb := by
  intro h_consistent h_alphabet h_freq
  induction a, h_consistent using huffmanTree_induct_consistent with
  | leaf wb b h_consistent =>
      simp [alphabet] at h_alphabet
      simp [freq, h_alphabet] at h_freq
      simp [cost, splitLeaf, h_alphabet, weight]
  | left w t1 t2 h_consistent h_consistent1 h_consistent2 hd h_alphabet1 h_alphabet2 h1 h2 =>
      have h3 := notin_alphabet_imp_freq_0 a t2 h_alphabet2
      simp [freq, h3] at h_freq
      simp [h_alphabet1, h_freq] at h1
      have h4 := weight_splitLeaf (HuffmanTree.node w t1 t2) wa wb a b h_consistent h_alphabet
      simp [freq, h3, h_freq, weight,splitLeaf] at h4
      simp [cost, splitLeaf, h1]
      aesop (add norm [h4, cost, weight, splitLeaf])
      ring_nf
  | right w t1 t2 h_consistent h_consistent1 h_consistent2 hd h_alphabet1 h_alphabet2 h1 h2 =>
      have h3 := notin_alphabet_imp_freq_0 a t1 h_alphabet1
      simp [freq, h3] at h_freq
      simp [h_alphabet2, h_freq] at h2
      have h4 := weight_splitLeaf (HuffmanTree.node w t1 t2) wa wb a b h_consistent h_alphabet
      simp [freq, h3, h_freq, weight,splitLeaf] at h4
      simp [cost, splitLeaf, h2]
      aesop (add norm [h4, cost, weight, splitLeaf])
      ring_nf
  | none w t1 t2 h_consistent h_consistent1 h_consistent2 hd h_alphabet1 h_alphabet2 h1 h2 =>
      aesop(add norm [alphabet])

/-
SortedByWeight Lemmas
-/
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

@[simp]
lemma sortedByWeight_insortTree {α}
  (t : HuffmanTree α) (ts : Forest α)
  (h_sbw : sortedByWeight ts) (h_height_t : height t = 0) (h_height_ts : heightF ts = 0) :
  sortedByWeight (insortTree t ts) := by
  induction ts using sortedByWeight.induct <;>
    grind[heightF, insortTree,height_0_imp_cachedWeight_eq_weight,sortedByWeight]

/-
lemma cost_swapFourSyms_le
-/

lemma cost_swapFourSyms_le {α} [DecidableEq α]
  (t : HuffmanTree α) (a b c d : α)
  (h_consistent : consistent t) (h_minima : minima t a b) (hc : c ∈ alphabet t)
  (hd : d ∈ alphabet t) (hdhc : depth t c = height t)
  (hdhd : depth t d = height t) (h_cd : c ≠ d) :
  cost (swapFourSyms t a b c d) ≤ cost t := by
  rcases h_minima with ⟨ha, hb, h_ab, h_freq⟩
  by_cases h : a ≠ d ∧ b ≠ c
  · rcases h with ⟨h_ad, h_bc⟩
    by_cases h_ac : a = c
    · simp [swapFourSyms, h_bc, h_ac, h_cd, swapLeaves_id t c h_consistent,swapSyms]
      by_cases h_bd : b = d
      · simp [h_bd, swapLeaves_id t d h_consistent]
      · have hcost := cost_swapLeaves t (freq t b) (freq t d) b d h_consistent h_bd
        simp [hb, hd] at hcost
        have h_freq2: freq t b ≤ freq t d := (h_freq d hd (Ne.symm h_ad) (Ne.symm h_bd)).2
        have hd2: depth t b ≤ depth t d := by grind[depth_le_height]
        nlinarith
    · by_cases h_bd : b = d
      · have : swapFourSyms t a b c d = swapLeaves t (freq t a) a (freq t c) c := by
          grind[swapFourSyms,swapLeaves_id,swapSyms, consistent_swapLeaves]
        rw [this]
        have hcost := cost_swapLeaves t (freq t a) (freq t c) a c h_consistent h_ac
        simp [ha, hc] at hcost
        have h_freq2: freq t a ≤ freq t c := (h_freq c hc (Ne.symm h_ac) (Ne.symm h_bc)).1
        have hd2: depth t a ≤ depth t c := by grind[depth_le_height]
        nlinarith
      · have := h_freq c hc (Ne.symm h_ac) (Ne.symm h_bc)
        calc
          cost (swapFourSyms t a b c d) ≤ cost (swapSyms t a c) := by
            let t' := swapLeaves t (freq t a) a (freq t c) c
            have h_freq' : freq t' b ≤ freq t' d := by grind[freq_swapLeaves,freq,alphabet]
            aesop(add norm[swapFourSyms])
          _ ≤ cost t := by aesop
  · grind[swapSyms, cost_swapSyms_le,depth_le_height,swapFourSyms,cost_swapLeaves]

lemma twice_freq_le_imp_minima {α} [DecidableEq α]
  (t u : HuffmanTree α) (a b : α) (wa wb : ℕ)
  (h1 : ∀ c ∈ alphabet t, wa ≤ freq t c ∧ wb ≤ freq t c)
  (h2 : alphabet u = alphabet t ∪ {b})
  (h3 : a ∈ alphabet u)
  (h4 : a ≠ b)
  (h5 : freq u =
    fun c => if c = a then wa else if c = b then wb else freq t c) :
  minima u a b := by grind[minima,alphabet,freq]

@[simp]
lemma optimum_splitLeaf {α : Type} [DecidableEq α]
  (t : HuffmanTree α) (a b : α) (wa wb : ℕ)
  (h_consistent : consistent t) (h_optimum : optimum t)
  (ha_t : a ∈ alphabet t) (hb_t : b ∉ alphabet t) (h_freq : freq t a = wa + wb)
  (h1 : ∀ c ∈ alphabet t, freq t c ≥ wa ∧ freq t c ≥ wb) :
  optimum (splitLeaf t wa a wb b) := by
  intro u h_consistent_u h_alp_t_u h_freq_u
  let t' := splitLeaf t wa a wb b
  change cost t' ≤ cost u
  by_cases h_height_t_0 : height t' = 0
  · simp[*]
  · have ha_u : a ∈ alphabet u := by
      have ha_t' : a ∈ alphabet t' := by simp [t', ha_t]
      grind
    have hb_u : b ∈ alphabet u := by
      have hb_t' : b ∈ alphabet t' := by simp [t', ha_t]
      grind
    have h_ab : a ≠ b := by grind
    have h_height_u : height u > 0 := by cases u <;> grind[height,alphabet]
    obtain ⟨c, hc_u, hc_depth⟩ := exists_at_height u h_consistent_u
    let d := sibling u c
    have h_dc : d ≠ c := by grind[depth_height_imp_sibling_ne]
    have hd_u : d ∈ alphabet u := by
      simp [d, sibling_ne_imp_sibling_in_alphabet u c h_dc]
    have hd_depth : depth u d = height u := by grind[depth_sibling]
    let u' := swapFourSyms u a b c d
    have h_consistent_u' : consistent u' :=
      consistent_swapFourSyms u a b c d h_consistent_u
    have h_alp_u'_u : alphabet u' = alphabet u :=
      alphabet_swapFourSyms u a b c d ha_u hb_u hc_u hd_u
    have h_freq_u' : freq u' = freq u :=
      freq_swapFourSyms u a b c d h_consistent_u ha_u hb_u hc_u hd_u
    have h_sib_a : sibling u' a = b := by grind[sibling_swapFourSyms_when_4th_is_sibling]
    let v := mergeSibling u' a
    have h_consistent_v : consistent v := by grind[consistent_mergeSibling]
    have h_freq_a : freq t' a = freq u a := congr_fun h_freq_u a
    have h_freq_b : freq t' b = freq u b := congr_fun h_freq_u b
    have h_freq_v : freq v = freq t := by
      ext x
      have ha_u': a ∈ alphabet u' := by simp [h_alp_u'_u, ha_u]
      rw [freq_mergesibling u' a h_consistent_u' ha_u' ?_] <;>
      aesop(add norm[h_freq_u',h_freq_u.symm])
    calc
      cost t' = cost t + wa + wb :=
        cost_splitLeaf t wa wb a b h_consistent ha_t h_freq
      _ ≤ cost v + wa + wb := by
        grind[optimum,consistent_mergeSibling,alphabet_splitLeaf,alphabet_mergeSibling]
      _ = cost u' := by
        have hwafreq : wa = freq u' a := by
          have : wa = freq t' a := by grind[freq_splitLeaf]
          rw [this, h_freq_a, h_freq_u']
        have hwbfreq : wb = freq u' (sibling u' a) := by
          have : wb = freq t' b := by grind[freq_splitLeaf]
          rw [h_sib_a, this, h_freq_b, h_freq_u']
        grind [cost_mergeSibling]
      _ ≤ cost u := by
        have h_minima : minima u a b := by
          refine ⟨ha_u, hb_u, h_ab, ?_⟩
          intro c hc hca hcb'
          have hc_t' : c ∈ alphabet t' := by
            rw [h_alp_t_u]
            exact hc
          simp [t', alphabet_splitLeaf, ha_t] at hc_t'
          rcases hc_t' with (h_cb | hc_t)
          · exfalso
            exact hcb' h_cb
          · have h_freq_uc: freq u c = freq t c := by
              simp [h_freq_u.symm,freq_splitLeaf t wa wb a b c h_consistent hb_t, hca, hcb']
            grind[freq_splitLeaf]
        exact cost_swapFourSyms_le u a b c d h_consistent_u h_minima hc_u
          hd_u hc_depth hd_depth h_dc.symm

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

@[simp]
lemma splitLeaf_huffman_commute {α : Type} [DecidableEq α]
  (ts : Forest α) (a b : α) (wa wb : Nat) (hne : ts ≠ [])
  (h_consistent : consistentF ts) (h_a : a ∈ alphabetF ts)
  (h_freq : freqF ts a = wa + wb) :
  splitLeaf (huffman ts hne) wa a wb b =
  huffman (splitLeafF ts wa a wb b) (splitLeafF_nonempty hne) := by
  induction ts, hne using huffman.induct with
  | case1 t h1 h2 => simp [splitLeafF, huffman]
  | case2 t1 t2 ts h1 h2 ih =>
      have h_disj1 : (alphabet t1 ∪ alphabet t2) ∩ alphabetF ts = ∅ := by
        grind[consistentF,alphabetF]
      have h_disj2 : alphabet t1 ∩ alphabet t2 = ∅ := by grind[consistentF,alphabetF]
      have h_cases :
        (a ∈ alphabet t1 ∧ a ∉ alphabet t2 ∧ a ∉ alphabetF ts) ∨
        (a ∉ alphabet t1 ∧ a ∈ alphabet t2 ∧ a ∉ alphabetF ts) ∨
        (a ∉ alphabet t1 ∧ a ∉ alphabet t2 ∧ a ∈ alphabetF ts):= by
        grind [alphabetF,not_mem_inter_empty, consistentF]
      rcases h_cases with h1 | h2 | h3 <;>
      aesop (add norm
          [splitLeafF, insortTree, huffman, splitLeaf,
           alphabet, alphabetF, consistentF, consistent,
           cachedWeight, freq, freqF, uniteTrees])
