import ProjectiveGeometry.Basic

/- HELPER LIST OPERATIONS-/

variable {α : Type} [DecidableEq α]

def List.distinct {α} [DecidableEq α] (l : List α) : Prop :=
  ∀ x ∈ l, x ∉ l.erase x

lemma List.distinct_singleton (a : α) : List.distinct [a] := by
  simp [List.distinct]

lemma List.distinct_filter_sub (l : List a) (p : a → Bool) :
   List.filter p l ⊆ l := by grind

lemma List.distinct_filter (l : List α) (p : α → Bool) (h : l.distinct) :
  List.distinct (l.filter p) := by
    simp_all only [distinct, mem_filter, and_imp]
    intro x hx hp hcontra
    have hxl: x ∈ l.erase x := by grind
    have hxl': x ∉ l.erase x := h x hx
    contradiction

theorem List.singleton_mem (l : List α) (a : α) :
l = [a] ↔ a ∈ l ∧ ∀ x ∈ l, x = a ∧ List.distinct l := by
  apply Iff.intro
  { intro h
    simp [h, List.distinct_singleton]
  }
  { cases l with
    | nil => simp
    | cons hd tl =>
      intro h1
      simp only [cons.injEq]
      apply And.intro
      { simp [h1] }
      { by_contra hne
        have h2: tl ≠ [] := by simp only [ne_eq, hne, not_false_eq_true]
        have h3: ∃ x, x ∈ tl := by
          rw [←isEmpty_eq_false_iff_exists_mem]
          simp [h2]
        obtain ⟨x, hx⟩ := h3
        let l := hd :: tl
        have h4: x = a := (h1.2 x (by simp [hx])).left
        rw [h4] at hx
        have h5: hd = a := (h1.2 hd (by simp)).left
        have h6: a ∈ l.erase a := by simp [l, hx, h5]
        have h7: a ∉ l.erase a := by
          simp_all only [List.distinct]
          grind
        contradiction
      }
  }

theorem List.product_mem_iff {α β} (xs: List α) (ys: List β) (a : α) (b : β) :
  (a, b) ∈ List.product xs ys ↔ a ∈ xs ∧ b ∈ ys := by
  induction xs with
  | nil =>
    simp [List.product]
  | cons x xt ih =>
    simp_all

set_option linter.unusedDecidableInType false

lemma distinct_subset_length_le (l s : List α) :
  s ⊆ l → s.distinct → s.length ≤ l.length := by
    induction s generalizing l with
    | nil => simp_all
    | cons hd tl ih =>
      intros hsub hdist
      let l' := l.erase hd
      have h1: tl ⊆ l' := by
        simp_all only [List.subset_def, List.mem_cons, forall_eq_or_imp]
        intro a ha
        have h2: a ≠ hd := by
          simp only [List.distinct, List.mem_cons, forall_eq_or_imp, List.erase_cons_head] at hdist
          simp_all only [ne_eq]
          obtain ⟨left, right⟩ := hsub
          obtain ⟨left_1, right_1⟩ := hdist
          exact ne_of_mem_of_not_mem ha left_1
        grind
      have h2: tl.distinct := by simp_all [List.distinct]; grind
      have h3 := ih l' h1 h2
      grind

lemma exist_3_list_length_fwd (l : List α) : (∃ P ∈ l, ∃ Q ∈ l, ∃ R ∈ l,
    P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧ P ∈ l ∧ Q ∈ l ∧ R ∈ l) → l.length ≥ 3 := by
      intro h
      obtain ⟨P, hP⟩ := h
      obtain ⟨Q, hQ⟩ := hP.right
      obtain ⟨R, hR⟩ := hQ.right
      have distinct: P ≠ Q ∧ P ≠ R ∧ Q ≠ R := by
        simp_all only [ne_eq, true_and, not_false_eq_true, and_self]
      let s := [P, Q, R]
      have h_s_len : s.length = 3 := by
        simp_all only [ne_eq, true_and, not_false_eq_true, List.length_cons,
        List.length_nil, Nat.zero_add, Nat.reduceAdd, s]
      have h1: s ⊆ l := by
        simp_all only [ne_eq, true_and, not_false_eq_true, List.length_cons, List.length_nil,
        Nat.zero_add, Nat.reduceAdd, List.cons_subset, List.nil_subset, and_self, s]
      have h2: s.distinct := by
        simp [List.distinct]
        grind
      have h_len: s.length ≤ l.length := distinct_subset_length_le l s h1 h2
      simp [h_s_len] at h_len
      assumption

lemma exist_3_list_length_bwd (l : List α) :
  l.length ≥ 3 → l.distinct → (∃ P ∈ l, ∃ Q ∈ l, ∃ R ∈ l,
    P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧ P ∈ l ∧ Q ∈ l ∧ R ∈ l) := by
    intro hl hd
    have hP: ∃ P, P ∈ l := by
      rw [← @List.isEmpty_eq_false_iff_exists_mem]
      rw [@List.isEmpty_eq_false_iff]
      rw [@List.ne_nil_iff_length_pos]
      omega
    simp [List.distinct] at hd
    obtain ⟨P, hP⟩ := hP
    let l2 := l.erase P
    have h2l : l2.length ≥ 2 := by simp [l2, hP]; omega
    have hQ : ∃ Q, Q ∈ l2 := by
      rw [← @List.isEmpty_eq_false_iff_exists_mem]
      rw [@List.isEmpty_eq_false_iff]
      rw [@List.ne_nil_iff_length_pos]
      omega
    obtain ⟨Q, hQ⟩ := hQ
    have hPQ: P ≠ Q := by grind
    let l3 := l2.erase Q
    have h3l : l3.length ≥ 1 := by simp [l3, hQ]; omega
    have hR: ∃ R, R ∈ l3 := by
      rw [← @List.isEmpty_eq_false_iff_exists_mem]
      rw [@List.isEmpty_eq_false_iff]
      rw [@List.ne_nil_iff_length_pos]
      omega
    obtain ⟨R, hR⟩ := hR
    have hQR : Q ≠ R := by grind
    have hPR : P ≠ R := by grind
    grind
