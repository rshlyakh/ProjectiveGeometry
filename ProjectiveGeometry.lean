import ProjectiveGeometry.Basic

/- TO-DO: Put this in a different file (ProjectiveGeometry is a REALLY bad name)-/

variable {α : Type} [DecidableEq α]

/- HELPER LIST OPERATIONS-/

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

def List.product {α β} (xs : List α) (ys : List β) : List (α × β) :=
  match xs with
  | [] => []
  | x :: xt => (ys.map (fun y => (x, y))) ++ List.product xt ys


theorem List.product_mem_iff {α β} (xs: List α) (ys: List β) (a : α) (b : β) :
  (a, b) ∈ List.product xs ys ↔ a ∈ xs ∧ b ∈ ys := by
  induction xs with
  | nil =>
    simp [List.product]
  | cons x xt ih =>
    simp only [product, mem_append, mem_map, Prod.mk.injEq, exists_eq_right_right, mem_cons]
    simp_all only
    apply Iff.intro
    · intro a_1
      cases a_1 with
      | inl h => simp_all only [and_true, true_or, and_self]
      | inr h_1 => simp_all only [and_self, iff_true, or_true]
    · intro a_1
      simp_all only [and_true, true_and]
      obtain ⟨left, right⟩ := a_1
      cases left with
      | inl h =>
        subst h
        simp_all only [true_or]
      | inr h_1 => simp_all only [iff_true, or_true]

/- BASIC DEFINITIONS -/

def IsDistinct (Points: List α) (Lines: List (List α)) : Prop :=
  Points.distinct ∧ Lines.distinct ∧ ∀ l ∈ Lines, l.distinct

structure PointsAndLines (α : Type) [DecidableEq α]
  where
  (Points : List α)
  (Lines : List (List α))
  (h : IsDistinct Points Lines)


def parallel (l1 l2 : List α) (pl : PointsAndLines α) : Prop :=
  l1 ∈ pl.Lines ∧ l2 ∈ pl.Lines ∧ (l1 = l2 ∨ (¬ ∃ P : α, P ∈ pl.Points ∧ P ∈ l1 ∧ P ∈ l2))

def collinear (P Q R : α) (pl: PointsAndLines α) : Prop :=
P ∈ pl.Points ∧ Q ∈ pl.Points ∧ R ∈ pl.Points ∧ P ≠ Q ∧ Q ≠ R ∧ P ≠ R
∧ ∃ l : List α, l ∈ pl.Lines ∧ P ∈ l ∧ Q ∈ l ∧ R ∈ l

/- AXIOMS -/

/- Given two distinct points P and Q, there is a unique line containing P and Q-/
def affine_axiom1 (pl : PointsAndLines α) : Prop :=
  let Points := pl.Points
  let Lines := pl.Lines
  ∀ P Q : α, P ∈ Points → Q ∈ Points → P ≠ Q → ∃! (l : List α), l ∈ Lines ∧ P ∈ l ∧ Q ∈ l

/- Given a line l and a point P not on l, there is a unique line m which is parallel to l
   and which passes through P-/
def affine_axiom2 (pl : PointsAndLines α) : Prop :=
  let Points := pl.Points
  let Lines := pl.Lines
  ∀ L: List α, ∀ P : α,  (h: L ∈ Lines) → P ∈ Points → P ∉ L →
  ∃! m, m ∈ Lines ∧ P ∈ m ∧ parallel L m pl

/- There exists three non-collinear points -/
def affine_axiom3 (pl : PointsAndLines α) : Prop :=
  let Points := pl.Points
  ∃ P Q R : α, P ∈ Points ∧ Q ∈ Points ∧ R ∈ Points ∧ ¬collinear P Q R pl

def IsAffinePlane (pl : PointsAndLines α) : Prop :=
  affine_axiom1 pl ∧ affine_axiom2 pl ∧ affine_axiom3 pl

structure AffinePlane (α : Type) [DecidableEq α]
  where
  (pl : PointsAndLines α)
  (isAffine : IsAffinePlane pl)

/- COMPUTATION HELPERS -/

def check_distinct (l : List α) : Bool :=
  List.all l (fun x => not (x ∈ l.erase x))

def check_parallel (plane : PointsAndLines α) (l1 l2 : List α) : Bool :=
  if not (l1 ∈ plane.Lines ∧ l2 ∈ plane.Lines) then
    false
  else
    if l1 = l2 then
      true
    else
      let PointsInBoth := plane.Points.filter (fun P => P ∈ l1 ∧ P ∈ l2)
      PointsInBoth.isEmpty

/- Checks whether three points are collinear-/
def check_collinear (plane : PointsAndLines α) (P Q R : α) : Bool :=
  if not (P ∈ plane.Points ∧ Q ∈ plane.Points ∧ R ∈ plane.Points ∧ P ≠ Q ∧ Q ≠ R ∧ P ≠ R) then
    false
  else
    let LinesWithPQR := plane.Lines.filter (fun l => P ∈ l ∧ Q ∈ l ∧ R ∈ l)
    ¬ LinesWithPQR.isEmpty

/- COMPUTING WITH THE AXIOMS -/


def check_affine_axiom1 (plane : PointsAndLines α) : Bool :=
    let PointPairs := List.product plane.Points plane.Points
    let ValidPairs := PointPairs.filter (fun pair => pair.1 ≠ pair.2)
    let lmd := (fun pair : (α × α) =>
      let P := pair.1
      let Q := pair.2
      let LinesWithPQ := plane.Lines.filter (fun l => P ∈ l ∧ Q ∈ l)
      LinesWithPQ.length = 1) -- returns true if there is a unique line through P and Q
    List.all ValidPairs lmd

def check_affine_axiom2 (plane : PointsAndLines α) :Bool :=
    let lmd := (fun L : List α =>
      let PointsNotOnL := plane.Points.filter (fun P => not (P ∈ L))
      let lmd2 := (fun P : α =>
        let LinesThroughP := plane.Lines.filter (fun M => P ∈ M)
        let ParallelLines := LinesThroughP.filter (fun M => check_parallel plane L M)
        ParallelLines.length = 1) -- returns true if there is a unique line through P parallel to L
      List.all PointsNotOnL lmd2) -- for all points not on L, check there is a unique parallel line
    List.all plane.Lines lmd -- check for all lines

/- Checks whether a PointsAndLines instance satisfies affine_axiom3 -/
def check_affine_axiom3 (plane : PointsAndLines α) : Bool :=
    let Triples := List.product (List.product plane.Points plane.Points) plane.Points
    let lmd := (fun triple : (α × α) × α =>
      not (check_collinear plane triple.1.1 triple.1.2 triple.2))
      -- returns true if triple is non-collinear
    List.any Triples lmd

def check_affine_plane (plane : PointsAndLines α) : Bool :=
  check_affine_axiom1 plane ∧ check_affine_axiom2 plane ∧ check_affine_axiom3 plane

/- PROOFS OF EQUIVALENCE -/

theorem distinct_equiv (l : List α) :
  List.distinct l ↔ check_distinct l := by
  simp [List.distinct, check_distinct]

@[simp] theorem IsDistinct_equiv (Points : List α) (Lines : List (List α)) :
  IsDistinct Points Lines ↔
  (check_distinct Points ∧ check_distinct Lines ∧
    ∀ l ∈ Lines, check_distinct l) := by
  simp [IsDistinct, distinct_equiv]

theorem collinear_equiv (pl : PointsAndLines α) (P Q R : α) :
  collinear P Q R pl ↔ check_collinear pl P Q R := by
  simp_all [collinear, check_collinear]
  aesop

theorem parallel_equiv (pl : PointsAndLines α) (l1 l2 : List α) :
  parallel l1 l2 pl ↔ check_parallel pl l1 l2 := by
  simp_all [parallel, check_parallel]
  aesop

theorem affine_axiom1_equiv (pl : PointsAndLines α) :
  affine_axiom1 pl ↔ check_affine_axiom1 pl := by
  simp_all only [affine_axiom1, ne_eq, check_affine_axiom1,
                decide_not, Bool.decide_and, List.all_filter,
    Bool.not_not, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq, Prod.forall]
  apply Iff.intro
  { intros h P Q hPQ
    rw [List.product_mem_iff] at hPQ
    by_cases heq: P = Q
    {exact Or.inl heq}
    {apply Or.inr
     rw [@List.length_eq_one_iff]
     have h1 := h P Q hPQ.1 hPQ.2 heq
     obtain ⟨l, hl⟩ := h1
     apply Exists.intro l
     have h2: l ∈ pl.Lines ∧ P ∈ l ∧ Q ∈ l := hl.1
     have h3: l ∈ List.filter (fun l ↦ decide (P ∈ l) && decide (Q ∈ l)) pl.Lines := by
      simp [h2]
     have h4: ∀y, y ∈ List.filter (fun l ↦ decide (P ∈ l) && decide (Q ∈ l)) pl.Lines → y = l := by
      intro y a
      simp_all only [and_self, and_imp, true_and,
      List.mem_filter, decide_true, Bool.and_self, Bool.and_eq_true,
        decide_eq_true_eq]
     rw [List.singleton_mem]
     constructor
     {exact h3}
     { intro x hx
       constructor
       {apply h4 x hx}
       {apply List.distinct_filter
        apply pl.h.right.left
       }
     }
    }
  }
  {
    intros h P Q hP hQ hne
    have h1: (P, Q) ∈ pl.Points.product pl.Points := by
      simp only [List.product_mem_iff]
      exact ⟨hP, hQ⟩
    have h2 := h P Q h1
    cases h2 with
    | inl => contradiction
    | inr hr =>
      rw [@List.length_eq_one_iff] at hr
      obtain ⟨l, hl⟩ := hr
      apply ExistsUnique.intro l
      { have h: l ∈ List.filter (fun l ↦ decide (P ∈ l) && decide (Q ∈ l)) pl.Lines := by simp [hl]
        simp [List.mem_filter] at h
        assumption
      }
      {
        intros y hy
        have h: y ∈ List.filter (fun l ↦ decide (P ∈ l) && decide (Q ∈ l)) pl.Lines := by simp [hy]
        rw [hl] at h
        simp at h
        assumption
      }
  }

theorem affine_axiom2_equiv (pl : PointsAndLines α) :
  affine_axiom2 pl ↔ check_affine_axiom2 pl := by
  simp_all only [affine_axiom2, parallel_equiv, check_affine_axiom2,
    List.filter_filter, List.all_filter,
    Bool.not_not, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  apply Iff.intro
  { intro h l1 hl1 P hP
    by_cases hPl: P ∈ l1
    { apply Or.inl; assumption}
    { apply Or.inr
      have h1 := h l1 P hl1 hP hPl
      obtain ⟨m, hm⟩ := h1
      rw [@List.length_eq_one_iff]
      apply Exists.intro m
      rw [@List.singleton_mem]
      simp_all only [and_imp, List.mem_filter,
      decide_true, Bool.and_self, and_self, Bool.and_eq_true, decide_eq_true_eq, true_and]
      intro x a a_1 a_2
      obtain ⟨left, right⟩ := hm
      obtain ⟨left, right_1⟩ := left
      obtain ⟨left_1, right_1⟩ := right_1
      apply List.distinct_filter
      apply pl.h.right.left
    }
  }
  { intro h l P hl hP hPl
    have h1 := h l hl P hP
    cases h1 with
    | inl => contradiction
    | inr hr =>
      rw [List.length_eq_one_iff] at hr
      obtain ⟨m, hm⟩ := hr
      rw [List.singleton_mem] at hm
      apply ExistsUnique.intro m
      {aesop}
      {
        intros y hy
        have hm2 := hm.right y
        aesop
      }
    }

theorem affine_axiom3_equiv (pl : PointsAndLines α) :
affine_axiom3 pl ↔ check_affine_axiom3 pl := by
  simp_all only [affine_axiom3, check_affine_axiom3, collinear_equiv]
  apply Iff.intro
  { simp_all only [Bool.not_eq_true, exists_and_left, List.any_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, Prod.exists, forall_exists_index, and_imp]
    intros P hP Q hQ R hR hcol
    apply Exists.intro P
    apply Exists.intro Q
    apply Exists.intro R
    constructor
    {
      simp only [List.product_mem_iff]
      constructor
      { exact ⟨hP, hQ⟩ }
      { exact hR}
    }
    { exact hcol}
  }
  {
    intros h
    simp only [List.any_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Prod.exists] at h
    obtain ⟨P, hP⟩ := h
    obtain ⟨Q, hQ⟩ := hP
    obtain ⟨R, hR⟩ := hQ
    apply Exists.intro P
    apply Exists.intro Q
    apply Exists.intro R
    constructor
    { simp only [List.product_mem_iff] at hR
      aesop
    }
    { simp only [List.product_mem_iff] at hR
      constructor
      { exact hR.left.left.right}
      { constructor
        {
          exact hR.left.right}
        { simp only [Bool.not_eq_true]; exact hR.right}
      }
    }
  }

@[simp] theorem IsAffinePlane_equiv (pl : PointsAndLines α) :
  IsAffinePlane pl ↔ check_affine_plane pl := by
  simp_all [IsAffinePlane, check_affine_plane,
  affine_axiom1_equiv, affine_axiom2_equiv, affine_axiom3_equiv]
