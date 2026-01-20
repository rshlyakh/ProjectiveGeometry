import ProjectiveGeometry.Basic
import ProjectiveGeometry

lemma exist_3_list_length {α : Type} (l : List α) : (∃ P ∈ l, ∃ Q ∈ l, ∃ R ∈ l,
    P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧ P ∈ l ∧ Q ∈ l ∧ R ∈ l) ↔ l.length ≥ 3 := by
    apply Iff.intro
    {
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
      have h_len: s.length ≤ l.length := by sorry
      simp [h_s_len] at h_len
      assumption
    }
    {intro h
     have hP: ∃ P, P ∈ l := by
      rw [← @List.isEmpty_eq_false_iff_exists_mem]
      rw [@List.isEmpty_eq_false_iff]
      rw [@List.ne_nil_iff_length_pos]
      omega
     obtain ⟨P, hP⟩ := hP
     have hQ: ∃ Q, Q ∈ l ∧ Q ≠ P := by sorry
     sorry
    }

variable {α : Type} [DecidableEq α]

/- Axiom 1: Two distinct points P, Q lie on a unique line -/

-- Same as affine axiom 1
#check affine_axiom1

/- Axiom 2: Any two lines meet in at least one point. -/

def projective_axiom2 (pl : PointsAndLines α) : Prop :=
  ∀ l1 ∈ pl.Lines, ∀ l2 ∈ pl.Lines, ∃ P ∈ pl.Points, P ∈ l1 ∧ P ∈ l2

/- Axiom 3: There exist three non-collinear points -/
-- Same as affine axiom 3
#check affine_axiom3

/- Axiom 4: Every line contains at least three points. -/

def projective_axiom4 (pl : PointsAndLines α) : Prop :=
  ∀ l ∈ pl.Lines, ∃ P ∈ pl.Points, ∃ Q ∈ pl.Points, ∃ R ∈ pl.Points,
    P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧ P ∈ l ∧ Q ∈ l ∧ R ∈ l

def IsProjectivePlane (pl : PointsAndLines α) : Prop :=
  affine_axiom1 pl ∧
  projective_axiom2 pl ∧
  affine_axiom3 pl ∧
  projective_axiom4 pl

structure ProjectivePlane (α : Type) [DecidableEq α]
  where
  (pl : PointsAndLines α)
  (isProjective : IsProjectivePlane pl)

def check_projective_axiom2 (pl : PointsAndLines α) : Bool :=
  let lmd := fun (l1 : List α) (l2 : List α) =>
    let pts_on_l1 := pl.Points.filter (fun P => P ∈ l1)
    let pts_on_l2 := pl.Points.filter (fun P => P ∈ l2)
    let common_pts := pts_on_l1.filter (fun P => P ∈ pts_on_l2)
    common_pts.length > 0
  List.all pl.Lines (fun l1 =>
    List.all pl.Lines (lmd l1)
    )

def check_projective_axiom4 (pl : PointsAndLines α) : Bool :=
  let lmd := fun (l : List α) =>
    let pts_on_l := pl.Points.filter (fun P => P ∈ l)
    pts_on_l.length ≥ 3
  List.all pl.Lines lmd

theorem check_projective_axiom2_equiv (pl : PointsAndLines α) :
  projective_axiom2 pl ↔ check_projective_axiom2 pl := by
  simp [projective_axiom2, check_projective_axiom2]
  grind

theorem check_projective_axiom4_equiv (pl : PointsAndLines α) :
  projective_axiom4 pl ↔ check_projective_axiom4 pl := by
  simp only [projective_axiom4, ne_eq, check_projective_axiom4, ge_iff_le, List.all_eq_true,
    decide_eq_true_eq]
  apply Iff.intro
  {
    intros h l hl
    have h1 := h l hl
    obtain ⟨P, hP⟩ := h1
    obtain ⟨Q, hQ⟩ := hP.right
    obtain ⟨R, hR⟩ := hQ.right
    have hP_fact: P ∈ pl.Points ∧ P ∈ l := by simp_all only [true_and, not_false_eq_true, and_self]
    have hQ_fact: Q ∈ pl.Points ∧ Q ∈ l := by simp_all only [true_and, not_false_eq_true, and_self]
    have hR_fact: R ∈ pl.Points ∧ R ∈ l := by simp_all only [true_and, not_false_eq_true, and_self]
    have distinct: P ≠ Q ∧ P ≠ R ∧ Q ≠ R := by
     simp_all only [true_and, not_false_eq_true, and_self, and_true, ne_eq]
    let pts_on_l := pl.Points.filter (fun P => decide (P ∈ l))
    have h_on: P ∈ pts_on_l ∧ Q ∈ pts_on_l ∧ R ∈ pts_on_l := by
      simp_all only [true_and, not_false_eq_true, and_self, ne_eq,
      List.mem_filter, decide_true, pts_on_l]
    apply (exist_3_list_length pts_on_l).mp
    grind
  }
  {
    intro h l hl
    have h1 := h l hl
    let pts_on_l := pl.Points.filter (fun P => decide (P ∈ l))
    have P_exists: ∃ P ∈ pts_on_l, ∃ Q ∈ pts_on_l, ∃ R ∈ pts_on_l,
      ¬ P = Q ∧ ¬ P = R ∧ ¬ Q = R ∧ P ∈ pts_on_l ∧ Q ∈ pts_on_l ∧ R ∈ pts_on_l := by
      apply (exist_3_list_length pts_on_l).mpr
      grind
    grind
  }

def check_projective_plane (pl : PointsAndLines α) :  Bool :=
  check_affine_axiom1 pl ∧
  check_projective_axiom2 pl ∧
  check_affine_axiom3 pl ∧
  check_projective_axiom4 pl

@[simp] theorem IsProjectivePlane_equiv (pl : PointsAndLines α) :
  IsProjectivePlane pl ↔ check_projective_plane pl := by
  simp_all [check_projective_plane, IsProjectivePlane, check_affine_axiom1, check_projective_axiom2,
            check_affine_axiom3, check_projective_axiom4,
            affine_axiom1_equiv, check_projective_axiom2_equiv,
            affine_axiom3_equiv, check_projective_axiom4_equiv]

/- EXAMPLES -/

def FanoPlane : PointsAndLines Nat :=
  { Points := [1, 2, 3, 4, 5, 6, 7],
    Lines := [[1, 2, 5], [1, 3, 6], [1, 4, 7], [5, 6, 7], [3, 4, 5], [2, 4, 6], [2, 3, 7]]
    h := by simp+decide }

#eval check_projective_plane FanoPlane

def FanoPlaneProjective : ProjectivePlane Nat :=
  {
    pl := FanoPlane
    isProjective := by simp+decide
  }

def ThirteenPointPlane : PointsAndLines Nat :=
  { Points := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13],
    Lines := [[1, 2, 3, 10], [1, 4, 7, 11], [1, 5, 9, 12], [1, 6, 8, 13],
             [4, 5, 6, 10], [2, 5, 8, 11], [2, 6, 7, 12], [2, 4, 9, 13],
             [7, 8, 9, 10], [3, 6, 9, 11], [3, 4, 8, 12], [3, 5, 7, 13], [10, 11, 12, 13]]
    h := by simp+decide }

#eval check_projective_plane ThirteenPointPlane

def ThirteenPointProjectivePlane : ProjectivePlane Nat :=
  {
    pl := ThirteenPointPlane
    isProjective := by simp+decide
  }

def TwentyOnePointPlane : PointsAndLines Nat :=
  { Points := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21],
    Lines := [[1, 2, 3, 4, 5],
             [5, 9, 13, 17, 18],
             [2, 6, 10, 14, 18],
             [2, 9, 11, 16, 20],
             [2, 7, 12, 17, 19],
             [1, 10, 11, 12, 13],
             [1, 18, 19, 20, 21],
             [3, 7, 11, 15, 18],
             [4, 9, 10, 15, 19],
             [5, 6, 12, 15, 20],
             [5, 8, 11, 14, 19],
             [1, 6, 7, 8, 9],
             [4, 7, 13, 14, 20],
             [2, 8, 13, 15, 21],
             [3, 8, 10, 17, 20],
             [1, 14, 15, 16, 17],
             [3, 6, 13, 16, 19],
             [5, 7, 10, 16, 21],
             [4, 8, 12, 16, 18],
             [3, 9, 12, 14, 21],
             [4, 6, 11, 17, 21]]
    h := by simp+decide }

#eval check_projective_plane TwentyOnePointPlane

set_option maxRecDepth 1000

def TwentyOnePointProjectivePlane : ProjectivePlane Nat :=
  {
    pl := TwentyOnePointPlane
    isProjective := by simp+decide
  }
