import ProjectiveGeometry

/- TO-DO : Fix naming scheme -/
variable {α : Type} [DecidableEq α]

/- AXIOMS -/

/- Axiom 1: Two distinct points P, Q lie on a unique line
   This is the same as affine axiom 1 -/
#check affine_axiom1

/- Axiom 2: Any two lines meet in at least one point. -/

def projective_axiom2 (pl : PointsAndLines α) : Prop :=
  ∀ l1 ∈ pl.Lines, ∀ l2 ∈ pl.Lines, ∃ P ∈ pl.Points, P ∈ l1 ∧ P ∈ l2

/- Axiom 3: There exist three non-collinear points
   This is the same as affine axiom 3 -/
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

/- COMPUTING WITH THE AXIOMS -/

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

/- PROOFS OF EQUIVALENCE -/

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
    apply (exist_3_list_length_fwd pts_on_l)
    grind
  }
  {
    intro h l hl
    have h1 := h l hl
    let pts_on_l := pl.Points.filter (fun P => decide (P ∈ l))
    have P_exists: ∃ P ∈ pts_on_l, ∃ Q ∈ pts_on_l, ∃ R ∈ pts_on_l,
      ¬ P = Q ∧ ¬ P = R ∧ ¬ Q = R ∧ P ∈ pts_on_l ∧ Q ∈ pts_on_l ∧ R ∈ pts_on_l := by
      apply (exist_3_list_length_bwd pts_on_l)
      {grind}
      {apply List.distinct_filter; exact pl.h.left}
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
