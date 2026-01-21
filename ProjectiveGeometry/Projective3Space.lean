import ProjectiveGeometry.ProjectivePlane

/- UNDER CONSTRUCTION -/

/- Q: should add a flag to check_collinear/coplanar, to check if points are Points? -/
variable {α : Type} [DecidableEq α]

/- BASIC DEFINITIONS -/

structure PointsLinesPlanes (α : Type) [DecidableEq α] extends PointsAndLines α
where
(Planes : List (List α))
(hP: Planes.distinct)

def coplanar [DecidableEq α] (P Q R S : α) (pl : PointsLinesPlanes α) : Prop :=
  /- Issue with distinct points -/
  [P, Q, R, S] ⊆ pl.Points ∧ ∃ π ∈ pl.Planes, [P, Q, R, S] ⊆ π

/- AXIOMS -/

/- Axiom 1:
   Given two distinct points P and Q, there exists a unique line containing P and Q.
   This is the same as affine_axiom1 -/

#check affine_axiom1

/- Axiom 2:
   Three non-collinear points P, Q, R lie on a unique plane.
-/

def three_space_axiom2 (pl : PointsLinesPlanes α) : Prop :=
  ∀ P ∈ pl.Points, ∀ Q ∈ pl.Points, ∀ R ∈ pl.Points,
  ¬ collinear P Q R pl.toPointsAndLines → ∃! π ∈ pl.Planes, [P, Q, R] ⊆ π

/- Axiom 3: A line meets a plane in at least one point. -/

def three_space_axiom3 (pl : PointsLinesPlanes α) : Prop :=
  ∀ l ∈ pl.Lines, ∀ π ∈ pl.Planes, l ∩ π ≠ []

/- Axiom 4: Two planes have at least a line in common. -/

def three_space_axiom4 (pl : PointsLinesPlanes α) : Prop :=
  ∀ π_1 ∈ pl.Planes, ∀ π_2 ∈ pl.Planes, ∃ l ∈ pl.Lines, l ⊆ (π_1 ∩ π_2)

/- Axiom 5: There exist four noncoplanar points, no three of which are collinear. -/

def three_space_axiom5 (pl : PointsLinesPlanes α) : Prop :=
  ∃ P ∈ pl.Points, ∃ Q ∈ pl.Points, ∃ R ∈ pl.Points, ∃ S ∈ pl.Points,
  ¬ coplanar P Q R S pl
  ∧ ¬ collinear P Q R pl.toPointsAndLines
  ∧ ¬ collinear P Q S pl.toPointsAndLines
  ∧ ¬ collinear P S R pl.toPointsAndLines
  ∧ ¬ collinear Q R S pl.toPointsAndLines

/- Axiom 6: Every line has at least three points.
   This is the same as projective_axiom4. -/

#check projective_axiom4

def IsProjective3Space (pl : PointsLinesPlanes α) : Prop :=
  affine_axiom1 pl.toPointsAndLines
  ∧ three_space_axiom2 pl
  ∧ three_space_axiom3 pl
  ∧ three_space_axiom4 pl
  ∧ three_space_axiom5 pl
  ∧ projective_axiom4 pl.toPointsAndLines

structure Projective3Space (α : Type) [DecidableEq α]
  where
  (pl : PointsLinesPlanes α)
  (is3Space: IsProjective3Space pl)

/- COMPUTING WITH THE AXIOMS -/

def check_coplanar (P Q R S : α) (pl : PointsLinesPlanes α) : Bool :=
  /- Note no need to check if they are points, since check_collinear does this,
     but makes proving easier -/
     if not ([P, Q, R, S] ⊆ pl.Points) then false
     else
     pl.Planes.any (fun π => [P, Q, R, S] ⊆ π)

theorem check_coplanar_equiv (P Q R S : α) (pl : PointsLinesPlanes α) :
  coplanar P Q R S pl ↔ check_coplanar P Q R S pl := by
    simp [coplanar, check_coplanar]

 -- Three non-collinear points P, Q, R lie on a unique plane.
def check_three_space_axiom2 (pl : PointsLinesPlanes α) : Bool :=
    let triples :=
      List.filter (fun (T : (α × α) × α) => ¬ check_collinear pl.toPointsAndLines T.1.1 T.1.2 T.2 )
      (List.product (List.product pl.Points pl.Points) pl.Points)
    let lmd : (α × α) × α → Bool :=
    (fun T => (List.filter (fun π => [T.1.1, T.1.2, T.2] ⊆ π) pl.Planes).length = 1)
    List.all triples lmd

/- lemma ExistsUnique_filter (p : α → Bool) (l: List α):
  ∃! a : α, p a → (List.filter p l).length = 1 := by sorry -/

theorem three_space_axiom2_equiv (pl: PointsLinesPlanes α) :
  three_space_axiom2 pl ↔ check_three_space_axiom2 pl := by
    simp [three_space_axiom2, check_three_space_axiom2]
    apply Iff.intro
    { intros h P Q R hP hQ hR
      by_cases hcol: collinear P Q R pl.toPointsAndLines
      { apply Or.inl; simp only [←collinear_equiv]; assumption }
      { apply Or.inr
        have h := h P hP Q hQ R hR hcol
        obtain ⟨π, hπ⟩ := h
        let l := (List.filter (fun π ↦ decide (P ∈ π) &&
        (decide (Q ∈ π) && decide (R ∈ π))) pl.Planes)
        have π_in: π ∈ l := by simp[l, hπ]
        have no_in: ∀y ∈ l, y = π := by grind
        have distinct: l.distinct := by
          apply List.distinct_filter
          exact pl.hP
        rw [@List.length_eq_one_iff]
        apply Exists.intro π
        rw [List.singleton_mem]
        simp [l, π_in, distinct]
        aesop
      }
    }
    { intros h P hP Q hQ R hR ncoll
      have h := h P Q R hP hQ hR
      cases h with
      | inl h=> rw [←collinear_equiv] at h; contradiction
      | inr h =>
        let l := (List.filter (fun π ↦ decide (P ∈ π) &&
        (decide (Q ∈ π) && decide (R ∈ π))) pl.Planes)
        have h2: ∃ π : List α, π ∈ l := by
          simp [← @List.isEmpty_eq_false_iff_exists_mem]
          grind
        obtain ⟨π, hπ⟩ := h2
        simp only [ExistsUnique, and_imp]
        apply Exists.intro π
        simp_all [l]
        intro y hy hPy hQy hRy
        have y_in: y ∈ l := by grind
        have h3: ∃ u, l = [u] := by
          rw [← @List.length_eq_one_iff]
          aesop
        
        sorry
    }
