import ProjectiveGeometry.ProjectivePlane

set_option linter.flexible false

variable {α : Type} [DecidableEq α]

/- BASIC DEFINITIONS -/

structure PointsLinesPlanes (α : Type) [DecidableEq α] extends PointsAndLines α
where
(Planes : List (List α))
(hP: Planes.distinct)

def coplanar [DecidableEq α] (P Q R S : α) (pl : PointsLinesPlanes α) : Prop :=
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
  -- note that it's not necesary to check distinctess, as this would be caught by collinearity
  ∃ P ∈ pl.Points, ∃ Q ∈ pl.Points, ∃ R ∈ pl.Points, ∃ S ∈ pl.Points,
  ¬ coplanar P Q R S pl
  ∧ ¬ collinear P Q R pl.toPointsAndLines
  ∧ ¬ collinear P Q S pl.toPointsAndLines
  ∧ ¬ collinear P R S pl.toPointsAndLines
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

def check_three_space_axiom2 (pl : PointsLinesPlanes α) : Bool :=
    let triples :=
      List.filter (fun (T : (α × α) × α) => ¬ check_collinear pl.toPointsAndLines T.1.1 T.1.2 T.2 )
      (List.product (List.product pl.Points pl.Points) pl.Points)
    let lmd : (α × α) × α → Bool :=
    (fun T => (List.filter (fun π => [T.1.1, T.1.2, T.2] ⊆ π) pl.Planes).length = 1)
    List.all triples lmd

def check_three_space_axiom3 (pl : PointsLinesPlanes α) : Bool :=
  pl.Lines.all (fun l => pl.Planes.all (fun π => ¬ (l ∩ π).isEmpty))

def check_three_space_axiom4 (pl : PointsLinesPlanes α) : Bool :=
  let pairs := List.product pl.Planes pl.Planes
  let lmd : (List α × List α) → Bool :=
    (fun πs => not (List.filter (fun l => l ⊆ (πs.1 ∩ πs.2)) pl.Lines).isEmpty)
  List.all pairs lmd

def check_three_space_axiom5 (pl : PointsLinesPlanes α) : Bool :=
  let quadruples :=
    List.filter (fun (Q : ((α × α) × α) × α) =>
      ¬ check_coplanar Q.1.1.1 Q.1.1.2 Q.1.2 Q.2 pl &&
      ¬ check_collinear pl.toPointsAndLines Q.1.1.1 Q.1.1.2 Q.1.2 &&
      ¬ check_collinear pl.toPointsAndLines Q.1.1.1 Q.1.1.2 Q.2 &&
      ¬ check_collinear pl.toPointsAndLines Q.1.1.1 Q.1.2 Q.2 &&
      ¬ check_collinear pl.toPointsAndLines Q.1.1.2 Q.1.2 Q.2)
    (List.product (List.product (List.product pl.Points pl.Points) pl.Points) pl.Points)
  not quadruples.isEmpty

def check_IsProjective3Space (pl : PointsLinesPlanes α) : Bool :=
  check_affine_axiom1 pl.toPointsAndLines
  ∧ check_three_space_axiom2 pl
  ∧ check_three_space_axiom3 pl
  ∧ check_three_space_axiom4 pl
  ∧ check_three_space_axiom5 pl
  ∧ check_projective_axiom4 pl.toPointsAndLines

/- PROOFS OF EQUIVALENCE -/

theorem check_coplanar_equiv (P Q R S : α) (pl : PointsLinesPlanes α) :
  coplanar P Q R S pl ↔ check_coplanar P Q R S pl := by
    simp [coplanar, check_coplanar]

theorem three_space_axiom2_equiv (pl : PointsLinesPlanes α) :
  three_space_axiom2 pl ↔ check_three_space_axiom2 pl := by
    simp only [three_space_axiom2, List.cons_subset, List.nil_subset, and_true,
      check_three_space_axiom2, Bool.not_eq_true, Bool.decide_eq_false, Bool.decide_and,
      List.all_filter, Bool.not_not, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      Prod.forall, List.pair_mem_product, and_imp]
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
        simp [l, π_in]
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
        simp_all only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, and_self, true_and, l]
        intro y hy hPy hQy hRy
        have y_in: y ∈ l := by grind
        apply singleton_equal_elems l y π
        {assumption}
        {assumption}
        {simp_all only [List.mem_filter, decide_true, Bool.and_self, and_self, l]}
    }

theorem three_space_axiom3_equiv (pl : PointsLinesPlanes α) :
  three_space_axiom3 pl ↔ check_three_space_axiom3 pl := by
    simp [three_space_axiom3, check_three_space_axiom3]

theorem three_space_axiom4_equiv (pl : PointsLinesPlanes α) :
  three_space_axiom4 pl ↔ check_three_space_axiom4 pl := by
    simp [three_space_axiom4, check_three_space_axiom4]
    grind

theorem three_space_axiom5_equiv (pl : PointsLinesPlanes α) :
  three_space_axiom5 pl ↔ check_three_space_axiom5 pl := by
    simp [three_space_axiom5, check_three_space_axiom5]
    apply Iff.intro
    { intro h
      obtain ⟨P, hP⟩ := h
      obtain ⟨Q, hQ⟩ := hP.right
      obtain ⟨R, hR⟩ := hQ.right
      obtain ⟨S, hS⟩ := hR.right
      apply Exists.intro P
      constructor
      {exact hP.left}
      {apply Exists.intro Q
       constructor
       {exact hQ.left}
       {
        apply Exists.intro R
        constructor
        {exact hR.left}
        { apply Exists.intro S
          constructor
          {exact hS.left}
          {
            simp_all [collinear_equiv, check_coplanar_equiv]
          }
        }
       }
      }
    }
    {
      intro h
      obtain ⟨P, hP⟩ := h
      obtain ⟨Q, hQ⟩ := hP.right
      obtain ⟨R, hR⟩ := hQ.right
      obtain ⟨S, hS⟩ := hR.right
      apply Exists.intro P
      constructor
      {exact hP.left}
      {apply Exists.intro Q
       constructor
       {exact hQ.left}
       {
          apply Exists.intro R
          constructor
          {exact hR.left}
          { apply Exists.intro S
            constructor
            {exact hS.left}
            {
              simp_all [collinear_equiv, check_coplanar_equiv]
            }
          }
        }
     }
    }

@[simp] theorem IsProjective3Space_equiv (pl : PointsLinesPlanes α) :
  IsProjective3Space pl ↔ check_IsProjective3Space pl := by
    simp [IsProjective3Space, check_IsProjective3Space,
      affine_axiom1_equiv, three_space_axiom2_equiv,
      three_space_axiom3_equiv, three_space_axiom4_equiv,
      three_space_axiom5_equiv, check_projective_axiom4_equiv]
