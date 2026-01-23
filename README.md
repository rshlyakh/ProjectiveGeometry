# Projective Geometry

A simple program capable of automatically verifying that a given (finite) configuration of points and lines is an affine plane, projective plane, or a projective 3-space.

## Code Structure

The program for checking whether a given object is an affine plane and the equivalence proofs are contained in `ProjectiveGeometry/AffinePlane.lean`. The program for checking whether a given object is a projective plane and the equivalence proofs are contained in `ProjectiveGeometry/ProjectivePlane.lean`. The program for checking whether a given object is a projective 3-space and the equivalence proofs are located in `ProjectiveGeometry/Projective3Space.lean`. Examples are located in `ProjectiveGeometry/Examples.lean`. 

## Definitions

We follow the formulation in Hartshorne's _Foundations of Projective Geometry_. We represent a point as a term of some type; lines and planes are both represented as a list of points. 

An _affine plane_ is a list of points together with a list of lines that satisfy the following three axioms:

**Axiom 1:** Given two distinct points _P_ and _Q_, there exists a unique line containing _P_ and _Q_. 

**Axiom 2:** Given a line _l_ and a point _P_ not on _l_, there exists a unique line which is parallel to _l_ and contains _P_.

**Axiom 3:** There exist three non-collinear points.

A _projective plane_ is a list of points together with a list of lines that satisfy the following four axioms:

**Axiom 1:** Given two distinct points _P_ and _Q_, there exists a unique line containing _P_ and _Q_. 

**Axiom 2:** Any two lines intersect in at least one point.

**Axiom 3:** There exist three non-collinear points.

**Axiom 4:** Every line contains at least three points.

A _projective 3-space_ is a list of points, together with a list of lines and a list of planes that satisfy the following six axioms:

**Axiom 1:** Given two distinct points _P_ and _Q_, there exists a unique line containing _P_ and _Q_.

**Axiom 2:** Three non-collinear points _P, Q, R_ lie on a unique plane.

**Axiom 3:** A line meets a plane in at least one point.

**Axiom 4:** Two planes have at least a line in common.

**Axiom 5:** There exist four noncoplanar points, no three of which are collinear.

**Axiom 6:** Every line has at least three points.

## Details & Usage

In this development, the axioms of affine and projective planes are first stated formally. Then, for each axiom, a function is written that takes in a `PointsAndLines` structure (or `PointsLinesPlanes`, for projective 3-space) and _computes_ whether or not the axiom holds for this structure. Equivalence is then proved between the abstract definitions of the axioms and the computable functions that check their validity. That is, we prove that for any `PointsAndLines` or `PointsLinesPlanes` structure, a given axiom holds if and only if the corresponding computable function outputs "true" on this structure.

To use this program, the user should do the following:

1. For affine and projective planes, define an instance of the `PointsAndLines` structure, which consists of Points (a list), Lines (a list of lists), and a proof that all inputted points and lines are distinct. This latter proof can (generally) be written in one step via `by simp +decide` (provied that the recursion depth for `decide` is set high enough). To check that this instance is an affine plane, use `#eval check_affine_plane [your instance]`. Similarly, to check that this instance is a projective plane, use `#eval check_projective_plane [your instance]`.  

2. For projective 3-spaces, define an instance of the `PointsLinesPlanes` structure, which consists of Points and Lines (as above), Planes (a list of lists), a proof that all inputted points and lines are distinct, and a separate proof that all planes are distinct. Again, these proofs can be done in a single line using `by simp +decide`. For checking, use `#eval check_IsProjective3Space [your instance]`.

Affine planes, projective planes, and projective 3-spaces can also be instantiated in the respective `AffinePlane`, `ProjectivePlane`, and `Projective3Space` structures; the proof that the axioms hold can (generally) be written in one step via `by simp +decide`, provided that the recursion depth for `decide` is set high enough. 

For larger objects, it is more efficient to use `by simp; decide +native` rather than `by simp +decide`, but [requires trusting Lean's built-in `#eval` compiler](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#decide). 
## Examples:

```
def FourPointPlane : PointsAndLines Nat :=
  {
    Points := [1, 2, 3, 4]
    Lines := [ [1,2], [3,4], [1,3], [2,4], [1,4], [2,3] ]
    h := by simp +decide
  }
#eval check_affine_plane FourPointPlane -- returns true

def FourPointAffinePlane : AffinePlane Nat :=
  {
    pl := FourPointPlane
    isAffine := by simp +decide
  }
```
The proof that `FourPointAffinePlane` satisfies the affine plane axioms takes a single line, thanks to the earlier work. 

Similarly, the proof that the Fano Plane is a projective plane takes a single line:

```
def FanoPlane : PointsAndLines Nat :=
  { Points := [1, 2, 3, 4, 5, 6, 7],
    Lines := [[1, 2, 5], [1, 3, 6], [1, 4, 7], [5, 6, 7], [3, 4, 5], [2, 4, 6], [2, 3, 7]]
    h := by simp +decide }

#eval check_projective_plane FanoPlane

def FanoPlaneProjective : ProjectivePlane Nat :=
  {
    pl := FanoPlane
    isProjective := by simp +decide
  }
```

For additional examples, see the `Examples.lean` file.

## Issues/Future Work

The programs were written in a way that would make reasoning about them as easy as possible, with no attempt made to optimize for efficiency. In some cases, this leads to unecessary computations.

For example, one improvement would be to add flags to the helper coplanarity and collinearity checking functions so that verifying whether `α` terms are points is optional, in case this is checked elsewhere in the main function.

The naming scheme is inconsistent and not in proper Lean style.

## Acknowledgements
Examples of finite affine and projective planes were drawn from: [Finite Plane Examples](https://web.york.cuny.edu/~malk/mycourses/math244/finite-plane-examples.html)
