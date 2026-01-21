# Projective Geometry

A simple program that automatically verifies that a given (finite) configuration of points and lines is an affine plane or a projective plane.

## Code Structure

The program for checking whether a given object is an affine plane and the equivalence proofs are contained in `ProjectiveGeometry/AffinePlane.lean`. The program for checking whether a given object is a projective plane and the equivalence proofs are contained in `ProjectiveGeometry/ProjectivePlane.lean`. The program for checking whether a given object is a projective 3-space and the equivalence proofs are located in `ProjectiveGeometry/Projective3Space.lean`. Examples are located in `ProjectiveGeometry/Examples.lean`. 

## Definitions

We follow the formulation in Hartshorne's _Foundations of Projective Geometry_. We represent a point as a term of some type; a line is represented as a list of points. 

An _affine plane_ is a list of points together with a list of lines which satisfy the following three axioms:

**Axiom 1:** Given two distinct points _P_ and _Q_, there exists a unique line containing _P_ and _Q_. 

**Axiom 2:** Given a line _l_ and a point _P_ not on _l_, there exists a unique line which is parallel to _l_ and contains _P_.

**Axiom 3:** There exist three non-collinear points.

A _projective plane_ is a list of points together with a list of lists which satisfy the following four axioms:

**Axiom 1:** Given two distinct points _P_ and _Q_, there exists a unique line containing _P_ and _Q_. 

**Axiom 2:** Any two lines intersect in at least one point.

**Axiom 3:** There exist three non-collinear points.

**Axiom 4:** Every line contains at least three points.

## Details & Usage

In this development, the axioms of affine and projective planes are first stated formally. Then, for each axiom, a function is written that takes in a `PointsAndLines` structure (or `PointsLinesPlanes`, for projective 3-space) and _computes_ whether or not the axiom holds for this structure. Equivalence is then proved between the abstract definitions of the axioms and the computable functions that check their validity. That is, we prove that for any `PointsAndLines` or `PointsLinesPlanes` structure, a given axiom holds if and only if the corresponding computable function outputs "true" on this structure.

To use this program, the user should define an instance of the `PointsAndLines` structure, which consists of Points (a list), Lines (a list of lists), and a proof that all inputted points and lines are distinct. This latter proof can (generally) be written in one step via `by simp +decide` (provied that the recursion depth for `decide` is set high enough). To check that this instance is an affine plane, use `#eval check_affine_plane [your instance]`. Similarly, to check that this instance is a projective plane, use `#eval check_projective_plane [your instance]`.  

Affine planes and projective planes can also be instantiated in the respective `AffinePlane` and `ProjectivePlane` structures; the proof that the axioms hold can (generally) be written in one step via `by simp +decide`, provided that the recursion depth for `decide` is set high enough.

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

## Future Work
Eventually, I hope to write a similar program that would accomplish the same task for a finite projective 3-space.

The programs were written in a way that would make reasoning about them as easy as possible, with no attempt made to optimize for efficiency. In some cases, this leads to unecessary computations -- another area for improvement. 

## Acknowledgements
Examples of finite affine and projective planes were drawn from: [Finite Plane Examples](https://web.york.cuny.edu/~malk/mycourses/math244/finite-plane-examples.html)
