# Projective Geometry

A simple program that automatically verifies that a given (finite) configuration of points and lines is an affine plane.

## Definitions

We follow Hartshorne's _Foundations of Projective Geometry_. A point is represented as an element of some type; a line is a list of points. An affine plane is a list of points together with a list of lines which satisfy the following three axioms:

**Axiom 1:** Given two distinct points P and Q, there exists a unique line containing P and Q. 

**Axiom 2:** Given a line l and a point P not on l, there exists a unique line which is parallel to l and contains P.

**Axiom 3:** There exist three non-collinear points.

## Usage

In this development, the axioms of an affine plane are first stated formally. Then, for each axiom, a function is written that takes in a "PointsAndLines" structure and _computes_ whether or not the axiom holds for this structure. Equivalence is then proved between the abstract definitions of the axioms and the computable functions that check their validity. That is, we prove that for any `PointsAndLines` structure, a given axiom holds if and only if the corresponding computable function outputs "true" on this structure.

To use this program, the user should define an instance of the `PointsAndLines` structure, which consists of Points (a List), Lines (a list of lists), and a proof that all inputted points and lines are distinct. This latter proof can (generally) be written in one step via `by simp+decide.` 

## Examples:

```
def FourPointPlane : PointsAndLines Nat :=
  {
    Points := [1, 2, 3, 4]
    Lines := [ [1,2], [3,4], [1,3], [2,4], [1,4], [2,3] ]
    h := by simp+decide
  }
#eval check_affine_plane FourPointPlane -- returns true

def FourPointAffinePlane : AffinePlane Nat :=
  {
    pl := FourPointPlane
    isAffine := by simp+decide
  }
```
The proof that `FourPointAffinePlane` satisfies the affine plane axioms takes a single line, thanks to the earlier work. For additional examples, see the `Examples.lean` file.

## Future Work
Eventually, I hope to write similar programs that would accomplish the same task for a finite projective plane and a finite projective 3-space.

## Acknowledgements
I used LeanCopilot for one or two of the simpler proofs. Examples of finite projective planes were drawn from: [Finite Plane Example](https://web.york.cuny.edu/~malk/mycourses/math244/finite-plane-examples.html)
