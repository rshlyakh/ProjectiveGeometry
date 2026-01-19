# Projective Geometry

A simple program that automatically verifies that a given (finite) configuration of points and lines is an affine plane.

## Definitions

We follow Hartshorne's _Foundations of Projective Geometry_. An affine plane is a list of points together with a list of lists of lines which satisfy the following three axioms:

Axiom 1: Given two distinct points P and Q, there exists a unique line containing P and Q. 

Axiom 2: Given a line l and a point P not on l, there exists a unique line which is parallel to l and contains P.

Axiom 3: There exist three non-collinear points.

## Usage

In this development, the axioms of an affine plane are first stated formally. Then, for each axiom, a function is written that takes in a "PointsAndLines" structure and _computes_ whether or not the axiom holds for this structure. Equivalence is then proved between the abstract mathematical axioms and the computable functions that check their validity.

To use this program, the user should define an instance of the "PointsAndLines" structure, which consists of Points (a List), Lines (a list of Lines), and a proof that all inputted points and lines are distinct. This latter proof can be written in one step via "by rw[IsDistinct_equiv]; decide." 

## Examples:

```
def FourPointPlane : PointsAndLines Nat :=
  {
    Points := [1, 2, 3, 4]
    Lines := [ [1,2], [3,4], [1,3], [2,4], [1,4], [2,3] ]
    h := by rw[IsDistinct_equiv]; decide
  }
#eval check_affine_plane FourPointPlane -- returns true

def FourPointAffinePlane : AffinePlane Nat :=
  {
    pl := FourPointPlane
    isAffine := by rw [IsAffinePlane_equiv]; decide
  }
```
The proof that 'FourPointAffinePlane' satisfies the affine plane axioms takes a single line, thanks to the earlier work. 
