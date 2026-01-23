import ProjectiveGeometry
import ProjectiveGeometry.ProjectivePlane
import ProjectiveGeometry.Projective3Space

/- AFFINE PLANE EXAMPLES -/

def FourPointPlane : PointsAndLines Nat :=
  /- here, nats are used for points names, but any type with decidable equality could be used -/
  {
    Points := [1, 2, 3, 4]
    Lines := [ [1,2], [3,4], [1,3], [2,4], [1,4], [2,3] ]
    h := by simp +decide
  }
#eval check_affine_plane FourPointPlane

def FourPointAffinePlane : AffinePlane Nat :=
  {
    pl := FourPointPlane
    isAffine := by simp +decide
  }

def NinePointPlane : PointsAndLines Nat :=
   {
     Points := [1, 2, 3, 4, 5, 6, 7, 8, 9]
     Lines := [ [1,2,3], [4,5,6], [7,8,9], [1,4,7], [2,5,8], [3,6,9],
                [1,5,9], [2,6,7], [3,4,8], [1,6,8], [2,4,9], [3,5,7] ]
     h := by simp +decide
   }

#eval check_affine_plane NinePointPlane

def NinePointAffinePlane : AffinePlane Nat :=
  {
    pl := NinePointPlane
    isAffine := by simp +decide
  }

def SixteenPointPlane : PointsAndLines Nat :=
  {
    Points := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
    Lines := [ [1,2,3,4], [1,5,9,14], [4,5,10,13], [2,6,10,14], [2,7,12,13],
               [3,8,10,16], [3,5,12,15], [5,6,7,8], [4,7,9,16], [4,8,12,14],
               [1,6,12,16], [1,7,10,15], [3,6,9,13], [2,8,9,15], [9,10,11,12],
               [3,7,11,14], [4,6,11,15], [13,14,15,16], [2,5,11,16], [1,8,11,13] ]
    h := by simp +decide
  }

#eval check_affine_plane SixteenPointPlane

set_option maxRecDepth 600 -- note that the recursion depth must be increased for larger examples.

def SixteenPointAffinePlane : AffinePlane Nat :=
  {
    pl := SixteenPointPlane
    isAffine := by simp +decide
  }

set_option maxRecDepth 1300

def TwentyFivePointPlane : PointsAndLines Nat :=
  {
    Points := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
              15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
    Lines := [ [1,2,3,4,5], [6,7,8,9,10], [11,12,13,14,15], [16,17,18,19,20], [21,22,23,24,25],
               [1,6,11,16,21], [2,7,12,17,22], [3,8,13,18,23], [4,9,14,19,24], [5,10,15,20,25],
               [1,7,13,19,25], [2,8,14,20,21], [3,9,15,16,22], [4,10,11,17,23], [5,6,12,18,24],
               [1,8,15,17,24], [2,9,11,18,25], [3,10,12,19,21], [4,6,13,20,22], [5,7,14,16,23],
               [1,9,12,20,23], [2,10,13,16,24], [3,6,14,17,25], [4,7,15,18,21], [5,8,11,19,22],
               [1,10,14,18,22], [2,6,15,19,23], [3,7,11,20,24], [4,8,12,16,25], [5,9,13,17,21] ]
    h := by simp +decide
  }

#eval check_affine_plane TwentyFivePointPlane

def TwentyFivePointAffinePlane : AffinePlane Nat :=
  {
    pl := TwentyFivePointPlane
    isAffine := by simp +decide
  }

/- PROJECTIVE PLANE EXAMPLES -/

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

def ThirteenPointPlane : PointsAndLines Nat :=
  { Points := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13],
    Lines := [[1, 2, 3, 10],
              [1, 4, 7, 11],
              [1, 5, 9, 12],
              [1, 6, 8, 13],
              [4, 5, 6, 10],
              [2, 5, 8, 11],
              [2, 6, 7, 12],
              [2, 4, 9, 13],
              [7, 8, 9, 10],
              [3, 6, 9, 11],
              [3, 4, 8, 12],
              [3, 5, 7, 13],
              [10, 11, 12, 13]]
    h := by simp +decide }

#eval check_projective_plane ThirteenPointPlane

def ThirteenPointProjectivePlane : ProjectivePlane Nat :=
  {
    pl := ThirteenPointPlane
    isProjective := by simp +decide
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
    h := by simp +decide }

#eval check_projective_plane TwentyOnePointPlane

set_option maxRecDepth 1000

def TwentyOnePointProjectivePlane : ProjectivePlane Nat :=
  {
    pl := TwentyOnePointPlane
    isProjective := by simp +decide
  }

/- PROJECTIVE 3-SPACE EXAMPLES -/

def PG32 : PointsLinesPlanes Nat :=
  /- This is the smallest projective 3-space. -/
  {
    Points := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
    Lines := [[1,2,3],[1,4,5],[1,6,7],[1,8,9],[1,10,11],[1,12,13],[1,14,15],
 [2,4,6],[2,5,7],[2,8,10],[2,9,11],[2,12,14],[2,13,15],
 [3,4,7],[3,5,6],[3,8,11],[3,9,10],[3,12,15],[3,13,14],
 [4,8,12],[4,9,13],[4,10,14],[4,11,15],
 [5,8,13],[5,9,12],[5,10,15],[5,11,14],
 [6,8,14],[6,9,15],[6,10,12],[6,11,13],
 [7,8,15],[7,9,14],[7,10,13],[7,11,12]]
    Planes := [[1,2,3,4,5,6,7],
 [1,2,3,8,9,10,11],
 [1,2,3,12,13,14,15],
 [1,4,5,8,9,12,13],
 [1,4,5,10,11,14,15],
 [1,6,7,8,9,14,15],
 [1,6,7,10,11,12,13],
 [2,4,6,8,10,12,14],
 [2,4,6,9,11,13,15],
 [2,5,7,8,10,13,15],
 [2,5,7,9,11,12,14],
 [3,4,7,8,11,12,15],
 [3,4,7,9,10,13,14],
 [3,5,6,8,11,13,14],
 [3,5,6,9,10,12,15]]
    h := by simp +decide
    hP := by simp +decide
  }

#eval check_IsProjective3Space PG32

set_option linter.style.nativeDecide false
-- set_option maxHeartbeats 1000000 in


def PG32Space : Projective3Space Nat :=
  {
    pl := PG32
    is3Space := by
      simp only [IsProjective3Space_equiv]
      decide +native -- native_decide could also be used here (they are synonyms)
  }
