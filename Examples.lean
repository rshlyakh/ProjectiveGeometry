import ProjectiveGeometry

/- AFFINE PLANE EXAMPLES -/

def FourPointPlane : PointsAndLines Nat :=
  {
    Points := [1, 2, 3, 4]
    Lines := [ [1,2], [3,4], [1,3], [2,4], [1,4], [2,3] ]
    h := by simp+decide
  }
#eval check_affine_plane FourPointPlane

def FourPointAffinePlane : AffinePlane Nat :=
  {
    pl := FourPointPlane
    isAffine := by simp+decide
  }

def NinePointPlane : PointsAndLines Nat :=
   {
     Points := [1, 2, 3, 4, 5, 6, 7, 8, 9]
     Lines := [ [1,2,3], [4,5,6], [7,8,9], [1,4,7], [2,5,8], [3,6,9],
                [1,5,9], [2,6,7], [3,4,8], [1,6,8], [2,4,9], [3,5,7] ]
     h := by simp+decide
   }

#eval check_affine_plane NinePointPlane

def NinePointAffinePlane : AffinePlane Nat :=
  {
    pl := NinePointPlane
    isAffine := by simp+decide
  }

def SixteenPointPlane : PointsAndLines Nat :=
  {
    Points := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
    Lines := [ [1,2,3,4], [1,5,9,14], [4,5,10,13], [2,6,10,14], [2,7,12,13],
               [3,8,10,16], [3,5,12,15], [5,6,7,8], [4,7,9,16], [4,8,12,14],
               [1,6,12,16], [1,7,10,15], [3,6,9,13], [2,8,9,15], [9,10,11,12],
               [3,7,11,14], [4,6,11,15], [13,14,15,16], [2,5,11,16], [1,8,11,13] ]
    h := by simp+decide
  }

#eval check_affine_plane SixteenPointPlane

set_option maxRecDepth 600

def SixteenPointAffinePlane : AffinePlane Nat :=
  {
    pl := SixteenPointPlane
    isAffine := by simp+decide
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
    h := by simp+decide
  }

#eval check_affine_plane TwentyFivePointPlane

def TwentyFivePointAffinePlane : AffinePlane Nat :=
  {
    pl := TwentyFivePointPlane
    isAffine := by simp+decide
  }

/- PROJECTIVE PLANE EXAMPLES -/

/- Fano Plane -/
