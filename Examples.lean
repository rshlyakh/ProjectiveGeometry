import ProjectiveGeometry

/- EXAMPLES -/

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
