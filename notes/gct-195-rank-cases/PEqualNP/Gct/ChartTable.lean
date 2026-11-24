import PEqualNP.Gct.SaturatedMatrixBound
namespace PEqualNP.Gct.FourierTable
def origMode (n : Nat) : Nat := [0,2,3,5,6,7,10][n-17]!
def extRow (i r : Nat) := if i<17 then row i r else if origMode i <6 then c (if r=3 then -1 else 3) else c (if r=3 then 1 else 0)
def extCol (i j : Nat) := if i<17 then col i j else
    let n := origMode i % 6
    if n/3=j/3 then wave (n%3*(j%3)) else c 0
def entry (j i : Nat) := times (extRow i (j/6)) (extCol i (j%6))
def grad (ids : List Nat) : E := times (injectSum extRow ids (List.range 4)) (injectSum extCol ids (List.range 6))

def den : Int := 108
def lut : List E := [(1,0),(0,1),(-1,-1),(0,0),(9,0),(0,9),(-9,-9),(12,0),(-12,-12),(0,12),(4,0),(-4,-4),(0,4),(5,0),(0,5),(-5,-5),(3,0),(-9,0),(36,0),(-36,-36),(0,36)]
def idx : List (List Nat) := [[0, 1, 2, 3, 3, 3, 0, 1, 2, 3, 3, 3, 0, 1, 2, 3, 3, 3, 4, 5, 6, 3, 3, 3], [3, 3, 3, 0, 0, 0, 3, 3, 3, 0, 0, 0, 3, 3, 3, 0, 0, 0, 3, 3, 3, 4, 4, 4], [3, 3, 3, 0, 1, 2, 3, 3, 3, 0, 1, 2, 3, 3, 3, 0, 1, 2, 3, 3, 3, 4, 5, 6], [7, 7, 7, 3, 3, 3, 8, 8, 8, 3, 3, 3, 9, 9, 9, 3, 3, 3, 3, 3, 3, 3, 3, 3], [7, 8, 9, 3, 3, 3, 8, 9, 7, 3, 3, 3, 9, 7, 8, 3, 3, 3, 3, 3, 3, 3, 3, 3], [7, 9, 8, 3, 3, 3, 8, 7, 9, 3, 3, 3, 9, 8, 7, 3, 3, 3, 3, 3, 3, 3, 3, 3], [3, 3, 3, 7, 7, 7, 3, 3, 3, 8, 8, 8, 3, 3, 3, 9, 9, 9, 3, 3, 3, 3, 3, 3], [3, 3, 3, 7, 8, 9, 3, 3, 3, 8, 9, 7, 3, 3, 3, 9, 7, 8, 3, 3, 3, 3, 3, 3], [3, 3, 3, 7, 9, 8, 3, 3, 3, 8, 7, 9, 3, 3, 3, 9, 8, 7, 3, 3, 3, 3, 3, 3], [7, 7, 7, 3, 3, 3, 9, 9, 9, 3, 3, 3, 8, 8, 8, 3, 3, 3, 3, 3, 3, 3, 3, 3], [7, 8, 9, 3, 3, 3, 9, 7, 8, 3, 3, 3, 8, 9, 7, 3, 3, 3, 3, 3, 3, 3, 3, 3], [7, 9, 8, 3, 3, 3, 9, 8, 7, 3, 3, 3, 8, 7, 9, 3, 3, 3, 3, 3, 3, 3, 3, 3], [3, 3, 3, 7, 7, 7, 3, 3, 3, 9, 9, 9, 3, 3, 3, 8, 8, 8, 3, 3, 3, 3, 3, 3], [3, 3, 3, 7, 8, 9, 3, 3, 3, 9, 7, 8, 3, 3, 3, 8, 9, 7, 3, 3, 3, 3, 3, 3], [3, 3, 3, 7, 9, 8, 3, 3, 3, 9, 8, 7, 3, 3, 3, 8, 7, 9, 3, 3, 3, 3, 3, 3], [10, 11, 12, 3, 3, 3, 10, 11, 12, 3, 3, 3, 10, 11, 12, 3, 3, 3, 3, 3, 3, 3, 3, 3], [3, 3, 3, 10, 11, 12, 3, 3, 3, 10, 11, 12, 3, 3, 3, 10, 11, 12, 3, 3, 3, 3, 3, 3], [10, 10, 10, 0, 0, 0, 10, 10, 10, 0, 0, 0, 10, 10, 10, 0, 0, 0, 3, 3, 3, 4, 4, 4], [13, 14, 15, 3, 3, 3, 13, 14, 15, 3, 3, 3, 13, 14, 15, 3, 3, 3, 4, 5, 6, 3, 3, 3], [3, 3, 3, 16, 16, 16, 3, 3, 3, 16, 16, 16, 3, 3, 3, 16, 16, 16, 3, 3, 3, 17, 17, 17], [3, 3, 3, 13, 14, 15, 3, 3, 3, 13, 14, 15, 3, 3, 3, 13, 14, 15, 3, 3, 3, 4, 5, 6], [10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 18, 18, 18, 18, 18, 18], [10, 11, 12, 3, 3, 3, 10, 11, 12, 3, 3, 3, 10, 11, 12, 3, 3, 3, 18, 19, 20, 3, 3, 3], [3, 3, 3, 10, 11, 12, 3, 3, 3, 10, 11, 12, 3, 3, 3, 10, 11, 12, 3, 3, 3, 18, 19, 20]]
def invEntry (i j : Nat) : E := lut[(idx[i]!)[j]!]!
def entrySum (r j : Nat) := ((List.range 24).map (fun i => times (entry r i) (invEntry i j))).foldl plus (c 0)
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem inverseRow0 : ((List.range 24).all (fun j => entrySum 0 j == c (if 0=j then den else 0)))=true := by decide
theorem inverseRow1 : ((List.range 24).all (fun j => entrySum 1 j == c (if 1=j then den else 0)))=true := by decide
theorem inverseRow2 : ((List.range 24).all (fun j => entrySum 2 j == c (if 2=j then den else 0)))=true := by decide
theorem inverseRow3 : ((List.range 24).all (fun j => entrySum 3 j == c (if 3=j then den else 0)))=true := by decide
theorem inverseRow4 : ((List.range 24).all (fun j => entrySum 4 j == c (if 4=j then den else 0)))=true := by decide
theorem inverseRow5 : ((List.range 24).all (fun j => entrySum 5 j == c (if 5=j then den else 0)))=true := by decide
theorem inverseRow6 : ((List.range 24).all (fun j => entrySum 6 j == c (if 6=j then den else 0)))=true := by decide
theorem inverseRow7 : ((List.range 24).all (fun j => entrySum 7 j == c (if 7=j then den else 0)))=true := by decide
theorem inverseRow8 : ((List.range 24).all (fun j => entrySum 8 j == c (if 8=j then den else 0)))=true := by decide
theorem inverseRow9 : ((List.range 24).all (fun j => entrySum 9 j == c (if 9=j then den else 0)))=true := by decide
theorem inverseRow10 : ((List.range 24).all (fun j => entrySum 10 j == c (if 10=j then den else 0)))=true := by decide
theorem inverseRow11 : ((List.range 24).all (fun j => entrySum 11 j == c (if 11=j then den else 0)))=true := by decide
theorem inverseRow12 : ((List.range 24).all (fun j => entrySum 12 j == c (if 12=j then den else 0)))=true := by decide
theorem inverseRow13 : ((List.range 24).all (fun j => entrySum 13 j == c (if 13=j then den else 0)))=true := by decide
theorem inverseRow14 : ((List.range 24).all (fun j => entrySum 14 j == c (if 14=j then den else 0)))=true := by decide
theorem inverseRow15 : ((List.range 24).all (fun j => entrySum 15 j == c (if 15=j then den else 0)))=true := by decide
theorem inverseRow16 : ((List.range 24).all (fun j => entrySum 16 j == c (if 16=j then den else 0)))=true := by decide
theorem inverseRow17 : ((List.range 24).all (fun j => entrySum 17 j == c (if 17=j then den else 0)))=true := by decide
theorem inverseRow18 : ((List.range 24).all (fun j => entrySum 18 j == c (if 18=j then den else 0)))=true := by decide
theorem inverseRow19 : ((List.range 24).all (fun j => entrySum 19 j == c (if 19=j then den else 0)))=true := by decide
theorem inverseRow20 : ((List.range 24).all (fun j => entrySum 20 j == c (if 20=j then den else 0)))=true := by decide
theorem inverseRow21 : ((List.range 24).all (fun j => entrySum 21 j == c (if 21=j then den else 0)))=true := by decide
theorem inverseRow22 : ((List.range 24).all (fun j => entrySum 22 j == c (if 22=j then den else 0)))=true := by decide
theorem inverseRow23 : ((List.range 24).all (fun j => entrySum 23 j == c (if 23=j then den else 0)))=true := by decide
def gradRow0 (i : Nat) : Int := if i=17 then 24 else if i=19 then 24 else if i=21 then 3 else 0
theorem gradCert0 : ((List.range 24).all (fun i => grad (i::[]) == c (gradRow0 i)))=true := by decide
def gradRow1 (i : Nat) : Int := if i=20 then -108 else 0
theorem gradCert1 : ((List.range 24).all (fun i => grad (i::[16]) == c (gradRow1 i)))=true := by decide
def gradRow2 (i : Nat) : Int := if i=23 then 324 else 0
theorem gradCert2 : ((List.range 24).all (fun i => grad (i::[16, 16]) == c (gradRow2 i)))=true := by decide
def gradRow3 (i : Nat) : Int := if i=17 then -11664 else if i=21 then 2916 else 0
theorem gradCert3 : ((List.range 24).all (fun i => grad (i::[16, 16, 16]) == c (gradRow3 i)))=true := by decide
def gradRow4 (i : Nat) : Int := if i=18 then -108 else 0
theorem gradCert4 : ((List.range 24).all (fun i => grad (i::[15]) == c (gradRow4 i)))=true := by decide
def gradRow5 (i : Nat) : Int := if i=22 then 324 else 0
theorem gradCert5 : ((List.range 24).all (fun i => grad (i::[15, 15]) == c (gradRow5 i)))=true := by decide
def gradRow6 (i : Nat) : Int := if i=19 then -11664 else 0
theorem gradCert6 : ((List.range 24).all (fun i => grad (i::[15, 15, 15]) == c (gradRow6 i)))=true := by decide
end PEqualNP.Gct.FourierTable
