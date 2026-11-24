import PEqualNP.Defs.LratEncoding

open PEqualNP.Defs.LratEncoding

def edgeMasks : List Nat := [129,257,1025,130,514,8194,260,4100,8196,136,2056,4104,1040,2064,8208,544,1056,4128,320,576,2112]
def hasEdge (r : Nat) : Bool := edgeMasks.any fun e => r &&& e == e
def neg (r : Nat) : Bool := !hasEdge r || r == 129
def maximalNeg (r : Nat) : Bool := neg r && (List.range 14).all fun i =>
  r.testBit i || !neg (r ||| 2^i)

def main : IO Unit := do
  let rows := edgeMasks.tail ++ (List.range (2^14)).filter maximalNeg
  unless rows.length == 58 do throw (IO.userError "expected 58 boundary rows")
  let clauses := enc2 14 24 (fun r => edgeMasks.tail.contains r) rows
  let top := clauses.foldl (fun m c => c.foldl (fun n l => max n (l/2)) m) 0
  IO.FS.withFile "heawood24.cnf" .write fun f => do
    f.putStrLn s!"p cnf {top} {clauses.length}"
    for c in clauses do
      f.putStrLn (String.intercalate " " (c.map fun l => (if l % 2 == 0 then "" else "-") ++ toString (l/2)) ++ " 0")
  IO.println s!"{rows.length} rows, {clauses.length} clauses, highest DIMACS variable {top}"

