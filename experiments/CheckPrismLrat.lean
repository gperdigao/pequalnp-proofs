import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

open Std.Sat

private def words (line : String) : List String :=
  (line.trimAscii.toString.splitOn " ").filter fun word => !word.isEmpty

private def parseClause (maxVar : Nat) (line : String) : Except String (CNF.Clause Nat) := do
  let literals : List Int ← (words line).mapM fun word => do
    let some literal := word.toInt? | throw s!"Invalid DIMACS literal {word}"
    pure literal
  if literals.getLast? != some 0 then
    throw "DIMACS clause is missing its terminating zero"
  let clause := literals.dropLast
  if clause.any fun lit => lit.natAbs == 0 || lit.natAbs > maxVar then
    throw "DIMACS literal is out of range"
  return clause.foldl (fun acc lit => acc.add (lit.natAbs - 1) (decide (lit > 0))) CNF.Clause.empty

private def parseDimacs (contents : String) : Except String (CNF Nat) := do
  let lines := (contents.splitOn "\n").map (·.trimAscii.toString)
  let header :: rows := lines.filter fun line => !line.isEmpty && !line.startsWith "c"
    | throw "Missing DIMACS header"
  let ["p", "cnf", variables, clauses] := words header
    | throw "Invalid DIMACS header"
  let some maxVar := variables.toNat? | throw "Invalid variable count"
  let some count := clauses.toNat? | throw "Invalid clause count"
  if rows.length != count then throw "DIMACS clause count mismatch"
  let parsed ← rows.mapM (parseClause maxVar)
  return ⟨parsed.toArray⟩

def main (args : List String) : IO UInt32 := do
  let [formulaPath, proofPath] := args
    | throw <| IO.userError "Expected a DIMACS path and an LRAT path"
  let contents ← IO.FS.readFile formulaPath
  let formula ← IO.ofExcept (parseDimacs contents)
  let proof ← Std.Tactic.BVDecide.LRAT.loadLRATProof proofPath
  if Std.Tactic.BVDecide.LRAT.check proof formula then
    IO.println s!"LRAT check passed for {formula.clauses.size} clauses and {proof.size} actions"
    return 0
  IO.eprintln "LRAT check failed"
  return 1
