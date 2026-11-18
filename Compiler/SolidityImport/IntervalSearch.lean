import Compiler.SolidityImport.ExprHelpers
import Compiler.CompilationModel.ValidationHelpers

/-! Bounded inclusive interval searches with source-derived exits. -/

open Lean
namespace Compiler.CompilationModel.SolidityImport.IntervalSearch

private def child (node : Json) (key : String) : Json := (field? node key).getD Json.null

private def kind (node : Json) : String := (optStr node "nodeType").getD ""

private partial def unparen (node : Json) : Json :=
  if kind node == "TupleExpression" then
    match (child node "components").getArr? with
    | .ok #[item] => unparen item
    | _ => node
  else node

private def ident? (node : Json) : Option Nat := do
  let node := unparen node
  guard (kind node == "Identifier")
  (child node "referencedDeclaration").getNat?.toOption

private def binary (node : Json) (op : String) : Bool :=
  kind node == "BinaryOperation" && optStr node "operator" == some op

private def number (node : Json) (n : Nat) : Bool :=
  kind node == "Literal" && optStr (child node "typeDescriptions") "typeString" ==
    some s!"int_const {n}"

private def statements (node : Json) : Array Json :=
  if kind node == "Block" then (child node "statements").getArr?.toOption.getD #[]
  else #[node]

private def block (nodes : Array Json) : Json :=
  Json.mkObj [("nodeType", .str "Block"), ("statements", .arr nodes)]

private def assignment? (node : Json) : Option (Json × Json) := do
  let expr := child node "expression"
  guard (kind node == "ExpressionStatement" && kind expr == "Assignment" &&
    optStr expr "operator" == some "=")
  return (child expr "leftHandSide", unparen (child expr "rightHandSide"))

private structure Bounds where
  low : Nat
  high : Nat
  mid : Nat
  bits : Nat

private def shift? (node : Json) (mid : Nat) (op : String) : Option Nat := do
  let (lhs, rhs) ← assignment? node
  guard (binary rhs op && ident? (child rhs "leftExpression") == some mid &&
    number (child rhs "rightExpression") 1)
  ident? lhs

private def endpoints? (endBranch : Json) (mid : Nat) : Option (Nat × Nat) := do
  guard (kind endBranch == "IfStatement")
  let #[yes] := statements (child endBranch "trueBody") | none
  let #[no] := statements (child endBranch "falseBody") | none
  (do return (← shift? yes mid "+", ← shift? no mid "-")) <|>
    (do return (← shift? no mid "+", ← shift? yes mid "-"))

private def bounds? (body : Array Json) : Option Bounds := do
  let (midpoint, rhs) ← assignment? (← body[0]?)
  let mid ← ident? midpoint
  let (low, high) ← endpoints? (← body.back?) mid
  guard (low != high && low != mid && high != mid)
  guard (binary rhs "/" && number (child rhs "rightExpression") 2)
  let sum := unparen (child rhs "leftExpression")
  guard (binary sum "+")
  let lhs := child sum "leftExpression"
  let rhs := child sum "rightExpression"
  let ids := (ident? lhs, ident? rhs)
  guard (ids == (some low, some high) || ids == (some high, some low))
  let typeOf (node : Json) := optStr (child node "typeDescriptions") "typeString"
  let some ty := typeOf midpoint | none
  guard (ty.startsWith "uint" && typeOf lhs == some ty && typeOf rhs == some ty)
  let bits ← bitsOf ty
  guard (bits > 0 && bits ≤ 256)
  return { low, high, mid, bits }

/-- Route only literal-true while loops with a floor midpoint and both unit bound updates. -/
def candidate (node : Json) : Bool :=
  let cond := child node "condition"
  kind node == "WhileStatement" && kind cond == "Literal" &&
    optStr cond "kind" == some "bool" && optStr cond "value" == some "true" &&
    (bounds? (statements (child node "body"))).isSome

private def compareIds (node : Json) (op : String) (a b : Nat) : Bool :=
  binary node op && ident? (child node "leftExpression") == some a &&
    ident? (child node "rightExpression") == some b

private def endpointExit (node : Json) (b : Bounds) : Bool :=
  let cond := unparen (child node "condition")
  let lhs := unparen (child cond "leftExpression")
  let rhs := unparen (child cond "rightExpression")
  let atLow (n : Json) := compareIds n "<=" b.mid b.low || compareIds n ">=" b.low b.mid
  let atHigh (n : Json) := compareIds n ">=" b.mid b.high || compareIds n "<=" b.high b.mid
  kind node == "IfStatement" && (child node "falseBody").isNull &&
    (statements (child node "trueBody")).map kind == #["Break"] &&
    binary cond "||" && ((atLow lhs && atHigh rhs) || (atLow rhs && atHigh lhs))

private def writesBounds (node : Json) (b : Bounds) : Bool :=
  (bodyAssignedIds node).any fun id => id == b.low || id == b.high || id == b.mid

/-- Lower a straight-line prefix before the next control transfer. Continue and break
both skip the entire suffix. The continue arm retains its source bound assignment. -/
private partial def lowerTail (nodes : List Json) (b : Bounds) (doneVar : String)
    (lowerExpr : Json → M Val) (lowerBody : Json → M (Array Stmt)) : M (Array Stmt) := do
  let node :: rest := nodes | return #[]
  if rest.isEmpty then
    if writesBounds (child node "condition") b then
      failAt node "the interval update condition may not change a search bound or midpoint"
    return ← lowerBody (block #[node])
  if kind node == "IfStatement" && (child node "falseBody").isNull then
    let arm := statements (child node "trueBody")
    let test := child node "condition"
    if writesBounds test b then failAt test "interval search guards may not change the bounds"
    let val ← lowerExpr test
    let take ← match arm.map kind with
      | #["Break"] => pure #[Stmt.assignVar doneVar (.literal 1)]
      | #["ExpressionStatement", "Continue"] => do
        unless shift? arm[0]! b.mid "+" == some b.low ||
            shift? arm[0]! b.mid "-" == some b.high do
          failAt node "continue must first exclude the midpoint from the search interval"
        lowerBody (block #[arm[0]!])
      | _ => failAt node "an interval search guard must break or update a bound and continue"
    let fallthrough ← lowerTail rest b doneVar lowerExpr lowerBody
    return val.pre.push (.ite val.expr take.toList fallthrough.toList)
  unless ["ExpressionStatement", "VariableDeclarationStatement", "EmitStatement",
      "RevertStatement"].contains (kind node) && !writesBounds node b do
    failAt node "unsupported control or intervening bound write in an interval search"
  let pre ← lowerBody (block #[node])
  return pre ++ (← lowerTail rest b doneVar lowerExpr lowerBody)

/-- Backward liveness across the iteration. Branches both start with the enclosing suffix.
Scalar assignments kill their previous value only after evaluating the right-hand side. -/
private partial def liveInputs (body : List Stmt) (after : Std.HashSet String) :
    Std.HashSet String := Id.run do
  let mut live := after
  for stmt in body.reverse do
    match stmt with
    | .letVar name rhs | .assignVar name rhs =>
      live := (collectExprNames rhs).foldl (·.insert ·) (live.erase name)
    | .ite cond yes no =>
      live := (collectExprNames cond).foldl (·.insert ·)
        ((liveInputs yes live).union (liveInputs no live))
    | _ => live := (collectStmtNames stmt).foldl (·.insert ·) live
  return live

/-- Intersect reads with actual allocations in the specialized outer frame. Generated
iteration temporaries, field names and other metadata are outside that lexical scope. -/
def entryInputs (names : List String) (body : List Stmt) : List String :=
  let live := liveInputs body {}
  names.filter live.contains

/-- Names and source-ordered model statements shared by both interval backends. -/
structure Iteration where
  bits : Nat
  lowName : String
  highName : String
  midName : String
  body : List Stmt

/-- Lower exactly one iteration in its current call frame. This routine imposes no fuel
and does not grant default admission to a loop with data-dependent progress. -/
def lowerIteration (node : Json) (doneVar : String) (lowerExpr : Json → M Val)
    (lowerBody : Json → M (Array Stmt)) : M Iteration := do
  let body := statements (child node "body")
  let some bounds := bounds? body | failAt node "unsupported interval search"
  let locals := (← get).writableLocals
  let some lowName := locals.find? bounds.low | failAt node "missing writable lower bound"
  let some highName := locals.find? bounds.high | failAt node "missing writable upper bound"
  let some midName := locals.find? bounds.mid | failAt node "missing writable midpoint"
  let first ← lowerBody (block #[body[0]!])
  let tail ← lowerTail body.toList.tail! bounds doneVar lowerExpr lowerBody
  return { bits := bounds.bits, lowName, highName, midName, body := (first ++ tail).toList }

/-- A strict-interior midpoint gives a nonwrapping unit update and at most half as many
remaining indices. An overflowing sum gives a midpoint below the low endpoint and reaches
the source exit. Consequently word width plus one includes the final test. -/
def lower (node : Json) (lowerExpr : Json → M Val) (lowerBody : Json → M (Array Stmt)) :
    M (Array Stmt) := do
  let body := statements (child node "body")
  let some bounds := bounds? body | failAt node "unsupported interval search"
  let some guardNode := body[1]? | failAt node "missing interval search exit"
  unless endpointExit guardNode bounds do
    failAt node ("interval search needs progress evidence: each continuing step must retain " ++
      "a nonempty interval and exclude the midpoint without wraparound until a source exit")
  let doneVar ← fresh
  let counter ← fresh
  let iteration ← lowerIteration node doneVar lowerExpr lowerBody
  return #[.letVar doneVar (.literal 0),
    .forEach counter (.literal (iteration.bits + 1))
      [.ite (.eq (.localVar doneVar) (.literal 0)) iteration.body []]]

end Compiler.CompilationModel.SolidityImport.IntervalSearch
