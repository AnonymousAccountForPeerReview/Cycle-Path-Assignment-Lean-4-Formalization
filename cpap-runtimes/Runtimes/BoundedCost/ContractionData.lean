module

public import Runtimes.BoundedCost.Contraction
import Mathlib.Tactic

/-! # Finite input tables for contracted occurrence cut graphs -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

structure TerminalRow where
  positiveForced : Bool
  negativeForced : Bool
  reference : Bool
  deriving Inhabited

def terminalLabel (x : ℕ) (row : TerminalRow) : ℕ :=
  if row.positiveForced then
    if row.negativeForced then 0 else if row.reference then 0 else 1
  else if row.negativeForced then if row.reference then 1 else 0
  else x + 2

def terminalConflict (row : TerminalRow) : Bool := row.positiveForced && row.negativeForced

def terminalConflictPrefix (rows : List TerminalRow) (count : ℕ) : Bool :=
  (List.range count).any fun x => terminalConflict (rows.getD x default)

def terminalLabels (rows : List TerminalRow) : List ℕ :=
  List.ofFn fun i : Fin (2 * rows.length) =>
    terminalLabel (i.val / 2) (rows.getD (i.val / 2) default)

structure ContractionRow where
  first : ℕ
  second : ℕ
  active : Bool
  firstReference : Bool
  secondReference : Bool
  deriving Inhabited

def retainContractedArc (tail head : ℕ) : Option (ℕ × ℕ) :=
  if head = 0 ∨ tail = 1 then none else some (tail, head)

def contractionRowArc (labels : ℕ → ℕ) (row : ContractionRow) : Option (ℕ × ℕ) :=
  if row.active then
    if row.firstReference then
      if row.secondReference then none else retainContractedArc (labels row.second) (labels row.first)
    else if row.secondReference then retainContractedArc (labels row.first) (labels row.second)
    else none
  else none

def contractionArcsPrefix (labels : ℕ → ℕ) (rows : List ContractionRow) (count : ℕ) :
    List (ℕ × ℕ) :=
  (List.range count).filterMap fun i => contractionRowArc labels (rows.getD i default)

def contractionArcCodes (arcs : List (ℕ × ℕ)) : List ℕ :=
  arcs.flatMap fun e => [e.1, e.2]

def contractionEdgeInput (nodes : ℕ) (arcs : List (ℕ × ℕ)) : List ℕ :=
  [nodes + 2, arcs.length, 0, 1, nodes] ++ contractionArcCodes arcs

def TerminalLabelValue (rows : List TerminalRow) (code : ℕ) : ℕ :=
  terminalLabel (code / 2) (rows.getD (code / 2) default)

theorem terminalLabels_length (rows : List TerminalRow) : (terminalLabels rows).length = 2 * rows.length := by
  simp [terminalLabels]

theorem terminalLabels_get (rows : List TerminalRow) (code : ℕ) (hc : code < 2 * rows.length) :
    (terminalLabels rows).getD code 0 = TerminalLabelValue rows code := by
  simp [terminalLabels, TerminalLabelValue, List.getD_eq_getElem?_getD, hc]

theorem terminalConflictPrefix_succ (rows : List TerminalRow) (x : ℕ) :
    terminalConflictPrefix rows (x + 1) =
      (terminalConflictPrefix rows x || terminalConflict (rows.getD x default)) := by
  simp [terminalConflictPrefix, List.range_succ]

end STACS2027.Runtimes.BoundedCost
