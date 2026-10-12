module

public import NPHardness.TaggedGraph
public import Complexity.SATBounds

/-! A concrete graph-and-budget format, reusing the foundation's code `encode`
for lists of literal lists. An empty record increments the budget; a positive
two-literal record supplies an edge. All other records are rejected. This is an
encoding of the target graph, not an encoding of the source formula with a
reduction hidden in the predicate. Like the registered languages, `CPAP k` is
the image of `encode`; words coding no record list are not in it. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-- The record of edge `e`. -/
def graphRecord (e : Edge) : Clause := [⟨e.1,true⟩,⟨e.2,true⟩]

/-- A record of a CPAP instance: empty (one unit of budget), or two positive literals (an edge). -/
def validGraphRecord (c : Clause) : Prop :=
  c = [] ∨ c.length = 2 ∧ c.all Literal.positive = true

/-- The edge between the variables of a record of two positive literals. -/
def recordEdge (c : Clause) : Option Edge :=
  if c.length == 2 && c.all Literal.positive then
    some (edge ((c[0]?).getD (Literal.mk 0 false)).var ((c[1]?).getD (Literal.mk 0 false)).var)
  else none

/-- The graph written by the records `f`: their edges, in order. -/
def instructionGraph (f : CNF) : Graph := f.filterMap recordEdge
/-- The budget written by the records `f`: the number of empty records. -/
def instructionBudget (f : CNF) : Nat := f.countP List.isEmpty
/-- Every record of `f` is an edge record or a budget record. -/
def ValidGraphInstructions (f : CNF) : Prop := ∀ c ∈ f, validGraphRecord c

def GraphOutput (f : CNF) (g : Graph) (budget : Nat) : Prop :=
  ValidGraphInstructions f ∧ instructionGraph f = g ∧ instructionBudget f = budget

/-- CPAP for fixed `k`: the words `encode f` whose records `f` are valid and write a graph with an
assignment of cost at most the written budget. -/
def CPAP (k : Nat) (input : Complexity.SAT.Word) : Prop :=
  ∃ f, encode f = input ∧ ValidGraphInstructions f ∧
    HasAssignment (instructionGraph f) k (instructionBudget f)

theorem cpapLanguage_encode (k : Nat) (f : CNF) :
    CPAP k (encode f) ↔ ValidGraphInstructions f ∧
      HasAssignment (instructionGraph f) k (instructionBudget f) := by
  constructor
  · rintro ⟨g, hg, h⟩
    obtain rfl := encode_injective _ _ hg
    exact h
  · exact fun h => ⟨f, rfl, h⟩

/-- Malformed words are rejected: membership is decided on the decoded records. -/
theorem cpap_iff_decode (k : Nat) (input : Complexity.SAT.Word) :
    CPAP k input ↔ ∃ f, decode input = some f ∧ ValidGraphInstructions f ∧
      HasAssignment (instructionGraph f) k (instructionBudget f) := by
  simp only [CPAP, decode_eq_some_iff]
  constructor <;> rintro ⟨f, h, r⟩ <;> exact ⟨f, h.symm, r⟩

theorem GraphOutput.encode_iff {f : CNF} {g : Graph} {budget : Nat}
    (h : GraphOutput f g budget) (k : Nat) :
    CPAP k (encode f) ↔ HasAssignment g k budget := by
  rw [cpapLanguage_encode,h.2.1,h.2.2]
  exact and_iff_right h.1

theorem GraphOutput.nil : GraphOutput [] [] 0 := by
  simp [GraphOutput,ValidGraphInstructions,instructionGraph,instructionBudget]

theorem GraphOutput.tick : GraphOutput [[]] [] 1 := by
  simp [GraphOutput,ValidGraphInstructions,validGraphRecord,instructionGraph,recordEdge,instructionBudget]

theorem GraphOutput.edge (u v : Nat) : GraphOutput [graphRecord (edge u v)] [edge u v] 0 := by
  simp [GraphOutput,ValidGraphInstructions,validGraphRecord,instructionGraph,recordEdge,
    instructionBudget,graphRecord,edge_normalized]

theorem GraphOutput.append {f h : CNF} {g j : Graph} {a b : Nat}
    (hf : GraphOutput f g a) (hh : GraphOutput h j b) : GraphOutput (f ++ h) (g ++ j) (a+b) := by
  refine ⟨?_,?_,?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hf.1 c hc
    · exact hh.1 c hc
  · change instructionGraph (f ++ h) = _
    simp only [instructionGraph,List.filterMap_append]
    change instructionGraph f ++ instructionGraph h = _
    rw [hf.2.1,hh.2.1]
  · change instructionBudget (f ++ h) = _
    simp only [instructionBudget,List.countP_append]
    change instructionBudget f + instructionBudget h = _
    rw [hf.2.2,hh.2.2]

theorem GraphOutput.flatMap {α : Type} (xs : List α) (F : α → CNF) (G : α → Graph) (B : α → Nat)
    (h : ∀ x ∈ xs, GraphOutput (F x) (G x) (B x)) :
    GraphOutput (xs.flatMap F) (xs.flatMap G) ((xs.map B).sum) := by
  induction xs with
  | nil => exact GraphOutput.nil
  | cons x xs ih =>
    exact (h x (by simp)).append (ih (fun y hy => h y (by simp [hy])))

def graphRecords (g : Graph) : CNF := g.map graphRecord

theorem graphRecords_output (g : Graph) (hn : ∀ e ∈ g, edge e.1 e.2 = e) : GraphOutput (graphRecords g) g 0 := by
  induction g with
  | nil => exact GraphOutput.nil
  | cons e g ih =>
    have hh : GraphOutput [graphRecord e] [e] 0 := hn e (by simp) ▸ GraphOutput.edge e.1 e.2
    exact hh.append (ih (fun d hd => hn d (by simp [hd])))

def clauseGraphRecords (k n j r : Nat) (c : Clause) : CNF :=
  [] :: graphRecords (placedClauseGraph k n j (c.map (fun l => PlacedLiteral.mk l r)))

theorem clauseGraphRecords_output (k n j r : Nat) (c : Clause) :
    GraphOutput (clauseGraphRecords k n j r c)
      (placedClauseGraph k n j (c.map (fun l => PlacedLiteral.mk l r))) 1 := by
  exact GraphOutput.tick.append (graphRecords_output _ (mapGraph_normalized _ _))

end STACS2027
