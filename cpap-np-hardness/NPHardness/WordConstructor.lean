module

public import NPHardness.RandomAccessPlacement
public import NPHardness.GlobalSize
public import NPHardness.OrientedGluing

/-!
An explicit small-step record/pointer RAM constructor. Input clause lists and
the three fixed-k gadget edge tables are read-only linked records. A transition
performs a bounded number of record reads, cell reads/writes, word operations,
and allocations. Output edges are consed, so output order is reversed. Counters
are random-access signed-literal cells initially zero, the usual zero-initial
RAM convention. The supplied dimension `n` is an input header, not computed by
an uncharged call to `variableBound`.

This is a specialized word-level machine, not a compiler to a primitive RAM
instruction set. It builds the raw graph; preprocessing and selecting planar
attachment orientations are outside the machine. The supplied `flips` is the
contents of a read-only random-access bit table; it is not an arbitrary Lean
function whose evaluation is silently charged one unit. The theorem below counts
actual transitions, not just the length of a graph-valued Lean expression.
-/

@[expose] public section
namespace STACS2027.WordConstructor
open Complexity.SAT

inductive Phase where
  | variables (next remaining : Nat)
  | variableEdges (v remaining : Nat) (edges : Graph)
  | clauses (j : Nat) (remaining : CNF)
  | literals (j : Nat) (tail : Clause) (remaining : CNF) (reversed : List PlacedLiteral)
  | clauseEdges (j : Nat) (remaining : CNF) (placed : List PlacedLiteral) (edges : Graph)
  | done
  | rejected

structure Config where
  phase : Phase
  memory : CounterMemory
  output : Graph

/-- A bounded sequence of record reads: no unbounded reversal in a step. -/
def ready : List PlacedLiteral → Option (List PlacedLiteral)
  | [] => some []
  | [a] => some [a]
  | [b,a] => some [a,b]
  | [c,b,a] => some [a,b,c]
  | _ => none

theorem ready_reverse (c : List PlacedLiteral) (h : c.length ≤ 3) :
    ready c.reverse = some c := by
  cases c with
  | nil => rfl
  | cons a c =>
    cases c with
    | nil => rfl
    | cons b c =>
      cases c with
      | nil => rfl
      | cons d c =>
        cases c with
        | nil => rfl
        | cons e c => simp only [List.length_cons] at h; omega

def step (flips : EndpointChoices) (k n : Nat) (input : CNF) (s : Config) : Config :=
  match s.phase with
  | .variables _ 0 => { s with phase := .clauses 0 input }
  | .variables v (r+1) => { s with phase := .variableEdges v r (variableGraph k) }
  | .variableEdges v r [] => { s with phase := .variables (v+1) r }
  | .variableEdges v r (e::es) =>
    { s with phase := .variableEdges v r es, output := mapEdge (blockVertex (gadgetWidth k) v) e :: s.output }
  | .clauses _ [] => { s with phase := .done }
  | .clauses j (c::f) => { s with phase := .literals j c f [] }
  | .literals j (l::ls) f rev =>
    { s with phase := .literals j ls f (⟨l,s.memory l⟩::rev), memory := incrementCounter s.memory l }
  | .literals j [] f rev =>
    match ready rev with
    | none => { s with phase := .rejected }
    | some c => { s with phase := .clauseEdges j f c (clauseGraph k c) }
  | .clauseEdges j f _ [] => { s with phase := .clauses (j+1) f }
  | .clauseEdges j f c (e::es) =>
    { s with phase := .clauseEdges j f c es, output := mapEdge (orientedClauseVertex flips (gadgetWidth k) n j c) e :: s.output }
  | .done => s
  | .rejected => s

inductive Executes (flips : EndpointChoices) (k n : Nat) (input : CNF) : Nat → Config → Config → Prop where
  | refl (s) : Executes flips k n input 0 s s
  | next {t s u} : Executes flips k n input t (step flips k n input s) u → Executes flips k n input (t+1) s u

theorem Executes.trans {flips : EndpointChoices} {k n : Nat} {input : CNF} {t u : Nat} {s q r : Config}
    (h : Executes flips k n input t s q) (g : Executes flips k n input u q r) :
    Executes flips k n input (t+u) s r := by
  induction h with
  | refl => simpa using g
  | next h ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Executes.next (ih g)

theorem run_variable_edges (flips : EndpointChoices) (k n : Nat) (input : CNF) (v r : Nat)
    (es : Graph) (m : CounterMemory) (out : Graph) :
    Executes flips k n input (es.length+1)
      ⟨.variableEdges v r es,m,out⟩
      ⟨.variables (v+1) r,m,(mapGraph (blockVertex (gadgetWidth k) v) es).reverse ++ out⟩ := by
  induction es generalizing out with
  | nil => exact Executes.next (Executes.refl _)
  | cons e es ih =>
    apply Executes.next
    simpa [step, mapGraph, List.reverse_cons, List.append_assoc] using
      ih (mapEdge (blockVertex (gadgetWidth k) v) e :: out)

def variableOutput (k v : Nat) : Nat → Graph
  | 0 => []
  | r+1 => placedVariableGraph k v ++ variableOutput k (v+1) r

theorem variableOutput_range (k v r : Nat) :
    variableOutput k v r = (List.range' v r).flatMap (placedVariableGraph k) := by
  induction r generalizing v with
  | zero => rfl
  | succ r ih => simp [variableOutput, List.range'_succ, ih]

theorem run_variables (flips : EndpointChoices) (k n : Nat) (input : CNF) (v r : Nat)
    (m : CounterMemory) (out : Graph) :
    Executes flips k n input (r*((variableGraph k).length+2)+1)
      ⟨.variables v r,m,out⟩
      ⟨.clauses 0 input,m,(variableOutput k v r).reverse ++ out⟩ := by
  induction r generalizing v out with
  | zero => simpa [step, variableOutput] using (Executes.next (s := ⟨.variables v 0,m,out⟩) (Executes.refl (step flips k n input ⟨.variables v 0,m,out⟩)))
  | succ r ih =>
    have h := (run_variable_edges flips k n input v r (variableGraph k) m out).trans
      (ih (v+1) ((placedVariableGraph k v).reverse ++ out))
    have h' := Executes.next (s := ⟨.variables v (r+1),m,out⟩) h
    have ht : ((variableGraph k).length+1+(r*((variableGraph k).length+2)+1))+1 =
        (r+1)*((variableGraph k).length+2)+1 := by rw [Nat.add_mul]; omega
    rw [ht] at h'
    simpa [step, variableOutput, placedVariableGraph, List.reverse_append, List.append_assoc] using h'

theorem run_literals (flips : EndpointChoices) (k n : Nat) (input : CNF) (j : Nat) (ls : Clause)
    (f : CNF) (rev : List PlacedLiteral) (m : CounterMemory) (out : Graph) :
    Executes flips k n input ls.length
      ⟨.literals j ls f rev,m,out⟩
      ⟨.literals j [] f ((allocateLiterals m ls).1.reverse ++ rev),
        (allocateLiterals m ls).2,out⟩ := by
  induction ls generalizing rev m with
  | nil => exact Executes.refl _
  | cons l ls ih =>
    apply Executes.next
    simpa [step, allocateLiterals, List.reverse_cons, List.append_assoc] using
      ih (⟨l,m l⟩::rev) (incrementCounter m l)

theorem run_clause_edges (flips : EndpointChoices) (k n : Nat) (input : CNF) (j : Nat)
    (f : CNF) (c : List PlacedLiteral) (es : Graph) (m : CounterMemory) (out : Graph) :
    Executes flips k n input (es.length+1)
      ⟨.clauseEdges j f c es,m,out⟩
      ⟨.clauses (j+1) f,m,(mapGraph (orientedClauseVertex flips (gadgetWidth k) n j c) es).reverse ++ out⟩ := by
  induction es generalizing out with
  | nil => exact Executes.next (Executes.refl _)
  | cons e es ih =>
    apply Executes.next
    simpa [step, mapGraph, List.reverse_cons, List.append_assoc] using
      ih (mapEdge (orientedClauseVertex flips (gadgetWidth k) n j c) e :: out)

def clauseOutput (flips : EndpointChoices) (k n j : Nat) (m : CounterMemory) : CNF → Graph
  | [] => []
  | c::f =>
    let p := allocateLiterals m c
    orientedPlacedClauseGraph flips k n j p.1 ++ clauseOutput flips k n (j+1) p.2 f

def clauseTime (k : Nat) (m : CounterMemory) : CNF → Nat
  | [] => 1
  | c::f =>
    let p := allocateLiterals m c
    c.length + (clauseGraph k p.1).length + 3 + clauseTime k p.2 f

theorem run_clauses (flips : EndpointChoices) (k n : Nat) (input : CNF) (j : Nat) (f : CNF)
    (hf : ∀ c ∈ f, c.length ≤ 3) (m : CounterMemory) (out : Graph) :
    Executes flips k n input (clauseTime k m f)
      ⟨.clauses j f,m,out⟩
      ⟨.done,(allocateFormula m f).2,(clauseOutput flips k n j m f).reverse ++ out⟩ := by
  induction f generalizing j m out with
  | nil => exact Executes.next (Executes.refl _)
  | cons c f ih =>
    have hc : (allocateLiterals m c).1.length ≤ 3 := by
      rw [allocateLiterals_length]
      exact hf c (by simp)
    have hrest := ih (j+1) (fun d hd => hf d (by simp [hd]))
      (allocateLiterals m c).2 ((orientedPlacedClauseGraph flips k n j (allocateLiterals m c).1).reverse ++ out)
    have he := (run_clause_edges flips k n input j f (allocateLiterals m c).1
      (clauseGraph k (allocateLiterals m c).1) (allocateLiterals m c).2 out).trans hrest
    have hready : Executes flips k n input
        ((clauseGraph k (allocateLiterals m c).1).length+1+clauseTime k (allocateLiterals m c).2 f+1)
        ⟨.literals j [] f (allocateLiterals m c).1.reverse,(allocateLiterals m c).2,out⟩
        ⟨.done,(allocateFormula (allocateLiterals m c).2 f).2,
          (clauseOutput flips k n (j+1) (allocateLiterals m c).2 f).reverse ++
            ((orientedPlacedClauseGraph flips k n j (allocateLiterals m c).1).reverse ++ out)⟩ := by
      apply Executes.next
      simpa [step, ready_reverse _ hc, orientedPlacedClauseGraph, Oriented.placedClauseGraph, orientedClauseVertex] using he
    have hs := (run_literals flips k n input j c f [] m out).trans (by simpa using hready)
    have h := Executes.next (s := ⟨.clauses j (c::f),m,out⟩) hs
    have ht : (c.length + ((clauseGraph k (allocateLiterals m c).1).length+1+
        clauseTime k (allocateLiterals m c).2 f+1))+1 = clauseTime k m (c::f) := by
      simp only [clauseTime]
      omega
    rw [ht] at h
    simpa [step, clauseOutput, allocateFormula, List.reverse_append, List.append_assoc] using h

theorem clauseOutput_refines (flips : EndpointChoices) (k n j : Nat) (past : List Literal) (f : CNF) :
    clauseOutput flips k n j (historyMemory past) f =
      ((placeFormula past f).mapIdx (fun i c => orientedPlacedClauseGraph flips k n (j+i) c)).flatten := by
  induction f generalizing j past with
  | nil => rfl
  | cons c f ih =>
    simp [clauseOutput, allocateLiterals_refines, placeFormula, List.mapIdx_cons, ih,
      Nat.add_comm, Nat.add_left_comm]

def initial (n : Nat) : Config := ⟨.variables 0 n,historyMemory [],[]⟩

def transitionCount (k n : Nat) (f : CNF) : Nat :=
  n*((variableGraph k).length+2)+1 + clauseTime k (historyMemory []) f

/-- The returned edge list is exactly the specification in reverse order. -/
theorem executes_graph (flips : EndpointChoices) (k : Nat) (f : CNF) (hf : ∀ c ∈ f, c.length ≤ 3) :
    Executes flips k (variableBound f) f (transitionCount k (variableBound f) f)
      (initial (variableBound f))
      ⟨.done,historyMemory f.flatten,(orientedFormulaGraph flips k f).reverse⟩ := by
  have h := (run_variables flips k (variableBound f) f 0 (variableBound f) (historyMemory []) []).trans
    (run_clauses flips k (variableBound f) f 0 f hf (historyMemory [])
      ((variableOutput k 0 (variableBound f)).reverse ++ []))
  simpa [initial, transitionCount, variableOutput_range, ← List.range_eq_range', clauseOutput_refines,
    allocateFormula_refines, orientedFormulaGraph, Oriented.formulaGraph, orientedPlacedClauseGraph, List.reverse_append] using h

end STACS2027.WordConstructor
