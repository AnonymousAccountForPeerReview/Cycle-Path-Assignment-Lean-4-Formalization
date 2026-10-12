module

public import NPHardness.WordPipelineHeader
public import NPHardness.LinearPreprocessInit

/-!
A deterministic composition of the charged normalization, initialization,
unit propagation, extraction, padding, dimension scan, and graph-construction
machines. Stage changes only pass pointers and word registers. In particular
they do not evaluate `contents`, `variableBound`, or a formula length.

The original clause count is a supplied input header (`budget`). The next
file proves the end-to-end theorem with `budget = f.length`.
-/

@[expose] public section
namespace STACS2027.WordPipeline
open Complexity.SAT

inductive State where
  | normalize (s : LinearPreprocessNormalize.State)
  | initialize (s : LinearPreprocessInit.State)
  | units (size : Nat) (adj : LinearPreprocessUnits.Incidences) (s : LinearPreprocessUnits.State)
  | extract (mem : LinearPreprocessUnits.Memory) (s : LinearPreprocessExtract.State)
  | padding (count : Nat) (s : LinearPreprocessPadding.State)
  | header (formula : CNF) (s : Header.State)
  | graph (n : Nat) (formula : CNF) (s : WordConstructor.Config)
  | done (output : Graph)

def normalizeState : LinearPreprocessNormalize.State → State
  | .done f => .initialize (.scanFormula 0 f (fun _ => none) (fun _ => []))
  | s => .normalize s

def initializeState : LinearPreprocessInit.State → State
  | .done size mem adj queue => .units size adj (.running mem queue)
  | s => .initialize s

def unitsState (budget size : Nat) (adj : LinearPreprocessUnits.Incidences) :
    LinearPreprocessUnits.State → State
  | .done mem => .extract mem (.scan 0 size [] 0)
  | .rejected => .padding (budget+1) (.scanFormula [] 0 [])
  | s => .units size adj s

def extractState (budget : Nat) (mem : LinearPreprocessUnits.Memory) :
    LinearPreprocessExtract.State → State
  | .done f count => .padding (budget-count) (.scanFormula f 0 [])
  | s => .extract mem s

def paddingState (count : Nat) : LinearPreprocessPadding.State → State
  | .done f => .header f (.formula f 0)
  | s => .padding count s

def headerState (f : CNF) : Header.State → State
  | .done n => .graph n f (WordConstructor.initial n)
  | s => .header f s

def graphState (n : Nat) (f : CNF) (s : WordConstructor.Config) : State :=
  match s.phase with
  | .done => .done s.output
  | _ => .graph n f s

def step (flips : EndpointChoices) (k budget : Nat) : State → State
  | .normalize s => normalizeState (LinearPreprocessNormalize.step s)
  | .initialize s => initializeState (LinearPreprocessInit.step s)
  | .units size adj s => unitsState budget size adj (LinearPreprocessUnits.step adj s)
  | .extract mem s => extractState budget mem (LinearPreprocessExtract.step mem s)
  | .padding count s => paddingState count (LinearPreprocessPadding.step count s)
  | .header f s => headerState f (Header.step s)
  | .graph n f s => graphState n f (WordConstructor.step flips k n f s)
  | .done out => .done out

def initial (f : CNF) : State := .normalize (.scan f [])

theorem normalize_simulation (flips : EndpointChoices) (k budget : Nat)
    {t : Nat} {s q : LinearPreprocessNormalize.State}
    (h : LinearPreprocessNormalize.Executes t s q) :
    ∃ u, u ≤ t ∧ Runs (step flips k budget) u (normalizeState s) (normalizeState q) := by
  have hr : Runs LinearPreprocessNormalize.step t s q := by
    induction h with
    | refl s => exact Runs.refl s
    | next h ih => exact Runs.next ih
  apply hr.simulate normalizeState
  intro s
  cases s <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem initialize_simulation (flips : EndpointChoices) (k budget : Nat)
    {t : Nat} {s q : LinearPreprocessInit.State}
    (h : LinearPreprocessInit.Executes t s q) :
    ∃ u, u ≤ t ∧ Runs (step flips k budget) u (initializeState s) (initializeState q) := by
  have hr : Runs LinearPreprocessInit.step t s q := by
    induction h with
    | refl s => exact Runs.refl s
    | next h ih => exact Runs.next ih
  apply hr.simulate initializeState
  intro s
  cases s <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem units_simulation (flips : EndpointChoices) (k budget size : Nat)
    (adj : LinearPreprocessUnits.Incidences) {t : Nat} {s q : LinearPreprocessUnits.State}
    (h : LinearPreprocessUnits.Executes adj t s q) :
    ∃ u, u ≤ t ∧ Runs (step flips k budget) u (unitsState budget size adj s) (unitsState budget size adj q) := by
  have hr : Runs (LinearPreprocessUnits.step adj) t s q := by
    induction h with
    | refl s => exact Runs.refl s
    | next h ih => exact Runs.next ih
  apply hr.simulate (unitsState budget size adj)
  intro s
  cases s <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem extract_simulation (flips : EndpointChoices) (k budget : Nat)
    (mem : LinearPreprocessUnits.Memory) {t : Nat} {s q : LinearPreprocessExtract.State}
    (h : LinearPreprocessExtract.Executes mem t s q) :
    ∃ u, u ≤ t ∧ Runs (step flips k budget) u (extractState budget mem s) (extractState budget mem q) := by
  have hr : Runs (LinearPreprocessExtract.step mem) t s q := by
    induction h with
    | refl s => exact Runs.refl s
    | next h ih => exact Runs.next ih
  apply hr.simulate (extractState budget mem)
  intro s
  cases s <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem padding_simulation (flips : EndpointChoices) (k budget count : Nat)
    {t : Nat} {s q : LinearPreprocessPadding.State}
    (h : LinearPreprocessPadding.Executes count t s q) :
    ∃ u, u ≤ t ∧ Runs (step flips k budget) u (paddingState count s) (paddingState count q) := by
  have hr : Runs (LinearPreprocessPadding.step count) t s q := by
    induction h with
    | refl s => exact Runs.refl s
    | next h ih => exact Runs.next ih
  apply hr.simulate (paddingState count)
  intro s
  cases s <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem header_simulation (flips : EndpointChoices) (k budget : Nat) (f : CNF)
    {t : Nat} {s q : Header.State} (h : Runs Header.step t s q) :
    ∃ u, u ≤ t ∧ Runs (step flips k budget) u (headerState f s) (headerState f q) := by
  apply h.simulate (headerState f)
  intro s
  cases s <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem graph_simulation (flips : EndpointChoices) (k budget n : Nat) (f : CNF)
    {t : Nat} {s q : WordConstructor.Config} (h : WordConstructor.Executes flips k n f t s q) :
    ∃ u, u ≤ t ∧ Runs (step flips k budget) u (graphState n f s) (graphState n f q) := by
  have hr : Runs (WordConstructor.step flips k n f) t s q := by
    induction h with
    | refl s => exact Runs.refl s
    | next h ih => exact Runs.next ih
  apply hr.simulate (graphState n f)
  intro s
  rcases s with ⟨phase,mem,out⟩
  cases phase <;> first | exact Or.inl rfl | exact Or.inr rfl

end STACS2027.WordPipeline
