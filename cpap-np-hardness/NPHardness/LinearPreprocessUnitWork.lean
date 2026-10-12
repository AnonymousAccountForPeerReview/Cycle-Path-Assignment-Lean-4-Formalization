module

public import NPHardness.LinearPreprocessResult

/-!
Why one valid unit-kernel step is a bounded amount of word work: every visited
incidence list has length at most three, and every clause cell encountered
during its updates has at most three literals.  The latter also holds between
updates, not just at macro-step boundaries.

`literalInspectionBound` counts a full membership pass and a full filtering
pass per visited clause; early termination can only reduce that amount.  It
does not count a whole-formula operation as a primitive instruction.
-/

@[expose] public section
namespace STACS2027.LinearPreprocessUnitWork
open Complexity.SAT
open LinearPreprocessUnits

def CellsSmall (size : Nat) (mem : Memory) : Prop :=
  ∀ j, j < size → ∀ c, mem j = some c → c.length ≤ 3

theorem updateAt_small {size : Nat} (l : Literal) (j : Nat) (mem : Memory) (queue : List Nat)
    (h : CellsSmall size mem) : CellsSmall size (updateAt l j mem queue).1 := by
  intro i hi c hc
  change write mem j (simplifyCell l (mem j)) i = some c at hc
  by_cases he : i = j
  · subst i
    rw [write_same] at hc
    obtain ⟨d,hd,hsub⟩ := simplifyCell_deletion hc
    exact Nat.le_trans hsub.length_le (h j hi d hd)
  · rw [write_other mem i j _ he] at hc
    exact h i hi c hc

def cellLength : Option Clause → Nat
  | none => 0
  | some c => c.length

def literalInspectionBound (l : Literal) : List Nat → Memory → List Nat → Nat
  | [], _, _ => 0
  | j :: js, mem, queue =>
      let next := updateAt l j mem queue
      2*cellLength (mem j) + literalInspectionBound l js next.1 next.2

theorem inspection_bound {size : Nat} (l : Literal) (ids : List Nat) (mem : Memory) (queue : List Nat)
    (h : CellsSmall size mem) (hi : ∀ j ∈ ids, j < size) :
    literalInspectionBound l ids mem queue ≤ 6*ids.length := by
  induction ids generalizing mem queue with
  | nil => simp [literalInspectionBound]
  | cons j js ih =>
    have hnext := ih (updateAt l j mem queue).1 (updateAt l j mem queue).2
      (updateAt_small l j mem queue h) (fun i hm => hi i (by simp [hm]))
    have hcell : cellLength (mem j) ≤ 3 := by
      cases hc : mem j with
      | none => simp [cellLength]
      | some c => exact h j (hi j (by simp)) c hc
    simp only [literalInspectionBound,List.length_cons]
    omega

theorem unit_work_bounded {size : Nat} {adj : Incidences} {mem : Memory} {queue : List Nat}
    (ha : AdjacencyValid size adj) (hv : Valid size adj mem queue) (l : Literal) :
    (adj l.var).length ≤ 3 ∧ literalInspectionBound l (adj l.var) mem queue ≤ 18 := by
  have h := inspection_bound l (adj l.var) mem queue hv.clauses (ha.ids l.var)
  exact ⟨ha.degree l.var,by have := ha.degree l.var; omega⟩

def Invariant (size : Nat) (adj : Incidences) : State → Prop
  | .running mem queue => Valid size adj mem queue
  | .done _ => True
  | .rejected => True

theorem step_invariant (size : Nat) (adj : Incidences) (ha : AdjacencyValid size adj)
    (s : State) (h : Invariant size adj s) : Invariant size adj (step adj s) := by
  cases s with
  | done mem => trivial
  | rejected => trivial
  | running mem queue =>
    cases queue with
    | nil => trivial
    | cons j queue =>
      cases hj : mem j with
      | none =>
        simpa only [step,hj,Invariant] using h.pop_inactive (by simp [short,hj])
      | some c => cases c with
        | nil => simp [step,hj,Invariant]
        | cons l c => cases c with
          | nil => simpa only [step,hj,Invariant] using h.pop_unit ha hj
          | cons r c =>
            simpa only [step,hj,Invariant] using h.pop_inactive (by simp [short,hj])

theorem executes_invariant {size : Nat} {adj : Incidences} (ha : AdjacencyValid size adj)
    {t : Nat} {s u : State} (h : Executes adj t s u) (hv : Invariant size adj s) :
    Invariant size adj u := by
  induction h with
  | refl => exact hv
  | next h ih => exact ih (step_invariant size adj ha _ hv)

/-- The constant bound holds at every reachable running state. -/
theorem reachable_unit_work {size : Nat} {adj : Incidences} (ha : AdjacencyValid size adj)
    {t : Nat} {mem mem' : Memory} {queue queue' : List Nat}
    (h : Executes adj t (.running mem queue) (.running mem' queue'))
    (hv : Valid size adj mem queue) (l : Literal) :
    (adj l.var).length ≤ 3 ∧ literalInspectionBound l (adj l.var) mem' queue' ≤ 18 := by
  exact unit_work_bounded ha (executes_invariant ha h hv) l

def statePotential (size : Nat) : State → Nat
  | .running mem queue => potential size mem queue
  | .done _ => 0
  | .rejected => 0

theorem step_potential_le (size : Nat) (adj : Incidences) (ha : AdjacencyValid size adj)
    (s : State) (h : Invariant size adj s) : statePotential size (step adj s) ≤ statePotential size s := by
  cases s with
  | done mem => exact Nat.le_refl _
  | rejected => exact Nat.le_refl _
  | running mem queue =>
    cases queue with
    | nil => exact Nat.zero_le _
    | cons j queue =>
      cases hj : mem j with
      | none => simp [step,hj,statePotential,potential]
      | some c => cases c with
        | nil => simp [step,hj,statePotential]
        | cons l c => cases c with
          | nil =>
            simpa only [step,hj,statePotential] using Nat.le_of_lt (unit_potential_decreases ha h hj)
          | cons r c => simp [step,hj,statePotential,potential]

theorem executes_potential_le {size : Nat} {adj : Incidences} (ha : AdjacencyValid size adj)
    {t : Nat} {s u : State} (h : Executes adj t s u) (hv : Invariant size adj s) :
    statePotential size u ≤ statePotential size s := by
  induction h with
  | refl => exact Nat.le_refl _
  | next h ih =>
    exact Nat.le_trans (ih (step_invariant size adj ha _ hv)) (step_potential_le size adj ha _ hv)

/-- The live queue is also linearly bounded, including stale entries. -/
theorem normalized_reachable_queue {f : CNF} (hf : BoundedOccurrence f)
    {t : Nat} {mem : Memory} {queue : List Nat}
    (h : Executes (LinearPreprocessInit.initialAdj (normalizeClauses f)) t
      (.running (LinearPreprocessInit.initialMemory (normalizeClauses f))
        (List.range (normalizeClauses f).length)) (.running mem queue)) :
    queue.length ≤ 5*f.length := by
  obtain ⟨hv,ha⟩ := LinearPreprocessInit.normalized_initial_valid hf
  have hp := executes_potential_le ha h hv
  simp only [statePotential,potential,LinearPreprocessInit.contents_initialMemory,List.length_range] at hp
  have hm := (normalizeClauses_deletion f).2.1
  omega

end STACS2027.LinearPreprocessUnitWork
