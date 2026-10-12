module

public import NPHardness.LinearPreprocessNormalize

/-!
Indexed unit propagation.  Clause cells are random-access words containing
either an inactive tag or a pointer to a clause.  An immutable incidence table
lists the clause IDs at each variable.  The intended input has at most three
incidences per variable and three literals per clause.

The operational step below is a bounded-adjacency macro: it uses at most three
clause updates on valid inputs.  In particular it does not scan the formula.
The proof of the input table and its construction cost are separate from this
kernel.  All semantic table enumerations below occur only in specifications.
-/

@[expose] public section
namespace STACS2027.LinearPreprocessUnits
open Complexity.SAT

abbrev Memory := Nat → Option Clause
abbrev Incidences := Nat → List Nat

def write (mem : Memory) (j : Nat) (c : Option Clause) : Memory :=
  fun i => if i = j then c else mem i

theorem write_same (mem : Memory) (j : Nat) (c : Option Clause) : write mem j c j = c := by
  simp [write]

theorem write_other (mem : Memory) (i j : Nat) (c : Option Clause) (h : i ≠ j) :
    write mem j c i = mem i := by simp [write,h]

def contents (size : Nat) (mem : Memory) : CNF := (List.range size).filterMap mem

theorem mem_contents {size : Nat} {mem : Memory} {c : Clause} :
    c ∈ contents size mem ↔ ∃ j, j < size ∧ mem j = some c := by
  simp [contents, List.mem_filterMap]

def simplifyCell (l : Literal) : Option Clause → Option Clause
  | none => none
  | some c => if l ∈ c then none else some (c.filter fun r => r.var != l.var)

theorem simplifyCell_avoids (l : Literal) (cell : Option Clause) {c : Clause}
    (h : simplifyCell l cell = some c) : ∀ r ∈ c, r.var ≠ l.var := by
  cases cell with
  | none => cases h
  | some d =>
    simp only [simplifyCell] at h
    split at h
    · cases h
    · have he := Option.some.inj h
      subst c
      intro r hr
      exact bne_iff_ne.mp (List.mem_filter.mp hr).2

theorem simplifyCell_unchanged {l : Literal} {c : Clause}
    (h : ∀ r ∈ c, r.var ≠ l.var) : simplifyCell l (some c) = some c := by
  have hn : l ∉ c := fun hm => h l hm rfl
  simp only [simplifyCell, ite_eq_right hn]
  congr 1
  apply List.filter_eq_self.mpr
  intro r hr
  exact bne_iff_ne.mpr (h r hr)

theorem simplifyCell_idempotent (l : Literal) (cell : Option Clause) :
    simplifyCell l (simplifyCell l cell) = simplifyCell l cell := by
  cases h : simplifyCell l cell with
  | none => rfl
  | some c => exact simplifyCell_unchanged (simplifyCell_avoids l cell h)

theorem simplifyCell_deletion {l : Literal} {cell : Option Clause} {c : Clause}
    (h : simplifyCell l cell = some c) : ∃ d, cell = some d ∧ c.Sublist d := by
  cases cell with
  | none => cases h
  | some d =>
    simp only [simplifyCell] at h
    split at h
    · cases h
    · have he := Option.some.inj h
      subst c
      exact ⟨d,rfl,List.filter_sublist⟩

def short : Option Clause → Bool
  | some [] => true
  | some [_] => true
  | _ => false

def updateAt (l : Literal) (j : Nat) (mem : Memory) (queue : List Nat) : Memory × List Nat :=
  let c := simplifyCell l (mem j)
  (write mem j c, if short c then j :: queue else queue)

def updateIds (l : Literal) : List Nat → Memory → List Nat → Memory × List Nat
  | [], mem, queue => (mem,queue)
  | j :: js, mem, queue =>
    let next := updateAt l j mem queue
    updateIds l js next.1 next.2

theorem updateIds_memory (l : Literal) (ids : List Nat) (mem : Memory) (queue : List Nat) (i : Nat) :
    (updateIds l ids mem queue).1 i =
      if i ∈ ids then simplifyCell l (mem i) else mem i := by
  induction ids generalizing mem queue with
  | nil => simp [updateIds]
  | cons j js ih =>
    simp only [updateIds, ih, updateAt, write]
    by_cases hi : i = j
    · subst i
      by_cases hj : j ∈ js <;> simp [hj, simplifyCell_idempotent]
    · by_cases hm : i ∈ js <;> simp [hi,hm]

theorem updateIds_queue_bound (l : Literal) (ids : List Nat) (mem : Memory) (queue : List Nat) :
    (updateIds l ids mem queue).2.length ≤ queue.length + ids.length := by
  induction ids generalizing mem queue with
  | nil => simp [updateIds]
  | cons j js ih =>
    have h := ih (updateAt l j mem queue).1 (updateAt l j mem queue).2
    simp only [updateIds] at *
    have hq : (updateAt l j mem queue).2.length ≤ queue.length+1 := by
      simp only [updateAt]
      split <;> simp
    simp only [List.length_cons]
    omega

def Covers (size : Nat) (adj : Incidences) (mem : Memory) : Prop :=
  ∀ j, j < size → ∀ c, mem j = some c → ∀ l ∈ c, j ∈ adj l.var

theorem updateIds_all (size : Nat) (adj : Incidences) (mem : Memory) (queue : List Nat)
    (hcover : Covers size adj mem) (l : Literal) {j : Nat} (hj : j < size) :
    (updateIds l (adj l.var) mem queue).1 j = simplifyCell l (mem j) := by
  rw [updateIds_memory]
  split
  · rfl
  · next hn =>
      cases hm : mem j with
      | none => rfl
      | some c =>
        apply (simplifyCell_unchanged ?_).symm
        intro r hr he
        apply hn
        rw [← he]
        exact hcover j hj c hm r hr

theorem contents_simplify (size : Nat) (mem : Memory) (l : Literal) :
    contents size (fun j => simplifyCell l (mem j)) = setLiteral l (contents size mem) := by
  unfold contents
  generalize List.range size = ids
  induction ids with
  | nil => rfl
  | cons j js ih =>
    cases h : mem j with
    | none => simpa [simplifyCell,h] using ih
    | some c =>
      simp only [List.filterMap_cons, h, ih]
      by_cases hl : l ∈ c <;> simp only [simplifyCell, hl, ↓reduceIte, setLiteral]

theorem contents_update (size : Nat) (adj : Incidences) (mem : Memory) (queue : List Nat)
    (hcover : Covers size adj mem) (l : Literal) :
    contents size (updateIds l (adj l.var) mem queue).1 = setLiteral l (contents size mem) := by
  rw [← contents_simplify]
  unfold contents
  have hall : ∀ j ∈ List.range size,
      (updateIds l (adj l.var) mem queue).1 j = simplifyCell l (mem j) := by
    intro j hj
    exact updateIds_all size adj mem queue hcover l (List.mem_range.mp hj)
  generalize List.range size = ids at *
  induction ids with
  | nil => rfl
  | cons j js ih =>
    simp only [List.filterMap_cons, hall j (by simp), ih (fun i hi => hall i (by simp [hi]))]

theorem update_cover (size : Nat) (adj : Incidences) (mem : Memory) (queue : List Nat)
    (hcover : Covers size adj mem) (l : Literal) :
    Covers size adj (updateIds l (adj l.var) mem queue).1 := by
  intro j hj c hc r hr
  rw [updateIds_all size adj mem queue hcover l hj] at hc
  obtain ⟨d,hd,hsub⟩ := simplifyCell_deletion hc
  exact hcover j hj d hd r (hsub.subset hr)

/-- The queue may contain stale or repeated entries; every still-live empty
or unit clause must occur in it. -/
def Complete (size : Nat) (mem : Memory) (queue : List Nat) : Prop :=
  ∀ j, j < size → short (mem j) = true → j ∈ queue

def CompleteExcept (except size : Nat) (mem : Memory) (queue : List Nat) : Prop :=
  ∀ j, j < size → j ≠ except → short (mem j) = true → j ∈ queue

theorem updateAt_completeExcept (except size : Nat) (l : Literal) (j : Nat)
    (mem : Memory) (queue : List Nat) (h : CompleteExcept except size mem queue) :
    CompleteExcept except size (updateAt l j mem queue).1 (updateAt l j mem queue).2 := by
  intro i hi hex hs
  simp only [updateAt] at hs ⊢
  by_cases he : i = j
  · subst i
    simp only [write_same] at hs
    simp [hs]
  · rw [write_other mem i j _ he] at hs
    have hm := h i hi hex hs
    split <;> simp [hm]

theorem updateIds_completeExcept (except size : Nat) (l : Literal) (ids : List Nat)
    (mem : Memory) (queue : List Nat) (h : CompleteExcept except size mem queue) :
    CompleteExcept except size (updateIds l ids mem queue).1 (updateIds l ids mem queue).2 := by
  induction ids generalizing mem queue with
  | nil => exact h
  | cons j js ih => exact ih _ _ (updateAt_completeExcept except size l j mem queue h)

theorem updateIds_ids_below (size : Nat) (l : Literal) (ids : List Nat)
    (mem : Memory) (queue : List Nat)
    (hi : ∀ j ∈ ids, j < size) (hq : ∀ j ∈ queue, j < size) :
    ∀ j ∈ (updateIds l ids mem queue).2, j < size := by
  induction ids generalizing mem queue with
  | nil => exact hq
  | cons j js ih =>
    apply ih
    · intro i hm; exact hi i (by simp [hm])
    · intro i hm
      simp only [updateAt] at hm
      split at hm
      · rcases List.mem_cons.mp hm with rfl | hm
        · exact hi i (by simp)
        · exact hq i hm
      · exact hq i hm

structure Valid (size : Nat) (adj : Incidences) (mem : Memory) (queue : List Nat) : Prop where
  cover : Covers size adj mem
  ids : ∀ j ∈ queue, j < size
  complete : Complete size mem queue
  clauses : ∀ j, j < size → ∀ c, mem j = some c → c.length ≤ 3

structure AdjacencyValid (size : Nat) (adj : Incidences) : Prop where
  ids : ∀ v j, j ∈ adj v → j < size
  degree : ∀ v, (adj v).length ≤ 3

inductive State where
  | running (mem : Memory) (queue : List Nat)
  | done (mem : Memory)
  | rejected

def step (adj : Incidences) : State → State
  | .running mem [] => .done mem
  | .running mem (j :: queue) =>
      match mem j with
      | none => .running mem queue
      | some [] => .rejected
      | some [l] =>
        let next := updateIds l (adj l.var) mem queue
        .running next.1 next.2
      | some (_ :: _ :: _) => .running mem queue
  | .done mem => .done mem
  | .rejected => .rejected

inductive Executes (adj : Incidences) : Nat → State → State → Prop where
  | refl (s) : Executes adj 0 s s
  | next {t s u} : Executes adj t (step adj s) u → Executes adj (t+1) s u

def potential (size : Nat) (mem : Memory) (queue : List Nat) : Nat :=
  4 * (contents size mem).length + queue.length

theorem Valid.pop_inactive {size : Nat} {adj : Incidences} {mem : Memory}
    {j : Nat} {queue : List Nat} (h : Valid size adj mem (j :: queue))
    (hs : short (mem j) = false) : Valid size adj mem queue := by
  refine ⟨h.cover, fun i hi => h.ids i (by simp [hi]), ?_, h.clauses⟩
  intro i hi hshort
  rcases List.mem_cons.mp (h.complete i hi hshort) with he | hm
  · subst i
    rw [hs] at hshort
    cases hshort
  · exact hm

theorem Valid.pop_unit {size : Nat} {adj : Incidences} {mem : Memory}
    {j : Nat} {queue : List Nat} {l : Literal} (ha : AdjacencyValid size adj)
    (h : Valid size adj mem (j :: queue)) (hj : mem j = some [l]) :
    Valid size adj (updateIds l (adj l.var) mem queue).1 (updateIds l (adj l.var) mem queue).2 := by
  have hlt := h.ids j (by simp)
  have hexc : CompleteExcept j size mem queue := by
    intro i hi hne hs
    rcases List.mem_cons.mp (h.complete i hi hs) with he | hm
    · exact False.elim (hne he)
    · exact hm
  have hu := updateIds_completeExcept j size l (adj l.var) mem queue hexc
  refine ⟨update_cover size adj mem queue h.cover l,
    updateIds_ids_below size l (adj l.var) mem queue (ha.ids l.var)
      (fun i hi => h.ids i (by simp [hi])), ?_, ?_⟩
  · intro i hi hs
    by_cases he : i = j
    · subst i
      rw [updateIds_all size adj mem queue h.cover l hlt, hj] at hs
      simp [simplifyCell,short] at hs
    · exact hu i hi he hs
  · intro i hi c hc
    rw [updateIds_all size adj mem queue h.cover l hi] at hc
    obtain ⟨d,hd,hsub⟩ := simplifyCell_deletion hc
    exact Nat.le_trans hsub.length_le (h.clauses i hi d hd)

theorem unit_potential_decreases {size : Nat} {adj : Incidences} {mem : Memory}
    {j : Nat} {queue : List Nat} {l : Literal} (ha : AdjacencyValid size adj)
    (h : Valid size adj mem (j :: queue)) (hj : mem j = some [l]) :
    potential size (updateIds l (adj l.var) mem queue).1 (updateIds l (adj l.var) mem queue).2 <
      potential size mem (j :: queue) := by
  have hmem : [l] ∈ contents size mem := mem_contents.mpr ⟨j,h.ids j (by simp),hj⟩
  have hlen := setLiteral_length_lt hmem
  have hqueue := updateIds_queue_bound l (adj l.var) mem queue
  have hdegree := ha.degree l.var
  unfold potential
  rw [contents_update size adj mem queue h.cover l]
  simp only [List.length_cons]
  omega

/-- Completed cells contain no empty or unit clause. -/
theorem completed_clause_lower {size : Nat} {adj : Incidences} {mem : Memory}
    (h : Valid size adj mem []) : ∀ c ∈ contents size mem, 2 ≤ c.length := by
  intro c hc
  obtain ⟨j,hj,hm⟩ := mem_contents.mp hc
  cases c with
  | nil => have hc := h.complete j hj (by simp [hm,short]); cases hc
  | cons l c => cases c with
    | nil => have hc := h.complete j hj (by simp [hm,short]); cases hc
    | cons r c => simp

def TerminalSpec (size : Nat) (original : CNF) : State → Prop
  | .running _ _ => False
  | .rejected => ¬ Satisfiable original
  | .done mem =>
      (Satisfiable (contents size mem) ↔ Satisfiable original) ∧
      FormulaDeletion (contents size mem) original ∧
      (∀ c ∈ contents size mem, 2 ≤ c.length)

theorem terminalSpec_deletion {size : Nat} {f g : CNF} {result : State}
    (h : TerminalSpec size g result) (he : Satisfiable g ↔ Satisfiable f)
    (hd : FormulaDeletion g f) : TerminalSpec size f result := by
  cases result with
  | running mem queue => exact h
  | rejected => exact fun hf => h (he.mpr hf)
  | done mem => exact ⟨h.1.trans he, h.2.1.trans hd, h.2.2⟩

/-- The queue kernel terminates in linearly many bounded-adjacency macro
steps.  Its initialization and final table enumeration are not charged here. -/
theorem executes_terminal (fuel : Nat) (size : Nat) (adj : Incidences)
    (ha : AdjacencyValid size adj) (mem : Memory) (queue : List Nat)
    (hv : Valid size adj mem queue) (hfuel : potential size mem queue < fuel) :
    ∃ t result, t ≤ fuel ∧ Executes adj t (.running mem queue) result ∧
      TerminalSpec size (contents size mem) result := by
  induction fuel generalizing mem queue with
  | zero => omega
  | succ fuel ih =>
    cases queue with
    | nil =>
      exact ⟨1,.done mem,by omega,Executes.next (Executes.refl (.done mem)),
        ⟨Iff.rfl,FormulaDeletion.refl _,completed_clause_lower hv⟩⟩
    | cons j queue =>
      have hlt := hv.ids j (by simp)
      cases hj : mem j with
      | none =>
        have hv' := hv.pop_inactive (by simp [hj,short])
        have hp : potential size mem queue < fuel := by
          simp only [potential,List.length_cons] at hfuel ⊢
          omega
        obtain ⟨t,result,ht,hr,hs⟩ := ih mem queue hv' hp
        have he : step adj (.running mem (j :: queue)) = .running mem queue := by simp [step,hj]
        rw [← he] at hr
        exact ⟨t+1,result,by omega,Executes.next hr,hs⟩
      | some c => cases c with
        | nil =>
          have he : step adj (.running mem (j :: queue)) = .rejected := by simp [step,hj]
          have hr : Executes adj 0 (step adj (.running mem (j :: queue))) .rejected := by
            rw [he]
            exact Executes.refl _
          exact ⟨1,.rejected,by omega,Executes.next hr,
            empty_clause_unsatisfiable (mem_contents.mpr ⟨j,hlt,hj⟩)⟩
        | cons l c => cases c with
          | nil =>
            have hv' := hv.pop_unit ha hj
            have hp := unit_potential_decreases ha hv hj
            obtain ⟨t,result,ht,hr,hs⟩ := ih _ _ hv' (by omega)
            have he : step adj (.running mem (j :: queue)) =
                .running (updateIds l (adj l.var) mem queue).1 (updateIds l (adj l.var) mem queue).2 := by
              simp [step,hj]
            rw [← he] at hr
            refine ⟨t+1,result,by omega,Executes.next hr,?_⟩
            apply terminalSpec_deletion hs
            · rw [contents_update size adj mem queue hv.cover l]
              exact setLiteral_satisfiable (mem_contents.mpr ⟨j,hlt,hj⟩)
            · rw [contents_update size adj mem queue hv.cover l]
              exact setLiteral_deletion l _
          | cons r c =>
            have hv' := hv.pop_inactive (by simp [hj,short])
            have hp : potential size mem queue < fuel := by
              simp only [potential,List.length_cons] at hfuel ⊢
              omega
            obtain ⟨t,result,ht,hr,hs⟩ := ih mem queue hv' hp
            have he : step adj (.running mem (j :: queue)) = .running mem queue := by simp [step,hj]
            rw [← he] at hr
            exact ⟨t+1,result,by omega,Executes.next hr,hs⟩

theorem kernel_linear (size : Nat) (adj : Incidences) (ha : AdjacencyValid size adj)
    (mem : Memory) (hv : Valid size adj mem (List.range size)) :
    ∃ t result, t ≤ 5*size+1 ∧ Executes adj t (.running mem (List.range size)) result ∧
      TerminalSpec size (contents size mem) result := by
  have hlen : (contents size mem).length ≤ size := by
    simpa only [contents, List.length_range] using List.length_filterMap_le mem (List.range size)
  apply executes_terminal (5*size+1) size adj ha mem (List.range size) hv
  simp only [potential,List.length_range]
  omega

end STACS2027.LinearPreprocessUnits
