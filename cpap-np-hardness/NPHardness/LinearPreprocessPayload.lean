module

public import NPHardness.LinearPreprocessResult

/-! Bounds on every natural-number payload in the incidence initializer and
unit kernel.  List fields are immutable cell pointers; these predicates bound
their literal/ID contents and the addresses of active table entries. -/

@[expose] public section
namespace STACS2027.LinearPreprocessPayload
open Complexity.SAT
open LinearPreprocessUnits

def ClauseBound (bound : Nat) (c : Clause) : Prop := ∀ l ∈ c, l.var ≤ bound
def FormulaBound (bound : Nat) (f : CNF) : Prop := ∀ c ∈ f, ClauseBound bound c
def IdsBound (bound : Nat) (ids : List Nat) : Prop := ∀ i ∈ ids, i ≤ bound

def MemoryBound (bound : Nat) (mem : Memory) : Prop :=
  ∀ i c, mem i = some c → i ≤ bound ∧ ClauseBound bound c

def AdjacencyBound (bound : Nat) (adj : Incidences) : Prop :=
  ∀ v, IdsBound bound (adj v) ∧ (adj v ≠ [] → v ≤ bound)

theorem ClauseBound.mono {b d : Nat} {c : Clause} (h : ClauseBound b c) (hb : b ≤ d) : ClauseBound d c := by
  intro l hl
  exact Nat.le_trans (h l hl) hb

theorem FormulaBound.mono {b d : Nat} {f : CNF} (h : FormulaBound b f) (hb : b ≤ d) : FormulaBound d f := by
  intro c hc
  exact (h c hc).mono hb

theorem IdsBound.mono {b d : Nat} {ids : List Nat} (h : IdsBound b ids) (hb : b ≤ d) : IdsBound d ids := by
  intro i hi
  exact Nat.le_trans (h i hi) hb

theorem MemoryBound.mono {b d : Nat} {mem : Memory} (h : MemoryBound b mem) (hb : b ≤ d) : MemoryBound d mem := by
  intro i c hc
  obtain ⟨hi,hc⟩ := h i c hc
  exact ⟨Nat.le_trans hi hb,hc.mono hb⟩

theorem AdjacencyBound.mono {b d : Nat} {adj : Incidences} (h : AdjacencyBound b adj) (hb : b ≤ d) :
    AdjacencyBound d adj := by
  intro v
  exact ⟨(h v).1.mono hb,fun hn => Nat.le_trans ((h v).2 hn) hb⟩

theorem memory_write {b : Nat} {mem : Memory} (h : MemoryBound b mem)
    {j : Nat} (hj : j ≤ b) {cell : Option Clause} (hc : ∀ c, cell = some c → ClauseBound b c) :
    MemoryBound b (write mem j cell) := by
  intro i c hi
  by_cases he : i = j
  · subst i
    rw [write_same] at hi
    exact ⟨hj,hc c hi⟩
  · rw [write_other mem i j cell he] at hi
    exact h i c hi

theorem updateAt_bound {b : Nat} (l : Literal) (j : Nat) (mem : Memory) (queue : List Nat)
    (hm : MemoryBound b mem) (hq : IdsBound b queue) (hj : j ≤ b) :
    MemoryBound b (updateAt l j mem queue).1 ∧ IdsBound b (updateAt l j mem queue).2 := by
  refine ⟨?_,?_⟩
  · apply memory_write hm hj
    intro c hc
    obtain ⟨d,hd,hsub⟩ := simplifyCell_deletion hc
    intro r hr
    exact (hm j d hd).2 r (hsub.subset hr)
  · intro i hi
    simp only [updateAt] at hi
    split at hi
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact hj
      · exact hq i hi
    · exact hq i hi

theorem updateIds_bound {b : Nat} (l : Literal) (ids : List Nat) (mem : Memory) (queue : List Nat)
    (hm : MemoryBound b mem) (hq : IdsBound b queue) (hi : IdsBound b ids) :
    MemoryBound b (updateIds l ids mem queue).1 ∧ IdsBound b (updateIds l ids mem queue).2 := by
  induction ids generalizing mem queue with
  | nil => exact ⟨hm,hq⟩
  | cons j js ih =>
    have hn := updateAt_bound l j mem queue hm hq (hi j (by simp))
    exact ih _ _ hn.1 hn.2 (fun i hm => hi i (by simp [hm]))

def UnitsStateBound (bound : Nat) : LinearPreprocessUnits.State → Prop
  | .running mem queue => MemoryBound bound mem ∧ IdsBound bound queue
  | .done mem => MemoryBound bound mem
  | .rejected => True

theorem UnitsStateBound.mono {b d : Nat} {s : LinearPreprocessUnits.State}
    (h : UnitsStateBound b s) (hb : b ≤ d) : UnitsStateBound d s := by
  cases s with
  | running mem queue => exact ⟨h.1.mono hb,h.2.mono hb⟩
  | done mem => exact MemoryBound.mono h hb
  | rejected => trivial

theorem units_step_bound {b : Nat} (adj : Incidences) (ha : AdjacencyBound b adj)
    (s : LinearPreprocessUnits.State) (h : UnitsStateBound b s) :
    UnitsStateBound b (LinearPreprocessUnits.step adj s) := by
  cases s with
  | done mem => exact h
  | rejected => trivial
  | running mem queue =>
    cases queue with
    | nil => exact h.1
    | cons j queue =>
      have hq : IdsBound b queue := fun i hi => h.2 i (by simp [hi])
      cases hj : mem j with
      | none => simpa only [step,hj,UnitsStateBound] using And.intro h.1 hq
      | some c => cases c with
        | nil => simp [step,hj,UnitsStateBound]
        | cons l c => cases c with
          | nil => simpa only [step,hj,UnitsStateBound] using updateIds_bound l (adj l.var) mem queue h.1 hq (ha l.var).1
          | cons r c => simpa only [step,hj,UnitsStateBound] using And.intro h.1 hq

theorem push_bound {b : Nat} {adj : Incidences} (h : AdjacencyBound b adj)
    {v j : Nat} (hv : v ≤ b) (hj : j ≤ b) :
    AdjacencyBound b (LinearPreprocessInit.push adj v j) := by
  intro w
  by_cases he : w = v
  · subst w
    refine ⟨?_,fun _ => hv⟩
    intro i hi
    simp only [LinearPreprocessInit.push,↓reduceIte] at hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact hj
    · exact (h v).1 i hi
  · simpa only [LinearPreprocessInit.push,he,↓reduceIte] using h w

def InitStateBound (bound : Nat) : LinearPreprocessInit.State → Prop
  | .scanFormula j f mem adj => j ≤ bound ∧ FormulaBound bound f ∧ MemoryBound bound mem ∧ AdjacencyBound bound adj
  | .scanClause j c f mem adj => j ≤ bound ∧ ClauseBound bound c ∧ FormulaBound bound f ∧
      MemoryBound bound mem ∧ AdjacencyBound bound adj
  | .queue remaining size mem adj out => remaining ≤ bound ∧ size ≤ bound ∧ MemoryBound bound mem ∧
      AdjacencyBound bound adj ∧ IdsBound bound out
  | .done size mem adj queue => size ≤ bound ∧ MemoryBound bound mem ∧ AdjacencyBound bound adj ∧ IdsBound bound queue

theorem InitStateBound.mono {b d : Nat} {s : LinearPreprocessInit.State}
    (h : InitStateBound b s) (hb : b ≤ d) : InitStateBound d s := by
  cases s with
  | scanFormula j f mem adj =>
    exact ⟨Nat.le_trans h.1 hb,h.2.1.mono hb,h.2.2.1.mono hb,h.2.2.2.mono hb⟩
  | scanClause j c f mem adj =>
    exact ⟨Nat.le_trans h.1 hb,h.2.1.mono hb,h.2.2.1.mono hb,h.2.2.2.1.mono hb,h.2.2.2.2.mono hb⟩
  | queue remaining size mem adj out =>
    exact ⟨Nat.le_trans h.1 hb,Nat.le_trans h.2.1 hb,h.2.2.1.mono hb,h.2.2.2.1.mono hb,h.2.2.2.2.mono hb⟩
  | done size mem adj queue =>
    exact ⟨Nat.le_trans h.1 hb,h.2.1.mono hb,h.2.2.1.mono hb,h.2.2.2.mono hb⟩

theorem init_step_bound {b : Nat} (s : LinearPreprocessInit.State) (h : InitStateBound b s) :
    InitStateBound (b+1) (LinearPreprocessInit.step s) := by
  cases s with
  | scanFormula j f mem adj =>
    have hj : j ≤ b := h.1
    cases f with
    | nil =>
      exact ⟨by omega,by omega,h.2.2.1.mono (by omega),h.2.2.2.mono (by omega),by simp [IdsBound]⟩
    | cons c f =>
      have hc := h.2.1 c (by simp)
      have hf : FormulaBound b f := fun d hd => h.2.1 d (by simp [hd])
      have hm := memory_write h.2.2.1 h.1 (cell := some c) (by
        intro d hd
        cases hd
        exact hc)
      exact ⟨by omega,hc.mono (by omega),hf.mono (by omega),hm.mono (by omega),h.2.2.2.mono (by omega)⟩
  | scanClause j c f mem adj =>
    have hj : j ≤ b := h.1
    cases c with
    | nil => exact ⟨by omega,h.2.2.1.mono (by omega),h.2.2.2.1.mono (by omega),h.2.2.2.2.mono (by omega)⟩
    | cons l c =>
      have hl := h.2.1 l (by simp)
      have hc : ClauseBound b c := fun r hr => h.2.1 r (by simp [hr])
      have ha := push_bound h.2.2.2.2 hl h.1
      exact ⟨by omega,hc.mono (by omega),h.2.2.1.mono (by omega),h.2.2.2.1.mono (by omega),ha.mono (by omega)⟩
  | queue remaining size mem adj out =>
    have hr : remaining ≤ b := h.1
    have hs : size ≤ b := h.2.1
    cases remaining with
    | zero => exact ⟨by omega,h.2.2.1.mono (by omega),h.2.2.2.1.mono (by omega),h.2.2.2.2.mono (by omega)⟩
    | succ r =>
      refine ⟨by omega,by omega,h.2.2.1.mono (by omega),h.2.2.2.1.mono (by omega),?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · omega
      · exact Nat.le_trans (h.2.2.2.2 i hi) (by omega)
  | done size mem adj queue => exact h.mono (by omega)

theorem init_start_bound {b : Nat} {f : CNF} (hf : FormulaBound b f) :
    InitStateBound b (.scanFormula 0 f (fun _ => none) (fun _ => [])) := by
  refine ⟨Nat.zero_le _,hf,?_,?_⟩
  · intro i c hc
    cases hc
  · intro v
    simp [IdsBound]

end STACS2027.LinearPreprocessPayload
