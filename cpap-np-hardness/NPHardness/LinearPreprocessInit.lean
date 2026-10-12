module

public import NPHardness.LinearPreprocessUnits

/-! A single-pass incidence-table initializer for the unit-propagation kernel.
Memory reads and writes are direct accesses; the initially unused cells carry
the inactive/empty tag.  Each literal inserts one clause ID in an incidence
list.  No search for an occurrence or scan over the variable universe occurs.
-/

@[expose] public section
namespace STACS2027.LinearPreprocessInit
open Complexity.SAT
open LinearPreprocessUnits

def push (adj : Incidences) (v j : Nat) : Incidences :=
  fun w => if w = v then j :: adj w else adj w

def addClause (j : Nat) : Clause → Incidences → Incidences
  | [], adj => adj
  | l :: c, adj => addClause j c (push adj l.var j)

theorem addClause_length (j : Nat) (c : Clause) (adj : Incidences) (v : Nat) :
    (addClause j c adj v).length = (adj v).length + (c.filter fun l => l.var == v).length := by
  induction c generalizing adj with
  | nil => simp [addClause]
  | cons l c ih =>
    rw [addClause,ih]
    by_cases h : l.var = v <;> simp [push,h,Ne.symm, Nat.add_assoc,Nat.add_comm]

theorem addClause_mem (j : Nat) (c : Clause) (adj : Incidences) (v i : Nat) :
    i ∈ addClause j c adj v ↔ i ∈ adj v ∨ (i = j ∧ ∃ l ∈ c, l.var = v) := by
  induction c generalizing adj with
  | nil => simp [addClause]
  | cons l c ih =>
    rw [addClause,ih]
    by_cases h : l.var = v
    · simp only [push, ← h, ↓reduceIte, List.mem_cons]
      constructor
      · intro hh
        rcases hh with (he | hm) | ⟨he,r,hr,hv⟩
        · exact Or.inr ⟨he,l,by simp,rfl⟩
        · exact Or.inl hm
        · exact Or.inr ⟨he,r,Or.inr hr,hv⟩
      · rintro (hm | ⟨he,_,_,_⟩)
        · exact Or.inl (Or.inr hm)
        · exact Or.inl (Or.inl he)
    · have h' : v ≠ l.var := Ne.symm h
      simp only [push,h',↓reduceIte]
      constructor
      · rintro (hm | ⟨he,r,hr,hv⟩)
        · exact Or.inl hm
        · exact Or.inr ⟨he,r,List.mem_cons_of_mem _ hr,hv⟩
      · rintro (hm | ⟨he,r,hr,hv⟩)
        · exact Or.inl hm
        · rcases List.mem_cons.mp hr with rfl | hr
          · exact False.elim (h hv)
          · exact Or.inr ⟨he,r,hr,hv⟩

def buildTables : Nat → CNF → Memory → Incidences → Memory × Incidences
  | _, [], mem, adj => (mem,adj)
  | j, c :: f, mem, adj => buildTables (j+1) f (write mem j (some c)) (addClause j c adj)

theorem initialize_memory (start : Nat) (f : CNF) (mem : Memory) (adj : Incidences) (i : Nat) :
    (buildTables start f mem adj).1 i =
      if start ≤ i ∧ i < start+f.length then f[i-start]? else mem i := by
  induction f generalizing start mem adj with
  | nil =>
    simp only [buildTables,List.length_nil,Nat.add_zero]
    rw [ite_eq_right (by omega : ¬(start ≤ i ∧ i < start))]
  | cons c f ih =>
    rw [buildTables,ih]
    by_cases he : i = start
    · subst i
      rw [ite_eq_right (by omega : ¬(start+1 ≤ start ∧ start < start+1+f.length)),
        ite_eq_left (by simp)]
      simp [write]
    · by_cases ht : start+1 ≤ i ∧ i < start+1+f.length
      · have hs : start ≤ i ∧ i < start+(c::f).length := by simp only [List.length_cons]; omega
        rw [ite_eq_left ht,ite_eq_left hs]
        have hi : i-start = (i-(start+1))+1 := by omega
        rw [hi,List.getElem?_cons_succ]
      · have hs : ¬(start ≤ i ∧ i < start+(c::f).length) := by simp only [List.length_cons]; omega
        rw [ite_eq_right ht,ite_eq_right hs]
        exact write_other mem i start (some c) he

theorem initialize_adj_mono (start : Nat) (f : CNF) (mem : Memory) (adj : Incidences)
    (v i : Nat) (hi : i ∈ adj v) : i ∈ (buildTables start f mem adj).2 v := by
  induction f generalizing start mem adj with
  | nil => exact hi
  | cons c f ih =>
    exact ih _ _ _ ((addClause_mem start c adj v i).mpr (Or.inl hi))

theorem initialize_adj_length (start : Nat) (f : CNF) (mem : Memory) (adj : Incidences) (v : Nat) :
    ((buildTables start f mem adj).2 v).length =
      (adj v).length + (f.flatten.filter fun l => l.var == v).length := by
  induction f generalizing start mem adj with
  | nil => simp [buildTables]
  | cons c f ih =>
    simp only [buildTables,ih,addClause_length,List.flatten_cons,List.filter_append,List.length_append]
    omega

theorem initialize_adj_ids (bound start : Nat) (f : CNF) (mem : Memory) (adj : Incidences)
    (hb : start+f.length ≤ bound) (hi : ∀ v i, i ∈ adj v → i < bound) :
    ∀ v i, i ∈ (buildTables start f mem adj).2 v → i < bound := by
  induction f generalizing start mem adj with
  | nil => exact hi
  | cons c f ih =>
    apply ih
    · simp only [List.length_cons] at hb
      omega
    · intro v i hm
      rcases (addClause_mem start c adj v i).mp hm with hm | ⟨rfl,_⟩
      · exact hi v i hm
      · simp only [List.length_cons] at hb
        omega

theorem initialize_adj_occurrence (start : Nat) (f : CNF) (mem : Memory) (adj : Incidences)
    {i : Nat} (hi : i < f.length) {l : Literal} (hl : l ∈ f[i]) :
    start+i ∈ (buildTables start f mem adj).2 l.var := by
  induction f generalizing start mem adj i with
  | nil => simp at hi
  | cons c f ih =>
    cases i with
    | zero =>
      change start+0 ∈ (buildTables (start+1) f (write mem start (some c)) (addClause start c adj)).2 l.var
      apply initialize_adj_mono
      apply (addClause_mem start c adj l.var (start+0)).mpr
      exact Or.inr ⟨by omega,l,hl,rfl⟩
    | succ i =>
      have hi' : i < f.length := by simp only [List.length_cons] at hi; omega
      have h := ih (start+1) (write mem start (some c)) (addClause start c adj) hi' hl
      simpa only [buildTables, Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

def initialMemory (f : CNF) : Memory := (buildTables 0 f (fun _ => none) (fun _ => [])).1
def initialAdj (f : CNF) : Incidences := (buildTables 0 f (fun _ => none) (fun _ => [])).2

theorem initialMemory_eq (f : CNF) (i : Nat) : initialMemory f i = f[i]? := by
  rw [initialMemory,initialize_memory]
  simp only [Nat.zero_le, true_and,Nat.zero_add,Nat.sub_zero]
  split
  · rfl
  · next h => simp [List.getElem?_eq_none_iff.mpr (by omega : f.length ≤ i)]

theorem contents_initialMemory (f : CNF) : contents f.length (initialMemory f) = f := by
  have haux : ∀ (f : CNF) (start : Nat),
      (List.range' start f.length).filterMap (fun j => f[j-start]?) = f := by
    intro f
    induction f with
    | nil => intro start; rfl
    | cons c f ih =>
      intro start
      simp only [List.length_cons,List.range'_succ,List.filterMap_cons,Nat.sub_self,List.getElem?_cons_zero]
      have he : (List.range' (start+1) f.length).filterMap (fun j => (c::f)[j-start]?) = f := by
        have hpoint : ∀ j ∈ List.range' (start+1) f.length,
            (c::f)[j-start]? = f[j-(start+1)]? := by
          intro j hj
          obtain ⟨i,hi,he⟩ := List.mem_range'.mp hj
          have hsub : j-start = (j-(start+1))+1 := by omega
          rw [hsub,List.getElem?_cons_succ]
        have hall : ∀ (ids : List Nat), (∀ j ∈ ids, (c::f)[j-start]? = f[j-(start+1)]?) →
            ids.filterMap (fun j => (c::f)[j-start]?) = ids.filterMap (fun j => f[j-(start+1)]?) := by
          intro ids
          induction ids with
          | nil => intro _; rfl
          | cons j js ih =>
            intro hj
            simp only [List.filterMap_cons,hj j (by simp), ih (fun i hi => hj i (by simp [hi]))]
        rw [hall _ hpoint]
        exact ih (start+1)
      rw [he]
  unfold contents
  have he : initialMemory f = (fun j => f[j]?) := funext (initialMemory_eq f)
  rw [he,List.range_eq_range']
  simpa only [Nat.sub_zero] using haux f 0

theorem initial_valid (f : CNF) (hf : IsThreeCNF f) :
    Valid f.length (initialAdj f) (initialMemory f) (List.range f.length) := by
  refine ⟨?_,fun j hj => List.mem_range.mp hj,fun j hj _ => List.mem_range.mpr hj,?_⟩
  · intro j hj c hc l hl
    rw [initialMemory_eq,List.getElem?_eq_getElem hj] at hc
    have he : f[j] = c := Option.some.inj hc
    subst c
    have h := initialize_adj_occurrence 0 f (fun _ => none) (fun _ => []) hj hl
    simpa only [Nat.zero_add,initialAdj] using h
  · intro j hj c hc
    rw [initialMemory_eq,List.getElem?_eq_getElem hj] at hc
    have he : f[j] = c := Option.some.inj hc
    subst c
    exact hf _ (List.getElem_mem hj)

theorem initialAdj_valid (f : CNF)
    (hdegree : ∀ v, (f.flatten.filter fun l => l.var == v).length ≤ 3) :
    AdjacencyValid f.length (initialAdj f) := by
  refine ⟨?_,?_⟩
  · exact initialize_adj_ids f.length 0 f (fun _ => none) (fun _ => []) (by omega) (by simp)
  · intro v
    simpa only [initialAdj,initialize_adj_length,List.length_nil,Nat.zero_add] using hdegree v

inductive State where
  | scanFormula (next : Nat) (remaining : CNF) (mem : Memory) (adj : Incidences)
  | scanClause (next : Nat) (remaining : Clause) (tail : CNF) (mem : Memory) (adj : Incidences)
  | queue (remaining size : Nat) (mem : Memory) (adj : Incidences) (out : List Nat)
  | done (size : Nat) (mem : Memory) (adj : Incidences) (queue : List Nat)

def step : State → State
  | .scanFormula j [] mem adj => .queue j j mem adj []
  | .scanFormula j (c :: f) mem adj => .scanClause j c f (write mem j (some c)) adj
  | .scanClause j [] f mem adj => .scanFormula (j+1) f mem adj
  | .scanClause j (l :: c) f mem adj => .scanClause j c f mem (push adj l.var j)
  | .queue 0 size mem adj out => .done size mem adj out
  | .queue (r+1) size mem adj out => .queue r size mem adj (r :: out)
  | .done size mem adj queue => .done size mem adj queue

inductive Executes : Nat → State → State → Prop where
  | refl (s) : Executes 0 s s
  | next {t s u} : Executes t (step s) u → Executes (t+1) s u

theorem Executes.trans {t u s mid dest}
    (h : Executes t s mid) (h' : Executes u mid dest) : Executes (t+u) s dest := by
  induction h with
  | refl => simpa using h'
  | next h ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Executes.next (ih h')

theorem run_clause (j : Nat) (c : Clause) (f : CNF) (mem : Memory) (adj : Incidences) :
    Executes (c.length+1) (.scanClause j c f mem adj) (.scanFormula (j+1) f mem (addClause j c adj)) := by
  induction c generalizing adj with
  | nil => exact Executes.next (Executes.refl _)
  | cons l c ih =>
    have h := Executes.next (s := .scanClause j (l::c) f mem adj) (ih (push adj l.var j))
    simpa only [List.length_cons,Nat.add_assoc,addClause] using h

theorem run_scan (j : Nat) (f : CNF) (mem : Memory) (adj : Incidences) :
    Executes (f.flatten.length+2*f.length+1) (.scanFormula j f mem adj)
      (.queue (j+f.length) (j+f.length) (buildTables j f mem adj).1 (buildTables j f mem adj).2 []) := by
  induction f generalizing j mem adj with
  | nil => simpa [buildTables] using Executes.next (s := .scanFormula j [] mem adj) (Executes.refl (.queue j j mem adj []))
  | cons c f ih =>
    have h := Executes.next (s := .scanFormula j (c::f) mem adj)
      ((run_clause j c f (write mem j (some c)) adj).trans
        (ih (j+1) (write mem j (some c)) (addClause j c adj)))
    have he : c.length+1 + (f.flatten.length+2*f.length+1)+1 =
        (c::f).flatten.length+2*(c::f).length+1 := by
      simp only [List.flatten_cons,List.length_append,List.length_cons]
      omega
    rw [he] at h
    simpa only [buildTables,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem run_queue (remaining size : Nat) (mem : Memory) (adj : Incidences) (out : List Nat) :
    Executes (remaining+1) (.queue remaining size mem adj out)
      (.done size mem adj (List.range remaining ++ out)) := by
  induction remaining generalizing out with
  | zero => exact Executes.next (Executes.refl _)
  | succ r ih =>
    have h := Executes.next (s := .queue (r+1) size mem adj out) (ih (r::out))
    simpa [List.range_succ,List.append_assoc,Nat.add_assoc] using h

theorem executes_initialize (f : CNF) :
    Executes (f.flatten.length+3*f.length+2) (.scanFormula 0 f (fun _ => none) (fun _ => []))
      (.done f.length (initialMemory f) (initialAdj f) (List.range f.length)) := by
  have hs := run_scan 0 f (fun _ => none) (fun _ => [])
  simp only [Nat.zero_add] at hs
  have h := hs.trans (run_queue f.length f.length (initialMemory f) (initialAdj f) [])
  have he : f.flatten.length+2*f.length+1+(f.length+1) = f.flatten.length+3*f.length+2 := by omega
  rw [he] at h
  simpa only [List.append_nil] using h

theorem normalized_degree {f : CNF} (hf : BoundedOccurrence f) (v : Nat) :
    ((normalizeClauses f).flatten.filter fun l => l.var == v).length ≤ 3 := by
  have hd := (normalizeClauses_deletion f).1.filter (fun l => l.var == v)
  have hle := hd.length_le
  have hs := signed_partition f.flatten v
  have hp := hf.2.1 v
  have hn := hf.2.2 v
  change (f.flatten.filter fun l => l.var == v && l.positive == true).length ≤ 1 at hp
  change (f.flatten.filter fun l => l.var == v && l.positive == false).length ≤ 2 at hn
  omega

theorem normalized_initial_valid {f : CNF} (hf : BoundedOccurrence f) :
    Valid (normalizeClauses f).length (initialAdj (normalizeClauses f)) (initialMemory (normalizeClauses f))
      (List.range (normalizeClauses f).length) ∧
    AdjacencyValid (normalizeClauses f).length (initialAdj (normalizeClauses f)) := by
  exact ⟨initial_valid _ ((normalizeClauses_deletion f).threeCNF hf.isThreeCNF),
    initialAdj_valid _ (normalized_degree hf)⟩

end STACS2027.LinearPreprocessInit
