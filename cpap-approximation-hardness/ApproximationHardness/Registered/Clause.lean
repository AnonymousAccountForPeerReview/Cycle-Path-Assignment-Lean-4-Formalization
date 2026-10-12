module

public import ApproximationHardness.Registered.Literal
public import NPHardness.GraphEncoding
import Lean.Elab.Tactic.Omega

/-!
# One clause and the clause loop

`clauseBody k` reads the length of the next clause (two or three), its literals
(`readLit`), computes the block of the clause (`setupClause`), emits the records of
its gadget with the endpoints taken from the slot registers (`emitEdges`), and
advances the clause index (`finishClause`). `passB k` runs it for every clause.
-/

@[expose] public section

namespace STACS2027.Registered

open Complexity
open Complexity.SAT
open Complexity.StackTableauProgram (Command Exec)
open Complexity.StackMachine (Registers set)
open Complexity.Restricted (writes exec_frame)

/-! ### The block of the clause -/

/-- `bnj := gadgetWidth k · (n + j)`. -/
def setupClause : Command K :=
  .seq (.copy R.n R.nj R.s) (.seq (.add R.j R.nj R.s)
    (.seq (.multiply R.nj R.W R.bnj R.mc R.s) (.clear R.nj)))

def setupModel (k : Nat) (r : Regs) : Regs :=
  set (set r R.bnj (unary (gadgetWidth k * ((r R.j).length + (r R.n).length)))) R.nj []

def setupCost (k L : Nat) : Nat :=
  (2 * L + 5 * L + 6) + (5 * L + 4) + (gadgetWidth k * (2 * L) + 5 * gadgetWidth k +
    gadgetWidth k * (5 * (2 * L) + 5) + 10) + (2 * L + 2)

theorem setupClause_writes (i : Reg) (h1 : i ≠ R.nj) (h2 : i ≠ R.bnj) (h3 : i ≠ R.mc) :
    writes setupClause i = false := by
  simp [setupClause, writes, h1, h2, h3]

theorem Spec.setupClause (k : Nat) {P : Regs → Prop} {L : Nat}
    (hb : ∀ r, P r → Base k r) (hn : ∀ r, P r → (r R.n).length ≤ L)
    (hj : ∀ r, P r → (r R.j).length ≤ L) (hnj : ∀ r, P r → (r R.nj).length ≤ 2 * L)
    (hbnj : ∀ r, P r → (r R.bnj).length ≤ gadgetWidth k * (2 * L)) :
    Spec Registered.setupClause P (setupCost k L) (fun r => some (setupModel k r)) := by
  let f₁ : Regs → Regs := fun r => set r R.nj (r R.n)
  let f₂ : Regs → Regs := fun r => set (f₁ r) R.nj (List.replicate (f₁ r R.j).length true ++ f₁ r R.nj)
  let f₃ : Regs → Regs := fun r => set (f₂ r) R.bnj (List.replicate (gadgetWidth k * (f₂ r R.nj).length) true)
  have s1 := Spec.copy (src := R.n) (dst := R.nj) (scratch := R.s) (by decide) (by decide) (by decide)
    (P := P) (a := L) (b := 2 * L) (fun r hr => (hb r hr).s) (fun r hr => ⟨hn r hr, hnj r hr⟩)
  have s2 := Spec.add (src := R.j) (dst := R.nj) (scratch := R.s) (by decide) (by decide) (by decide)
    (P := fun r' => ∃ r, P r ∧ r' = f₁ r) (a := L)
    (by rintro r' ⟨r, hr, rfl⟩; simp +decide [f₁, (hb r hr).s])
    (by rintro r' ⟨r, hr, rfl⟩; simpa +decide [f₁, StackMachine.set] using hj r hr)
  have s3 := Spec.multiply (src := R.nj) (factor := R.W) (dst := R.bnj) (counter := R.mc) (scratch := R.s)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (P := fun r' => ∃ r, P r ∧ r' = f₂ r) (w := gadgetWidth k) (a := 2 * L) (b := gadgetWidth k * (2 * L))
    (by rintro r' ⟨r, hr, rfl⟩; simp +decide [f₂, f₁, (hb r hr).s])
    (by rintro r' ⟨r, hr, rfl⟩; simp +decide [f₂, f₁, (hb r hr).W, unary])
    (by rintro r' ⟨r, hr, rfl⟩; simp +decide [f₂, f₁, (hb r hr).mc])
    (by
      rintro r' ⟨r, hr, rfl⟩
      have := hn r hr; have := hj r hr; have := hbnj r hr
      simp +decide [f₂, f₁, List.length_append, List.length_replicate]
      omega)
  have s4 := Spec.clear R.nj (P := fun r' => ∃ r, P r ∧ r' = f₃ r) (L := 2 * L) (by
    rintro r' ⟨r, hr, rfl⟩
    have := hn r hr; have := hj r hr
    simp +decide [f₃, f₂, f₁, StackMachine.set, List.length_append, List.length_replicate]
    omega)
  have h := s1.seq (fun r r' hr hm => ⟨r, hr, by simpa [f₁] using hm.symm⟩)
    (s2.seq (fun r' r'' hr' hm => by obtain ⟨r, hr, rfl⟩ := hr'; exact ⟨r, hr, by simpa [f₂] using hm.symm⟩)
      (s3.seq (fun r' r'' hr' hm => by obtain ⟨r, hr, rfl⟩ := hr'; exact ⟨r, hr, by simpa [f₃] using hm.symm⟩) s4))
  refine (h.mono (fun r hr => hr) ?_).congr ?_
  · simp only [setupCost]; omega
  · intro r hr
    simp only [Option.bind_some, Option.some.injEq, setupModel]
    funext i
    by_cases hi : i = R.nj
    · subst hi; simp +decide [StackMachine.set]
    · by_cases hi' : i = R.bnj
      · subst hi'
        simp +decide [StackMachine.set, List.length_append, List.length_replicate, unary, Nat.add_comm]
      · simp [StackMachine.set, hi, hi']

/-! ### Advancing the clause index and clearing the slots -/

/-- The registers cleared after a clause. -/
def slotRegs : List Reg :=
  [R.v0, R.v1, R.v2, R.sg0, R.sg1, R.sg2, R.b0, R.b1, R.b2, R.ef0, R.et0, R.ef1, R.et1, R.ef2, R.et2, R.bnj,
    R.cE]

def clearAll : List Reg → Command K
  | [] => .stop true
  | j :: js => .seq (.clear j) (clearAll js)

def clearAllModel : List Reg → Regs → Regs
  | [], r => r
  | j :: js, r => clearAllModel js (set r j [])

theorem clearAll_writes (js : List Reg) (i : Reg) (hi : i ∉ js) : writes (clearAll js) i = false := by
  induction js with
  | nil => simp [clearAll, writes]
  | cons j js ih =>
    simp only [List.mem_cons, not_or] at hi
    simp [clearAll, writes, hi.1, ih hi.2]

theorem Spec.clearAll (js : List Reg) {P : Regs → Prop} {L : Nat}
    (hL : ∀ r, P r → ∀ j ∈ js, (r j).length ≤ L) (hP : ∀ r j, P r → j ∈ js → P (set r j [])) :
    Spec (Registered.clearAll js) P (js.length * (L + 2) + 1) (fun r => some (clearAllModel js r)) := by
  induction js generalizing P with
  | nil =>
    have h := (Spec.stop_true P).congr (m' := fun r => some (clearAllModel [] r)) (fun r _ => rfl)
    simpa [Registered.clearAll] using h
  | cons j js ih =>
    have s1 := Spec.clear j (P := P) (L := L) (fun r hr => hL r hr j (by simp))
    have s2 := ih (P := P) (fun r hr j' hj' => hL r hr j' (by simp [hj']))
      (fun r j' hr hj' => hP r j' hr (by simp [hj']))
    have h := s1.seq (P₂ := P) (fun r r' hr hm => by
      simp only [Option.some.injEq] at hm; subst hm; exact hP r j hr (by simp)) s2
    refine (h.mono (fun r hr => hr) ?_).congr ?_
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
    · intro r _; simp [clearAllModel]

def finishClause : Command K := .seq (.push R.j true) (clearAll slotRegs)

def finishModel (r : Regs) : Regs := clearAllModel slotRegs (set r R.j (true :: r R.j))

def finishCost (k L : Nat) : Nat := 2 + (17 * (gadgetWidth k * (2 * L) + 6 + 2) + 1)

theorem finishClause_writes (i : Reg) (hi : i ≠ R.j) (hi' : i ∉ slotRegs) :
    writes finishClause i = false := by
  simp [finishClause, writes, hi, clearAll_writes slotRegs i hi']

theorem gadgetWidth_pos (k : Nat) : 0 < gadgetWidth k := by have := gadgetWidth_ge k; omega

/-- Work bounds hold after setting any slot register to a shorter word. -/
theorem Work.set_slot {k L : Nat} {r : Regs} (h : Work k L r) (j : Reg) (hj : j ∈ slotRegs)
    (w : SAT.Word) (hw : w.length ≤ (r j).length) : Work k L (set r j w) := by
  obtain ⟨hb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := h
  simp only [slotRegs, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> work_fields

/-! ### The gadget records of the clause -/

/-- The gadget of a clause with `len` literals (Section 5's `clauseGraph`). -/
def gadgetEdges (k len : Nat) : Graph := if len = 2 then clauseTwoGraph k else clauseThreeGraph k

/-- The endpoint of a local gadget vertex `a`: a variable port endpoint for the attachment
vertices of the slots `i < len`, a vertex of the clause's own block otherwise. -/
def clauseEndpoint (len a : Nat) : Endpoint :=
  match clausePortAt a with
  | some (i, side) => if i < len then .reg (slotB i) (slotE i side) else .const R.bnj a
  | none => .const R.bnj a

def clauseEdges (k len : Nat) : List (Endpoint × Endpoint) :=
  (gadgetEdges k len).map fun e => (clauseEndpoint len e.1, clauseEndpoint len e.2)

theorem clauseEndpoint_sane (len a : Nat) : (clauseEndpoint len a).Sane := by
  unfold clauseEndpoint
  split
  · split
    · simp [Endpoint.Sane]
    · exact ⟨by decide, by decide, by decide, by decide⟩
  · exact ⟨by decide, by decide, by decide, by decide⟩

theorem clauseEndpoint_constant (len a : Nat) : (clauseEndpoint len a).constant ≤ a := by
  unfold clauseEndpoint
  split
  · split
    · simp [Endpoint.constant]
    · simp [Endpoint.constant]
  · simp [Endpoint.constant]

theorem gadgetEdges_below (k len : Nat) : VerticesBelow (gadgetEdges k len) (gadgetWidth k) := by
  unfold gadgetEdges
  split
  · exact clauseTwoGraph_below k
  · exact clauseThreeGraph_below k

theorem clauseEndpoint_good {k L : Nat} {r : Regs} (h : Work k L r) (len a : Nat) :
    (clauseEndpoint len a).Good (gadgetWidth k * (2 * L)) 6 r := by
  unfold clauseEndpoint
  split
  · split
    · exact ⟨Nat.le_trans (h.b _) (Nat.mul_le_mul_left _ (by omega)), h.e _ _⟩
    · exact h.bnj
  · exact h.bnj

theorem Work.emitEdge {k L : Nat} {r : Regs} (h : Work k L r) (e₁ e₂ : Endpoint) :
    Work k L (emitEdgeModel e₁ e₂ r) := by
  obtain ⟨hb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := h
  simp only [emitEdgeModel]
  work_fields

/-- The number of records of a clause gadget is at most this bound. -/
def recordBound (k : Nat) : Nat := max (clauseTwoGraph k).length (clauseThreeGraph k).length

theorem clauseEdges_length_le (k len : Nat) : (clauseEdges k len).length ≤ recordBound k := by
  simp only [clauseEdges, List.length_map, gadgetEdges, recordBound]
  split
  · exact Nat.le_max_left _ _
  · exact Nat.le_max_right _ _

def clauseEmitCost (k L : Nat) : Nat :=
  recordBound k * edgeCost (gadgetWidth k * (2 * L)) 6 (gadgetWidth k) + 1

theorem Spec.clauseEmit (k len : Nat) {L : Nat} :
    Spec (Registered.emitEdges (clauseEdges k len)) (Work k L) (clauseEmitCost k L)
      (fun r => some (emitEdgesModel (clauseEdges k len) r)) := by
  have h := Spec.emitEdges (clauseEdges k len) (P := Work k L) (a := gadgetWidth k * (2 * L)) (b := 6)
    (c := gadgetWidth k)
    (by
      intro e he
      simp only [clauseEdges, List.mem_map] at he
      obtain ⟨d, _, rfl⟩ := he
      exact ⟨clauseEndpoint_sane _ _, clauseEndpoint_sane _ _⟩)
    (by
      intro e he
      simp only [clauseEdges, List.mem_map] at he
      obtain ⟨d, hd, rfl⟩ := he
      have := gadgetEdges_below k len d hd
      exact ⟨Nat.le_trans (clauseEndpoint_constant _ _) (by omega),
        Nat.le_trans (clauseEndpoint_constant _ _) (by omega)⟩)
    (fun r hr => hr.base.s) (fun r hr => hr.base.tmp) (fun r hr => hr.base.two)
    (by
      intro r hr e he
      simp only [clauseEdges, List.mem_map] at he
      obtain ⟨d, _, rfl⟩ := he
      exact ⟨clauseEndpoint_good hr _ _, clauseEndpoint_good hr _ _⟩)
    (fun r e₁ e₂ hr => hr.emitEdge e₁ e₂)
  refine h.mono (fun r hr => hr) ?_
  simp only [clauseEmitCost]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (clauseEdges_length_le k len)) 1

/-! ### The clause body -/

/-- The loop invariant of the clause loop, before the counter is popped: `G` records
per clause fit in the record budget `C`, and one more clause index fits in `L`. -/
structure ClauseInv (k L C : Nat) (r : Regs) : Prop where
  work : Work k L r
  jm : (r R.j).length + (r R.m).length + 1 ≤ L
  cnt : (r R.cnt).length + recordBound k * (r R.m).length ≤ C

/-- The precondition of the clause body, after the counter was popped. -/
structure BodyPre (k L C : Nat) (r : Regs) : Prop where
  work : Work k L r
  jm : (r R.j).length + (r R.m).length + 2 ≤ L
  cnt : (r R.cnt).length + recordBound k * (r R.m).length + recordBound k ≤ C

/-- After the emission, before the clause index is advanced. -/
structure BodyPost (k L C : Nat) (r : Regs) : Prop where
  work : Work k L r
  jm : (r R.j).length + (r R.m).length + 2 ≤ L
  cnt : (r R.cnt).length + recordBound k * (r R.m).length ≤ C

/-- The literals of the clause; the third only when `len = 3`. -/
def clauseLits (len : Nat) : Command K :=
  .seq (readLit 0) (.seq (readLit 1) (if len = 3 then readLit 2 else .stop true))

def clauseLitsModel (k len : Nat) (r : Regs) : Option Regs :=
  (readLitModel k 0 r).bind fun r₁ => (readLitModel k 1 r₁).bind fun r₂ =>
    if len = 3 then readLitModel k 2 r₂ else some r₂

/-- The processing of one clause of `len ∈ {2, 3}` literals. -/
def clauseK (k len : Nat) : Command K :=
  .seq (clauseLits len) (.seq setupClause (.seq (emitEdges (clauseEdges k len)) finishClause))

def clauseKModel (k len : Nat) (r : Regs) : Option Regs :=
  (clauseLitsModel k len r).bind fun r₁ =>
    some (finishModel (emitEdgesModel (clauseEdges k len) (setupModel k r₁)))

def clauseKCost (k L : Nat) : Nat :=
  3 * readLitCost k L + 1 + setupCost k L + clauseEmitCost k L + finishCost k L

theorem BodyPre.readLit {k L C : Nat} {i : Nat} (hi : i < 3) {r r' : Regs} (h : BodyPre k L C r)
    (hm : readLitModel k i r = some r') : BodyPre k L C r' := by
  have hw := Work.readLit hi h.work hm
  have hfr := (Spec.readLit k i hi (L := L)).frame h.work hm
  have hj : r' R.j = r R.j := hfr R.j (readLit_writes i R.j (by simp +decide))
  have hmm : r' R.m = r R.m := hfr R.m (readLit_writes i R.m (by simp +decide))
  have hc : r' R.cnt = r R.cnt := hfr R.cnt (readLit_writes i R.cnt (by simp +decide))
  exact ⟨hw, by rw [hj, hmm]; exact h.jm, by rw [hc, hmm]; exact h.cnt⟩

theorem Spec.clauseLits (k len : Nat) {L C : Nat} :
    Spec (Registered.clauseLits len) (BodyPre k L C) (3 * readLitCost k L + 1) (clauseLitsModel k len) := by
  have s0 : Spec (Registered.readLit 0) (BodyPre k L C) (readLitCost k L) (readLitModel k 0) :=
    (Spec.readLit k 0 (by decide) (L := L)).mono (fun r hr => hr.work) (Nat.le_refl _)
  have s1 : Spec (Registered.readLit 1) (BodyPre k L C) (readLitCost k L) (readLitModel k 1) :=
    (Spec.readLit k 1 (by decide) (L := L)).mono (fun r hr => hr.work) (Nat.le_refl _)
  have s2 : Spec (if len = 3 then Registered.readLit 2 else .stop true) (BodyPre k L C) (readLitCost k L + 1)
      (fun r => if len = 3 then readLitModel k 2 r else some r) := by
    by_cases h3 : len = 3
    · simp only [h3, ↓reduceIte]
      exact (Spec.readLit k 2 (by decide) (L := L)).mono (fun r hr => hr.work) (by omega)
    · simp only [h3, ↓reduceIte]
      exact (Spec.stop_true _).mono (fun r hr => hr) (by omega)
  have h := s0.seq (P₂ := BodyPre k L C) (fun r r' hr hm => hr.readLit (by decide) hm)
    (s1.seq (P₂ := BodyPre k L C) (fun r r' hr hm => hr.readLit (by decide) hm) s2)
  exact (h.mono (fun r hr => hr) (by omega)).congr (fun r _ => rfl)

theorem BodyPre.clauseLits {k L C len : Nat} {r r' : Regs} (h : BodyPre k L C r)
    (hm : clauseLitsModel k len r = some r') : BodyPre k L C r' := by
  unfold clauseLitsModel at hm
  cases h₀ : readLitModel k 0 r with
  | none => rw [h₀] at hm; simp at hm
  | some r₀ =>
    rw [h₀, Option.bind_some] at hm
    cases h₁ : readLitModel k 1 r₀ with
    | none => rw [h₁] at hm; simp at hm
    | some r₁ =>
      rw [h₁, Option.bind_some] at hm
      have hp₁ := (h.readLit (by decide) h₀).readLit (by decide) h₁
      by_cases h3 : len = 3
      · rw [ite_eq_left h3] at hm
        exact hp₁.readLit (by decide) hm
      · rw [ite_eq_right h3] at hm
        simp only [Option.some.injEq] at hm
        subst hm
        exact hp₁

theorem BodyPre.setup {k L C : Nat} {r : Regs} (h : BodyPre k L C r) : BodyPre k L C (setupModel k r) := by
  obtain ⟨hw, hjm, hc⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨hb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25⟩ := hw
    simp only [setupModel]
    work_fields
    all_goals exact Nat.mul_le_mul_left _ (by omega)
  · simpa +decide [setupModel, StackMachine.set] using hjm
  · simpa +decide [setupModel, StackMachine.set] using hc

theorem BodyPre.emit {k L C len : Nat} {r : Regs} (h : BodyPre k L C r) :
    BodyPost k L C (emitEdgesModel (clauseEdges k len) r) := by
  obtain ⟨hw, hjm, hc⟩ := h
  have hlen := clauseEdges_length_le k len
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨hb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25⟩ := hw
    simp only [emitEdgesModel]
    work_fields
  · simpa +decide [emitEdgesModel, StackMachine.set] using hjm
  · simp +decide [emitEdgesModel, StackMachine.set, List.length_append, unary_length]
    omega

theorem BodyPost.finish {k L C : Nat} {r : Regs} (h : BodyPost k L C r) : ClauseInv k L C (finishModel r) := by
  obtain ⟨hw, hjm, hc⟩ := h
  have hj : Work k L (set r R.j (true :: r R.j)) := by
    obtain ⟨hb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25⟩ := hw
    work_fields
  refine ⟨?_, ?_, ?_⟩
  · simp only [finishModel, slotRegs, clearAllModel]
    apply Work.set_slot _ R.cE (by simp [slotRegs]) [] (by simp)
    apply Work.set_slot _ R.bnj (by simp [slotRegs]) [] (by simp)
    apply Work.set_slot _ R.et2 (by simp [slotRegs]) [] (by simp)
    apply Work.set_slot _ R.ef2 (by simp [slotRegs]) [] (by simp)
    apply Work.set_slot _ R.et1 (by simp [slotRegs]) [] (by simp)
    apply Work.set_slot _ R.ef1 (by simp [slotRegs]) [] (by simp)
    apply Work.set_slot _ R.et0 (by simp [slotRegs]) [] (by simp)
    apply Work.set_slot _ R.ef0 (by simp [slotRegs]) [] (by simp)
    apply Work.set_slot _ R.b2 (by simp [slotRegs]) [] (by simp)
    apply Work.set_slot _ R.b1 (by simp [slotRegs]) [] (by simp)
    apply Work.set_slot _ R.b0 (by simp [slotRegs]) [] (by simp)
    apply Work.set_slot _ R.sg2 (by simp [slotRegs]) [] (by simp)
    apply Work.set_slot _ R.sg1 (by simp [slotRegs]) [] (by simp)
    apply Work.set_slot _ R.sg0 (by simp [slotRegs]) [] (by simp)
    apply Work.set_slot _ R.v2 (by simp [slotRegs]) [] (by simp)
    apply Work.set_slot _ R.v1 (by simp [slotRegs]) [] (by simp)
    apply Work.set_slot _ R.v0 (by simp [slotRegs]) [] (by simp)
    exact hj
  · simp +decide [finishModel, slotRegs, clearAllModel, StackMachine.set, List.length_cons]
    omega
  · simpa +decide [finishModel, slotRegs, clearAllModel, StackMachine.set] using hc

theorem Spec.clauseK (k len : Nat) {L C : Nat} :
    Spec (Registered.clauseK k len) (BodyPre k L C) (clauseKCost k L) (clauseKModel k len) := by
  have s1 := Spec.clauseLits k len (L := L) (C := C)
  have s2 := Spec.setupClause k (P := BodyPre k L C) (L := L) (fun r hr => hr.work.base)
    (fun r hr => hr.work.n) (fun r hr => by have := hr.jm; omega) (fun r hr => hr.work.nj)
    (fun r hr => hr.work.bnj)
  have s3 := (Spec.clauseEmit k len (L := L)).mono (fun r (hr : BodyPre k L C r) => hr.work) (Nat.le_refl _)
  have s4 : Spec finishClause (BodyPost k L C) (finishCost k L) (fun r => some (finishModel r)) := by
    have c1 := Spec.push R.j true (BodyPost k L C)
    have c2 := Spec.clearAll slotRegs (P := Work k L) (L := gadgetWidth k * (2 * L) + 6)
      (by
        intro r hw j hj
        have hW := gadgetWidth_pos k
        have h2L : gadgetWidth k * L ≤ gadgetWidth k * (2 * L) := Nat.mul_le_mul_left _ (by omega)
        have hL1 : L ≤ gadgetWidth k * (2 * L) := by
          have := gadgetWidth_ge k
          have : 24 * (2 * L) ≤ gadgetWidth k * (2 * L) := Nat.mul_le_mul_right _ this
          omega
        have hv0 := hw.v0; have hv1 := hw.v1; have hv2 := hw.v2
        have hs0 := hw.sg0; have hs1 := hw.sg1; have hs2 := hw.sg2
        have hb0 := hw.b0; have hb1 := hw.b1; have hb2 := hw.b2
        have he0 := hw.ef0; have he1 := hw.et0; have he2 := hw.ef1
        have he3 := hw.et1; have he4 := hw.ef2; have he5 := hw.et2
        have hbnj := hw.bnj
        have hcE := hw.cE
        simp only [slotRegs, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl
        all_goals omega)
      (fun r j hw hj => hw.set_slot j hj [] (by simp))
    have h := c1.seq (P₂ := Work k L) (fun r r' hr hm => by
      simp only [Option.some.injEq] at hm
      subst hm
      obtain ⟨hw, hjm, hc⟩ := hr
      obtain ⟨hb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
        h20, h21, h22, h23, h24, h25⟩ := hw
      work_fields) c2
    refine (h.mono (fun r hr => hr) ?_).congr ?_
    · simp only [finishCost, slotRegs, List.length_cons, List.length_nil]; omega
    · intro r _; rfl
  have h := s1.seq (P₂ := BodyPre k L C) (fun r r' hr hm => hr.clauseLits hm)
    (s2.seq (P₂ := BodyPre k L C) (fun r r' hr hm => by
        simp only [Option.some.injEq] at hm; subst hm; exact hr.setup)
      (s3.seq (P₂ := BodyPost k L C) (fun r r' hr hm => by
        simp only [Option.some.injEq] at hm; subst hm; exact hr.emit) s4))
  refine (h.mono (fun r hr => hr) ?_).congr ?_
  · simp only [clauseKCost]; omega
  · intro r _
    simp only [clauseKModel, Option.bind_some]

theorem BodyPre.clauseK {k L C len : Nat} {r r' : Regs} (h : BodyPre k L C r)
    (hm : clauseKModel k len r = some r') : ClauseInv k L C r' := by
  unfold clauseKModel at hm
  cases h₁ : clauseLitsModel k len r with
  | none => rw [h₁] at hm; simp at hm
  | some r₁ =>
    rw [h₁, Option.bind_some] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact ((h.clauseLits h₁).setup.emit).finish

end STACS2027.Registered

namespace STACS2027.Registered

open Complexity
open Complexity.SAT
open Complexity.StackTableauProgram (Command Exec)
open Complexity.StackMachine (Registers set)
open Complexity.Restricted (writes exec_frame)

/-! ### Dispatch on the clause length -/

/-- Run `two` when `len = 1 1`, `three` when `len = 1 1 1`, and fail otherwise;
`len` is emptied. -/
def caseLen (two three : Command K) : Command K :=
  .branch R.len (.stop false) (.stop false)
    (.seq (.pop R.len) (.branch R.len (.stop false) (.stop false)
      (.seq (.pop R.len) (.branch R.len two (.stop false)
        (.seq (.pop R.len) (.branch R.len three (.stop false) (.stop false)))))))

def caseLenModel (m₂ m₃ : Regs → Option Regs) (r : Regs) : Option Regs :=
  match r R.len with
  | [true, true] => m₂ (set r R.len [])
  | [true, true, true] => m₃ (set r R.len [])
  | _ => none

theorem caseLen_writes (two three : Command K) (i : Reg) (hi : i ≠ R.len)
    (h₂ : writes two i = false) (h₃ : writes three i = false) : writes (caseLen two three) i = false := by
  simp [caseLen, writes, hi, h₂, h₃]

theorem Spec.caseLen {two three : Command K} {P : Regs → Prop} {cost : Nat}
    {m₂ m₃ : Regs → Option Regs} (hP : ∀ r, P r → P (set r R.len []))
    (h₂ : Spec two P cost m₂) (h₃ : Spec three P cost m₃) :
    Spec (Registered.caseLen two three) P (cost + 12) (caseLenModel m₂ m₃) := by
  intro r hr
  have hset : ∀ (w w' : SAT.Word), set (set r R.len w) R.len w' = set r R.len w' := by
    intro w w'
    funext j
    by_cases hj : j = R.len
    · subst hj; simp [StackMachine.set]
    · simp [StackMachine.set, hj]
  cases hl : r R.len with
  | nil =>
    exact ⟨2, (false, r), Exec.branchEmpty hl (Exec.stop false r), by omega, by simp [caseLenModel, hl, Realizes]⟩
  | cons b₁ t₁ =>
    cases b₁ with
    | false =>
      exact ⟨2, (false, r), Exec.branchZero hl (Exec.stop false r), by omega, by simp [caseLenModel, hl, Realizes]⟩
    | true =>
      let r₁ := set r R.len t₁
      have hp₁ : Exec (.pop R.len) r 2 (true, r₁) := by have := Exec.pop R.len r; rwa [hl] at this
      have hl₁ : r₁ R.len = t₁ := by simp [r₁]
      cases t₁ with
      | nil =>
        exact ⟨2 + 2 + 1, (false, r₁), Exec.branchOne hl (Exec.seq hp₁ (Exec.branchEmpty hl₁ (Exec.stop false r₁))),
          by omega, by simp [caseLenModel, hl, Realizes]⟩
      | cons b₂ t₂ =>
        cases b₂ with
        | false =>
          exact ⟨2 + 2 + 1, (false, r₁), Exec.branchOne hl (Exec.seq hp₁ (Exec.branchZero hl₁ (Exec.stop false r₁))),
            by omega, by simp [caseLenModel, hl, Realizes]⟩
        | true =>
          let r₂ := set r₁ R.len t₂
          have hp₂ : Exec (.pop R.len) r₁ 2 (true, r₂) := by have := Exec.pop R.len r₁; rwa [hl₁] at this
          have hl₂ : r₂ R.len = t₂ := by simp [r₂]
          have hr₂ : r₂ = set r R.len t₂ := by simp only [r₂, r₁]; exact hset _ _
          cases t₂ with
          | nil =>
            obtain ⟨t, res, he, ht, hres⟩ := h₂ r₂ (by rw [hr₂]; exact hP r hr)
            refine ⟨_, res, Exec.branchOne hl (Exec.seq hp₁ (Exec.branchOne hl₁
              (Exec.seq hp₂ (Exec.branchEmpty hl₂ he)))), by omega, ?_⟩
            simpa [caseLenModel, hl, hr₂] using hres
          | cons b₃ t₃ =>
            cases b₃ with
            | false =>
              exact ⟨_, (false, r₂), Exec.branchOne hl (Exec.seq hp₁ (Exec.branchOne hl₁
                (Exec.seq hp₂ (Exec.branchZero hl₂ (Exec.stop false r₂))))), by omega,
                by simp [caseLenModel, hl, Realizes]⟩
            | true =>
              let r₃ := set r₂ R.len t₃
              have hp₃ : Exec (.pop R.len) r₂ 2 (true, r₃) := by have := Exec.pop R.len r₂; rwa [hl₂] at this
              have hl₃ : r₃ R.len = t₃ := by simp [r₃]
              have hr₃ : r₃ = set r R.len t₃ := by simp only [r₃]; rw [hr₂]; exact hset _ _
              cases t₃ with
              | nil =>
                obtain ⟨t, res, he, ht, hres⟩ := h₃ r₃ (by rw [hr₃]; exact hP r hr)
                refine ⟨_, res, Exec.branchOne hl (Exec.seq hp₁ (Exec.branchOne hl₁
                  (Exec.seq hp₂ (Exec.branchOne hl₂ (Exec.seq hp₃ (Exec.branchEmpty hl₃ he)))))), by omega, ?_⟩
                simpa [caseLenModel, hl, hr₃] using hres
              | cons b₄ t₄ =>
                have hlast : Exec (.branch R.len three (.stop false) (.stop false)) r₃ 2 (false, r₃) := by
                  cases b₄ with
                  | false => exact Exec.branchZero hl₃ (Exec.stop false r₃)
                  | true => exact Exec.branchOne hl₃ (Exec.stop false r₃)
                refine ⟨2 + (2 + (2 + 2 + 1) + 1) + 1, (false, r₃), Exec.branchOne hl (Exec.seq hp₁
                  (Exec.branchOne hl₁ (Exec.seq hp₂ (Exec.branchOne hl₂ (Exec.seq hp₃ hlast))))), ?_,
                  by simp [caseLenModel, hl, Realizes]⟩
                omega

/-! ### The clause body -/

def clauseBody (k : Nat) : Command K :=
  .seq (readUnary R.inB R.len) (caseLen (clauseK k 2) (clauseK k 3))

def clauseBodyModel (k : Nat) (r : Regs) : Option Regs :=
  (readUnaryModel R.inB R.len r).bind (caseLenModel (clauseKModel k 2) (clauseKModel k 3))

def clauseBodyCost (k L : Nat) : Nat := (9 * L + 10) + (clauseKCost k L + 12)

theorem BodyPre.set_len {k L C : Nat} {r : Regs} (h : BodyPre k L C r) (w : SAT.Word)
    (hw : w.length ≤ L) : BodyPre k L C (set r R.len w) := by
  obtain ⟨hw', hjm, hc⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨hb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25⟩ := hw'
    work_fields
  · simpa +decide [StackMachine.set] using hjm
  · simpa +decide [StackMachine.set] using hc

theorem BodyPre.readLen {k L C : Nat} {r r' : Regs} (h : BodyPre k L C r)
    (hm : readUnaryModel R.inB R.len r = some r') : BodyPre k L C r' := by
  unfold readUnaryModel at hm
  cases hn : readNat (r R.inB) with
  | none => rw [hn] at hm; simp at hm
  | some p =>
    obtain ⟨v, rest⟩ := p
    rw [hn] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    have hlen := congrArg List.length (readNat_eq_some hn)
    simp only [List.length_append, SATBounds.writeNat_length] at hlen
    have hsize := h.work.size
    have h1 : BodyPre k L C (set r R.inB rest) := by
      obtain ⟨hw', hjm, hc⟩ := h
      refine ⟨?_, ?_, ?_⟩
      · obtain ⟨hb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
          h20, h21, h22, h23, h24, h25⟩ := hw'
        work_fields
      · simpa +decide [StackMachine.set] using hjm
      · simpa +decide [StackMachine.set] using hc
    exact h1.set_len _ (by simp only [unary_length]; omega)

theorem Spec.clauseBody (k : Nat) {L C : Nat} :
    Spec (Registered.clauseBody k) (BodyPre k L C) (clauseBodyCost k L) (clauseBodyModel k) := by
  have s1 := Spec.readUnary R.inB R.len (by decide) (by decide) (by decide) (P := BodyPre k L C) (L := L)
    (fun r hr => hr.work.base.g) (fun r hr => ⟨by have := hr.work.size; omega, hr.work.len⟩)
  have s2 := Spec.caseLen (P := BodyPre k L C) (fun r hr => hr.set_len [] (by simp))
    (Spec.clauseK k 2 (L := L) (C := C)) (Spec.clauseK k 3 (L := L) (C := C))
  have h := s1.seq (P₂ := BodyPre k L C) (fun r r' hr hm => hr.readLen hm) s2
  exact (h.mono (fun r hr => hr) (by simp only [clauseBodyCost]; omega)).congr (fun r _ => rfl)

theorem BodyPre.clauseBody {k L C : Nat} {r r' : Regs} (h : BodyPre k L C r)
    (hm : clauseBodyModel k r = some r') : ClauseInv k L C r' := by
  unfold clauseBodyModel at hm
  cases h₁ : readUnaryModel R.inB R.len r with
  | none => rw [h₁] at hm; simp at hm
  | some r₁ =>
    rw [h₁, Option.bind_some] at hm
    have hp := h.readLen h₁
    unfold caseLenModel at hm
    split at hm
    · exact (hp.set_len [] (by simp)).clauseK hm
    · exact (hp.set_len [] (by simp)).clauseK hm
    · simp at hm

theorem clauseBody_writes (k : Nat) (i : Reg) (hi : i ∉ [R.inB, R.len, R.g, R.v0, R.v1, R.v2, R.sg0,
    R.sg1, R.sg2, R.done, R.dc, R.scan, R.sv, R.cE, R.t1, R.t2, R.sc, R.ef0, R.et0, R.ef1, R.et1,
    R.ef2, R.et2, R.b0, R.b1, R.b2, R.mc, R.nj, R.bnj, R.out, R.tmp, R.cnt, R.j]) :
    writes (clauseBody k) i = false := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33⟩ := hi
  have hlit : ∀ i', i' < 3 → writes (readLit i') i = false := by
    intro i' hi'
    apply readLit_writes
    rcases slot_cases hi' with rfl | rfl | rfl <;> simp [slotS, slotV, slotE, slotB, *]
  have hK : ∀ len, writes (clauseK k len) i = false := by
    intro len
    simp only [clauseK, clauseLits, writes, Bool.or_eq_false_iff]
    refine ⟨⟨hlit 0 (by decide), hlit 1 (by decide), ?_⟩, setupClause_writes i h28 h29 h27,
      emitEdges_writes _ i h30 h31 h32, finishClause_writes i h33 (by simp [slotRegs, *])⟩
    split
    · exact hlit 2 (by decide)
    · rfl
  simp only [clauseBody, writes, Bool.or_eq_false_iff]
  exact ⟨readUnary_writes _ _ _ h1 h2 h3, caseLen_writes _ _ i h2 (hK 2) (hK 3)⟩

/-! ### The clause loop -/

/-- Read the clause count, then process every clause. -/
def passB (k : Nat) : Command K := .seq (readUnary R.inB R.m) (.repeat R.m (clauseBody k))

def passBModel (k : Nat) (r : Regs) : Option Regs :=
  (readUnaryModel R.inB R.m r).bind fun r₁ => iter (clauseBodyModel k) R.m (r₁ R.m).length r₁

def passBCost (k L : Nat) : Nat := (9 * L + 10) + (L * (clauseBodyCost k L + 1) + 2)

/-- The record budget: the variable gadgets emitted before the clause loop, and at most
`recordBound k` records per clause. -/
def recordBudget (k L : Nat) : Nat := (variableGraph k).length * L + recordBound k * L

/-- The precondition of the clause loop. -/
structure PassBPre (k L : Nat) (r : Regs) : Prop where
  work : Work k L r
  j : r R.j = []
  m : (r R.m).length ≤ L
  cnt : (r R.cnt).length ≤ (variableGraph k).length * L

theorem ClauseInv.pop {k L C : Nat} {r : Regs} (h : ClauseInv k L C r) (b : Bool) (tail : SAT.Word)
    (hm : r R.m = b :: tail) : BodyPre k L C (set r R.m tail) := by
  obtain ⟨hw, hjm, hc⟩ := h
  rw [hm] at hjm hc
  simp only [List.length_cons] at hjm hc
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨hb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25⟩ := hw
    work_fields
  · simp +decide [StackMachine.set]; omega
  · simp +decide [StackMachine.set]
    rw [Nat.mul_succ] at hc
    omega

theorem PassBPre.start {k L : Nat} {r r' : Regs} (h : PassBPre k L r)
    (hm : readUnaryModel R.inB R.m r = some r') : ClauseInv k L (recordBudget k L) r' := by
  unfold readUnaryModel at hm
  cases hn : readNat (r R.inB) with
  | none => rw [hn] at hm; simp at hm
  | some p =>
    obtain ⟨v, rest⟩ := p
    rw [hn] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    have hlen := congrArg List.length (readNat_eq_some hn)
    simp only [List.length_append, SATBounds.writeNat_length] at hlen
    obtain ⟨hw, hj, hmm, hc⟩ := h
    have hsize := hw.size
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨hb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
        h20, h21, h22, h23, h24, h25⟩ := hw
      work_fields
    · simp +decide [StackMachine.set, hj]; omega
    · simp +decide [StackMachine.set, recordBudget]
      have : recordBound k * v ≤ recordBound k * L := Nat.mul_le_mul_left _ (by omega)
      omega

theorem Spec.passB (k : Nat) {L : Nat} :
    Spec (Registered.passB k) (PassBPre k L) (passBCost k L) (passBModel k) := by
  have s1 := Spec.readUnary R.inB R.m (by decide) (by decide) (by decide) (P := PassBPre k L) (L := L)
    (fun r hr => hr.work.base.g) (fun r hr => ⟨by have := hr.work.size; omega, hr.m⟩)
  have s2 := Spec.repeat (j := R.m) (body := Registered.clauseBody k) (P := ClauseInv k L (recordBudget k L))
    (Pb := BodyPre k L (recordBudget k L)) (L := L)
    (clauseBody_writes k R.m (by decide))
    (fun r b tail hr hm => hr.pop b tail hm)
    (fun r b tail r' hr hm hb => (hr.pop b tail hm).clauseBody hb)
    (fun r hr => by have := hr.jm; omega)
    (Spec.clauseBody k)
  have h := s1.seq (P₂ := ClauseInv k L (recordBudget k L)) (fun r r' hr hm => hr.start hm) s2
  exact (h.mono (fun r hr => hr) (by simp only [passBCost]; omega)).congr (fun r _ => rfl)

end STACS2027.Registered
