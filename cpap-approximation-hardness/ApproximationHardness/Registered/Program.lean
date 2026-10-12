module

public import ApproximationHardness.Registered.Clause
import Lean.Elab.Tactic.Omega

/-!
# The variable gadgets and the first pass

* `varLoop k` emits the records of the `n` variable gadgets, `n = variableBound f`;
* `passA` computes `n` as the maximum of `var + 1` over all literals of the input;
* `passB` (in `Clause.lean`) emits the clause gadgets.

`Machine.lean` assembles them (`main k`, `program k`) and proves that the compiled
single-tape machine halts within a polynomial number of steps on every input
(`polyTime_instanceMapWord`, the registered foundation's `PolyTime`).
-/

@[expose] public section

namespace STACS2027.Registered

open Complexity
open Complexity.SAT
open Complexity.StackTableauProgram (Command Exec)
open Complexity.StackMachine (Registers set)
open Complexity.Restricted (writes exec_frame)

/-! ### The variable gadgets -/

/-- The edges of the variable gadget, with both endpoints in the block `vb`. -/
def variableEdges (k : Nat) : List (Endpoint × Endpoint) :=
  (variableGraph k).map fun e => (.const R.vb e.1, .const R.vb e.2)

/-- Emit one variable gadget and advance the block by the gadget width. -/
def varBody (k : Nat) : Command K := .seq (emitEdges (variableEdges k)) (.add R.W R.vb R.s)

def varBodyModel (k : Nat) (r : Regs) : Option Regs :=
  some (set (emitEdgesModel (variableEdges k) r) R.vb
    (List.replicate (emitEdgesModel (variableEdges k) r R.W).length true ++
      emitEdgesModel (variableEdges k) r R.vb))

/-- `vc := n`, then one gadget per count. -/
def varLoop (k : Nat) : Command K := .seq (.copy R.n R.vc R.s) (.repeat R.vc (varBody k))

def varLoopModel (k : Nat) (r : Regs) : Option Regs :=
  iter (varBodyModel k) R.vc (r R.n).length (set r R.vc (r R.n))

def varBodyCost (k L : Nat) : Nat :=
  (variableGraph k).length * edgeCost (gadgetWidth k * L) 0 (gadgetWidth k) + 1 + (5 * gadgetWidth k + 4)

def varLoopCost (k L : Nat) : Nat := (L + 5 * L + 6) + (L * (varBodyCost k L + 1) + 2)

/-- The loop invariant of the variable loop (before the counter is popped). -/
structure VarInv (k L : Nat) (r : Regs) : Prop where
  base : Base k r
  vb : (r R.vb).length + gadgetWidth k * (r R.vc).length ≤ gadgetWidth k * L
  cnt : (r R.cnt).length + (variableGraph k).length * (r R.vc).length ≤ (variableGraph k).length * L
  vc : (r R.vc).length ≤ L

/-- After the counter was popped. -/
structure VarPre (k L : Nat) (r : Regs) : Prop where
  base : Base k r
  vb : (r R.vb).length + gadgetWidth k * (r R.vc).length + gadgetWidth k ≤ gadgetWidth k * L
  cnt : (r R.cnt).length + (variableGraph k).length * (r R.vc).length + (variableGraph k).length ≤
    (variableGraph k).length * L
  vc : (r R.vc).length + 1 ≤ L

theorem VarInv.pop {k L : Nat} {r : Regs} (h : VarInv k L r) (b : Bool) (tail : SAT.Word)
    (hvc : r R.vc = b :: tail) : VarPre k L (set r R.vc tail) := by
  obtain ⟨hb, h1, h2, h3⟩ := h
  rw [hvc] at h1 h2 h3
  simp only [List.length_cons, Nat.mul_succ] at h1 h2 h3
  refine ⟨hb.set R.vc (by decide) _, ?_, ?_, ?_⟩
  · simp +decide [StackMachine.set]; omega
  · simp +decide [StackMachine.set]; omega
  · simp +decide [StackMachine.set]; omega

theorem variableEdges_sane (k : Nat) : ∀ e ∈ variableEdges k, e.1.Sane ∧ e.2.Sane := by
  intro e he
  simp only [variableEdges, List.mem_map] at he
  obtain ⟨d, _, rfl⟩ := he
  exact ⟨⟨by decide, by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩⟩

theorem variableEdges_constant (k : Nat) :
    ∀ e ∈ variableEdges k, e.1.constant ≤ gadgetWidth k ∧ e.2.constant ≤ gadgetWidth k := by
  intro e he
  simp only [variableEdges, List.mem_map] at he
  obtain ⟨d, hd, rfl⟩ := he
  have := variableGraph_below k d hd
  exact ⟨by simp only [Endpoint.constant]; omega, by simp only [Endpoint.constant]; omega⟩

/-- The bounds needed while a variable gadget is emitted. -/
def VarEmit (k L : Nat) (r : Regs) : Prop :=
  Base k r ∧ (r R.vb).length + gadgetWidth k * (r R.vc).length + gadgetWidth k ≤ gadgetWidth k * L

theorem Spec.varBody (k : Nat) {L : Nat} :
    Spec (Registered.varBody k) (VarPre k L) (varBodyCost k L) (varBodyModel k) := by
  have s1 := Spec.emitEdges (variableEdges k) (variableEdges_sane k) (P := VarEmit k L)
    (a := gadgetWidth k * L) (b := 0) (c := gadgetWidth k) (variableEdges_constant k)
    (fun r hr => hr.1.s) (fun r hr => hr.1.tmp) (fun r hr => hr.1.two)
    (by
      intro r hr e he
      simp only [variableEdges, List.mem_map] at he
      obtain ⟨d, _, rfl⟩ := he
      have := hr.2
      exact ⟨by simp only [Endpoint.Good]; omega, by simp only [Endpoint.Good]; omega⟩)
    (by
      intro r e₁ e₂ hr
      obtain ⟨hb, h1⟩ := hr
      refine ⟨hb.of_eq ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩ <;> simp +decide [emitEdgeModel, StackMachine.set]
      exact h1)
  have s1' := s1.mono (fun r (hr : VarPre k L r) => ⟨hr.base, hr.vb⟩) (Nat.le_refl _)
  have s2 := Spec.add (src := R.W) (dst := R.vb) (scratch := R.s) (by decide) (by decide) (by decide)
    (P := fun r' => ∃ r, VarPre k L r ∧ r' = emitEdgesModel (variableEdges k) r) (a := gadgetWidth k)
    (by rintro r' ⟨r, hr, rfl⟩; simp +decide [emitEdgesModel, StackMachine.set, hr.base.s])
    (by rintro r' ⟨r, hr, rfl⟩; simp +decide [emitEdgesModel, StackMachine.set, hr.base.W])
  have h := s1'.seq (fun r r' hr hm => ⟨r, hr, by simpa using hm.symm⟩) s2
  refine (h.mono (fun r hr => hr) ?_).congr ?_
  · simp only [varBodyCost, List.length_map, variableEdges]; omega
  · intro r _; rfl

theorem VarPre.body {k L : Nat} {r r' : Regs} (h : VarPre k L r) (hm : varBodyModel k r = some r') :
    VarInv k L r' := by
  simp only [varBodyModel, Option.some.injEq] at hm
  subst hm
  obtain ⟨hb, h1, h2, h3⟩ := h
  have hlen : (variableEdges k).length = (variableGraph k).length := by simp [variableEdges]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine hb.of_eq ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp +decide [emitEdgesModel, StackMachine.set]
  · simp +decide [emitEdgesModel, StackMachine.set, hb.W, List.length_append, unary_length]; omega
  · simp +decide [emitEdgesModel, StackMachine.set, List.length_append, unary_length, hlen]; omega
  · simp +decide [emitEdgesModel, StackMachine.set]; omega

theorem varBody_writes (k : Nat) (i : Reg) (hi : i ≠ R.out ∧ i ≠ R.tmp ∧ i ≠ R.cnt ∧ i ≠ R.vb) :
    writes (varBody k) i = false := by
  obtain ⟨h1, h2, h3, h4⟩ := hi
  simp [varBody, writes, emitEdges_writes _ i h1 h2 h3, h4]

/-- The precondition of the variable loop. -/
structure VarLoopPre (k L : Nat) (r : Regs) : Prop where
  base : Base k r
  n : (r R.n).length ≤ L
  vb : r R.vb = []
  vc : (r R.vc).length ≤ L
  cnt : r R.cnt = []

theorem VarLoopPre.start {k L : Nat} {r : Regs} (h : VarLoopPre k L r) : VarInv k L (set r R.vc (r R.n)) := by
  obtain ⟨hb, h1, h2, h3, h4⟩ := h
  refine ⟨hb.set R.vc (by decide) _, ?_, ?_, ?_⟩ <;> simp +decide [StackMachine.set, h2, h4]
  · exact Nat.mul_le_mul_left _ h1
  · exact Nat.mul_le_mul_left _ h1
  · exact h1

theorem Spec.varLoop (k : Nat) {L : Nat} :
    Spec (Registered.varLoop k) (VarLoopPre k L) (varLoopCost k L) (varLoopModel k) := by
  have s1 := Spec.copy (src := R.n) (dst := R.vc) (scratch := R.s) (by decide) (by decide) (by decide)
    (P := VarLoopPre k L) (a := L) (b := L) (fun r hr => hr.base.s) (fun r hr => ⟨hr.n, hr.vc⟩)
  have s2 := Spec.repeat (j := R.vc) (body := Registered.varBody k) (P := VarInv k L) (Pb := VarPre k L) (L := L)
    (varBody_writes k R.vc (by decide))
    (fun r b tail hr hvc => hr.pop b tail hvc)
    (fun r b tail r' hr hvc hm => (hr.pop b tail hvc).body hm)
    (fun r hr => hr.vc)
    (Spec.varBody k)
  have h := s1.seq (P₂ := VarInv k L) (fun r r' hr hm => by
    simp only [Option.some.injEq] at hm; subst hm; exact hr.start) s2
  refine (h.mono (fun r hr => hr) (by simp only [varLoopCost]; omega)).congr ?_
  intro r _
  simp only [Option.bind_some, varLoopModel]
  simp +decide [StackMachine.set]

theorem VarLoopPre.run {k L : Nat} {r r' : Regs} (h : VarLoopPre k L r) (hm : varLoopModel k r = some r') :
    VarInv k L r' :=
  iter_invariant (j := R.vc) (P := VarInv k L) (m := varBodyModel k)
    (fun _ b tail _ hr hvc hm => (hr.pop b tail hvc).body hm) _ _ _ h.start hm

/-! ### The first pass: the number of variables -/

/-- `n := max n (x + 1)` where `x` holds the variable just read; then `x` is emptied. -/
def maxStep : Command K :=
  .seq (.push R.x true) (.seq (.ifThenElse (leU R.x R.n) (.stop true) (.copy R.x R.n R.s)) (.clear R.x))

/-- After the sign bit: read the variable and update the maximum. -/
def litA' : Command K := .seq (readUnary R.inA R.x) maxStep

/-- One literal of the first pass. -/
def litA : Command K :=
  .branch R.inA (.stop false) (.seq (.pop R.inA) litA') (.seq (.pop R.inA) litA')

def litAModel (r : Regs) : Option Regs :=
  match readLiteral (r R.inA) with
  | some (l, rest) => some (set (set (set r R.inA rest) R.n
      (if l.var + 1 ≤ (r R.n).length then r R.n else unary (l.var + 1))) R.x [])
  | none => none

def litACost (L : Nat) : Nat := 9 * L + 10 + (2 + (15 * (L + 1) + 18 + (L + 5 * (L + 1) + 6)) + (L + 1 + 2)) + 5

/-- The invariant of the first pass. -/
structure AInv (k L : Nat) (r : Regs) : Prop where
  base : Base k r
  inA : (r R.inA).length ≤ L
  n : (r R.n).length ≤ L
  x : r R.x = []
  m : (r R.m).length ≤ L
  len : (r R.len).length ≤ L

theorem AInv.set_inA {k L : Nat} {r : Regs} (h : AInv k L r) (w : SAT.Word) (hw : w.length ≤ L) :
    AInv k L (set r R.inA w) := by
  obtain ⟨hb, h1, h2, h3, h4, h5⟩ := h
  exact ⟨hb.set R.inA (by decide) _, by simpa [StackMachine.set] using hw,
    by simpa +decide [StackMachine.set] using h2, by simpa +decide [StackMachine.set] using h3,
    by simpa +decide [StackMachine.set] using h4, by simpa +decide [StackMachine.set] using h5⟩

theorem AInv.set_m {k L : Nat} {r : Regs} (h : AInv k L r) (w : SAT.Word) (hw : w.length ≤ L) :
    AInv k L (set r R.m w) := by
  obtain ⟨hb, h1, h2, h3, h4, h5⟩ := h
  exact ⟨hb.set R.m (by decide) _, by simpa +decide [StackMachine.set] using h1,
    by simpa +decide [StackMachine.set] using h2, by simpa +decide [StackMachine.set] using h3,
    by simpa [StackMachine.set] using hw, by simpa +decide [StackMachine.set] using h5⟩

theorem AInv.set_len {k L : Nat} {r : Regs} (h : AInv k L r) (w : SAT.Word) (hw : w.length ≤ L) :
    AInv k L (set r R.len w) := by
  obtain ⟨hb, h1, h2, h3, h4, h5⟩ := h
  exact ⟨hb.set R.len (by decide) _, by simpa +decide [StackMachine.set] using h1,
    by simpa +decide [StackMachine.set] using h2, by simpa +decide [StackMachine.set] using h3,
    by simpa +decide [StackMachine.set] using h4, by simpa [StackMachine.set] using hw⟩

/-- `maxStep` from a state with `x = 1^v`, `v + 1 ≤ L`. -/
theorem exec_maxStep {k L : Nat} (r : Regs) (v : Nat) (hb : Base k r) (hx : r R.x = unary v)
    (hv : v + 1 ≤ L) (hn : (r R.n).length ≤ L) :
    ∃ t, Exec maxStep r t (true, set (set r R.n (if v + 1 ≤ (r R.n).length then r R.n else unary (v + 1))) R.x []) ∧
      t ≤ 2 + (15 * (L + 1) + 18 + (L + 5 * (L + 1) + 6)) + (L + 1 + 2) := by
  let r₁ := set r R.x (true :: r R.x)
  have hp : Exec (.push R.x true) r 2 (true, r₁) := Exec.push R.x true r
  have hx₁ : r₁ R.x = unary (v + 1) := by simp [r₁, hx, unary_succ]
  have hb₁ : Base k r₁ := hb.set R.x (by decide) _
  obtain ⟨t₂, he₂, ht₂⟩ := SpecT.leU R.x R.n (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (P := fun r' => r' = r₁) (L := L + 1) (fun _ h => h ▸ hb₁.s) (fun _ h => h ▸ hb₁.t1)
    (fun _ h => h ▸ hb₁.t2) (fun _ h => h ▸ ⟨by rw [hx₁, unary_length]; omega,
      by simp +decide [r₁]; omega⟩) r₁ rfl
  have hn₁ : r₁ R.n = r R.n := by simp +decide [r₁]
  simp only [] at he₂
  rw [hx₁, hn₁, unary_length] at he₂
  by_cases hle : v + 1 ≤ (r R.n).length
  · have hd : decide (v + 1 ≤ (r R.n).length) = true := by simp [hle]
    rw [hd] at he₂
    let r₂ := set r₁ R.x []
    have hc : Exec (.clear R.x) r₁ ((r₁ R.x).length + 2) (true, r₂) := Exec.clear R.x r₁
    rw [hx₁, unary_length] at hc
    refine ⟨2 + ((t₂ + 1) + (v + 1 + 2)), ?_, by omega⟩
    have he : Exec maxStep r (2 + ((t₂ + 1) + (v + 1 + 2))) (true, r₂) :=
      Exec.seq hp (Exec.seq (Exec.ifTrue he₂ (Exec.stop true r₁)) hc)
    have : r₂ = set (set r R.n (if v + 1 ≤ (r R.n).length then r R.n else unary (v + 1))) R.x [] := by
      funext j
      simp only [hle, ↓reduceIte, r₂, r₁, StackMachine.set]
      by_cases hj : j = R.x
      · subst hj; simp
      · by_cases hj' : j = R.n
        · subst hj'; simp +decide
        · simp [hj, hj']
    rw [← this]
    exact he
  · have hd : decide (v + 1 ≤ (r R.n).length) = false := by simp [hle]
    rw [hd] at he₂
    let r₂ := set r₁ R.n (r₁ R.x)
    have hcopy : Exec (.copy R.x R.n R.s) r₁ ((r₁ R.n).length + 5 * (r₁ R.x).length + 6) (true, r₂) :=
      Exec.copy (by decide) (by decide) (by decide) hb₁.s
    rw [hx₁, hn₁, unary_length] at hcopy
    let r₃ := set r₂ R.x []
    have hc : Exec (.clear R.x) r₂ ((r₂ R.x).length + 2) (true, r₃) := Exec.clear R.x r₂
    have hx₂ : r₂ R.x = unary (v + 1) := by simp +decide [r₂, hx₁]
    rw [hx₂, unary_length] at hc
    refine ⟨2 + ((t₂ + ((r R.n).length + 5 * (v + 1) + 6)) + (v + 1 + 2)), ?_, by omega⟩
    have he : Exec maxStep r _ (true, r₃) :=
      Exec.seq hp (Exec.seq (Exec.ifFalse he₂ hcopy) hc)
    have : r₃ = set (set r R.n (if v + 1 ≤ (r R.n).length then r R.n else unary (v + 1))) R.x [] := by
      funext j
      simp only [hle, ↓reduceIte, r₃, r₂, r₁, StackMachine.set]
      by_cases hj : j = R.x
      · subst hj; simp
      · by_cases hj' : j = R.n
        · subst hj'; simp +decide [hx, unary_succ]
        · simp [hj, hj']
    rw [← this]
    exact he

theorem Spec.litA (k : Nat) {L : Nat} : Spec Registered.litA (AInv k L) (litACost L) litAModel := by
  intro r hr
  cases hin : r R.inA with
  | nil =>
    refine ⟨2, (false, r), Exec.branchEmpty hin (Exec.stop false r), by simp [litACost], ?_⟩
    simp [litAModel, hin, readLiteral, Realizes]
  | cons s tail =>
    let r₁ := set r R.inA tail
    have hp₁ : Exec (.pop R.inA) r 2 (true, r₁) := by have := Exec.pop R.inA r; rwa [hin] at this
    have hr₁ : AInv k L r₁ := hr.set_inA tail (by have := hr.inA; rw [hin] at this; simp at this; omega)
    obtain ⟨t₂, res₂, he₂, ht₂, hres₂⟩ := Spec.readUnary R.inA R.x (by decide) (by decide) (by decide)
      (P := AInv k L) (L := L) (fun r hr => hr.base.g) (fun r hr => ⟨hr.inA, by rw [hr.x]; simp⟩) r₁ hr₁
    have hin₁ : r₁ R.inA = tail := by simp [r₁]
    simp only [readUnaryModel, hin₁] at hres₂
    have hbranch : ∀ t res, Exec (.seq (.pop R.inA) litA') r t res →
        Exec Registered.litA r (t + 1) res := by
      intro t res h
      cases s with
      | false => exact Exec.branchZero hin h
      | true => exact Exec.branchOne hin h
    cases hn : readNat tail with
    | none =>
      simp only [hn, Realizes] at hres₂
      obtain ⟨b, r₂⟩ := res₂
      simp only at hres₂
      subst hres₂
      refine ⟨_, (false, r₂), hbranch _ _ (Exec.seq hp₁ (Exec.seqFailure he₂)), ?_, ?_⟩
      · simp only [litACost]; omega
      · simp [litAModel, hin, readLiteral, hn, Realizes]
    | some p =>
      obtain ⟨v, rest⟩ := p
      simp only [hn, Realizes] at hres₂
      subst hres₂
      have hlen := congrArg List.length (readNat_eq_some hn)
      simp only [List.length_append, SATBounds.writeNat_length] at hlen
      have hL := hr.inA
      rw [hin] at hL
      simp only [List.length_cons] at hL
      let r₂ := set (set r₁ R.inA rest) R.x (unary v)
      have hb₂ : Base k r₂ := (hr₁.base.set R.inA (by decide) _).set R.x (by decide) _
      have hn₂ : r₂ R.n = r R.n := by simp +decide [r₂, r₁, StackMachine.set]
      obtain ⟨t₃, he₃, ht₃⟩ := exec_maxStep (k := k) (L := L) r₂ v hb₂ (by simp [r₂])
        (by omega) (by rw [hn₂]; exact hr.n)
      refine ⟨_, _, hbranch _ _ (Exec.seq hp₁ (Exec.seq he₂ he₃)), ?_, ?_⟩
      · simp only [litACost]; omega
      · simp only [litAModel, hin, readLiteral, hn, Option.pure_def, Realizes,
          Prod.mk.injEq, true_and]
        rw [hn₂]
        funext j
        by_cases hj : j = R.x
        · subst hj; simp [StackMachine.set]
        · by_cases hj' : j = R.n
          · subst hj'; simp +decide [StackMachine.set]
          · by_cases hj'' : j = R.inA
            · subst hj''; simp +decide [r₂, r₁, StackMachine.set]
            · simp [r₂, r₁, StackMachine.set, hj, hj', hj'']

theorem AInv.litA {k L : Nat} {r r' : Regs} (h : AInv k L r) (hm : litAModel r = some r') : AInv k L r' := by
  unfold litAModel at hm
  cases hl : readLiteral (r R.inA) with
  | none => rw [hl] at hm; simp at hm
  | some p =>
    obtain ⟨l, rest⟩ := p
    rw [hl] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    have hlen := congrArg List.length (readLiteral_eq_some hl)
    simp only [List.length_append, SATBounds.encodeLiteral_length] at hlen
    obtain ⟨hb, h1, h2, h3, h4, h5⟩ := h
    refine ⟨(hb.set R.inA (by decide) _ |>.set R.n (by decide) _).set R.x (by decide) _, ?_, ?_, ?_, ?_, ?_⟩
    · simp +decide [StackMachine.set]; omega
    · simp +decide [StackMachine.set]
      split
      · exact h2
      · simp; omega
    · simp [StackMachine.set]
    · simpa +decide [StackMachine.set] using h4
    · simpa +decide [StackMachine.set] using h5

theorem litA_writes (i : Reg) (hi : i ≠ R.inA ∧ i ≠ R.x ∧ i ≠ R.n ∧ i ≠ R.g ∧ i ≠ R.t1 ∧ i ≠ R.t2) :
    writes litA i = false := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hi
  simp [litA, litA', maxStep, leU, writes, readUnary, Complexity.Restricted.readUnaryC,
    Complexity.Restricted.readUnaryBody, Complexity.Restricted.drainBody, h1, h2, h3, h4, h5, h6]

/-- One clause of the first pass: read the literal count, then every literal. -/
def clauseA : Command K := .seq (readUnary R.inA R.len) (.repeat R.len litA)

def clauseAModel (r : Regs) : Option Regs :=
  (readUnaryModel R.inA R.len r).bind fun r₁ => iter litAModel R.len (r₁ R.len).length r₁

def clauseACost (L : Nat) : Nat := (9 * L + 10) + (L * (litACost L + 1) + 2)

theorem AInv.readUnary {k L : Nat} {r r' : Regs} (h : AInv k L r) (dst : Reg)
    (hd : dst = R.len ∨ dst = R.m) (hm : readUnaryModel R.inA dst r = some r') : AInv k L r' := by
  unfold readUnaryModel at hm
  cases hn : readNat (r R.inA) with
  | none => rw [hn] at hm; simp at hm
  | some p =>
    obtain ⟨v, rest⟩ := p
    rw [hn] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    have hlen := congrArg List.length (readNat_eq_some hn)
    simp only [List.length_append, SATBounds.writeNat_length] at hlen
    have h1 := h.set_inA rest (by have := h.inA; omega)
    rcases hd with rfl | rfl
    · exact h1.set_len _ (by simp only [unary_length]; have := h.inA; omega)
    · exact h1.set_m _ (by simp only [unary_length]; have := h.inA; omega)

theorem AInv.pop_len {k L : Nat} {r : Regs} (h : AInv k L r) (b : Bool) (tail : SAT.Word)
    (hl : r R.len = b :: tail) : AInv k L (set r R.len tail) :=
  h.set_len tail (by have := h.len; rw [hl] at this; simp at this; omega)

theorem AInv.pop_m {k L : Nat} {r : Regs} (h : AInv k L r) (b : Bool) (tail : SAT.Word)
    (hl : r R.m = b :: tail) : AInv k L (set r R.m tail) :=
  h.set_m tail (by have := h.m; rw [hl] at this; simp at this; omega)

theorem Spec.clauseA (k : Nat) {L : Nat} : Spec Registered.clauseA (AInv k L) (clauseACost L) clauseAModel := by
  have s1 := Spec.readUnary R.inA R.len (by decide) (by decide) (by decide) (P := AInv k L) (L := L)
    (fun r hr => hr.base.g) (fun r hr => ⟨hr.inA, hr.len⟩)
  have s2 := Spec.repeat (j := R.len) (body := Registered.litA) (P := AInv k L) (Pb := AInv k L) (L := L)
    (litA_writes R.len (by decide)) (fun r b tail hr hl => hr.pop_len b tail hl)
    (fun r b tail r' hr hl hm => (hr.pop_len b tail hl).litA hm) (fun r hr => hr.len) (Spec.litA k)
  have h := s1.seq (P₂ := AInv k L) (fun r r' hr hm => hr.readUnary R.len (Or.inl rfl) hm) s2
  exact (h.mono (fun r hr => hr) (by simp only [clauseACost]; omega)).congr (fun r _ => rfl)

theorem AInv.clauseA {k L : Nat} {r r' : Regs} (h : AInv k L r) (hm : clauseAModel r = some r') : AInv k L r' := by
  unfold clauseAModel at hm
  cases h₁ : readUnaryModel R.inA R.len r with
  | none => rw [h₁] at hm; simp at hm
  | some r₁ =>
    rw [h₁, Option.bind_some] at hm
    exact iter_invariant (j := R.len) (P := AInv k L) (m := litAModel)
      (fun r b tail r' hr hl hm => (hr.pop_len b tail hl).litA hm) _ _ _ (h.readUnary R.len (Or.inl rfl) h₁) hm

theorem clauseA_writes (i : Reg) (hi : i ≠ R.inA ∧ i ≠ R.x ∧ i ≠ R.n ∧ i ≠ R.g ∧ i ≠ R.t1 ∧ i ≠ R.t2 ∧
    i ≠ R.len) : writes clauseA i = false := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hi
  simp [clauseA, writes, readUnary, Complexity.Restricted.readUnaryC, Complexity.Restricted.readUnaryBody,
    h1, h4, h7, litA_writes i ⟨h1, h2, h3, h4, h5, h6⟩]

/-- The first pass. -/
def passA : Command K := .seq (readUnary R.inA R.m) (.repeat R.m clauseA)

def passAModel (r : Regs) : Option Regs :=
  (readUnaryModel R.inA R.m r).bind fun r₁ => iter clauseAModel R.m (r₁ R.m).length r₁

def passACost (L : Nat) : Nat := (9 * L + 10) + (L * (clauseACost L + 1) + 2)

theorem Spec.passA (k : Nat) {L : Nat} : Spec Registered.passA (AInv k L) (passACost L) passAModel := by
  have s1 := Spec.readUnary R.inA R.m (by decide) (by decide) (by decide) (P := AInv k L) (L := L)
    (fun r hr => hr.base.g) (fun r hr => ⟨hr.inA, hr.m⟩)
  have s2 := Spec.repeat (j := R.m) (body := Registered.clauseA) (P := AInv k L) (Pb := AInv k L) (L := L)
    (clauseA_writes R.m (by decide)) (fun r b tail hr hl => hr.pop_m b tail hl)
    (fun r b tail r' hr hl hm => (hr.pop_m b tail hl).clauseA hm) (fun r hr => hr.m) (Spec.clauseA k)
  have h := s1.seq (P₂ := AInv k L) (fun r r' hr hm => hr.readUnary R.m (Or.inr rfl) hm) s2
  exact (h.mono (fun r hr => hr) (by simp only [passACost]; omega)).congr (fun r _ => rfl)

theorem AInv.passA {k L : Nat} {r r' : Regs} (h : AInv k L r) (hm : passAModel r = some r') : AInv k L r' := by
  unfold passAModel at hm
  cases h₁ : readUnaryModel R.inA R.m r with
  | none => rw [h₁] at hm; simp at hm
  | some r₁ =>
    rw [h₁, Option.bind_some] at hm
    exact iter_invariant (j := R.m) (P := AInv k L) (m := clauseAModel)
      (fun r b tail r' hr hl hm => (hr.pop_m b tail hl).clauseA hm) _ _ _ (h.readUnary R.m (Or.inr rfl) h₁) hm

theorem passA_writes (i : Reg) (hi : i ≠ R.inA ∧ i ≠ R.x ∧ i ≠ R.n ∧ i ≠ R.g ∧ i ≠ R.t1 ∧ i ≠ R.t2 ∧
    i ≠ R.len ∧ i ≠ R.m) : writes passA i = false := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hi
  simp [passA, writes, readUnary, Complexity.Restricted.readUnaryC, Complexity.Restricted.readUnaryBody,
    h1, h4, h8, clauseA_writes i ⟨h1, h2, h3, h4, h5, h6, h7⟩]

end STACS2027.Registered
