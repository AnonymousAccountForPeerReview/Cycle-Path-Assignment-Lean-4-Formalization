module

public import Runtimes.Flow.Reloc
public import Outerplanar.RAM.Layout
import Mathlib.Tactic

/-! # Reusable RAM calls with a cleared reserved workspace -/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027.RAM

abbrev callIndex : ℕ := 107
abbrev callSpan : ℕ := 111
abbrev callInput : ℕ := 115
abbrev callLength : ℕ := 119
abbrev callOutput : ℕ := 123
abbrev callAddress : ℕ := 127
abbrev callValue : ℕ := 131
abbrev callZero : ℕ := 135
abbrev callCount : ℕ := 139
abbrev callRemaining : ℕ := 143
abbrev callBegin : ℕ := 147
abbrev callOne : ℕ := 151

/-- Reset the fixed, finite syntactic register footprint of the component program. -/
def resetCallRegisters : List ℕ → Stmt
  | [] => .skip
  | r :: rest => .seq (.const (rl 0 r) 0) (resetCallRegisters rest)

private theorem resetCallRegisters_loopFree (registers : List ℕ) :
    LoopFree (resetCallRegisters registers) := by
  induction registers with
  | nil => trivial
  | cons r registers ih => exact ⟨trivial, ih⟩

private theorem resetCallRegisters_size (registers : List ℕ) :
    size (resetCallRegisters registers) = registers.length + 1 := by
  induction registers with
  | nil => rfl
  | cons r registers ih => simp [resetCallRegisters, size, ih]; omega

private theorem resetCallRegisters_run (registers : List ℕ) (c : Config) :
    (∀ r, (run (resetCallRegisters registers) c).reg (rl 0 r) =
      if r ∈ registers then 0 else c.reg (rl 0 r)) ∧
    (∀ r, r % 4 ≠ 0 → (run (resetCallRegisters registers) c).reg r = c.reg r) ∧
    (run (resetCallRegisters registers) c).mem = c.mem ∧
    (run (resetCallRegisters registers) c).out = c.out := by
  induction registers generalizing c with
  | nil => simp [resetCallRegisters]
  | cons r registers ih =>
    have h := ih (c.setReg (rl 0 r) 0)
    simp only [resetCallRegisters, run_seq', run_const]
    refine ⟨fun s => ?_, fun s hs => ?_, h.2.2.1, h.2.2.2⟩
    · rw [h.1]
      by_cases hmem : s ∈ registers
      · simp [hmem]
      · by_cases heq : s = r
        · subst s; simp [hmem]
        · have hne : rl 0 s ≠ rl 0 r := fun he => heq (rl_inj he)
          simp [hmem, heq, hne]
    · rw [h.2.1 s hs]
      have hne : s ≠ rl 0 r := fun he => hs (he ▸ rl_mod (by decide) r)
      simp [hne]

theorem resetCallRegisters_spec {S : ℕ} (registers : List ℕ) (c₀ : Config) :
    HTB S (resetCallRegisters registers) (fun c => c = c₀)
      (fun c => (∀ r, c.reg (rl 0 r) = if r ∈ registers then 0 else c₀.reg (rl 0 r)) ∧
        (∀ r, r % 4 ≠ 0 → c.reg r = c₀.reg r) ∧ c.mem = c₀.mem ∧ c.out = c₀.out)
      (registers.length + 1) := by
  refine HTB.run_le (resetCallRegisters_loopFree registers)
    (le_of_eq (resetCallRegisters_size registers)) fun c hc => ?_
  subst c
  have hmem : memFree (resetCallRegisters registers) = true := by
    induction registers with
    | nil => rfl
    | cons r registers ih => simpa [resetCallRegisters, memFree] using ih
  exact ⟨AddrOK.of_memFree hmem, resetCallRegisters_run registers c₀⟩

/-- A bounded component cannot modify memory at or above its address bound. -/
theorem ExecB.memory_above {S : ℕ} {program : Stmt} {c c' : Config} {time : ℕ}
    (h : ExecB S program c time c') (a : ℕ) (ha : S ≤ a) : c'.mem a = c.mem a := by
  induction h with
  | store address value c haddress =>
    have hne : a ≠ c.reg address := by omega
    simp [Config.setMem, hne]
  | seq _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | ifzTrue _ _ ih | ifzFalse _ _ ih => exact ih
  | loopNext _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | _ => rfl

/-- Every written output consumes at least one RAM step. -/
theorem ExecB.output_length_bound {S : ℕ} {program : Stmt} {c c' : Config} {time : ℕ}
    (h : ExecB S program c time c') : c'.out.length ≤ c.out.length + time := by
  induction h with
  | seq _ _ ih₁ ih₂ => omega
  | ifzTrue _ _ ih | ifzFalse _ _ ih => omega
  | loopNext _ _ _ ih₁ ih₂ => omega
  | _ => simp [Config.setReg, Config.setMem, Config.emit] <;> omega

def clearCallBody : Stmt := .seq (.add callAddress callIndex callIndex)
  (.seq (.add callAddress callAddress callAddress) (.store callAddress callZero))

def copyCallBody : Stmt := .seq (.add callAddress callInput callIndex)
  (.seq (.load callValue callAddress) (.seq (.add callAddress callIndex callIndex)
  (.seq (.add callAddress callAddress callAddress) (.store callAddress callValue))))

def initializeCall : Stmt := .seq (.const callZero 0) (.seq (.const callOne 1)
  (.seq (.const xFour 4) (.seq (.const (xJ 0) 0) (.seq (.const callCount 0)
  (.seq (.add callBegin callOutput callOutput) (.seq (.add callBegin callBegin callBegin)
  (.seq (.add callBegin callBegin callOne) (.add xP callBegin callZero))))))))

def countCallBody : Stmt := .seq (.sub callRemaining callRemaining xFour)
  (.add callCount callCount callOne)

def countCallOutput : Stmt := .seq (.sub callRemaining xP callBegin)
  (.seq (.const callCount 0) (.loop callRemaining countCallBody))

/-- All metadata and caller state are in class three. The component uses only class zero;
its output is buffered in the reserved class-one cells. -/
def reusableCall (program : Stmt) : Stmt := .seq initializeCall
  (.seq (forUp callIndex callSpan clearCallBody)
  (.seq (forUp callIndex callLength copyCallBody)
  (.seq (resetCallRegisters (wregs program))
  (.seq (tr 0 true program) countCallOutput))))

@[mk_iff] structure CallMeta (span inputBase inputLength outputBase : ℕ) (c : Config) : Prop where
  span : c.reg callSpan = span
  input : c.reg callInput = inputBase
  length : c.reg callLength = inputLength
  output : c.reg callOutput = outputBase
  zero : c.reg callZero = 0
  one : c.reg callOne = 1
  four : c.reg xFour = 4
  sourceClass : c.reg (xJ 0) = 0
  beginning : c.reg callBegin = 4 * outputBase + 1

private theorem CallMeta.kept {span inputBase inputLength outputBase : ℕ} {c : Config}
    {program : Stmt} (hs : LoopFree program)
    (hw : ∀ r ∈ wregs program,
      r ∉ [callSpan, callInput, callLength, callOutput, callZero, callOne, xFour, xJ 0, callBegin])
    (h : CallMeta span inputBase inputLength outputBase c) :
    CallMeta span inputBase inputLength outputBase (run program c) := by
  have hr : ∀ r ∈ [callSpan, callInput, callLength, callOutput, callZero, callOne, xFour, xJ 0, callBegin],
      (run program c).reg r = c.reg r := by
    intro r hr
    exact run_reg_of_not_mem hs (fun hm => hw r hm hr) c
  constructor
  · rw [hr callSpan (by simp)]; exact h.span
  · rw [hr callInput (by simp)]; exact h.input
  · rw [hr callLength (by simp)]; exact h.length
  · rw [hr callOutput (by simp)]; exact h.output
  · rw [hr callZero (by simp)]; exact h.zero
  · rw [hr callOne (by simp)]; exact h.one
  · rw [hr xFour (by simp)]; exact h.four
  · rw [hr (xJ 0) (by simp)]; exact h.sourceClass
  · rw [hr callBegin (by simp)]; exact h.beginning

private theorem classZeroReg_kept {program : Stmt} (hs : LoopFree program)
    (hw : ∀ r ∈ wregs program, r % 4 ≠ 0) (c : Config) (r : ℕ) (hr : r % 4 = 0) :
    (run program c).reg r = c.reg r :=
  run_reg_of_not_mem hs (fun hm => hw r hm hr) c

def clearedCallMemory (original : ℕ → ℕ) (count : ℕ) (a : ℕ) : ℕ :=
  if a % 4 = 0 ∧ a / 4 < count then 0 else original a

def copiedCallMemory (original : ℕ → ℕ) (span : ℕ) (input : List ℕ) (count : ℕ) (a : ℕ) : ℕ :=
  if a % 4 = 0 ∧ a / 4 < count then input.getD (a / 4) 0 else clearedCallMemory original span a

def CallClearInv (c₀ : Config) (span inputBase inputLength outputBase count : ℕ) (c : Config) : Prop :=
  CallMeta span inputBase inputLength outputBase c ∧
    c.mem = clearedCallMemory c₀.mem count ∧ c.out = c₀.out ∧
    ∀ r, r % 4 = 0 → c.reg r = c₀.reg r

def CallCopyInv (c₀ : Config) (span inputBase outputBase : ℕ) (input : List ℕ) (count : ℕ)
    (c : Config) : Prop := CallMeta span inputBase input.length outputBase c ∧
    c.mem = copiedCallMemory c₀.mem span input count ∧ c.out = c₀.out ∧
    ∀ r, r % 4 = 0 → c.reg r = c₀.reg r

theorem clearCallBody_spec {S : ℕ} (c₀ : Config) (span inputBase inputLength outputBase j : ℕ)
    (hj : j < span) (hS : 4 * span ≤ S) :
    HTB S clearCallBody
      (fun c => CallClearInv c₀ span inputBase inputLength outputBase j c ∧
        c.reg callIndex = j ∧ c.reg callSpan = span)
      (fun c => CallClearInv c₀ span inputBase inputLength outputBase (j + 1) c ∧
        c.reg callIndex = j ∧ c.reg callSpan = span) 3 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hm, hmem, hout, hreg⟩, hi, hn⟩ => ?_
  have hc : (run clearCallBody c).mem = upd c.mem (4 * j) 0 := by
    simp +decide [clearCallBody, hi, hm.zero]
    congr 2
    omega
  refine ⟨by addr_ok [clearCallBody, hi],
    ⟨CallMeta.kept (by decide) (by decide) hm, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hc, hmem]
    funext a
    by_cases ha : a = 4 * j
    · subst a
      simp [upd_apply, clearedCallMemory]
    · have hcond : (a % 4 = 0 ∧ a / 4 < j + 1) ↔ (a % 4 = 0 ∧ a / 4 < j) := by omega
      simp only [upd_apply, ha, ite_false, clearedCallMemory, hcond]
  · rw [run_out_of_writes (by decide) rfl]; exact hout
  · intro r hr
    rw [classZeroReg_kept (by decide) (by decide) c r hr]
    exact hreg r hr
  · simp +decide [clearCallBody, hi]
  · simp +decide [clearCallBody, hn]

theorem copyCallBody_spec {S : ℕ} (c₀ : Config) (span inputBase outputBase : ℕ)
    (input : List ℕ) (hinput : Arr c₀.mem inputBase input)
    (hlen : input.length ≤ span) (hbase : 4 * span ≤ inputBase)
    (hS : inputBase + input.length ≤ S) (j : ℕ) (hj : j < input.length) :
    HTB S copyCallBody
      (fun c => CallCopyInv c₀ span inputBase outputBase input j c ∧
        c.reg callIndex = j ∧ c.reg callLength = input.length)
      (fun c => CallCopyInv c₀ span inputBase outputBase input (j + 1) c ∧
        c.reg callIndex = j ∧ c.reg callLength = input.length) 5 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hm, hmem, hout, hreg⟩, hi, hn⟩ => ?_
  have hread : c.mem (inputBase + j) = input.getD j 0 := by
    rw [hmem]
    have hnot : ¬ ((inputBase + j) % 4 = 0 ∧ (inputBase + j) / 4 < j) := by omega
    have hnot' : ¬ ((inputBase + j) % 4 = 0 ∧ (inputBase + j) / 4 < span) := by omega
    simp only [copiedCallMemory, clearedCallMemory, hnot, hnot', ite_false]
    exact hinput.getD hj
  have hc : (run copyCallBody c).mem = upd c.mem (4 * j) (input.getD j 0) := by
    simp +decide [copyCallBody, hi, hm.input, hread]
    congr 2
    omega
  refine ⟨by addr_ok [copyCallBody, hi, hm.input],
    ⟨CallMeta.kept (by decide) (by decide) hm, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hc, hmem]
    funext a
    by_cases ha : a = 4 * j
    · subst a
      simp [upd_apply, copiedCallMemory]
    · have hcond : (a % 4 = 0 ∧ a / 4 < j + 1) ↔ (a % 4 = 0 ∧ a / 4 < j) := by omega
      simp only [upd_apply, ha, ite_false, copiedCallMemory, hcond]
  · rw [run_out_of_writes (by decide) rfl]; exact hout
  · intro r hr
    rw [classZeroReg_kept (by decide) (by decide) c r hr]
    exact hreg r hr
  · simp +decide [copyCallBody, hi]
  · simp +decide [copyCallBody, hn]

private theorem CallClearInv.independent (c₀ : Config)
    (span inputBase inputLength outputBase count : ℕ) :
    Indep [callIndex, rT] (CallClearInv c₀ span inputBase inputLength outputBase count) := by
  intro c c' ha ⟨hm, hmem, hout, hreg⟩
  refine ⟨?_, ha.mem.trans hmem, ha.out.trans hout, ?_⟩
  · rw [callMeta_iff] at hm ⊢
    simpa only [ha.reg callSpan (by decide), ha.reg callInput (by decide),
      ha.reg callLength (by decide), ha.reg callOutput (by decide),
      ha.reg callZero (by decide), ha.reg callOne (by decide),
      ha.reg xFour (by decide), ha.reg (xJ 0) (by decide),
      ha.reg callBegin (by decide)] using hm
  · intro r hr
    have hn : r ∉ [callIndex, rT] := by
      intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h <;> subst r <;> norm_num at hr
    rw [ha.reg r hn]
    exact hreg r hr

private theorem CallCopyInv.independent (c₀ : Config) (span inputBase outputBase : ℕ)
    (input : List ℕ) (count : ℕ) :
    Indep [callIndex, rT] (CallCopyInv c₀ span inputBase outputBase input count) := by
  intro c c' ha ⟨hm, hmem, hout, hreg⟩
  refine ⟨?_, ha.mem.trans hmem, ha.out.trans hout, ?_⟩
  · rw [callMeta_iff] at hm ⊢
    simpa only [ha.reg callSpan (by decide), ha.reg callInput (by decide),
      ha.reg callLength (by decide), ha.reg callOutput (by decide),
      ha.reg callZero (by decide), ha.reg callOne (by decide),
      ha.reg xFour (by decide), ha.reg (xJ 0) (by decide),
      ha.reg callBegin (by decide)] using hm
  · intro r hr
    have hn : r ∉ [callIndex, rT] := by
      intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h <;> subst r <;> norm_num at hr
    rw [ha.reg r hn]
    exact hreg r hr

theorem initializeCall_spec {S : ℕ} (c₀ : Config) (span inputBase inputLength outputBase : ℕ)
    (hspan : c₀.reg callSpan = span) (hinput : c₀.reg callInput = inputBase)
    (hlen : c₀.reg callLength = inputLength) (hout : c₀.reg callOutput = outputBase) :
    HTB S initializeCall (fun c => c = c₀)
      (fun c => CallClearInv c₀ span inputBase inputLength outputBase 0 c ∧
        c.reg xP = 4 * outputBase + 1) 9 := by
  refine HTB.run_le (by decide) (by decide) fun c hc => ?_
  subst c
  refine ⟨AddrOK.of_memFree rfl, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [callMeta_iff]
    simp +decide [initializeCall, hspan, hinput, hlen, hout]
    omega
  · rw [run_mem_of_stores (by decide) rfl]
    funext a
    simp [clearedCallMemory]
  · exact run_out_of_writes (by decide) rfl c₀
  · intro r hr
    exact classZeroReg_kept (by decide) (by decide) c₀ r hr
  · simp +decide [initializeCall]
    omega

private theorem clearCall_spec {S : ℕ} (c₀ : Config) (span inputBase inputLength outputBase : ℕ)
    (hS : 4 * span ≤ S) :
    HTB S (forUp callIndex callSpan clearCallBody)
      (fun c => CallClearInv c₀ span inputBase inputLength outputBase 0 c)
      (fun c => CallClearInv c₀ span inputBase inputLength outputBase span c) (7 * span + 3) := by
  exact (HTB.forUpC (CallClearInv c₀ span inputBase inputLength outputBase) 3
    (by decide) (by decide) (by decide)
    (CallClearInv.independent c₀ span inputBase inputLength outputBase)
    (clearCallBody_spec c₀ span inputBase inputLength outputBase · · hS)).pre
      (fun c hc => ⟨hc, hc.1.span⟩) |>.post (fun c hc => hc.1) |>.weaken (by omega)

private theorem copyCall_spec {S : ℕ} (c₀ : Config) (span inputBase outputBase : ℕ)
    (input : List ℕ) (hinput : Arr c₀.mem inputBase input)
    (hlen : input.length ≤ span) (hbase : 4 * span ≤ inputBase)
    (hS : inputBase + input.length ≤ S) :
    HTB S (forUp callIndex callLength copyCallBody)
      (fun c => CallClearInv c₀ span inputBase input.length outputBase span c)
      (fun c => CallCopyInv c₀ span inputBase outputBase input input.length c)
      (9 * input.length + 3) := by
  exact (HTB.forUpC (CallCopyInv c₀ span inputBase outputBase input) 5
    (by decide) (by decide) (by decide)
    (CallCopyInv.independent c₀ span inputBase outputBase input)
    (copyCallBody_spec c₀ span inputBase outputBase input hinput hlen hbase hS)).pre
      (fun c hc => ⟨⟨hc.1, by rw [hc.2.1]; funext a; simp [copiedCallMemory], hc.2.2⟩,
        hc.1.length⟩) |>.post (fun c hc => hc.1) |>.weaken (by omega)

private def CallCountInv (length : ℕ) (c : Config) : Prop :=
  c.reg xFour = 4 ∧ c.reg callOne = 1 ∧
    4 * c.reg callCount + c.reg callRemaining = 4 * length

private theorem countCallBody_spec {S : ℕ} (length v : ℕ) :
    HTB S countCallBody
      (fun c => CallCountInv length c ∧ c.reg callRemaining ≠ 0 ∧ c.reg callRemaining = v)
      (fun c => CallCountInv length c ∧ c.reg callRemaining < v) 2 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hf, ho, hsum⟩, hne, hv⟩ => ?_
  refine ⟨AddrOK.of_memFree rfl, ?_, ?_⟩
  · unfold CallCountInv
    simp +decide [countCallBody, hf, ho]
    omega
  · simp +decide [countCallBody, hf]
    omega

theorem countCallOutput_spec {S : ℕ} (length outputBase : ℕ) :
    HTB S countCallOutput
      (fun c => c.reg xP = 4 * (outputBase + length) + 1 ∧
        c.reg callBegin = 4 * outputBase + 1 ∧ c.reg xFour = 4 ∧ c.reg callOne = 1)
      (fun c => c.reg callCount = length) (12 * length + 3) := by
  have hinit : HTB S (.seq (.sub callRemaining xP callBegin) (.const callCount 0))
      (fun c => c.reg xP = 4 * (outputBase + length) + 1 ∧
        c.reg callBegin = 4 * outputBase + 1 ∧ c.reg xFour = 4 ∧ c.reg callOne = 1)
      (fun c => CallCountInv length c ∧ c.reg callRemaining ≤ 4 * length) 2 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨hp, hb, hf, ho⟩ => ?_
    refine ⟨AddrOK.of_memFree rfl, ?_, ?_⟩
    · unfold CallCountInv
      simp +decide [hp, hb, hf, ho]
      omega
    · simp +decide [hp, hb]
      omega
  have hl := HTB.loopT (S := S) (a := callRemaining) (body := countCallBody)
    (Inv := CallCountInv length) (fun c => c.reg callRemaining)
    (countCallBody_spec length) (4 * length)
  exact (hinit.seq hl |>.post (fun c ⟨⟨_, _, hsum⟩, hzero⟩ => by omega)).assoc.weaken (by omega)

private theorem CallMeta.transfer {span inputBase inputLength outputBase : ℕ} {c c' : Config}
    (h : CallMeta span inputBase inputLength outputBase c)
    (hr : ∀ r ∈ [callSpan, callInput, callLength, callOutput, callZero, callOne, xFour, xJ 0, callBegin],
      c'.reg r = c.reg r) : CallMeta span inputBase inputLength outputBase c' := by
  rw [callMeta_iff] at h ⊢
  simpa only [hr callSpan (by simp), hr callInput (by simp), hr callLength (by simp),
    hr callOutput (by simp), hr callZero (by simp), hr callOne (by simp),
    hr xFour (by simp), hr (xJ 0) (by simp), hr callBegin (by simp)] using h

/-- Buffered result and the exact frame needed for repeated component calls. -/
def CallResult (program : Stmt) (span outputBase : ℕ) (c₀ : Config) (output : List ℕ)
    (c : Config) : Prop :=
  c.reg callCount = output.length ∧
  (∀ i, i < output.length → c.mem (4 * (outputBase + i) + 1) = output.getD i 0) ∧
  c.out = c₀.out ∧
  (∀ r, r ∉ wregs program → c.reg (rl 0 r) = 0) ∧
  (∀ r, 152 ≤ r → r % 4 ≠ 0 → c.reg r = c₀.reg r) ∧
  (∀ a, (a % 4 ≠ 0 ∨ 4 * span ≤ a) →
    (a % 4 ≠ 1 ∨ a < 4 * outputBase + 1 ∨ 4 * (outputBase + output.length) + 1 ≤ a) →
    c.mem a = c₀.mem a)

/-- Execute a component in a fixed cleared workspace, buffering its output and preserving
caller state. The bound includes clearing, copying, register reset, simulation and counting. -/
theorem reusableCall_spec {S span steps : ℕ} (program : Stmt) (input output : List ℕ)
    (hcompute : ComputesIn program input output steps span) (htime : steps ≤ span)
    (hlen : input.length ≤ span) (inputBase outputBase : ℕ)
    (hbase : 4 * span ≤ inputBase) (hinputSpace : inputBase + input.length ≤ S)
    (houtputSpace : 4 * (outputBase + span) + 1 ≤ S)
    (c₀ : Config) (hinput : Arr c₀.mem inputBase input)
    (hspanReg : c₀.reg callSpan = span) (hinputReg : c₀.reg callInput = inputBase)
    (hlenReg : c₀.reg callLength = input.length) (houtReg : c₀.reg callOutput = outputBase)
    (hzero : ∀ r, r ∉ wregs program → c₀.reg (rl 0 r) = 0) :
    HTB S (reusableCall program) (fun c => c = c₀)
      (CallResult program span outputBase c₀ output)
      ((40 + (wregs program).length) * (span + 1)) := by
  intro c hc
  subst c
  have hworkSpace : 4 * span ≤ S := by omega
  obtain ⟨c₁, t₁, e₁, ⟨h₁, hp₁⟩, ht₁⟩ :=
    initializeCall_spec (S := S) c₀ span inputBase input.length outputBase
      hspanReg hinputReg hlenReg houtReg c₀ rfl
  obtain ⟨c₂, t₂, e₂, h₂, ht₂⟩ :=
    clearCall_spec c₀ span inputBase input.length outputBase hworkSpace c₁ h₁
  obtain ⟨c₃, t₃, e₃, h₃, ht₃⟩ :=
    copyCall_spec c₀ span inputBase outputBase input hinput hlen hbase hinputSpace c₂ h₂
  obtain ⟨c₄, t₄, e₄, hr₄, ht₄⟩ := resetCallRegisters_spec (S := S) (wregs program) c₃ c₃ rfl
  have hz₄ : ∀ r, c₄.reg (rl 0 r) = 0 := by
    intro r
    rw [hr₄.1]
    by_cases hr : r ∈ wregs program
    · simp [hr]
    · simp only [hr, ite_false]
      exact (h₃.2.2.2 (rl 0 r) (rl_mod (by decide) r)).trans (hzero r hr)
  have hm₄ : CallMeta span inputBase input.length outputBase c₄ :=
    h₃.1.transfer fun r hr => hr₄.2.1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hmem₄ : c₄.mem = copiedCallMemory c₀.mem span input input.length :=
    hr₄.2.2.1.trans h₃.2.1
  have hp₄ : c₄.reg xP = 4 * outputBase + 1 := by
    rw [hr₄.2.1 xP (by decide), e₃.reg_frame (by decide), e₂.reg_frame (by decide)]
    exact hp₁
  have hvinput : ∀ a, a < span → c₄.mem (4 * a) = input.getD a 0 := by
    intro a ha
    rw [hmem₄]
    by_cases h : a < input.length
    · simp [copiedCallMemory, h]
    · simp [copiedCallMemory, clearedCallMemory, h, ha, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega)]
  obtain ⟨componentFinal, eComponent, hcomponentOut⟩ :=
    hcompute.of_mem (m := fun a => c₄.mem (4 * a)) hvinput
  have houtLength : output.length ≤ span := by
    have h := ExecB.output_length_bound eComponent
    simp only [List.length_nil, zero_add] at h
    rw [hcomponentOut] at h
    exact h.trans htime
  obtain ⟨c₅, t₅, e₅, hs₅, ho₅, ht₅, _, hr₅, hmem₅⟩ :=
    sim_step (j := 0) (k := 1) (B := outputBase) (b := true) (O₀ := c₀.out)
      (S' := S) (by decide) (by decide) (by decide) hworkSpace eComponent c₄
      ⟨fun r => hz₄ r, fun a => by simp, hm₄.sourceClass, hm₄.four⟩
      ⟨by simpa using hp₄,
        fun i hi => by simp at hi,
        hr₄.2.2.2.trans h₃.2.2.1⟩
      (fun _ => by rw [hcomponentOut]; omega)
  have hm₅ : CallMeta span inputBase input.length outputBase c₅ :=
    hm₄.transfer fun r hr => hr₅ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  rw [hcomponentOut] at ho₅
  obtain ⟨c₆, t₆, e₆, hcount, ht₆⟩ := countCallOutput_spec (S := S) output.length outputBase c₅
    ⟨ho₅.1, hm₅.beginning, hm₅.four, hm₅.one⟩
  have hm₆ := e₆.mem_frame (by decide)
  have ho₆ := e₆.out_frame (by decide)
  refine ⟨c₆, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + t₆)))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))),
    ⟨hcount, ?_, ho₆.trans ho₅.2.2, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    rw [hm₆]
    exact ho₅.2.1 i hi
  · intro r hr
    rw [e₆.reg_frame (by
      simp [countCallOutput, countCallBody, wregs, rl, callRemaining, callCount]
      omega)]
    rw [hs₅.reg]
    exact eComponent.reg_frame hr
  · intro r hr hmod
    rw [e₆.reg_frame (by simp [countCallOutput, countCallBody, wregs, callCount, callRemaining]; omega),
      hr₅ r hmod (by change r ≠ 3; omega) (by change r ≠ 7; omega), hr₄.2.1 r hmod,
      e₃.reg_frame (by simp [RAM.forUp, copyCallBody, wregs, callAddress, callValue, callIndex, rT]; omega),
      e₂.reg_frame (by simp [RAM.forUp, clearCallBody, wregs, callAddress, callIndex, rT]; omega),
      e₁.reg_frame (by simp [initializeCall, wregs, callZero, callOne, callCount, callBegin, xFour, xJ, xP]; omega)]
  · intro a hwork hbuffer
    rw [hm₆]
    by_cases hclass : a % 4 = 0
    · have ha : 4 * span ≤ a := by omega
      have he : a = 4 * (a / 4) := by omega
      rw [he]
      rw [show c₅.mem (4 * (a / 4)) = componentFinal.mem (a / 4) by simpa using hs₅.mem (a / 4)]
      have hsame := ExecB.memory_above eComponent (a / 4) (by omega)
      rw [hsame]
      change c₄.mem (4 * (a / 4)) = c₀.mem (4 * (a / 4))
      have hquot : span ≤ a / 4 := by omega
      have hnotInput : ¬ a / 4 < input.length := by omega
      have hnotWork : ¬ a / 4 < span := by omega
      rw [hmem₄]
      simp [copiedCallMemory, clearedCallMemory, hnotInput, hnotWork]
    · rw [hmem₅ a hclass (by
        rw [ho₅.1]
        rw [hp₄]
        exact hbuffer), hmem₄]
      simp [copiedCallMemory, clearedCallMemory, hclass]
  · have hstepBound : t₅ ≤ 4 * span := ht₅.trans (Nat.mul_le_mul_left 4 htime)
    nlinarith

/-- Cells above both reserved regions are unchanged by a reusable call. -/
theorem CallResult.memory_high {program : Stmt} {span outputBase : ℕ} {c₀ c : Config}
    {output : List ℕ} (h : CallResult program span outputBase c₀ output c)
    (a : ℕ) (hwork : 4 * span ≤ a)
    (hbuffer : 4 * (outputBase + output.length) + 1 ≤ a) : c.mem a = c₀.mem a :=
  h.2.2.2.2.2 a (Or.inr hwork) (Or.inr (Or.inr hbuffer))

/-- Contiguous caller tables above the reserved workspace and output are preserved. -/
theorem CallResult.array_high {program : Stmt} {span outputBase : ℕ} {c₀ c : Config}
    {output values : List ℕ} (h : CallResult program span outputBase c₀ output c)
    {base : ℕ} (hwork : 4 * span ≤ base)
    (hbuffer : 4 * (outputBase + output.length) + 1 ≤ base)
    (harray : Arr c₀.mem base values) : Arr c.mem base values := by
  intro i hi
  rw [h.memory_high (base + i) (by omega) (by omega)]
  exact harray i hi

end STACS2027.Runtimes.Flow
