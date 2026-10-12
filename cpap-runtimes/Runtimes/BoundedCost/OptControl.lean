module

public import Runtimes.BoundedCost.OptMemory
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.OptControl

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost

abbrev inputK : ℕ := 620
abbrev inputT : ℕ := 621
abbrev budget : ℕ := 622
abbrev span : ℕ := 624
abbrev alive : ℕ := 630
abbrev address : ℕ := 631
abbrev answerBit : ℕ := 632
abbrev outputIndex : ℕ := 633
abbrev outputLength : ℕ := 634

def Fixed (g : Graph) (k : ℕ) (c : Config) : Prop :=
  c.reg (callerRegister inputK) = k ∧ c.reg (callerRegister inputT) = (cycles g k).length ∧
    c.reg (callerRegister CoreRAM.coreBase) = bD g k ∧
    c.reg (callerRegister CoreRAM.coreLength) = 3 * (k * (cycles g k).length) + 4

theorem Fixed.transfer {g : Graph} {k : ℕ} {c c' : Config} (h : Fixed g k c)
    (hreg : ∀ r ∈ [inputK, inputT, CoreRAM.coreBase, CoreRAM.coreLength],
      c'.reg (callerRegister r) = c.reg (callerRegister r)) : Fixed g k c' := by
  exact ⟨(hreg _ (by decide)).trans h.1, (hreg _ (by decide)).trans h.2.1,
    (hreg _ (by decide)).trans h.2.2.1, (hreg _ (by decide)).trans h.2.2.2⟩

def startProgram : Stmt := onCallerRegisters
  (.seq (mov inputK gK) (.seq (mov inputT gT)
    (.seq (.const budget 0) (.const alive 1))))

theorem startProgram_spec {g : Graph} {k S : ℕ} (c₀ : Config)
    (hg : CoreRAM.CoreGlobals g k (registerView callerRegister c₀)) :
    HTB S startProgram (· = c₀)
      (fun c => Fixed g k c ∧ c.reg (callerRegister budget) = 0 ∧
        c.reg (callerRegister alive) = 1 ∧ c.mem = c₀.mem ∧ c.out = c₀.out) 6 := by
  refine HTB.run_le (by decide) (by decide) ?_
  intro c hc
  subst c
  refine ⟨AddrOK.of_memFree (by decide), ?_⟩
  have hk := hg.1.2.2.1
  have ht := hg.1.2.2.2.1
  have hb := hg.1.2.1
  have hl := hg.2.2.1
  change c₀.reg (callerRegister gK) = k at hk
  change c₀.reg (callerRegister gT) = (cycles g k).length at ht
  change c₀.reg (callerRegister CoreRAM.coreBase) = bD g k at hb
  change c₀.reg (callerRegister CoreRAM.coreLength) = 3 * (k * (cycles g k).length) + 4 at hl
  simp +decide [startProgram, Fixed, onCallerRegisters, renameRegisters, mov, registerView,
    hk, ht, hb, hl]

def callReady : Stmt :=
  .seq (mov Flow.callSpan (callerRegister span))
    (.seq (mov Flow.callLength (callerRegister CoreRAM.coreLength))
      (mov Flow.offsetBase (callerRegister CoreRAM.coreBase)))

theorem callReady_spec {g : Graph} {k S b : ℕ} (c₀ : Config)
    (hg : Fixed g k c₀) (hspan : c₀.reg (callerRegister span) = b) :
    HTB S callReady (· = c₀)
      (fun c => Fixed g k c ∧ c.reg Flow.callSpan = b ∧
        c.reg Flow.callLength = (CoreRAM.coreInput g k 0).length ∧
        c.reg Flow.offsetBase = bD g k ∧ c.mem = c₀.mem ∧ c.out = c₀.out ∧ Frame callReady c₀ c) 6 := by
  intro c hc
  subst c
  obtain ⟨c, t, he, hp, ht⟩ :=
    (show HTB S callReady (· = c₀)
      (fun c => Fixed g k c ∧ c.reg Flow.callSpan = b ∧
        c.reg Flow.callLength = (CoreRAM.coreInput g k 0).length ∧
        c.reg Flow.offsetBase = bD g k ∧ c.mem = c₀.mem ∧ c.out = c₀.out) 6 by
      refine HTB.run_le (by decide) (by decide) ?_
      intro c hc
      subst c
      refine ⟨AddrOK.of_memFree (by decide), ?_⟩
      obtain ⟨hk, ht, hb, hl⟩ := hg
      simp +decide [callReady, Fixed, mov, hk, ht, hb, hl, hspan, CoreRAM.coreInput_length]) c₀ rfl
  exact ⟨c, t, he, ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1,
    hp.2.2.2.2.2, he.frame⟩, ht⟩

def readAnswer : Stmt := .seq (.add address span span)
  (.seq (.add address address address) (.seq (addc address address 1) (.load answerBit address)))

def reject : Stmt := .seq (inc budget)
  (.seq (.add address CoreRAM.coreBase CoreRAM.coreLength)
    (.seq (dec address) (.seq (.add address address address)
      (.seq (.add address address address) (.seq (addc address address 2) (.store address budget))))))

def decideAnswer : Stmt := .seq readAnswer (.ifz answerBit reject (.const alive 0))

def DecisionGlobals (base length bound p : ℕ) (c : Config) : Prop :=
  c.reg CoreRAM.coreBase = base ∧ c.reg CoreRAM.coreLength = length ∧
    c.reg span = bound ∧ c.reg budget = p ∧ c.reg alive = 1

theorem decideAnswer_zero_spec {S base length bound p : ℕ} {memory : ℕ → ℕ} {out : List ℕ}
    (hlen : 0 < length) (hinputSpace : 4 * (base + length - 1) + 2 < S)
    (houtputSpace : 4 * bound + 1 < S) (hhead : memory (4 * bound + 1) = 0) :
    HTB S decideAnswer
      (fun c => DecisionGlobals base length bound p c ∧ c.mem = memory ∧ c.out = out)
      (fun c => c.reg budget = p + 1 ∧ c.reg alive = 1 ∧
        c.mem = upd memory (4 * (base + length - 1) + 2) (p + 1) ∧ c.out = out) 20 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨⟨hb, hl, hs, hp, ha⟩, hm, ho⟩
  have hread : c.mem (bound + bound + (bound + bound) + 1) = 0 := by
    rw [show bound + bound + (bound + bound) + 1 = 4 * bound + 1 by omega, hm, hhead]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · addr_ok [decideAnswer, readAnswer, reject, hb, hl, hs, hp, ha, hm, hread, hhead]
  all_goals simp +decide only [decideAnswer, readAnswer, reject, run_seq', run_add,
    run_inc, run_dec, run_addc, run_subc, run_ifz', run_load, run_const, run_store,
    setReg_reg, setReg_mem, setMem_reg, setMem_mem_upd, setReg_out, setMem_out,
    hb, hl, hs, hp, ha, hread, hm, ho, ↓reduceIte]
  · congr 1
    omega

theorem decideAnswer_one_spec {S base length bound p : ℕ} {memory : ℕ → ℕ} {out : List ℕ}
    (hinputSpace : 4 * (base + length - 1) + 2 < S)
    (houtputSpace : 4 * bound + 1 < S) (hhead : memory (4 * bound + 1) = 1) :
    HTB S decideAnswer
      (fun c => DecisionGlobals base length bound p c ∧ c.mem = memory ∧ c.out = out)
      (fun c => c.reg budget = p ∧ c.reg alive = 0 ∧ c.mem = memory ∧ c.out = out) 20 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨⟨hb, hl, hs, hp, ha⟩, hm, ho⟩
  have hread : c.mem (bound + bound + (bound + bound) + 1) = 1 := by
    rw [show bound + bound + (bound + bound) + 1 = 4 * bound + 1 by omega, hm, hhead]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · addr_ok [decideAnswer, readAnswer, reject, hb, hl, hs, hp, ha, hm, hread, hhead]
  all_goals simp +decide only [decideAnswer, readAnswer, reject, run_seq', run_add,
    run_inc, run_dec, run_addc, run_subc, run_ifz', run_load, run_const, run_store,
    setReg_reg, setReg_mem, setMem_reg, setMem_mem_upd, setReg_out, setMem_out,
    hb, hl, hs, hp, ha, hread, hm, ho, ↓reduceIte]

end STACS2027.Runtimes.BoundedCost.OptControl
