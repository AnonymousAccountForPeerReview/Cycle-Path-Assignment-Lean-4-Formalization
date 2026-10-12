module

public import Runtimes.BoundedCost.OptControl
public import BoundedCost.Algorithm3Search
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.OptEmit

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost OptControl

set_option maxHeartbeats 1000000

def emitOne : Stmt := .seq (.add address span outputIndex)
  (.seq (.add address address address) (.seq (.add address address address)
  (.seq (addc address address 1) (.seq (.load answerBit address) (.write answerBit)))))

def emitBlock : Stmt := forUp outputIndex outputLength emitOne

def emitAnswer : Stmt := .seq (.write budget) emitBlock

def OutputInv (b : ℕ) (output old : List ℕ) (j : ℕ) (c : Config) : Prop :=
  c.reg span = b ∧ c.reg outputLength = output.length ∧
    (∀ i, i < output.length → c.mem (4 * (b + i) + 1) = output.getD i 0) ∧
    c.out = old ++ output.take j

theorem emitOne_spec {S b : ℕ} {output old : List ℕ} (hS : 4 * (b + output.length) + 1 ≤ S)
    (j : ℕ) (hj : j < output.length) :
    HTB S emitOne
      (fun c => OutputInv b output old j c ∧ c.reg outputIndex = j ∧ c.reg outputLength = output.length)
      (fun c => OutputInv b output old (j + 1) c ∧ c.reg outputIndex = j ∧ c.reg outputLength = output.length) 7 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨⟨hb, hl, hm, ho⟩, hi, _⟩
  have he : b + j + (b + j) + (b + j + (b + j)) + 1 = 4 * (b + j) + 1 := by omega
  have hread : c.mem (b + j + (b + j) + (b + j + (b + j)) + 1) = output.getD j 0 := by
    rw [he]
    exact hm j hj
  refine ⟨?_, ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · addr_ok [emitOne, hb, hl, hi]
  all_goals simp +decide only [emitOne, run_seq', run_add, run_addc, run_load, run_write,
    setReg_reg, setReg_mem, setReg_out, emit_reg, emit_mem, emit_out,
    hb, hl, hi, hread, ho, ↓reduceIte]
  · intro i hi
    exact hm i hi
  · rw [List.take_succ_eq_append_getElem hj]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some, List.append_assoc]

theorem emitBlock_spec {S b : ℕ} {output old : List ℕ}
    (hS : 4 * (b + output.length) + 1 ≤ S) :
    HTB S emitBlock (OutputInv b output old 0)
      (fun c => c.out = old ++ output) (11 * output.length + 3) := by
  have h := HTB.forUpC (S := S) (i := outputIndex) (n := outputLength)
    (N := output.length) (body := emitOne) (OutputInv b output old) 7
    (by decide) (by decide) (by decide) (fun _ => by indep [OutputInv])
    (fun j hj => emitOne_spec hS j hj)
  refine h.mono (fun c hc => ⟨hc, hc.2.1⟩) ?_ (by omega)
  intro c hc
  simpa using hc.1.2.2.2

theorem emitAnswer_spec {S b p : ℕ} {output old : List ℕ}
    (hS : 4 * (b + output.length) + 1 ≤ S) :
    HTB S emitAnswer
      (fun c => c.reg budget = p ∧ c.reg span = b ∧ c.reg outputLength = output.length ∧
        (∀ i, i < output.length → c.mem (4 * (b + i) + 1) = output.getD i 0) ∧ c.out = old)
      (fun c => c.out = old ++ p :: output) (11 * output.length + 4) := by
  have hw : HTB S (.write budget)
      (fun c => c.reg budget = p ∧ c.reg span = b ∧ c.reg outputLength = output.length ∧
        (∀ i, i < output.length → c.mem (4 * (b + i) + 1) = output.getD i 0) ∧ c.out = old)
      (OutputInv b output (old ++ [p]) 0) 1 := by
    refine HTB.run (by decide) ?_
    rintro c ⟨hp, hb, hl, hm, ho⟩
    refine ⟨AddrOK.of_memFree (by decide), hb, hl, hm, ?_⟩
    simp [run_write, hp, ho]
  simpa only [emitAnswer, List.append_assoc, List.singleton_append] using (hw.seq (emitBlock_spec hS)).weaken (by omega : 1 + (11 * output.length + 3) ≤ 11 * output.length + 4)

def captureLength : Stmt := mov (callerRegister outputLength) Flow.callCount

def program : Stmt := .seq captureLength (onCallerRegisters emitAnswer)

theorem program_spec {S b p : ℕ} {output old : List ℕ} (c₀ : Config)
    (hp : c₀.reg (callerRegister budget) = p) (hb : c₀.reg (callerRegister span) = b)
    (hl : c₀.reg Flow.callCount = output.length)
    (hm : ∀ i, i < output.length → c₀.mem (4 * (b + i) + 1) = output.getD i 0)
    (ho : c₀.out = old) (hS : 4 * (b + output.length) + 1 ≤ S) :
    HTB S program (· = c₀) (fun c => c.out = old ++ p :: output) (11 * output.length + 6) := by
  intro c hc
  subst c
  have hcapture : HTB S captureLength (· = c₀)
      (fun c => c.reg (callerRegister budget) = p ∧ c.reg (callerRegister span) = b ∧
        c.reg (callerRegister outputLength) = output.length ∧ c.mem = c₀.mem ∧ c.out = old) 2 := by
    refine HTB.run_le (by decide) (by decide) ?_
    intro c hc
    subst c
    refine ⟨AddrOK.of_memFree (by decide), ?_⟩
    simp +decide [captureLength, mov, hp, hb, hl, ho]
  obtain ⟨middle, time, he, h, ht⟩ := hcapture c₀ rfl
  obtain ⟨last, time', he', ho', ht'⟩ := onCallerRegisters_htb (emitAnswer_spec hS) middle
    ⟨h.1, h.2.1, h.2.2.1, by rw [registerView, h.2.2.2.1]; exact hm, h.2.2.2.2⟩
  exact ⟨last, time + time', .seq he he', ho', by omega⟩

/-- The optimizing program emits the optimum followed by a certified assignment. -/
def OptimumAnswer (g : Graph) (k : ℕ) (output : List ℕ) : Prop :=
  ∃ optimum answer, output = optimum :: answer ∧ IsOptimalCost g k optimum ∧
    BoundedCostAnswer g k optimum answer ∧ answer.getD 0 0 = 1

end STACS2027.Runtimes.BoundedCost.OptEmit
