module

public import Runtimes.BoundedCost.NormalizedAnswer
public import Outerplanar.RAM.BoundedLib
import Mathlib.Tactic

/-!
# RAM output of normalized Almost 2-SAT certificates

The component reads the original clause codes and a dense dual-literal truth
table. It emits deleted clause positions and occurring true variables in
increasing order. Artifact date: 2026-10-12.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.Certificate

open STACS2027 STACS2027.RAM Complexity.SAT
open STACS2027.Runtimes.BoundedCost

abbrev formulaBase : ℕ := 200
abbrev clauseCount : ℕ := 201
abbrev candidateBase : ℕ := 203
abbrev variableCount : ℕ := 220
abbrev index : ℕ := 230
abbrev offset : ℕ := 231
abbrev firstCode : ℕ := 232
abbrev secondCode : ℕ := 233
abbrev firstTruth : ℕ := 234
abbrev secondTruth : ℕ := 235
abbrev value : ℕ := 236
abbrev deletedCount : ℕ := 237
abbrev variableIndex : ℕ := 238
abbrev positiveCode : ℕ := 239
abbrev negativeCode : ℕ := 240
abbrev literalIndex : ℕ := 241
abbrev literalCount : ℕ := 242
abbrev literalValue : ℕ := 243
abbrev occurs : ℕ := 244

def scratch : List ℕ := rT :: (List.range' 230 12 ++ List.range' 243 57)

def readClause : Stmt :=
  .seq (.add offset index index)
    (.seq (ld firstCode formulaBase offset)
      (.seq (inc offset)
        (.seq (ld secondCode formulaBase offset)
          (.seq (ld firstTruth candidateBase firstCode)
            (.seq (ld secondTruth candidateBase secondCode)
              (.add value firstTruth secondTruth))))))

def countClause : Stmt := .seq readClause (.ifz value (inc deletedCount) .skip)

def emitClause : Stmt := .seq readClause (.ifz value (.write index) .skip)

def occurrenceBody : Stmt := .seq (ld literalValue formulaBase literalIndex)
  (ifEq literalValue positiveCode (.const occurs 1)
    (ifEq literalValue negativeCode (.const occurs 1) .skip))

def occurrenceScan : Stmt := .seq (.const occurs 0)
  (forUp literalIndex literalCount occurrenceBody)

def prepareVariable : Stmt := .seq (.add positiveCode variableIndex variableIndex)
  (addc negativeCode positiveCode 1)

def finishVariable : Stmt := .seq (ld value candidateBase positiveCode)
  (.ifz value .skip (.ifz occurs .skip (.write variableIndex)))

def emitVariable : Stmt := .seq prepareVariable (.seq occurrenceScan finishVariable)

def init : Stmt := .seq (.const deletedCount 0) (.add literalCount clauseCount clauseCount)

def header : Stmt := .seq (.const value 1) (.seq (.write value) (.write deletedCount))

def outputCertificate : Stmt := .seq init
  (.seq (forUp index clauseCount countClause)
    (.seq header (.seq (forUp index clauseCount emitClause)
      (forUp variableIndex variableCount emitVariable))))

def Globals (formula candidate m n : ℕ) (memory : ℕ → ℕ) (c : Config) : Prop :=
  c.reg formulaBase = formula ∧ c.reg candidateBase = candidate ∧
    c.reg clauseCount = m ∧ c.reg variableCount = n ∧
    c.reg literalCount = 2 * m ∧ c.mem = memory

/-- Every physical clause row contains the original two literal codes, and each
candidate table entry is exactly the truth value of that literal. -/
def ClauseMemory (f : CNF) (σ : Assignment) (formula candidate bound : ℕ)
    (memory : ℕ → ℕ) : Prop :=
  ∀ i (hi : i < f.length), ∃ a b : Literal,
    f[i] = [a, b] ∧ TwoSat.code a < bound ∧ TwoSat.code b < bound ∧
    memory (formula + 2 * i) = TwoSat.code a ∧
    memory (formula + 2 * i + 1) = TwoSat.code b ∧
    memory (candidate + TwoSat.code a) = (if evalLiteral σ a then 1 else 0) ∧
    memory (candidate + TwoSat.code b) = (if evalLiteral σ b then 1 else 0)

theorem globals_indep {formula candidate m n : ℕ} {memory : ℕ → ℕ}
    {W : List ℕ} (h : ∀ r ∈ W, r ∈ scratch) : Indep W (Globals formula candidate m n memory) := by
  intro c c' hag ⟨hf, hc, hm, hn, hl, hmemory⟩
  have hnmem : ∀ r, r ∉ scratch → r ∉ W := fun r hr hw => hr (h r hw)
  exact ⟨(hag.reg _ (hnmem _ (by decide))).trans hf,
    (hag.reg _ (hnmem _ (by decide))).trans hc,
    (hag.reg _ (hnmem _ (by decide))).trans hm,
    (hag.reg _ (hnmem _ (by decide))).trans hn,
    (hag.reg _ (hnmem _ (by decide))).trans hl, hag.mem.trans hmemory⟩

theorem readClause_loopFree : LoopFree readClause := by decide

theorem readClause_stores : stores readClause = false := by decide

theorem readClause_writes : writes readClause = false := by decide

theorem readClause_wregs {r : ℕ} (h : r ∈ wregs readClause) : r ∈ scratch := by
  simp [readClause, wregs, inc, addc] at h
  rcases h with h | h | h | h | h | h | h | h <;> subst r <;> decide

theorem readClause_spec {S formula candidate n bound : ℕ} {f : CNF} {σ : Assignment}
    {memory : ℕ → ℕ} (hmem : ClauseMemory f σ formula candidate bound memory)
    (hS : formula + 2 * f.length ≤ S ∧ candidate + bound ≤ S)
    (i : ℕ) (hi : i < f.length) :
    HTB S readClause
      (fun c => Globals formula candidate f.length n memory c ∧ c.reg index = i)
      (fun c => Globals formula candidate f.length n memory c ∧ c.reg index = i ∧
        (c.reg value = 0 ↔ evalClause σ (f.getD i []) = false)) 13 := by
  obtain ⟨a, b, hab, ha, hb, hmfirst, hmsecond, hta, htb⟩ := hmem i hi
  have hfirst : memory (formula + (i + i)) = TwoSat.code a := by
    simpa [Nat.two_mul] using hmfirst
  have hsecond : memory (formula + (i + i + 1)) = TwoSat.code b := by
    simpa [Nat.two_mul, Nat.add_assoc] using hmsecond
  refine HTB.run_le readClause_loopFree (by decide) ?_
  rintro c ⟨hg, hi'⟩
  obtain ⟨hf, hc, hm, hn, hl, hmemory⟩ := hg
  have hglobals : Globals formula candidate f.length n memory c :=
    ⟨hf, hc, hm, hn, hl, hmemory⟩
  have hr : (run readClause c).reg value =
      (if evalLiteral σ a then 1 else 0) + (if evalLiteral σ b then 1 else 0) := by
    simp +decide [readClause, inc, addc, hi', hf, hc, hmemory, hfirst, hsecond, hta, htb]
  refine ⟨?_, ?_⟩
  · addr_ok [readClause, inc, addc, hi', hf, hc, hmemory, hfirst, hsecond]
  · have hag : Agree scratch c (run readClause c) := agree_run readClause_loopFree
      readClause_stores readClause_writes (fun _ => readClause_wregs) c
    refine ⟨globals_indep (fun _ h => h) _ _ hag hglobals, ?_, ?_⟩
    · exact (run_reg_of_not_mem readClause_loopFree
        (by simp [readClause, wregs, inc, addc]) c).trans hi'
    · rw [hr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hab]
      cases hσa : evalLiteral σ a <;> cases hσb : evalLiteral σ b <;>
        simp [evalClause, hσa, hσb]

theorem readClause_checked {S formula candidate n bound : ℕ} {f : CNF} {σ : Assignment}
    {memory : ℕ → ℕ} (hmem : ClauseMemory f σ formula candidate bound memory)
    (hS : formula + 2 * f.length ≤ S ∧ candidate + bound ≤ S)
    {i : ℕ} (hi : i < f.length) (c : Config)
    (hg : Globals formula candidate f.length n memory c) (hindex : c.reg index = i) :
    AddrOK S readClause c ∧ Globals formula candidate f.length n memory (run readClause c) ∧
      (run readClause c).reg index = i ∧
      ((run readClause c).reg value = 0 ↔ evalClause σ (f.getD i []) = false) := by
  obtain ⟨d, t, he, hq, _⟩ := readClause_spec hmem hS i hi c ⟨hg, hindex⟩
  have haddr := he.addrOK readClause_loopFree
  obtain ⟨hd, _⟩ := Exec.det (exec_run readClause readClause_loopFree c) he.exec
  subst d
  exact ⟨haddr, hq⟩

def CountInv (formula candidate n : ℕ) (memory : ℕ → ℕ) (f : CNF)
    (σ : Assignment) (O : List ℕ) (j : ℕ) (c : Config) : Prop :=
  Globals formula candidate f.length n memory c ∧
    c.reg deletedCount = (falseIndicesPrefix σ f j).length ∧ c.out = O

theorem countInv_indep {formula candidate n j : ℕ} {memory : ℕ → ℕ}
    {f : CNF} {σ : Assignment} {O : List ℕ} :
    Indep [index, rT] (CountInv formula candidate n memory f σ O j) := by
  intro c c' hag ⟨hg, hd, ho⟩
  have hsub : ∀ r ∈ [index, rT], r ∈ scratch := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  exact ⟨globals_indep hsub _ _ hag hg,
    (hag.reg _ (by decide)).trans hd, hag.out.trans ho⟩

theorem countClause_spec {S formula candidate n bound j : ℕ} {f : CNF} {σ : Assignment}
    {memory : ℕ → ℕ} {O : List ℕ}
    (hmem : ClauseMemory f σ formula candidate bound memory)
    (hS : formula + 2 * f.length ≤ S ∧ candidate + bound ≤ S) (hj : j < f.length) :
    HTB S countClause
      (fun c => CountInv formula candidate n memory f σ O j c ∧
        c.reg index = j ∧ c.reg clauseCount = f.length)
      (fun c => CountInv formula candidate n memory f σ O (j + 1) c ∧
        c.reg index = j ∧ c.reg clauseCount = f.length) 18 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨⟨hg, hd, ho⟩, hi, hm⟩
  obtain ⟨ha, hg', hi', hv⟩ := readClause_checked hmem hS hj c hg hi
  let d := run readClause c
  have hiD : d.reg index = j := hi'
  have hmD : d.reg clauseCount = f.length := hg'.2.2.1
  have hdagree : Agree scratch c d := agree_run readClause_loopFree
    readClause_stores readClause_writes (fun _ => readClause_wregs) c
  have hd' : d.reg deletedCount = (falseIndicesPrefix σ f j).length :=
    (run_reg_of_not_mem readClause_loopFree (by simp [readClause, wregs, inc, addc]) c).trans hd
  have ho' : d.out = O := hdagree.out.trans ho
  refine ⟨AddrOK.seq ha (AddrOK.of_memFree rfl), ?_⟩
  change CountInv formula candidate n memory f σ O (j + 1)
    (run (.ifz value (inc deletedCount) .skip) d) ∧
    (run (.ifz value (inc deletedCount) .skip) d).reg index = j ∧
    (run (.ifz value (inc deletedCount) .skip) d).reg clauseCount = f.length
  simp only [CountInv, falseIndicesPrefix_succ]
  by_cases hz : d.reg value = 0
  · have hf : evalClause σ (f.getD j []) = false := hv.mp hz
    have hf' := hf
    simp only [List.getD_eq_getElem?_getD] at hf'
    have hw : ∀ r ∈ wregs (inc deletedCount), r ∈ scratch := by
      intro r hr
      simp [inc, addc, wregs] at hr
      rcases hr with rfl | rfl <;> decide
    have hag : Agree scratch d (run (inc deletedCount) d) := agree_run
      (by decide) (by decide) (by decide) hw d
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · simpa [run_ifz', hz] using globals_indep (fun _ h => h) _ _ hag hg'
    · simp [run_ifz', hz, run_inc (show deletedCount ≠ rT by decide), hd', hf']
    · simpa [run_ifz', hz] using hag.out.trans ho'
    · simpa [run_ifz', hz, run_inc (show deletedCount ≠ rT by decide)] using hiD
    · simpa [run_ifz', hz, run_inc (show deletedCount ≠ rT by decide)] using hmD
  · have hf : evalClause σ (f.getD j []) = true :=
      Bool.eq_true_of_ne_false (fun h => hz (hv.mpr h))
    have hf' := hf
    simp only [List.getD_eq_getElem?_getD] at hf'
    simpa [run_ifz', hz, hf'] using
      (show (Globals formula candidate f.length n memory d ∧
        d.reg deletedCount = (falseIndicesPrefix σ f j).length ∧ d.out = O) ∧
        d.reg index = j ∧ d.reg clauseCount = f.length from
        ⟨⟨hg', hd', ho'⟩, hi', hg'.2.2.1⟩)

theorem countDeleted_spec {S formula candidate n bound : ℕ} {f : CNF} {σ : Assignment}
    {memory : ℕ → ℕ} {O : List ℕ}
    (hmem : ClauseMemory f σ formula candidate bound memory)
    (hS : formula + 2 * f.length ≤ S ∧ candidate + bound ≤ S) :
    HTB S (forUp index clauseCount countClause)
      (fun c => Globals formula candidate f.length n memory c ∧
        c.reg deletedCount = 0 ∧ c.out = O)
      (fun c => Globals formula candidate f.length n memory c ∧
        c.reg deletedCount = (falseIndices σ f).length ∧ c.out = O)
      (22 * f.length + 3) := by
  have h := HTB.forUpC (CountInv formula candidate n memory f σ O) 18
    (by decide) (by decide) (by decide) (fun _ => countInv_indep)
    (fun _ hj => countClause_spec hmem hS hj)
  refine h.mono ?_ ?_ (by omega)
  · intro c ⟨hg, hd, ho⟩
    exact ⟨⟨hg, by simpa using hd, ho⟩, hg.2.2.1⟩
  · rintro c ⟨⟨hg, hd, ho⟩, _, _⟩
    refine ⟨hg, ?_, ho⟩
    rw [falseIndices_as_filterRange]
    exact hd

def EmitInv (formula candidate n : ℕ) (memory : ℕ → ℕ) (f : CNF)
    (σ : Assignment) (O : List ℕ) (j : ℕ) (c : Config) : Prop :=
  Globals formula candidate f.length n memory c ∧
    c.reg deletedCount = (falseIndices σ f).length ∧
    c.out = O ++ falseIndicesPrefix σ f j

theorem emitInv_indep {formula candidate n j : ℕ} {memory : ℕ → ℕ}
    {f : CNF} {σ : Assignment} {O : List ℕ} :
    Indep [index, rT] (EmitInv formula candidate n memory f σ O j) := by
  intro c c' hag ⟨hg, hd, ho⟩
  have hsub : ∀ r ∈ [index, rT], r ∈ scratch := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  exact ⟨globals_indep hsub _ _ hag hg,
    (hag.reg _ (by decide)).trans hd, hag.out.trans ho⟩

theorem emitClause_spec {S formula candidate n bound j : ℕ} {f : CNF} {σ : Assignment}
    {memory : ℕ → ℕ} {O : List ℕ}
    (hmem : ClauseMemory f σ formula candidate bound memory)
    (hS : formula + 2 * f.length ≤ S ∧ candidate + bound ≤ S) (hj : j < f.length) :
    HTB S emitClause
      (fun c => EmitInv formula candidate n memory f σ O j c ∧
        c.reg index = j ∧ c.reg clauseCount = f.length)
      (fun c => EmitInv formula candidate n memory f σ O (j + 1) c ∧
        c.reg index = j ∧ c.reg clauseCount = f.length) 18 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨⟨hg, hd, ho⟩, hi, _⟩
  obtain ⟨ha, hg', hi', hv⟩ := readClause_checked hmem hS hj c hg hi
  let d := run readClause c
  have hgD : Globals formula candidate f.length n memory d := hg'
  have hiD : d.reg index = j := hi'
  have hmD : d.reg clauseCount = f.length := hg'.2.2.1
  have hdD : d.reg deletedCount = (falseIndices σ f).length :=
    (run_reg_of_not_mem readClause_loopFree (by simp [readClause, wregs, inc, addc]) c).trans hd
  have hoD : d.out = O ++ falseIndicesPrefix σ f j :=
    (run_out_of_writes readClause_loopFree readClause_writes c).trans ho
  refine ⟨AddrOK.seq ha (AddrOK.of_memFree rfl), ?_⟩
  change EmitInv formula candidate n memory f σ O (j + 1)
    (run (.ifz value (.write index) .skip) d) ∧
    (run (.ifz value (.write index) .skip) d).reg index = j ∧
    (run (.ifz value (.write index) .skip) d).reg clauseCount = f.length
  simp only [EmitInv, falseIndicesPrefix_succ]
  by_cases hz : d.reg value = 0
  · have hf := hv.mp hz
    simp only [List.getD_eq_getElem?_getD] at hf
    simpa [run_ifz', hz, hf, Globals, hiD, hoD, List.append_assoc] using
      (show (Globals formula candidate f.length n memory d ∧
        d.reg deletedCount = (falseIndices σ f).length ∧
        d.out = O ++ falseIndicesPrefix σ f j) ∧ d.reg index = j ∧
        d.reg clauseCount = f.length from ⟨⟨hgD, hdD, hoD⟩, hiD, hmD⟩)
  · have hf : evalClause σ (f.getD j []) = true :=
      Bool.eq_true_of_ne_false (fun h => hz (hv.mpr h))
    simp only [List.getD_eq_getElem?_getD] at hf
    simpa [run_ifz', hz, hf] using
      (show (Globals formula candidate f.length n memory d ∧
        d.reg deletedCount = (falseIndices σ f).length ∧
        d.out = O ++ falseIndicesPrefix σ f j) ∧ d.reg index = j ∧
        d.reg clauseCount = f.length from ⟨⟨hgD, hdD, hoD⟩, hiD, hmD⟩)

theorem emitDeleted_spec {S formula candidate n bound : ℕ} {f : CNF} {σ : Assignment}
    {memory : ℕ → ℕ} {O : List ℕ}
    (hmem : ClauseMemory f σ formula candidate bound memory)
    (hS : formula + 2 * f.length ≤ S ∧ candidate + bound ≤ S) :
    HTB S (forUp index clauseCount emitClause)
      (fun c => Globals formula candidate f.length n memory c ∧
        c.reg deletedCount = (falseIndices σ f).length ∧ c.out = O)
      (fun c => Globals formula candidate f.length n memory c ∧
        c.reg deletedCount = (falseIndices σ f).length ∧ c.out = O ++ falseIndices σ f)
      (22 * f.length + 3) := by
  have h := HTB.forUpC (EmitInv formula candidate n memory f σ O) 18
    (by decide) (by decide) (by decide) (fun _ => emitInv_indep)
    (fun _ hj => emitClause_spec hmem hS hj)
  refine h.mono ?_ ?_ (by omega)
  · intro c ⟨hg, hd, ho⟩
    exact ⟨⟨hg, hd, by simpa using ho⟩, hg.2.2.1⟩
  · rintro c ⟨⟨hg, hd, ho⟩, _, _⟩
    refine ⟨hg, hd, ?_⟩
    rw [falseIndices_as_filterRange]
    exact ho

theorem header_spec {S formula candidate n : ℕ} {f : CNF} {memory : ℕ → ℕ}
    {σ : Assignment} {O : List ℕ} :
    HTB S header
      (fun c => Globals formula candidate f.length n memory c ∧
        c.reg deletedCount = (falseIndices σ f).length ∧ c.out = O)
      (fun c => Globals formula candidate f.length n memory c ∧
        c.reg deletedCount = (falseIndices σ f).length ∧
        c.out = O ++ [1, (falseIndices σ f).length]) 3 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨hg, hd, ho⟩
  exact ⟨AddrOK.of_memFree rfl, by
    simpa [header, Globals, hd, ho, List.append_assoc] using hg⟩

def seen (codes : List ℕ) (v j : ℕ) : ℕ :=
  if 2 * v ∈ codes.take j ∨ 2 * v + 1 ∈ codes.take j then 1 else 0

theorem seen_succ {codes : List ℕ} {v j : ℕ} (hj : j < codes.length) :
    seen codes v (j + 1) =
      if codes[j] = 2 * v ∨ codes[j] = 2 * v + 1 then 1 else seen codes v j := by
  rw [seen, List.take_succ_eq_append_getElem hj]
  simp only [List.mem_append, List.mem_singleton]
  by_cases hp : codes[j] = 2 * v <;> by_cases hn : codes[j] = 2 * v + 1 <;>
    by_cases hseen : 2 * v ∈ codes.take j ∨ 2 * v + 1 ∈ codes.take j <;>
    simp_all [seen, eq_comm]

def OccurrenceInv (formula candidate n : ℕ) (memory : ℕ → ℕ) (f : CNF)
    (σ : Assignment) (O : List ℕ) (v j : ℕ) (c : Config) : Prop :=
  Globals formula candidate f.length n memory c ∧
    c.reg variableIndex = v ∧ c.reg positiveCode = 2 * v ∧
    c.reg negativeCode = 2 * v + 1 ∧ c.reg deletedCount = (falseIndices σ f).length ∧
    c.reg occurs = seen (TwoSat.codes f) v j ∧ c.out = O

theorem occurrenceBody_spec {S formula candidate n v j : ℕ} {f : CNF} {σ : Assignment}
    {memory : ℕ → ℕ} {O : List ℕ}
    (hcodes : (TwoSat.codes f).length = 2 * f.length)
    (hmem : Arr memory formula (TwoSat.codes f))
    (hS : formula + 2 * f.length ≤ S) (hj : j < 2 * f.length) :
    HTB S occurrenceBody
      (fun c => OccurrenceInv formula candidate n memory f σ O v j c ∧
        c.reg literalIndex = j ∧ c.reg literalCount = 2 * f.length)
      (fun c => OccurrenceInv formula candidate n memory f σ O v (j + 1) c ∧
        c.reg literalIndex = j ∧ c.reg literalCount = 2 * f.length) 30 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨⟨hg, hv, hp, hn, hd, hs, ho⟩, hi, hl⟩
  have hj' : j < (TwoSat.codes f).length := by omega
  have hm : c.mem (formula + j) = (TwoSat.codes f)[j] := by
    rw [hg.2.2.2.2.2]
    exact hmem j hj'
  have hiGlobal : Indep (wregs occurrenceBody)
      (fun c => Globals formula candidate f.length n memory c ∧
        c.reg variableIndex = v ∧ c.reg positiveCode = 2 * v ∧
        c.reg negativeCode = 2 * v + 1 ∧ c.reg deletedCount = (falseIndices σ f).length ∧
        c.out = O ∧ c.reg literalIndex = j ∧ c.reg literalCount = 2 * f.length) := by
    indep [Globals, occurrenceBody, wregs, ifEq, ld]
  have hframe := hiGlobal.run (by decide) (by decide) (by decide)
    (show Globals formula candidate f.length n memory c ∧
      c.reg variableIndex = v ∧ c.reg positiveCode = 2 * v ∧
      c.reg negativeCode = 2 * v + 1 ∧ c.reg deletedCount = (falseIndices σ f).length ∧
      c.out = O ∧ c.reg literalIndex = j ∧ c.reg literalCount = 2 * f.length from
      ⟨hg, hv, hp, hn, hd, ho, hi, hl⟩)
  obtain ⟨hg', hv', hp', hn', hd', ho', hi', hl'⟩ := hframe
  refine ⟨?_, ⟨hg', hv', hp', hn', hd', ?_, ho'⟩, hi', hl'⟩
  · apply AddrOK.seq
    · simp only [addrOK_ld, hg.1, hi]
      omega
    · exact AddrOK.of_memFree rfl
  · rw [seen_succ hj']
    by_cases hpos : (TwoSat.codes f)[j] = 2 * v <;>
      by_cases hneg : (TwoSat.codes f)[j] = 2 * v + 1 <;>
      simp +decide [occurrenceBody, run_ifEq (show literalValue ≠ rT by decide)
        (show positiveCode ≠ rT by decide),
        run_ifEq (show literalValue ≠ rT by decide) (show negativeCode ≠ rT by decide),
        hg.1, hi, hm, hp, hn, hs, hpos, hneg]

theorem occurrenceScan_spec {S formula candidate n v : ℕ} {f : CNF} {σ : Assignment}
    {memory : ℕ → ℕ} {O : List ℕ}
    (hcodes : (TwoSat.codes f).length = 2 * f.length)
    (hmem : Arr memory formula (TwoSat.codes f)) (hS : formula + 2 * f.length ≤ S) :
    HTB S occurrenceScan
      (fun c => Globals formula candidate f.length n memory c ∧
        c.reg variableIndex = v ∧ c.reg positiveCode = 2 * v ∧
        c.reg negativeCode = 2 * v + 1 ∧ c.reg deletedCount = (falseIndices σ f).length ∧
        c.out = O)
      (fun c => Globals formula candidate f.length n memory c ∧
        c.reg variableIndex = v ∧ c.reg positiveCode = 2 * v ∧
        c.reg negativeCode = 2 * v + 1 ∧ c.reg deletedCount = (falseIndices σ f).length ∧
        c.reg occurs = (if occursInBool f v then 1 else 0) ∧ c.out = O)
      (68 * f.length + 4) := by
  let Inv := OccurrenceInv formula candidate n memory f σ O v
  have hinit : HTB S (.const occurs 0)
      (fun c => Globals formula candidate f.length n memory c ∧
        c.reg variableIndex = v ∧ c.reg positiveCode = 2 * v ∧
        c.reg negativeCode = 2 * v + 1 ∧ c.reg deletedCount = (falseIndices σ f).length ∧
        c.out = O)
      (fun c => Inv 0 c ∧ c.reg literalCount = 2 * f.length) 1 := by
    refine HTB.run_le (by decide) (by decide) ?_
    rintro c ⟨hg, hv, hp, hn, hd, ho⟩
    have hgi : Indep [occurs] (Globals formula candidate f.length n memory) := by
      indep [Globals]
    have hgp : Globals formula candidate f.length n memory (c.setReg occurs 0) :=
      hgi.setReg (by simp) 0 hg
    refine ⟨trivial, ⟨hgp, ?_, ?_, ?_, ?_, ?_, ?_⟩, hgp.2.2.2.2.1⟩
    · simpa using hv
    · simpa using hp
    · simpa using hn
    · simpa using hd
    · simp [seen]
    · simpa using ho
  have hloop := HTB.forUpC (S := S) (i := literalIndex) (n := literalCount)
    Inv 30 (by decide) (by decide) (by decide)
    (fun _ => by indep [Inv, OccurrenceInv, Globals])
    (fun _ hj => occurrenceBody_spec hcodes hmem hS hj)
  refine (hinit.seq hloop).mono (fun _ h => h) ?_ (by omega)
  rintro c ⟨⟨hg, hv, hp, hn, hd, hs, ho⟩, _, _⟩
  refine ⟨hg, hv, hp, hn, hd, ?_, ho⟩
  have htake : (TwoSat.codes f).take (2 * f.length) = TwoSat.codes f := by
    rw [← hcodes, List.take_length]
  change c.reg occurs = _ at hs ⊢
  rw [seen, htake] at hs
  have hiff := occursInBool_iff_codes f v
  cases hv : occursInBool f v <;> simp_all

theorem trueVariables_succ (n : ℕ) (f : CNF) (σ : Assignment) :
    trueVariables (n + 1) f σ = trueVariables n f σ ++
      if σ n && occursInBool f n then [n] else [] := by
  cases hσ : σ n <;> cases ho : occursInBool f n <;>
    simp [trueVariables, List.range_succ, List.filter_append, hσ, ho]

theorem finishVariable_spec {S formula candidate n v : ℕ} {f : CNF} {σ : Assignment}
    {memory : ℕ → ℕ} {O : List ℕ}
    (htruth : memory (candidate + 2 * v) = (if σ v then 1 else 0))
    (hS : candidate + 2 * n ≤ S) (hv : v < n) :
    HTB S finishVariable
      (fun c => Globals formula candidate f.length n memory c ∧
        c.reg variableIndex = v ∧ c.reg positiveCode = 2 * v ∧
        c.reg negativeCode = 2 * v + 1 ∧ c.reg deletedCount = (falseIndices σ f).length ∧
        c.reg occurs = (if occursInBool f v then 1 else 0) ∧ c.out = O)
      (fun c => Globals formula candidate f.length n memory c ∧
        c.reg variableIndex = v ∧ c.reg deletedCount = (falseIndices σ f).length ∧
        c.out = O ++ if σ v && occursInBool f v then [v] else []) 10 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨hg, hvar, hp, hn, hd, hocc, ho⟩
  have hc := hg.2.1
  have hm := hg.2.2.2.2.2
  refine ⟨?_, ?_⟩
  · apply AddrOK.seq
    · simp only [addrOK_ld, hc, hp]
      omega
    · exact AddrOK.of_memFree rfl
  · cases hs : σ v <;> cases he : occursInBool f v <;>
      simpa +decide [finishVariable, Globals, hc, hp, hm, htruth, hvar,
        hd, hocc, ho, hs, he] using hg

def VariableInv (formula candidate n : ℕ) (memory : ℕ → ℕ) (f : CNF)
    (σ : Assignment) (O : List ℕ) (j : ℕ) (c : Config) : Prop :=
  Globals formula candidate f.length n memory c ∧
    c.reg deletedCount = (falseIndices σ f).length ∧ c.out = O ++ trueVariables j f σ

theorem emitVariable_spec {S formula candidate n v : ℕ} {f : CNF} {σ : Assignment}
    {memory : ℕ → ℕ} {O : List ℕ}
    (hcodes : (TwoSat.codes f).length = 2 * f.length)
    (hmem : Arr memory formula (TwoSat.codes f))
    (htruth : ∀ x, x < n → memory (candidate + 2 * x) = (if σ x then 1 else 0))
    (hS : formula + 2 * f.length ≤ S ∧ candidate + 2 * n ≤ S) (hv : v < n) :
    HTB S emitVariable
      (fun c => VariableInv formula candidate n memory f σ O v c ∧
        c.reg variableIndex = v ∧ c.reg variableCount = n)
      (fun c => VariableInv formula candidate n memory f σ O (v + 1) c ∧
        c.reg variableIndex = v ∧ c.reg variableCount = n) (100 * (f.length + 1)) := by
  have hp : HTB S prepareVariable
      (fun c => VariableInv formula candidate n memory f σ O v c ∧
        c.reg variableIndex = v ∧ c.reg variableCount = n)
      (fun c => Globals formula candidate f.length n memory c ∧
        c.reg variableIndex = v ∧ c.reg positiveCode = 2 * v ∧
        c.reg negativeCode = 2 * v + 1 ∧ c.reg deletedCount = (falseIndices σ f).length ∧
        c.out = O ++ trueVariables v f σ) 3 := by
    refine HTB.run_le (by decide) (by decide) ?_
    rintro c ⟨⟨hg, hd, ho⟩, hvar, _⟩
    exact ⟨AddrOK.of_memFree rfl, by
      simpa +decide [prepareVariable, addc, Globals, hvar, hd, ho, Nat.two_mul] using hg⟩
  have hs := occurrenceScan_spec (candidate := candidate) (n := n) (σ := σ)
    (v := v) (O := O ++ trueVariables v f σ) hcodes hmem hS.1
  have hf := finishVariable_spec (formula := formula) (f := f)
    (O := O ++ trueVariables v f σ) (htruth v hv) hS.2 hv
  have h := hp.seq (hs.seq hf)
  change HTB S (.seq prepareVariable (.seq occurrenceScan finishVariable)) _ _ _
  refine h.mono (fun _ h => h) ?_ (by omega)
  rintro c ⟨hg, hvar, hd, ho⟩
  exact ⟨⟨hg, hd, by simpa only [trueVariables_succ, List.append_assoc] using ho⟩,
    hvar, hg.2.2.2.1⟩

theorem emitTrueVariables_spec {S formula candidate n : ℕ} {f : CNF} {σ : Assignment}
    {memory : ℕ → ℕ} {O : List ℕ}
    (hcodes : (TwoSat.codes f).length = 2 * f.length)
    (hmem : Arr memory formula (TwoSat.codes f))
    (htruth : ∀ x, x < n → memory (candidate + 2 * x) = (if σ x then 1 else 0))
    (hS : formula + 2 * f.length ≤ S ∧ candidate + 2 * n ≤ S) :
    HTB S (forUp variableIndex variableCount emitVariable)
      (fun c => Globals formula candidate f.length n memory c ∧
        c.reg deletedCount = (falseIndices σ f).length ∧ c.out = O)
      (fun c => Globals formula candidate f.length n memory c ∧
        c.reg deletedCount = (falseIndices σ f).length ∧ c.out = O ++ trueVariables n f σ)
      (104 * n * (f.length + 1) + 3) := by
  have h := HTB.forUpC (S := S) (i := variableIndex) (n := variableCount)
    (VariableInv formula candidate n memory f σ O) (100 * (f.length + 1))
    (by decide) (by decide) (by decide)
    (fun _ => by indep [VariableInv, Globals])
    (fun _ hv => emitVariable_spec hcodes hmem htruth hS hv)
  refine h.mono ?_ ?_ (by nlinarith)
  · rintro c ⟨hg, hd, ho⟩
    exact ⟨⟨hg, hd, by simpa [trueVariables] using ho⟩, hg.2.2.2.1⟩
  · rintro c ⟨hi, _, _⟩
    exact hi

def InputGlobals (formula candidate m n : ℕ) (memory : ℕ → ℕ) (c : Config) : Prop :=
  c.reg formulaBase = formula ∧ c.reg candidateBase = candidate ∧
    c.reg clauseCount = m ∧ c.reg variableCount = n ∧ c.mem = memory

theorem init_spec {S formula candidate m n : ℕ} {memory : ℕ → ℕ} {O : List ℕ} :
    HTB S init (fun c => InputGlobals formula candidate m n memory c ∧ c.out = O)
      (fun c => Globals formula candidate m n memory c ∧
        c.reg deletedCount = 0 ∧ c.out = O) 2 := by
  refine HTB.run_le (by decide) (by decide) ?_
  rintro c ⟨⟨hf, hc, hm, hn, hmemory⟩, ho⟩
  exact ⟨AddrOK.of_memFree rfl, by
    simp +decide [init, Globals, hf, hc, hm, hn, hmemory, ho, Nat.two_mul]⟩

/-- The complete read-only certificate emitter has an explicit polynomial bound
and preserves the original formula and computed truth table. -/
theorem outputCertificate_spec {S formula candidate n : ℕ} {f : CNF} {σ : Assignment}
    {memory : ℕ → ℕ} {O : List ℕ}
    (hclause : ClauseMemory f σ formula candidate (2 * n) memory)
    (hcodes : (TwoSat.codes f).length = 2 * f.length)
    (hmem : Arr memory formula (TwoSat.codes f))
    (htruth : ∀ x, x < n → memory (candidate + 2 * x) = (if σ x then 1 else 0))
    (hS : formula + 2 * f.length ≤ S ∧ candidate + 2 * n ≤ S) :
    HTB S outputCertificate
      (fun c => InputGlobals formula candidate f.length n memory c ∧ c.out = O)
      (fun c => Globals formula candidate f.length n memory c ∧
        c.out = O ++ [1, (falseIndices σ f).length] ++ falseIndices σ f ++
          trueVariables n f σ) (160 * (n + 1) * (f.length + 1)) := by
  have hi := init_spec (S := S) (formula := formula) (candidate := candidate)
    (m := f.length) (n := n) (memory := memory) (O := O)
  have hc := countDeleted_spec (n := n) (O := O) hclause hS
  have hh := header_spec (S := S) (formula := formula) (candidate := candidate)
    (n := n) (f := f) (memory := memory) (σ := σ) (O := O)
  have he := emitDeleted_spec (n := n) (O := O ++ [1, (falseIndices σ f).length]) hclause hS
  have hv := emitTrueVariables_spec (candidate := candidate) (n := n) (σ := σ)
    (O := (O ++ [1, (falseIndices σ f).length]) ++ falseIndices σ f)
    hcodes hmem htruth hS
  have h := hi.seq (hc.seq (hh.seq (he.seq hv)))
  change HTB S (.seq init (.seq (forUp index clauseCount countClause)
    (.seq header (.seq (forUp index clauseCount emitClause)
      (forUp variableIndex variableCount emitVariable))))) _ _ _
  exact h.mono (fun _ h => h) (fun _ h => ⟨h.1, h.2.2⟩) (by nlinarith)

/-- For the dense solver domain this is precisely the normalized positive
answer required by `Almost2SatSolver`. -/
theorem outputCertificate_assignmentAnswer {S formula candidate : ℕ} {f : CNF}
    {σ : Assignment} {memory : ℕ → ℕ} {O : List ℕ}
    (hclause : ClauseMemory f σ formula candidate (2 * (2 * f.length + 1)) memory)
    (hcodes : (TwoSat.codes f).length = 2 * f.length)
    (hmem : Arr memory formula (TwoSat.codes f))
    (htruth : ∀ x, x < 2 * f.length + 1 →
      memory (candidate + 2 * x) = (if σ x then 1 else 0))
    (hS : formula + 2 * f.length ≤ S ∧ candidate + 2 * (2 * f.length + 1) ≤ S) :
    HTB S outputCertificate
      (fun c => InputGlobals formula candidate f.length (2 * f.length + 1) memory c ∧ c.out = O)
      (fun c => Globals formula candidate f.length (2 * f.length + 1) memory c ∧
        c.out = O ++ assignmentAnswer f σ) (320 * (f.length + 1) ^ 2) := by
  refine (outputCertificate_spec hclause hcodes hmem htruth hS).mono
    (fun _ h => h) ?_ (by nlinarith)
  rintro c ⟨hg, ho⟩
  exact ⟨hg, by simpa [assignmentAnswer, List.append_assoc] using ho⟩

end STACS2027.Runtimes.BoundedCost.Certificate
