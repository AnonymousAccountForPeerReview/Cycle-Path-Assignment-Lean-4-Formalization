module

public import ApproximationHardness.Registered.Records
import Lean.Elab.Tactic.Omega

/-!
# Correctness of the instance-map machine on encoded formulas

For every formula `f` whose clauses have two or three literals, the machine's
output on `encode f` is `encode (formulaRecords k f).reverse`
(`instanceMapWord_encode`): the records of the edges of the Theorem 8 graph,
in reverse order.
-/

@[expose] public section

namespace STACS2027.Registered

open Complexity
open Complexity.SAT
open Complexity.StackMachine (Registers set)

/-! ### Reading registers after each stage -/

theorem finishModel_j (r : Regs) : finishModel r R.j = true :: r R.j := by
  simp +decide [finishModel, clearAllModel, slotRegs, StackMachine.set]

theorem finishModel_other (r : Regs) (x : Reg) (hx : x ∉ slotRegs) (hj : x ≠ R.j) :
    finishModel r x = r x := by
  simp only [slotRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := hx
  simp [finishModel, clearAllModel, slotRegs, StackMachine.set, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, hj]

theorem emitEdgesModel_out (es : List (Endpoint × Endpoint)) (r : Regs) :
    emitEdgesModel es r R.out = recordsWord es r ++ r R.out := by
  simp +decide [emitEdgesModel, StackMachine.set]

theorem emitEdgesModel_cnt (es : List (Endpoint × Endpoint)) (r : Regs) :
    emitEdgesModel es r R.cnt = unary es.length ++ r R.cnt := by
  simp [emitEdgesModel, StackMachine.set]

theorem emitEdgesModel_other (es : List (Endpoint × Endpoint)) (r : Regs) (x : Reg) (h1 : x ≠ R.out)
    (h2 : x ≠ R.cnt) : emitEdgesModel es r x = r x := by
  simp [emitEdgesModel, StackMachine.set, h1, h2]

theorem setupModel_bnj (k : Nat) (r : Regs) :
    setupModel k r R.bnj = unary (gadgetWidth k * ((r R.j).length + (r R.n).length)) := by
  simp +decide [setupModel, StackMachine.set]

theorem setupModel_other (k : Nat) (r : Regs) (x : Reg) (h1 : x ≠ R.bnj) (h2 : x ≠ R.nj) :
    setupModel k r x = r x := by
  simp [setupModel, StackMachine.set, h1, h2]

theorem litState_inB (k i : Nat) (l : Literal) (rest : SAT.Word) (past : List Literal) (r : Regs) :
    litState k i l rest past r R.inB = rest := by
  simp +decide [litState, StackMachine.set]

theorem litState_done (k i : Nat) (l : Literal) (rest : SAT.Word) (past : List Literal) (r : Regs) :
    litState k i l rest past r R.done = encodeLiteral l ++ r R.done := by
  simp +decide [litState, StackMachine.set]

theorem litState_dc (k i : Nat) (l : Literal) (rest : SAT.Word) (past : List Literal) (r : Regs) :
    litState k i l rest past r R.dc = true :: r R.dc := by
  simp +decide [litState, StackMachine.set]

theorem litState_B (k i : Nat) (l : Literal) (rest : SAT.Word) (past : List Literal) (r : Regs) :
    litState k i l rest past r (slotB i) = unary (gadgetWidth k * l.var) := by
  simp [litState]

theorem litState_E (k i : Nat) (l : Literal) (rest : SAT.Word) (past : List Literal) (r : Regs) (b : Bool) :
    litState k i l rest past r (slotE i b) = unary (variableEndpoint (placed l past).port b) := by
  have hfs := slotE_ne_slotE_side i i
  cases b <;> simp [litState, StackMachine.set, hfs]

/-- The registers `litState` writes. -/
def litRegs (i : Nat) : List Reg :=
  [R.inB, R.done, R.dc, R.scan, R.sc, R.cE, slotS i, slotV i, slotE i false, slotE i true, slotB i]

theorem litState_other (k i : Nat) (l : Literal) (rest : SAT.Word) (past : List Literal) (r : Regs) (x : Reg)
    (hx : x ∉ litRegs i) : litState k i l rest past r x = r x := by
  simp only [litRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hx
  simp [litState, StackMachine.set, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

/-! ### The endpoint values of a clause gadget -/

theorem clauseEndpoint_value (k n j len : Nat) (pc : List PlacedLiteral) (hlen : pc.length = len) (r : Regs)
    (hB : ∀ i (h : i < pc.length), (r (slotB i)).length = gadgetWidth k * pc[i].literal.var)
    (hE : ∀ i (h : i < pc.length) b, (r (slotE i b)).length = variableEndpoint pc[i].port b)
    (hbnj : (r R.bnj).length = gadgetWidth k * (j + n)) (a : Nat) :
    (clauseEndpoint len a).value r = clauseVertex (gadgetWidth k) n j pc a := by
  subst hlen
  unfold clauseEndpoint clauseVertex attachmentAt
  cases h : clausePortAt a with
  | none =>
    simp only [Option.bind_none, Endpoint.value, hbnj, blockVertex]
    rw [Nat.mul_comm, Nat.add_comm j n]
  | some ib =>
    obtain ⟨i, side⟩ := ib
    by_cases hi : i < pc.length
    · simp only [Option.bind_some, hi, ↓reduceIte, List.getElem?_eq_getElem hi, Option.map_some,
        Endpoint.value, hB i hi, hE i hi side, blockVertex]
      rw [Nat.mul_comm]
    · simp only [Option.bind_some, hi, ↓reduceIte, List.getElem?_eq_none (Nat.le_of_not_lt hi),
        Option.map_none, Endpoint.value, hbnj, blockVertex]
      rw [Nat.mul_comm, Nat.add_comm j n]

theorem clauseEdges_records (k n j len : Nat) (pc : List PlacedLiteral) (hlen : pc.length = len) (r : Regs)
    (hB : ∀ i (h : i < pc.length), (r (slotB i)).length = gadgetWidth k * pc[i].literal.var)
    (hE : ∀ i (h : i < pc.length) b, (r (slotE i b)).length = variableEndpoint pc[i].port b)
    (hbnj : (r R.bnj).length = gadgetWidth k * (j + n)) :
    (clauseEdges k len).map (fun e => edgeRecord e.1 e.2 r) =
      rawRecords (clauseVertex (gadgetWidth k) n j pc) (clauseGraph k pc) := by
  have hg : clauseGraph k pc = gadgetEdges k len := by
    simp only [clauseGraph, gadgetEdges, hlen]
  rw [hg]
  simp only [clauseEdges, rawRecords, List.map_map]
  apply List.map_congr_left
  intro e _
  simp only [Function.comp, edgeRecord, pairRecord,
    clauseEndpoint_value k n j len pc hlen r hB hE hbnj]

/-! ### Setup, emission and finish of one clause -/

theorem unary_append_comm (a b : Nat) : unary a ++ unary b = unary (b + a) := by
  simp [unary, Nat.add_comm]

theorem tail_eval (k n j len c : Nat) (pc : List PlacedLiteral) (hlen : pc.length = len) (r : Regs)
    (hB : ∀ i (h : i < pc.length), r (slotB i) = unary (gadgetWidth k * pc[i].literal.var))
    (hE : ∀ i (h : i < pc.length) b, r (slotE i b) = unary (variableEndpoint pc[i].port b))
    (hj : r R.j = unary j) (hn : r R.n = unary n) (hc : r R.cnt = unary c) :
    let r' := finishModel (emitEdgesModel (clauseEdges k len) (setupModel k r))
    r' R.out = writeValues encodeClause (rawRecords (clauseVertex (gadgetWidth k) n j pc)
        (clauseGraph k pc)).reverse ++ r R.out ∧
      r' R.cnt = unary (c + (rawRecords (clauseVertex (gadgetWidth k) n j pc) (clauseGraph k pc)).length) ∧
      r' R.j = unary (j + 1) ∧
      ∀ x, x ∉ slotRegs → x ≠ R.j → x ≠ R.out → x ≠ R.cnt → x ≠ R.nj → r' x = r x := by
  intro r'
  have hsB : ∀ i (h : i < pc.length), (setupModel k r (slotB i)).length = gadgetWidth k * pc[i].literal.var := by
    intro i h
    rw [setupModel_other k r _ (by simp) (by simp), hB i h, unary_length]
  have hsE : ∀ i (h : i < pc.length) b, (setupModel k r (slotE i b)).length = variableEndpoint pc[i].port b := by
    intro i h b
    rw [setupModel_other k r _ (by simp) (by simp), hE i h b, unary_length]
  have hsbnj : (setupModel k r R.bnj).length = gadgetWidth k * (j + n) := by
    rw [setupModel_bnj, hj, hn, unary_length, unary_length, unary_length]
  have hrec := clauseEdges_records k n j len pc hlen (setupModel k r) hsB hsE hsbnj
  have hglen : (clauseEdges k len).length = (rawRecords (clauseVertex (gadgetWidth k) n j pc)
      (clauseGraph k pc)).length := by
    rw [← hrec, List.length_map]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [r']
    rw [finishModel_other _ _ (by decide) (by decide), emitEdgesModel_out, recordsWord, hrec,
      setupModel_other k r _ (by decide) (by decide)]
  · simp only [r']
    rw [finishModel_other _ _ (by decide) (by decide), emitEdgesModel_cnt,
      setupModel_other k r _ (by decide) (by decide), hglen, hc, unary_append_comm]
  · simp only [r']
    rw [finishModel_j, emitEdgesModel_other _ _ _ (by decide) (by decide),
      setupModel_other k r _ (by decide) (by decide), hj, unary_succ]
  · intro x h1 h2 h3 h4 h5
    simp only [r']
    have hbnj : x ≠ R.bnj := by intro h; subst h; simp [slotRegs] at h1
    rw [finishModel_other _ _ h1 h2, emitEdgesModel_other _ _ _ h3 h4, setupModel_other k r _ hbnj h5]

end STACS2027.Registered

namespace STACS2027.Registered

open Complexity
open Complexity.SAT
open Complexity.StackMachine (Registers set)

/-! ### The literals of one clause -/

/-- Every register the literal reading of a clause may write. -/
def allLitRegs : List Reg :=
  [R.inB, R.done, R.dc, R.scan, R.sc, R.cE, R.sg0, R.sg1, R.sg2, R.v0, R.v1, R.v2, R.ef0, R.et0, R.ef1,
    R.et1, R.ef2, R.et2, R.b0, R.b1, R.b2]

theorem litRegs_sub {i : Nat} (hi : i < 3) : ∀ x, x ∉ allLitRegs → x ∉ litRegs i := by
  rcases slot_cases hi with rfl | rfl | rfl <;> decide

theorem slot_not_mem (i i' : Nat) (hi : i < 3) (hi' : i' < 3) (hne : i ≠ i') :
    slotB i ∉ litRegs i' ∧ ∀ b, slotE i b ∉ litRegs i' := by
  rcases slot_cases hi with rfl | rfl | rfl <;> rcases slot_cases hi' with rfl | rfl | rfl <;>
    first | exact absurd rfl hne | exact ⟨by decide, by decide⟩

theorem placeLiterals_two (P : List Literal) (l₀ l₁ : Literal) :
    placeLiterals P [l₀, l₁] = [⟨l₀, P.count l₀⟩, ⟨l₁, (P ++ [l₀]).count l₁⟩] := by
  simp [placeLiterals]

theorem placeLiterals_three (P : List Literal) (l₀ l₁ l₂ : Literal) :
    placeLiterals P [l₀, l₁, l₂] =
      [⟨l₀, P.count l₀⟩, ⟨l₁, (P ++ [l₀]).count l₁⟩, ⟨l₂, (P ++ [l₀] ++ [l₁]).count l₂⟩] := by
  simp [placeLiterals]

theorem placed_eq (l : Literal) (pastRev : List Literal) (P : List Literal) (hP : P.count l = pastRev.count l) :
    placed l pastRev = ⟨l, P.count l⟩ := by
  simp [placed, hP]

theorem count_rev_cons (l a : Literal) (pastRev : List Literal) :
    (pastRev.reverse ++ [a]).count l = (a :: pastRev).count l := by
  simp [List.count_cons, List.count_append]

theorem count_rev_cons₂ (l a b : Literal) (pastRev : List Literal) :
    (pastRev.reverse ++ [a] ++ [b]).count l = (b :: a :: pastRev).count l := by
  simp [List.count_cons, List.count_append]
  omega

/-- The facts about the slots after reading the literals `c` of a clause. -/
def SlotFacts (k : Nat) (pc : List PlacedLiteral) (r : Regs) : Prop :=
  (∀ i (h : i < pc.length), r (slotB i) = unary (gadgetWidth k * pc[i].literal.var)) ∧
  (∀ i (h : i < pc.length) b, r (slotE i b) = unary (variableEndpoint pc[i].port b))

theorem lits_eval (k : Nat) (c : Clause) (hc : c.length = 2 ∨ c.length = 3) (pastRev : List Literal)
    (rest : SAT.Word) (r : Regs) (hin : r R.inB = writeValues encodeLiteral c ++ rest)
    (hdone : r R.done = writeValues encodeLiteral pastRev) (hdc : r R.dc = unary pastRev.length) :
    ∃ r', clauseLitsModel k c.length r = some r' ∧ r' R.inB = rest ∧
      r' R.done = writeValues encodeLiteral (c.reverse ++ pastRev) ∧
      r' R.dc = unary (c.length + pastRev.length) ∧
      SlotFacts k (placeLiterals pastRev.reverse c) r' ∧
      ∀ x, x ∉ allLitRegs → r' x = r x := by
  match c, hc with
  | [l₀, l₁], _ =>
    have hin₀ : r R.inB = encodeLiteral l₀ ++ (encodeLiteral l₁ ++ rest) := by
      rw [hin]; simp [writeValues]
    have e₀ := readLitModel_eval k 0 r l₀ (encodeLiteral l₁ ++ rest) pastRev hin₀ hdone hdc
    have e₁ := readLitModel_eval k 1 (litState k 0 l₀ (encodeLiteral l₁ ++ rest) pastRev r) l₁ rest
      (l₀ :: pastRev) (by rw [litState_inB])
      (by rw [litState_done, hdone]; rfl) (by rw [litState_dc, hdc]; simp [unary_succ])
    refine ⟨litState k 1 l₁ rest (l₀ :: pastRev) (litState k 0 l₀ (encodeLiteral l₁ ++ rest) pastRev r),
      ?_, litState_inB .., ?_, ?_, ⟨?_, ?_⟩, ?_⟩
    · simp only [clauseLitsModel, List.length_cons, List.length_nil, e₀, Option.bind_some, e₁]
      simp
    · rw [litState_done, litState_done, hdone]; simp [writeValues]
    · rw [litState_dc, litState_dc, hdc]
      show _ = unary (2 + pastRev.length)
      rw [show 2 + pastRev.length = pastRev.length + 1 + 1 by omega, unary_succ, unary_succ]
    · intro i h
      simp only [placeLiterals_two, List.length_cons, List.length_nil] at h ⊢
      match i, h with
      | 0, _ =>
        rw [litState_other _ _ _ _ _ _ _ (slot_not_mem 0 1 (by decide) (by decide) (by decide)).1, litState_B]
        rfl
      | 1, _ => rw [litState_B]; rfl
    · intro i h b
      simp only [placeLiterals_two, List.length_cons, List.length_nil] at h ⊢
      match i, h with
      | 0, _ =>
        rw [litState_other _ _ _ _ _ _ _ ((slot_not_mem 0 1 (by decide) (by decide) (by decide)).2 b), litState_E,
          placed_eq l₀ pastRev pastRev.reverse (by simp)]
        rfl
      | 1, _ =>
        rw [litState_E, placed_eq l₁ (l₀ :: pastRev) (pastRev.reverse ++ [l₀]) (count_rev_cons _ _ _)]
        rfl
    · intro x hx
      rw [litState_other _ _ _ _ _ _ _ (litRegs_sub (by decide) x hx),
        litState_other _ _ _ _ _ _ _ (litRegs_sub (by decide) x hx)]
  | [l₀, l₁, l₂], _ =>
    have hin₀ : r R.inB = encodeLiteral l₀ ++ (encodeLiteral l₁ ++ (encodeLiteral l₂ ++ rest)) := by
      rw [hin]; simp [writeValues]
    have e₀ := readLitModel_eval k 0 r l₀ _ pastRev hin₀ hdone hdc
    have e₁ := readLitModel_eval k 1 (litState k 0 l₀ (encodeLiteral l₁ ++ (encodeLiteral l₂ ++ rest)) pastRev r)
      l₁ (encodeLiteral l₂ ++ rest) (l₀ :: pastRev) (by rw [litState_inB])
      (by rw [litState_done, hdone]; rfl) (by rw [litState_dc, hdc]; simp [unary_succ])
    have e₂ := readLitModel_eval k 2 (litState k 1 l₁ (encodeLiteral l₂ ++ rest) (l₀ :: pastRev)
      (litState k 0 l₀ (encodeLiteral l₁ ++ (encodeLiteral l₂ ++ rest)) pastRev r)) l₂ rest (l₁ :: l₀ :: pastRev)
      (by rw [litState_inB])
      (by rw [litState_done, litState_done, hdone]; rfl)
      (by rw [litState_dc, litState_dc, hdc]; simp [unary_succ])
    refine ⟨litState k 2 l₂ rest (l₁ :: l₀ :: pastRev) (litState k 1 l₁ (encodeLiteral l₂ ++ rest) (l₀ :: pastRev)
      (litState k 0 l₀ (encodeLiteral l₁ ++ (encodeLiteral l₂ ++ rest)) pastRev r)),
      ?_, litState_inB .., ?_, ?_, ⟨?_, ?_⟩, ?_⟩
    · simp only [clauseLitsModel, List.length_cons, List.length_nil, e₀, Option.bind_some, e₁]
      simp [e₂]
    · rw [litState_done, litState_done, litState_done, hdone]; simp [writeValues]
    · rw [litState_dc, litState_dc, litState_dc, hdc]
      show _ = unary (3 + pastRev.length)
      rw [show 3 + pastRev.length = pastRev.length + 1 + 1 + 1 by omega, unary_succ, unary_succ, unary_succ]
    · intro i h
      simp only [placeLiterals_three, List.length_cons, List.length_nil] at h ⊢
      match i, h with
      | 0, _ =>
        rw [litState_other _ _ _ _ _ _ _ (slot_not_mem 0 2 (by decide) (by decide) (by decide)).1,
          litState_other _ _ _ _ _ _ _ (slot_not_mem 0 1 (by decide) (by decide) (by decide)).1, litState_B]
        rfl
      | 1, _ =>
        rw [litState_other _ _ _ _ _ _ _ (slot_not_mem 1 2 (by decide) (by decide) (by decide)).1, litState_B]
        rfl
      | 2, _ => rw [litState_B]; rfl
    · intro i h b
      simp only [placeLiterals_three, List.length_cons, List.length_nil] at h ⊢
      match i, h with
      | 0, _ =>
        rw [litState_other _ _ _ _ _ _ _ ((slot_not_mem 0 2 (by decide) (by decide) (by decide)).2 b),
          litState_other _ _ _ _ _ _ _ ((slot_not_mem 0 1 (by decide) (by decide) (by decide)).2 b), litState_E,
          placed_eq l₀ pastRev pastRev.reverse (by simp)]
        rfl
      | 1, _ =>
        rw [litState_other _ _ _ _ _ _ _ ((slot_not_mem 1 2 (by decide) (by decide) (by decide)).2 b),
          litState_E, placed_eq l₁ (l₀ :: pastRev) (pastRev.reverse ++ [l₀]) (count_rev_cons _ _ _)]
        rfl
      | 2, _ =>
        rw [litState_E, placed_eq l₂ (l₁ :: l₀ :: pastRev) (pastRev.reverse ++ [l₀] ++ [l₁])
          (count_rev_cons₂ _ _ _ _)]
        rfl
    · intro x hx
      rw [litState_other _ _ _ _ _ _ _ (litRegs_sub (by decide) x hx),
        litState_other _ _ _ _ _ _ _ (litRegs_sub (by decide) x hx),
        litState_other _ _ _ _ _ _ _ (litRegs_sub (by decide) x hx)]

/-! ### One clause of the second pass -/

theorem encodeClause_split (c : Clause) (rest : SAT.Word) :
    encodeClause c ++ rest = writeNat c.length ++ (writeValues encodeLiteral c ++ rest) := by
  simp [encodeClause, writeList]

theorem placeLiterals_length (P c : List Literal) : (placeLiterals P c).length = c.length := by
  have h := congrArg List.length (placeLiterals_forget P c)
  simpa using h

theorem caseLen_eval (k : Nat) (c : Clause) (hc : c.length = 2 ∨ c.length = 3) (r : Regs)
    (hl : r R.len = unary c.length) :
    caseLenModel (clauseKModel k 2) (clauseKModel k 3) r = clauseKModel k c.length (set r R.len []) := by
  rcases hc with h | h <;> rw [h] at hl ⊢ <;> simp [caseLenModel, hl, unary, List.replicate_succ]

/-- The registers one clause of the second pass may write. -/
def bodyRegs : List Reg := allLitRegs ++ slotRegs ++ [R.j, R.out, R.cnt, R.nj, R.len]

theorem body_eval (k n j cnt : Nat) (c : Clause) (hc : c.length = 2 ∨ c.length = 3) (rest : SAT.Word)
    (pastRev : List Literal) (r : Regs) (hin : r R.inB = encodeClause c ++ rest)
    (hdone : r R.done = writeValues encodeLiteral pastRev) (hdc : r R.dc = unary pastRev.length)
    (hj : r R.j = unary j) (hn : r R.n = unary n) (hcnt : r R.cnt = unary cnt) :
    ∃ r', clauseBodyModel k r = some r' ∧ r' R.inB = rest ∧
      r' R.done = writeValues encodeLiteral (c.reverse ++ pastRev) ∧
      r' R.dc = unary (c.length + pastRev.length) ∧ r' R.j = unary (j + 1) ∧
      r' R.out = writeValues encodeClause (clauseRecords k n j pastRev.reverse c).reverse ++ r R.out ∧
      r' R.cnt = unary (cnt + (clauseRecords k n j pastRev.reverse c).length) ∧
      ∀ x, x ∉ bodyRegs → r' x = r x := by
  rw [encodeClause_split] at hin
  let r₁ := set (set r R.inB (writeValues encodeLiteral c ++ rest)) R.len (unary c.length)
  let r₂ := set r₁ R.len []
  have h₂ : ∀ x, x ≠ R.inB → x ≠ R.len → r₂ x = r x := by
    intro x h1 h2; simp [r₂, r₁, StackMachine.set, h1, h2]
  obtain ⟨rL, hL, hLin, hLdone, hLdc, ⟨hB, hE⟩, hLo⟩ := lits_eval k c hc pastRev rest r₂
    (by simp +decide [r₂, r₁, StackMachine.set]) (by rw [h₂ _ (by decide) (by decide), hdone])
    (by rw [h₂ _ (by decide) (by decide), hdc])
  have hpl := placeLiterals_length pastRev.reverse c
  have hLx : ∀ x, x ∉ allLitRegs → x ≠ R.len → rL x = r x := by
    intro x h1 h2
    rw [hLo x h1, h₂ x (by intro h; subst h; exact h1 (by decide)) h2]
  obtain ⟨hTo, hTc, hTj, hTx⟩ := tail_eval k n j c.length cnt (placeLiterals pastRev.reverse c) hpl rL hB hE
    (by rw [hLx _ (by decide) (by decide), hj]) (by rw [hLx _ (by decide) (by decide), hn])
    (by rw [hLx _ (by decide) (by decide), hcnt])
  refine ⟨finishModel (emitEdgesModel (clauseEdges k c.length) (setupModel k rL)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [clauseBodyModel, readUnaryModel_writeNat R.inB R.len r c.length _ hin, Option.bind_some]
    rw [caseLen_eval k c hc r₁ (by simp [r₁])]
    simp only [clauseKModel]
    rw [show set r₁ R.len [] = r₂ from rfl, hL, Option.bind_some]
  · rw [hTx _ (by decide) (by decide) (by decide) (by decide) (by decide), hLin]
  · rw [hTx _ (by decide) (by decide) (by decide) (by decide) (by decide), hLdone]
  · rw [hTx _ (by decide) (by decide) (by decide) (by decide) (by decide), hLdc]
  · exact hTj
  · rw [hTo, hLx _ (by decide) (by decide)]; rfl
  · exact hTc
  · intro x hx
    simp only [bodyRegs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨⟨h1, h2⟩, h3, h4, h5, h6, h7⟩ := hx
    rw [hTx x h2 h3 h4 h5 h6, hLx x h1 h7]

/-! ### The clause loop -/

theorem writeValues_reverse_append (A B : CNF) :
    writeValues encodeClause B.reverse ++ writeValues encodeClause A.reverse =
      writeValues encodeClause (A ++ B).reverse := by
  rw [List.reverse_append, writeValues_append]

theorem passB_iter (k n : Nat) (f : CNF) (hf : ∀ c ∈ f, c.length = 2 ∨ c.length = 3) :
    ∀ (j : Nat) (pastRev : List Literal) (E : CNF) (r : Regs),
      r R.inB = writeValues encodeClause f → r R.done = writeValues encodeLiteral pastRev →
      r R.dc = unary pastRev.length → r R.j = unary j → r R.n = unary n →
      r R.out = writeValues encodeClause E.reverse → r R.cnt = unary E.length → r R.m = unary f.length →
      ∃ r', iter (clauseBodyModel k) R.m f.length r = some r' ∧
        r' R.out = writeValues encodeClause (E ++ clauseRecordsFrom k n j pastRev.reverse f).reverse ∧
        r' R.cnt = unary (E ++ clauseRecordsFrom k n j pastRev.reverse f).length := by
  induction f with
  | nil =>
    intro j pastRev E r _ _ _ _ _ hout hcnt _
    exact ⟨r, rfl, by simpa [clauseRecordsFrom] using hout, by simpa [clauseRecordsFrom] using hcnt⟩
  | cons c f ih =>
    intro j pastRev E r hin hdone hdc hj hn hout hcnt hm
    have hm' : r R.m = true :: unary f.length := by rw [hm]; simp [unary_succ]
    let r₀ := set r R.m (unary f.length)
    have h₀ : ∀ x, x ≠ R.m → r₀ x = r x := by intro x h; simp [r₀, h]
    obtain ⟨r₁, h₁, hin₁, hdone₁, hdc₁, hj₁, hout₁, hcnt₁, hx₁⟩ :=
      body_eval k n j E.length c (hf c (by simp)) (writeValues encodeClause f) pastRev r₀
        (by rw [h₀ _ (by decide), hin]; rfl) (by rw [h₀ _ (by decide), hdone])
        (by rw [h₀ _ (by decide), hdc]) (by rw [h₀ _ (by decide), hj]) (by rw [h₀ _ (by decide), hn])
        (by rw [h₀ _ (by decide), hcnt])
    have hm₁ : r₁ R.m = unary f.length := by rw [hx₁ _ (by decide)]; simp [r₀]
    have hn₁ : r₁ R.n = unary n := by rw [hx₁ _ (by decide), h₀ _ (by decide), hn]
    obtain ⟨r₂, h₂, hout₂, hcnt₂⟩ := ih (fun c' hc' => hf c' (by simp [hc'])) (j + 1) (c.reverse ++ pastRev)
      (E ++ clauseRecords k n j pastRev.reverse c) r₁ hin₁ hdone₁ (by rw [hdc₁]; simp []) hj₁ hn₁
      (by rw [hout₁, h₀ _ (by decide), hout, writeValues_reverse_append])
      (by rw [hcnt₁]; simp) hm₁
    refine ⟨r₂, ?_, ?_, ?_⟩
    · rw [List.length_cons, iter_cons _ _ _ _ true (unary f.length) hm', h₁, Option.bind_some]
      exact h₂
    · rw [hout₂]; simp [clauseRecordsFrom, List.reverse_append, List.append_assoc]
    · rw [hcnt₂]; simp [clauseRecordsFrom, List.reverse_append, List.append_assoc]

/-! ### The variable loop -/

theorem varRecords_succ (k v t : Nat) :
    varRecords k v (t + 1) = rawRecords (blockVertex (gadgetWidth k) v) (variableGraph k) ++ varRecords k (v + 1) t := by
  simp [varRecords, List.range'_succ]

theorem variableEdges_records (k v : Nat) (r : Regs) (hvb : r R.vb = unary (gadgetWidth k * v)) :
    (variableEdges k).map (fun e => edgeRecord e.1 e.2 r) = rawRecords (blockVertex (gadgetWidth k) v) (variableGraph k) := by
  simp only [variableEdges, rawRecords, List.map_map]
  apply List.map_congr_left
  intro e _
  simp [edgeRecord, pairRecord, Endpoint.value, hvb, blockVertex, Nat.mul_comm]

theorem var_iter (k : Nat) : ∀ (t v : Nat) (E : CNF) (r : Regs),
    r R.vc = unary t → r R.vb = unary (gadgetWidth k * v) → r R.W = unary (gadgetWidth k) →
    r R.out = writeValues encodeClause E.reverse → r R.cnt = unary E.length →
    ∃ r', iter (varBodyModel k) R.vc t r = some r' ∧
      r' R.out = writeValues encodeClause (E ++ varRecords k v t).reverse ∧
      r' R.cnt = unary (E ++ varRecords k v t).length ∧
      ∀ x, x ≠ R.out → x ≠ R.cnt → x ≠ R.vb → x ≠ R.vc → r' x = r x := by
  intro t
  induction t with
  | zero =>
    intro v E r _ _ _ hout hcnt
    exact ⟨r, rfl, by simpa [varRecords] using hout, by simpa [varRecords] using hcnt, fun _ _ _ _ _ => rfl⟩
  | succ t ih =>
    intro v E r hvc hvb hW hout hcnt
    have hvc' : r R.vc = true :: unary t := by rw [hvc, unary_succ]
    let r₀ := set r R.vc (unary t)
    let r₁ := set (emitEdgesModel (variableEdges k) r₀) R.vb
      (List.replicate (emitEdgesModel (variableEdges k) r₀ R.W).length true ++
        emitEdgesModel (variableEdges k) r₀ R.vb)
    have hrec := variableEdges_records k v r₀ (by simp +decide [r₀, hvb])
    have hlen : (variableEdges k).length = (rawRecords (blockVertex (gadgetWidth k) v) (variableGraph k)).length := by
      rw [← hrec, List.length_map]
    obtain ⟨r₂, h₂, hout₂, hcnt₂, hx₂⟩ := ih (v + 1) (E ++ rawRecords (blockVertex (gadgetWidth k) v) (variableGraph k)) r₁
      (by simp +decide [r₁, r₀, emitEdgesModel, StackMachine.set])
      (by
        simp +decide [r₁, r₀, emitEdgesModel, StackMachine.set, hW, hvb, unary]
        rw [Nat.mul_succ, Nat.add_comm])
      (by simp +decide [r₁, r₀, emitEdgesModel, StackMachine.set, hW])
      (by
        simp only [r₁]
        rw [show set (emitEdgesModel (variableEdges k) r₀) R.vb _ R.out = emitEdgesModel (variableEdges k) r₀ R.out by
          simp +decide [StackMachine.set], emitEdgesModel_out, recordsWord, hrec]
        simp only [r₀]
        rw [show set r R.vc (unary t) R.out = r R.out by simp +decide [StackMachine.set], hout,
          writeValues_reverse_append])
      (by
        simp only [r₁]
        rw [show set (emitEdgesModel (variableEdges k) r₀) R.vb _ R.cnt = emitEdgesModel (variableEdges k) r₀ R.cnt by
          simp +decide [StackMachine.set], emitEdgesModel_cnt]
        simp only [r₀]
        rw [show set r R.vc (unary t) R.cnt = r R.cnt by simp +decide [StackMachine.set], hcnt, hlen,
          unary_append_comm]
        simp)
    refine ⟨r₂, ?_, ?_, ?_, ?_⟩
    · rw [iter_cons _ _ _ _ true (unary t) hvc']
      simp only [varBodyModel, Option.bind_some]
      exact h₂
    · rw [hout₂, varRecords_succ, List.append_assoc]
    · rw [hcnt₂, varRecords_succ, List.append_assoc]
    · intro x h1 h2 h3 h4
      rw [hx₂ x h1 h2 h3 h4]
      simp [r₁, r₀, emitEdgesModel, StackMachine.set, h1, h2, h3, h4]

/-! ### The first pass -/

theorem litA_eval (r : Regs) (l : Literal) (rest : SAT.Word) (a : Nat) (hin : r R.inA = encodeLiteral l ++ rest)
    (hn : r R.n = unary a) :
    litAModel r = some (set (set (set r R.inA rest) R.n (unary (max a (l.var + 1)))) R.x []) := by
  simp only [litAModel, hin, readLiteral_encodeLiteral, hn, unary_length, Option.some.injEq]
  congr 2
  split
  · congr 1; omega
  · congr 1; omega

theorem litA_iter (ls : List Literal) : ∀ (r : Regs) (a : Nat) (rest : SAT.Word),
    r R.len = unary ls.length → r R.inA = writeValues encodeLiteral ls ++ rest → r R.n = unary a →
    r R.x = [] →
    ∃ r', iter litAModel R.len ls.length r = some r' ∧ r' R.inA = rest ∧
      r' R.n = unary (max a (clauseBound ls)) ∧ r' R.x = [] ∧
      ∀ y, y ≠ R.inA → y ≠ R.n → y ≠ R.x → y ≠ R.len → r' y = r y := by
  induction ls with
  | nil =>
    intro r a rest _ hin hn hx
    refine ⟨r, rfl, by simpa [writeValues] using hin, by simpa [clauseBound] using hn, hx, fun _ _ _ _ _ => rfl⟩
  | cons l ls ih =>
    intro r a rest hl hin hn hx
    have hl' : r R.len = true :: unary ls.length := by rw [hl]; simp [unary_succ]
    let r₀ := set r R.len (unary ls.length)
    have e := litA_eval r₀ l (writeValues encodeLiteral ls ++ rest) a
      (by simp +decide [r₀, hin, writeValues]) (by simp +decide [r₀, hn])
    obtain ⟨r₂, h₂, hin₂, hn₂, hx₂, hy₂⟩ := ih (set (set (set r₀ R.inA (writeValues encodeLiteral ls ++ rest)) R.n
        (unary (max a (l.var + 1)))) R.x []) (max a (l.var + 1)) rest
      (by simp +decide [r₀, StackMachine.set]) (by simp +decide [StackMachine.set])
      (by simp +decide [StackMachine.set]) (by simp +decide [StackMachine.set])
    refine ⟨r₂, ?_, hin₂, ?_, hx₂, ?_⟩
    · rw [List.length_cons, iter_cons _ _ _ _ true (unary ls.length) hl', e, Option.bind_some]
      exact h₂
    · rw [hn₂]; simp only [clauseBound, Nat.max_assoc]
    · intro y h1 h2 h3 h4
      rw [hy₂ y h1 h2 h3 h4]
      simp [r₀, StackMachine.set, h1, h2, h3, h4]

theorem clauseA_eval (r : Regs) (c : Clause) (rest : SAT.Word) (a : Nat)
    (hin : r R.inA = encodeClause c ++ rest) (hn : r R.n = unary a) (hx : r R.x = []) :
    ∃ r', clauseAModel r = some r' ∧ r' R.inA = rest ∧ r' R.n = unary (max a (clauseBound c)) ∧ r' R.x = [] ∧
      ∀ y, y ≠ R.inA → y ≠ R.n → y ≠ R.x → y ≠ R.len → r' y = r y := by
  rw [encodeClause_split] at hin
  let r₁ := set (set r R.inA (writeValues encodeLiteral c ++ rest)) R.len (unary c.length)
  obtain ⟨r₂, h₂, hin₂, hn₂, hx₂, hy₂⟩ := litA_iter c r₁ a rest (by simp [r₁])
    (by simp +decide [r₁, StackMachine.set]) (by simp +decide [r₁, StackMachine.set, hn])
    (by simp +decide [r₁, StackMachine.set, hx])
  refine ⟨r₂, ?_, hin₂, hn₂, hx₂, ?_⟩
  · simp only [clauseAModel, readUnaryModel_writeNat R.inA R.len r c.length _ hin, Option.bind_some]
    rw [show (set (set r R.inA (writeValues encodeLiteral c ++ rest)) R.len (unary c.length) R.len).length
      = c.length by simp [StackMachine.set]]
    exact h₂
  · intro y h1 h2 h3 h4
    rw [hy₂ y h1 h2 h3 h4]
    simp [r₁, StackMachine.set, h1, h4]

theorem passA_iter (f : CNF) : ∀ (r : Regs) (a : Nat) (rest : SAT.Word),
    r R.m = unary f.length → r R.inA = writeValues encodeClause f ++ rest → r R.n = unary a → r R.x = [] →
    ∃ r', iter clauseAModel R.m f.length r = some r' ∧ r' R.n = unary (max a (variableBound f)) ∧
      ∀ y, y ≠ R.inA → y ≠ R.n → y ≠ R.x → y ≠ R.len → y ≠ R.m → r' y = r y := by
  induction f with
  | nil =>
    intro r a rest _ _ hn _
    exact ⟨r, rfl, by simpa [variableBound] using hn, fun _ _ _ _ _ _ => rfl⟩
  | cons c f ih =>
    intro r a rest hm hin hn hx
    have hm' : r R.m = true :: unary f.length := by rw [hm]; simp [unary_succ]
    let r₀ := set r R.m (unary f.length)
    obtain ⟨r₁, h₁, hin₁, hn₁, hx₁, hy₁⟩ := clauseA_eval r₀ c (writeValues encodeClause f ++ rest) a
      (by simp +decide [r₀, hin, writeValues]) (by simp +decide [r₀, hn])
      (by simp +decide [r₀, hx])
    obtain ⟨r₂, h₂, hn₂, hy₂⟩ := ih r₁ (max a (clauseBound c)) rest
      (by rw [hy₁ _ (by decide) (by decide) (by decide) (by decide)]; simp [r₀]) hin₁ hn₁ hx₁
    refine ⟨r₂, ?_, ?_, ?_⟩
    · rw [List.length_cons, iter_cons _ _ _ _ true (unary f.length) hm', h₁, Option.bind_some]
      exact h₂
    · rw [hn₂]; simp only [variableBound, Nat.max_assoc]
    · intro y h1 h2 h3 h4 h5
      rw [hy₂ y h1 h2 h3 h4 h5, hy₁ y h1 h2 h3 h4]
      simp [r₀, h5]

/-! ### The complete model -/

theorem initModel_read (k : Nat) (w : SAT.Word) (x : Reg) :
    initModel k (initRegs w) x =
      if x = R.two then [true, true] else if x = R.W then unary (gadgetWidth k) else if x = R.out then []
      else if x = R.inB then w else if x = R.inA then w else [] := by
  by_cases h1 : x = R.two
  · subst h1; simp +decide [initModel, StackMachine.set]
  · by_cases h2 : x = R.W
    · subst h2; simp +decide [initModel, StackMachine.set]
    · by_cases h3 : x = R.out
      · subst h3; simp +decide [initModel, StackMachine.set]
      · by_cases h4 : x = R.inB
        · subst h4; simp +decide [initModel, StackMachine.set, initRegs]
        · by_cases h5 : x = R.inA
          · subst h5; simp +decide [initModel, StackMachine.set, initRegs]
          · have h0 : x ≠ 0 := h3
            simp [initModel, StackMachine.set, initRegs, h1, h2, h3, h4, h5]

theorem mainModel_encode (k : Nat) (f : CNF) (hf : ∀ c ∈ f, c.length = 2 ∨ c.length = 3) :
    ∃ r', mainModel k (initRegs (encode f)) = some r' ∧ r' R.out = encode (formulaRecords k f).reverse := by
  obtain ⟨rI, hrI⟩ : ∃ q, q = initModel k (initRegs (encode f)) := ⟨_, rfl⟩
  have hI : ∀ x, rI x = _ := fun x => hrI ▸ initModel_read k (encode f) x
  have hencode : encode f = writeNat f.length ++ (writeValues encodeClause f ++ []) := by
    simp [encode, writeList]
  -- the first pass
  have hmI : (readUnaryModel R.inA R.m rI) = some (set (set rI R.inA (writeValues encodeClause f ++ [])) R.m
      (unary f.length)) :=
    readUnaryModel_writeNat _ _ _ _ _ (by rw [hI]; simp +decide; simpa using hencode)
  obtain ⟨rA, hrA⟩ : ∃ q, q = set (set rI R.inA (writeValues encodeClause f ++ [])) R.m (unary f.length) :=
    ⟨_, rfl⟩
  rw [← hrA] at hmI
  obtain ⟨r₁, h₁, hn₁, hy₁⟩ := passA_iter f rA 0 [] (by simp [hrA])
    (by simp +decide [hrA, StackMachine.set]) (by simp +decide [hrA, StackMachine.set, hI])
    (by simp +decide [hrA, StackMachine.set, hI])
  have hA : passAModel rI = some r₁ := by
    simp only [passAModel, hmI, Option.bind_some]
    rw [show (rA R.m).length = f.length by simp [hrA]]
    exact h₁
  have h₁x : ∀ y, y ≠ R.inA → y ≠ R.n → y ≠ R.x → y ≠ R.len → y ≠ R.m → r₁ y = rI y := by
    intro y a1 a2 a3 a4 a5
    rw [hy₁ y a1 a2 a3 a4 a5]
    simp [hrA, StackMachine.set, a1, a5]
  -- the variable gadgets
  have hn0 : max 0 (variableBound f) = variableBound f := by simp
  rw [hn0] at hn₁
  obtain ⟨r₂, h₂, hout₂, hcnt₂, hy₂⟩ := var_iter k (variableBound f) 0 [] (set r₁ R.vc (r₁ R.n))
    (by simp [StackMachine.set, hn₁])
    (by simp +decide [StackMachine.set]; rw [h₁x _ (by decide) (by decide) (by decide) (by decide) (by decide), hI]; simp +decide)
    (by simp +decide [StackMachine.set]; rw [h₁x _ (by decide) (by decide) (by decide) (by decide) (by decide), hI]; simp +decide)
    (by simp +decide [StackMachine.set]; rw [h₁x _ (by decide) (by decide) (by decide) (by decide) (by decide), hI]; simp +decide [writeValues])
    (by simp +decide [StackMachine.set]; rw [h₁x _ (by decide) (by decide) (by decide) (by decide) (by decide), hI]; simp +decide)
  have hV : varLoopModel k r₁ = some r₂ := by
    simp only [varLoopModel]
    rw [hn₁, unary_length]
    rw [hn₁] at h₂
    exact h₂
  have h₂x : ∀ y, y ≠ R.out → y ≠ R.cnt → y ≠ R.vb → y ≠ R.vc → y ≠ R.inA → y ≠ R.n → y ≠ R.x → y ≠ R.len →
      y ≠ R.m → r₂ y = rI y := by
    intro y a1 a2 a3 a4 a5 a6 a7 a8 a9
    rw [hy₂ y a1 a2 a3 a4]
    simp only [StackMachine.set, a4, ↓reduceIte]
    exact h₁x y a5 a6 a7 a8 a9
  have hr₂n : r₂ R.n = unary (variableBound f) := by
    rw [hy₂ _ (by decide) (by decide) (by decide) (by decide)]
    simp +decide [StackMachine.set, hn₁]
  -- the clause gadgets
  have hinB : r₂ R.inB = writeNat f.length ++ writeValues encodeClause f := by
    rw [h₂x _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hI]
    simp +decide [encode, writeList]
  obtain ⟨rB, hrB⟩ : ∃ q, q = set (set r₂ R.inB (writeValues encodeClause f)) R.m (unary f.length) := ⟨_, rfl⟩
  have hzero : ∀ y, y ∉ [R.out, R.cnt, R.vb, R.vc, R.inA, R.n, R.x, R.len, R.m, R.two, R.W, R.inB] → rB y = [] := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hy
    simp only [hrB, StackMachine.set, a9, a12, ↓reduceIte]
    rw [h₂x y a1 a2 a3 a4 a5 a6 a7 a8 a9, hI]
    simp [a10, a11, a1, a12, a5]
  obtain ⟨r₃, h₃, hout₃, hcnt₃⟩ := passB_iter k (variableBound f) f hf 0 [] (varRecords k 0 (variableBound f)) rB
    (by simp +decide [hrB, StackMachine.set]) (by rw [hzero _ (by decide)]; rfl)
    (by rw [hzero _ (by decide)]; rfl) (by rw [hzero _ (by decide)]; rfl)
    (by simp +decide [hrB, StackMachine.set, hr₂n])
    (by simp +decide [hrB, StackMachine.set, hout₂])
    (by simp +decide [hrB, StackMachine.set, hcnt₂])
    (by simp [hrB])
  have hB : passBModel k r₂ = some r₃ := by
    simp only [passBModel, readUnaryModel_writeNat R.inB R.m r₂ f.length _ hinB, Option.bind_some, ← hrB]
    rw [show (rB R.m).length = f.length by simp [hrB]]
    exact h₃
  refine ⟨set r₃ R.out (writeNat (r₃ R.cnt).length ++ r₃ R.out), ?_, ?_⟩
  · simp only [mainModel, ← hrI, hA, hV, hB, Option.bind_some]
  · simp only [StackMachine.set, ↓reduceIte, hcnt₃, hout₃, unary_length]
    simp [encode, writeList, formulaRecords, Nat.add_comm]

/-- **The machine computes the Theorem 8 graph.** On the code of every formula whose clauses have
two or three literals, the output of the machine is the code of the records of the edges of
`formulaGraph k f`, in reverse order. -/
theorem instanceMapWord_encode (k : Nat) (f : CNF) (hf : ∀ c ∈ f, c.length = 2 ∨ c.length = 3) :
    instanceMapWord k (encode f) = encode (formulaRecords k f).reverse := by
  obtain ⟨r', hm, hout⟩ := mainModel_encode k f hf
  obtain ⟨r, hrun, hr⟩ := machine_run k (encode f)
  rw [instanceMapWord_eq k (encode f) hrun, hr r' hm]
  exact hout

end STACS2027.Registered
