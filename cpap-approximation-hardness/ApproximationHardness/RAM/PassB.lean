module

public import ApproximationHardness.RAM.SlotRegs
import Lean.Elab.Tactic.Omega

/-!
# The third pass of the RAM program: the clause gadgets
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT

/-! ### Reading one literal -/

theorem signCode_lt (l : Literal) : signCode l < 2 := by unfold signCode; split <;> omega

theorem literal_of_code (l : Literal) : (⟨l.var, decide (signCode l = 1)⟩ : Literal) = l := by
  cases l with
  | mk v s => cases s <;> rfl

theorem code_eq_iff (l : Literal) (v s : Nat) (hs : s < 2) :
    (N + l.var + l.var + signCode l = N + v + v + s) ↔ (⟨v, decide (s = 1)⟩ : Literal) = l := by
  constructor
  · intro h
    have hb : l.var = v ∧ signCode l = s := by
      have := signCode_lt l
      omega
    rw [← literal_of_code l, hb.2, hb.1]
  · intro h
    subst h
    simp only [signCode, decide_eq_true_eq]
    split <;> omega

/-- The port endpoints written for a literal of sign `sg` whose earlier occurrences number `cc`. -/
theorem port_endpoints (l : Literal) (e : Nat) (b : Bool) :
    (if signCode l = 0 then (if e = 0 then (if b then 5 else 4) else (if b then 3 else 0)) else (if b then 6 else 2))
      = variableEndpoint (⟨l, e⟩ : PlacedLiteral).port b := by
  cases l with
  | mk v s =>
    cases s <;> cases b <;> simp [signCode, PlacedLiteral.port, variableEndpoint] <;> split <;> simp_all <;> omega

/-- The registers `readLit i` writes. -/
def litRegs (i : Nat) : List Nat := [Reg.v, Reg.sg, Reg.addr, Reg.cc, Reg.t, Reg.p, eReg i false, eReg i true, bReg i]

theorem readLit_run (i : Nat) (hi : i < 3) (c : Config) (l : Literal) (w : List Nat) (P : List Literal)
    (n N : Nat) (hAt : At c (litCode l ++ w)) (_hpN : c.reg Reg.p + 2 ≤ N)
    (hN : c.reg Reg.N = N) (hB : c.reg Reg.B = N + n + n) (hone : c.reg Reg.one = 1) (hl : l.var < n)
    (hcount : ∀ v, v < n → ∀ s, s < 2 → c.mem (N + v + v + s) = P.count ⟨v, decide (s = 1)⟩) :
    (run (readLit i) c).reg Reg.p = c.reg Reg.p + 2 ∧
    (∀ j, j < N → (run (readLit i) c).mem j = c.mem j) ∧
    (∀ v, v < n → ∀ s, s < 2 → (run (readLit i) c).mem (N + v + v + s) = (P ++ [l]).count ⟨v, decide (s = 1)⟩) ∧
    (∀ u, u < n → (run (readLit i) c).mem (N + n + n + u) = c.mem (N + n + n + u)) ∧
    (∀ b, (run (readLit i) c).reg (eReg i b) = variableEndpoint (⟨l, P.count l⟩ : PlacedLiteral).port b) ∧
    (run (readLit i) c).reg (bReg i) = c.mem (N + n + n + l.var) ∧
    (run (readLit i) c).out = c.out ∧
    ∀ r, r ∉ litRegs i → (run (readLit i) c).reg r = c.reg r := by
  have hv : c.mem (c.reg Reg.p) = l.var := hAt.head
  have hs : c.mem (c.reg Reg.p + 1) = signCode l := by
    have := hAt 1 (by simp [litCode])
    simpa [litCode] using this
  have hsl := signCode_lt l
  have hcl : c.mem (N + l.var + l.var + signCode l) = P.count l := by
    rw [hcount l.var hl (signCode l) hsl, literal_of_code]
  have hfs := eReg_side i
  -- the configuration after the first ten instructions
  let a := N + l.var + l.var + signCode l
  let c₁ := ((((((((((c.setReg Reg.v l.var).setReg Reg.p (c.reg Reg.p + 1)).setReg Reg.sg (signCode l)).setReg
    Reg.p (c.reg Reg.p + 2)).setReg Reg.addr (N + l.var)).setReg Reg.addr (N + l.var + l.var)).setReg Reg.addr a).setReg
    Reg.cc (P.count l)).setReg Reg.t (P.count l + 1)).setMem a (P.count l + 1))
  have hpre : run (seqs [Stmt.load Reg.v Reg.p, Stmt.add Reg.p Reg.p Reg.one, Stmt.load Reg.sg Reg.p,
      Stmt.add Reg.p Reg.p Reg.one, Stmt.add Reg.addr Reg.N Reg.v, Stmt.add Reg.addr Reg.addr Reg.v,
      Stmt.add Reg.addr Reg.addr Reg.sg, Stmt.load Reg.cc Reg.addr, Stmt.add Reg.t Reg.cc Reg.one,
      Stmt.store Reg.addr Reg.t]) c = c₁ := by
    simp +decide only [run_seqs_cons, run_seqs_nil, run, setReg_reg, setReg_mem, ↓reduceIte, hv, hone, hN, hs]
    simp only [c₁, a]
    rw [show c.reg Reg.p + 1 + 1 = c.reg Reg.p + 2 by omega, hcl]
  have hsplit : readLit i = seqs ([Stmt.load Reg.v Reg.p, Stmt.add Reg.p Reg.p Reg.one, Stmt.load Reg.sg Reg.p,
      Stmt.add Reg.p Reg.p Reg.one, Stmt.add Reg.addr Reg.N Reg.v, Stmt.add Reg.addr Reg.addr Reg.v,
      Stmt.add Reg.addr Reg.addr Reg.sg, Stmt.load Reg.cc Reg.addr, Stmt.add Reg.t Reg.cc Reg.one,
      Stmt.store Reg.addr Reg.t] ++ [Stmt.ifz Reg.sg
      (Stmt.ifz Reg.cc (Stmt.seq (Stmt.const (eReg i false) 4) (Stmt.const (eReg i true) 5))
        (Stmt.seq (Stmt.const (eReg i false) 0) (Stmt.const (eReg i true) 3)))
      (Stmt.seq (Stmt.const (eReg i false) 2) (Stmt.const (eReg i true) 6)),
      Stmt.add Reg.addr Reg.B Reg.v, Stmt.load (bReg i) Reg.addr]) := rfl
  rw [hsplit, run_seqs_append, hpre]
  -- the remaining three instructions
  have hsg₁ : c₁.reg Reg.sg = signCode l := by simp +decide [c₁]
  have hcc₁ : c₁.reg Reg.cc = P.count l := by simp +decide [c₁]
  let e₀ : Bool → Nat := fun b => variableEndpoint (⟨l, P.count l⟩ : PlacedLiteral).port b
  let c₂ := (c₁.setReg (eReg i false) (e₀ false)).setReg (eReg i true) (e₀ true)
  have hif : run (Stmt.ifz Reg.sg
      (Stmt.ifz Reg.cc (Stmt.seq (Stmt.const (eReg i false) 4) (Stmt.const (eReg i true) 5))
        (Stmt.seq (Stmt.const (eReg i false) 0) (Stmt.const (eReg i true) 3)))
      (Stmt.seq (Stmt.const (eReg i false) 2) (Stmt.const (eReg i true) 6))) c₁ = c₂ := by
    simp only [run, hsg₁, hcc₁, c₂, e₀]
    have h1 := port_endpoints l (P.count l) false
    have h2 := port_endpoints l (P.count l) true
    simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2
    by_cases hs0 : signCode l = 0
    · by_cases hc0 : P.count l = 0
      · simp only [hs0, hc0, ↓reduceIte] at h1 h2 ⊢; rw [← h1, ← h2]
      · simp only [hs0, hc0, ↓reduceIte] at h1 h2 ⊢; rw [← h1, ← h2]
    · simp only [hs0, ↓reduceIte] at h1 h2 ⊢; rw [← h1, ← h2]
  have hB₂ : c₂.reg Reg.B = N + n + n := by
    simp +decide [c₂, c₁, hi]; exact hB
  have hv₂ : c₂.reg Reg.v = l.var := by simp +decide [c₂, c₁, hi]
  have hm₂ : c₂.mem = c₁.mem := rfl
  have hfinal : run (seqs [Stmt.ifz Reg.sg
      (Stmt.ifz Reg.cc (Stmt.seq (Stmt.const (eReg i false) 4) (Stmt.const (eReg i true) 5))
        (Stmt.seq (Stmt.const (eReg i false) 0) (Stmt.const (eReg i true) 3)))
      (Stmt.seq (Stmt.const (eReg i false) 2) (Stmt.const (eReg i true) 6)),
      Stmt.add Reg.addr Reg.B Reg.v, Stmt.load (bReg i) Reg.addr]) c₁ =
      ((c₂.setReg Reg.addr (N + n + n + l.var)).setReg (bReg i) (c₁.mem (N + n + n + l.var))) := by
    simp only [run_seqs_cons, run_seqs_nil, hif]
    simp only [run, hB₂, hv₂]
    simp +decide
    rfl
  rw [hfinal]
  have ha_lt : a < N + n + n := by simp only [a]; have := signCode_lt l; omega
  have hmem₁ : ∀ j, c₁.mem j = if j = a then P.count l + 1 else c.mem j := by intro j; simp [c₁]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp +decide [c₂, c₁, hi]
  · intro j hj
    simp only [setReg_mem, hm₂, hmem₁]
    have : j ≠ a := by simp only [a]; omega
    simp [this]
  · intro v hv' s hs'
    simp only [setReg_mem, hm₂, hmem₁]
    by_cases he : N + v + v + s = a
    · rw [ite_eq_left he]
      have hlv := (code_eq_iff (N := N) l v s hs').mp (by simp only [a] at he; omega)
      rw [hlv]; simp
    · rw [ite_eq_right he, hcount v hv' s hs', List.count_append]
      have hne : (⟨v, decide (s = 1)⟩ : Literal) ≠ l := fun h' =>
        he (by simp only [a]; exact ((code_eq_iff (N := N) l v s hs').mpr h').symm)
      simp [Ne.symm hne]
  · intro u hu
    simp only [setReg_mem, hm₂, hmem₁]
    have : N + n + n + u ≠ a := by omega
    simp [this]
  · intro b
    have hne : eReg i b ≠ bReg i := eReg_ne_bReg i i b hi
    cases b with
    | false => simp [c₂, hne, hi, hfs]; rfl
    | true => simp [c₂, hne, hi]; rfl
  · simp only [setReg_reg, ↓reduceIte, hmem₁]
    have : N + n + n + l.var ≠ a := by omega
    simp [this]
  · simp [c₂, c₁]
  · intro r hr
    simp only [litRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hr
    simp [c₂, c₁, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-! ### Emitting the gadget of a clause -/

theorem clausePortAt_lt {a i : Nat} {side : Bool} (h : clausePortAt a = some (i, side)) : i < 3 := by
  unfold clausePortAt at h
  split at h
  · simp at h; omega
  split at h
  · simp at h; omega
  split at h
  · simp at h; omega
  split at h
  · simp at h; omega
  split at h
  · simp at h; omega
  split at h
  · simp at h; omega
  · simp at h

/-- The value `endpointCode len a` writes to `x`. -/
def endpointVal (len a : Nat) (c : Config) : Nat :=
  match clausePortAt a with
  | some (i, side) => if i < len then c.reg (bReg i) + c.reg (eReg i side) else c.reg Reg.cb + a
  | none => c.reg Reg.cb + a

theorem endpointCode_run (len a : Nat) (c : Config) :
    (run (seqs (endpointCode len a)) c).reg Reg.x = endpointVal len a c ∧
    (run (seqs (endpointCode len a)) c).mem = c.mem ∧ (run (seqs (endpointCode len a)) c).out = c.out ∧
    ∀ r, r ≠ Reg.t → r ≠ Reg.x → (run (seqs (endpointCode len a)) c).reg r = c.reg r := by
  unfold endpointCode endpointVal
  cases h : clausePortAt a with
  | none =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp +decide [run]
    intro r h1 h2; simp [h1, h2]
  | some ib =>
    obtain ⟨i, side⟩ := ib
    have hi := clausePortAt_lt h
    by_cases hl : i < len
    · simp only [hl, ↓reduceIte]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp +decide [run]
      intro r _ h2; simp [h2]
    · simp only [hl, ↓reduceIte]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp +decide [run]
      intro r h1 h2; simp [h1, h2]

theorem endpointVal_congr (len a : Nat) (c c' : Config) (h : ∀ r, r ≠ Reg.t → r ≠ Reg.x → c'.reg r = c.reg r) :
    endpointVal len a c' = endpointVal len a c := by
  unfold endpointVal
  cases hc : clausePortAt a with
  | none => simp [h Reg.cb (by decide) (by decide)]
  | some ib =>
    obtain ⟨i, side⟩ := ib
    have hi := clausePortAt_lt hc
    simp only
    split
    · rw [h _ (by simp [hi]) (by simp [hi]), h _ (by simp [hi]) (by simp [hi])]
    · simp [h Reg.cb (by decide) (by decide)]

theorem clauseEmit_run (es : List (Nat × Nat)) (len : Nat) (c : Config) :
    let code := es.flatMap fun e => endpointCode len e.1 ++ [Stmt.write Reg.x] ++ endpointCode len e.2 ++ [Stmt.write Reg.x]
    (run (seqs code) c).out = c.out ++ edgeWord (es.map fun e => (endpointVal len e.1 c, endpointVal len e.2 c)) ∧
    (run (seqs code) c).mem = c.mem ∧
    ∀ r, r ≠ Reg.t → r ≠ Reg.x → (run (seqs code) c).reg r = c.reg r := by
  induction es generalizing c with
  | nil => exact ⟨by simp [edgeWord], rfl, fun _ _ _ => rfl⟩
  | cons e es ih =>
    intro code
    simp only [code, List.flatMap_cons]
    rw [run_seqs_append, run_seqs_append, run_seqs_append, run_seqs_append]
    obtain ⟨x₁, m₁, o₁, r₁⟩ := endpointCode_run len e.1 c
    generalize hd₁ : run (seqs (endpointCode len e.1)) c = c₁ at x₁ m₁ o₁ r₁
    generalize hd₂ : run (seqs [Stmt.write Reg.x]) c₁ = c₂
    have x₂ : c₂.out = c.out ++ [endpointVal len e.1 c] := by rw [← hd₂]; simp [run, x₁, o₁]
    have m₂ : c₂.mem = c.mem := by rw [← hd₂]; simp [run, m₁]
    have r₂ : ∀ r, r ≠ Reg.t → r ≠ Reg.x → c₂.reg r = c.reg r := by
      intro r a1 a2; rw [← hd₂]; simp [run, r₁ r a1 a2]
    obtain ⟨y₃, m₃, o₃, r₃⟩ := endpointCode_run len e.2 c₂
    generalize hd₃ : run (seqs (endpointCode len e.2)) c₂ = c₃ at y₃ m₃ o₃ r₃
    generalize hd₄ : run (seqs [Stmt.write Reg.x]) c₃ = c₄
    have hv₂ : endpointVal len e.2 c₂ = endpointVal len e.2 c := endpointVal_congr len e.2 c c₂ r₂
    have x₄ : c₄.out = c.out ++ [endpointVal len e.1 c, endpointVal len e.2 c] := by
      rw [← hd₄]; simp [run, y₃, o₃, x₂, hv₂]
    have m₄ : c₄.mem = c.mem := by rw [← hd₄]; simp [run, m₃, m₂]
    have r₄ : ∀ r, r ≠ Reg.t → r ≠ Reg.x → c₄.reg r = c.reg r := by
      intro r a1 a2; rw [← hd₄]; simp [run, r₃ r a1 a2, r₂ r a1 a2]
    obtain ⟨o₅, m₅, r₅⟩ := ih c₄
    refine ⟨?_, ?_, ?_⟩
    · rw [o₅, x₄]
      have : (es.map fun e => (endpointVal len e.1 c₄, endpointVal len e.2 c₄)) =
          (es.map fun e => (endpointVal len e.1 c, endpointVal len e.2 c)) := by
        apply List.map_congr_left; intro e' _
        rw [endpointVal_congr len e'.1 c c₄ r₄, endpointVal_congr len e'.2 c c₄ r₄]
      rw [this]
      simp [edgeWord]
    · rw [m₅, m₄]
    · intro r a1 a2; rw [r₅ r a1 a2, r₄ r a1 a2]

/-- The endpoint values of a clause gadget are the vertices of Section 5's `clauseVertex`. -/
theorem endpointVal_eq (k n j len : Nat) (pc : List PlacedLiteral) (hlen : pc.length = len) (c : Config)
    (hB : ∀ i (h : i < pc.length), c.reg (bReg i) = gadgetWidth k * pc[i].literal.var)
    (hE : ∀ i (h : i < pc.length) b, c.reg (eReg i b) = variableEndpoint pc[i].port b)
    (hcb : c.reg Reg.cb = gadgetWidth k * (n + j)) (a : Nat) :
    endpointVal len a c = clauseVertex (gadgetWidth k) n j pc a := by
  subst hlen
  unfold endpointVal clauseVertex attachmentAt
  cases h : clausePortAt a with
  | none =>
    simp only [Option.bind_none, hcb, blockVertex]
    rw [Nat.mul_comm]
  | some ib =>
    obtain ⟨i, side⟩ := ib
    by_cases hi : i < pc.length
    · simp only [Option.bind_some, hi, ↓reduceIte, List.getElem?_eq_getElem hi, Option.map_some,
        hB i hi, hE i hi side, blockVertex]
      rw [Nat.mul_comm]
    · simp only [Option.bind_some, hi, ↓reduceIte, List.getElem?_eq_none (Nat.le_of_not_lt hi),
        Option.map_none, hcb, blockVertex]
      rw [Nat.mul_comm]

theorem clauseEmit_pairs (k n j len : Nat) (pc : List PlacedLiteral) (hlen : pc.length = len) (c : Config)
    (hB : ∀ i (h : i < pc.length), c.reg (bReg i) = gadgetWidth k * pc[i].literal.var)
    (hE : ∀ i (h : i < pc.length) b, c.reg (eReg i b) = variableEndpoint pc[i].port b)
    (hcb : c.reg Reg.cb = gadgetWidth k * (n + j)) :
    ((Registered.gadgetEdges k len).map fun e => (endpointVal len e.1 c, endpointVal len e.2 c)) =
      rawPairs (clauseVertex (gadgetWidth k) n j pc) (clauseGraph k pc) := by
  have hg : clauseGraph k pc = Registered.gadgetEdges k len := by
    simp only [clauseGraph, Registered.gadgetEdges, hlen]
  rw [hg, rawPairs]
  apply List.map_congr_left
  intro e _
  rw [endpointVal_eq k n j len pc hlen c hB hE hcb, endpointVal_eq k n j len pc hlen c hB hE hcb]

/-! ### The state while reading literals -/

theorem At.drop' {c c' : Config} {u w : List Nat} (h : At c (u ++ w)) (hp : c'.reg Reg.p = c.reg Reg.p + u.length)
    (hm : ∀ j, j < c.reg Reg.p + (u ++ w).length → c'.mem j = c.mem j) : At c' w := by
  intro i hi
  rw [hp, Nat.add_assoc, hm _ (by simp; omega)]
  have := h (u.length + i) (by simp; omega)
  rw [this, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp

/-- What the literal reading needs: the remaining input `w` at `p`, the tables, the constants. -/
structure LitPre (k n N : Nat) (P : List Literal) (w : List Nat) (c : Config) : Prop where
  hAt : At c w
  hpN : c.reg Reg.p + w.length ≤ N
  hN : c.reg Reg.N = N
  hB : c.reg Reg.B = N + n + n
  hW : c.reg Reg.W = gadgetWidth k
  hone : c.reg Reg.one = 1
  hcount : ∀ v, v < n → ∀ s, s < 2 → c.mem (N + v + v + s) = P.count ⟨v, decide (s = 1)⟩
  htable : ∀ u, u < n → c.mem (N + n + n + u) = gadgetWidth k * u

/-- Reading one literal; its memory accesses (the input cells `p`, `p + 1`, the count `N + 2v + s` and
the table entry `B + v`) are below `S` when `N + 3n ≤ S`. -/
theorem readLit_step (k n N : Nat) (i : Nat) (hi : i < 3) (c : Config) (l : Literal) (w : List Nat)
    (P : List Literal) (h : LitPre k n N P (litCode l ++ w) c) (hl : l.var < n) {S : Nat}
    (hS : N + n + n + n ≤ S) :
    LitPre k n N (P ++ [l]) w (run (readLit i) c) ∧
    (∀ b, (run (readLit i) c).reg (eReg i b) = variableEndpoint (⟨l, P.count l⟩ : PlacedLiteral).port b) ∧
    (run (readLit i) c).reg (bReg i) = gadgetWidth k * l.var ∧
    (run (readLit i) c).out = c.out ∧
    (run (readLit i) c).reg Reg.p = c.reg Reg.p + 2 ∧
    (∀ r, r ∉ litRegs i → (run (readLit i) c).reg r = c.reg r) ∧ AddrOK S (readLit i) c := by
  have hpN2 : c.reg Reg.p + 2 ≤ N := by have := h.hpN; simp [litCode] at this; omega
  have hA : AddrOK S (readLit i) c := by
    have hv : c.mem (c.reg Reg.p) = l.var := h.hAt.head
    have hs : c.mem (c.reg Reg.p + 1) = signCode l := by
      have := h.hAt 1 (by simp [litCode])
      simpa [litCode] using this
    have hsl := signCode_lt l
    simp +decide [readLit, run, h.hone, h.hN, h.hB, hv, hs, hi]
    omega
  obtain ⟨hp, hlow, hcnt, htab, hE, hBr, hout, hfr⟩ :=
    readLit_run i hi c l w P n N h.hAt hpN2 h.hN h.hB h.hone hl h.hcount
  have hnot : ∀ r, r ∈ [Reg.N, Reg.B, Reg.W, Reg.one] → r ∉ litRegs i := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [litRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
    rcases hr with rfl | rfl | rfl | rfl <;> simp +decide [hi]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, hcnt, ?_⟩, hE, ?_, hout, hp, hfr, hA⟩
  · exact h.hAt.drop' (u := litCode l) (by rw [hp]; rfl) (fun j hj => hlow j (by have := h.hpN; omega))
  · rw [hp]; have := h.hpN; simp [litCode] at this; omega
  · rw [hfr _ (hnot _ (by simp)), h.hN]
  · rw [hfr _ (hnot _ (by simp)), h.hB]
  · rw [hfr _ (hnot _ (by simp)), h.hW]
  · rw [hfr _ (hnot _ (by simp)), h.hone]
  · intro u hu; rw [htab u hu, h.htable u hu]
  · rw [hBr, h.htable _ hl]

theorem slot_not_mem (i i' : Nat) (hi : i < 3) (hi' : i' < 3) (hne : i ≠ i') :
    bReg i ∉ litRegs i' ∧ ∀ b, eReg i b ∉ litRegs i' := by
  refine ⟨?_, ?_⟩
  · simp only [litRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨by simp [hi], by simp [hi], by simp [hi], by simp [hi], by simp [hi], by simp [hi],
      bReg_ne_eReg _ _ _ hi, bReg_ne_eReg _ _ _ hi, fun h => hne (bReg_inj h)⟩
  · intro b
    simp only [litRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨by simp [hi], by simp [hi], by simp [hi], by simp [hi], by simp [hi], by simp [hi],
      fun h => hne (eReg_inj h).1, fun h => hne (eReg_inj h).1, eReg_ne_bReg _ _ _ hi'⟩

/-! ### One clause -/

theorem clausePairsFrom_snoc (k n : Nat) (A : CNF) (cl : Clause) : ∀ (j : Nat) (past : List Literal),
    clausePairsFrom k n j past (A ++ [cl]) =
      clausePairsFrom k n j past A ++ clausePairs k n (j + A.length) (past ++ A.flatten) cl := by
  induction A with
  | nil => intro j past; simp [clausePairsFrom]
  | cons c A ih =>
    intro j past
    simp only [List.cons_append, clausePairsFrom, ih, List.append_assoc, List.length_cons, List.flatten_cons]
    rw [show j + 1 + A.length = j + (A.length + 1) by omega]

/-- The state of the clause loop: the clauses `pre` are done, `suf` remain. -/
structure StateB (k : Nat) (f : CNF) (n N : Nat) (pre suf : CNF) (c : Config) : Prop where
  hsplit : pre ++ suf = f
  hm : c.reg Reg.m = suf.length
  lit : LitPre k n N pre.flatten (suf.flatMap clauseCode) c
  hcb : c.reg Reg.cb = gadgetWidth k * (n + pre.length)
  hout : c.out = f.length :: edgeWord (varPairs k 0 n ++ clausePairsFrom k n 0 [] pre)

theorem LitPre.of_eq {k n N : Nat} {P : List Literal} {w : List Nat} {c c' : Config} (h : LitPre k n N P w c)
    (hreg : ∀ r, r ∈ [Reg.p, Reg.N, Reg.B, Reg.W, Reg.one] → c'.reg r = c.reg r) (hmem : c'.mem = c.mem) :
    LitPre k n N P w c' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.hAt.of_mem (hreg _ (by simp)) (fun i _ => by rw [hmem])
  · rw [hreg _ (by simp)]; exact h.hpN
  · rw [hreg _ (by simp)]; exact h.hN
  · rw [hreg _ (by simp)]; exact h.hB
  · rw [hreg _ (by simp)]; exact h.hW
  · rw [hreg _ (by simp)]; exact h.hone
  · intro v hv s hs; rw [hmem]; exact h.hcount v hv s hs
  · intro u hu; rw [hmem]; exact h.htable u hu

/-- The slot facts after reading the literals of a clause. -/
def SlotOK (k : Nat) (pc : List PlacedLiteral) (c : Config) : Prop :=
  (∀ i (h : i < pc.length), c.reg (bReg i) = gadgetWidth k * pc[i].literal.var) ∧
  (∀ i (h : i < pc.length) b, c.reg (eReg i b) = variableEndpoint pc[i].port b)

theorem clauseB_split (k : Nat) : clauseB k = seqs ([Stmt.sub Reg.m Reg.m Reg.one, Stmt.load Reg.len Reg.p,
    Stmt.add Reg.p Reg.p Reg.one] ++ [readLit 0, readLit 1, Stmt.const Reg.t 2, Stmt.sub Reg.t Reg.len Reg.t,
    Stmt.ifz Reg.t (seqs (clauseEmit k 2)) (Stmt.seq (readLit 2) (seqs (clauseEmit k 3))),
    Stmt.add Reg.cb Reg.cb Reg.W]) := rfl

theorem placeLiterals_two' (P : List Literal) (l₀ l₁ : Literal) :
    placeLiterals P [l₀, l₁] = [⟨l₀, P.count l₀⟩, ⟨l₁, (P ++ [l₀]).count l₁⟩] := by
  simp [placeLiterals]

theorem placeLiterals_three' (P : List Literal) (l₀ l₁ l₂ : Literal) :
    placeLiterals P [l₀, l₁, l₂] =
      [⟨l₀, P.count l₀⟩, ⟨l₁, (P ++ [l₀]).count l₁⟩, ⟨l₂, (P ++ [l₀] ++ [l₁]).count l₂⟩] := by
  simp [placeLiterals]

theorem emit_finish {k : Nat} {f : CNF} {n N : Nat} {pre suf : CNF} {cl : Clause} {len : Nat}
    (hlenEq : cl.length = len) (cE : Config)
    (hLE : LitPre k n N (pre.flatten ++ cl) (suf.flatMap clauseCode) cE)
    (hS : SlotOK k (placeLiterals pre.flatten cl) cE) (hcb : cE.reg Reg.cb = gadgetWidth k * (n + pre.length))
    (hm : cE.reg Reg.m = suf.length)
    (hout : cE.out = f.length :: edgeWord (varPairs k 0 n ++ clausePairsFrom k n 0 [] pre))
    (hsplit : pre ++ cl :: suf = f) :
    StateB k f n N (pre ++ [cl]) suf (run (Stmt.add Reg.cb Reg.cb Reg.W) (run (seqs (clauseEmit k len)) cE)) := by
  have hpl : (placeLiterals pre.flatten cl).length = len := by
    have h := congrArg List.length (placeLiterals_forget pre.flatten cl)
    simp only [List.length_map] at h
    rw [h, hlenEq]
  obtain ⟨o₁', m₁', r₁'⟩ := clauseEmit_run (Registered.gadgetEdges k len) len cE
  have o₁ : (run (seqs (clauseEmit k len)) cE).out = _ := o₁'
  have m₁ : (run (seqs (clauseEmit k len)) cE).mem = _ := m₁'
  have r₁ : ∀ r, r ≠ Reg.t → r ≠ Reg.x → (run (seqs (clauseEmit k len)) cE).reg r = cE.reg r := r₁'
  clear o₁' m₁' r₁'
  have hpairs := clauseEmit_pairs k n pre.length len (placeLiterals pre.flatten cl) hpl cE hS.1 hS.2 hcb
  generalize hd : run (seqs (clauseEmit k len)) cE = c₁ at o₁ m₁ r₁
  have hfr : ∀ r, r ≠ Reg.cb → r ≠ Reg.t → r ≠ Reg.x → (run (Stmt.add Reg.cb Reg.cb Reg.W) c₁).reg r = cE.reg r := by
    intro r a1 a2 a3; simp [run, a1, r₁ r a2 a3]
  refine ⟨by simpa using hsplit, ?_, ?_, ?_, ?_⟩
  · rw [hfr _ (by decide) (by decide) (by decide), hm]
  · rw [List.flatten_append, List.flatten_singleton]
    exact hLE.of_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hfr _ (by decide) (by decide) (by decide))
      (by simp [run, m₁])
  · simp +decide only [run, setReg_reg, ↓reduceIte]
    rw [r₁ _ (by decide) (by decide), r₁ _ (by decide) (by decide), hcb, hLE.hW]
    simp only [List.length_append, List.length_singleton, ← Nat.add_assoc, Nat.mul_succ]
  · simp only [run, setReg_out]
    rw [o₁, hout, hpairs, clausePairsFrom_snoc, edgeWord_append, edgeWord_append, edgeWord_append]
    simp [clausePairs]

theorem memFree_clauseEmit (k len : Nat) : memFree (seqs (clauseEmit k len)) = true :=
  memFree_flatMap _ _ (fun _ => memFree_seqs_append (memFree_seqs_append (memFree_seqs_append
    (by unfold endpointCode; split <;> (try split) <;> rfl) rfl) (by unfold endpointCode; split <;> (try split) <;> rfl)) rfl)

/-- One clause of the third pass; its memory accesses are below `S` when `N + 3n ≤ S`. -/
theorem StateB.step {k : Nat} {f : CNF} {n N : Nat} {pre suf : CNF} {c : Config}
    (h : StateB k f n N pre suf c) (hm : c.reg Reg.m ≠ 0)
    (hf : ∀ cl ∈ f, cl.length = 2 ∨ cl.length = 3) (hvars : ∀ cl ∈ f, ∀ l ∈ cl, l.var < n) {S : Nat}
    (hS : N + n + n + n ≤ S) :
    AddrOK S (clauseB k) c ∧ ∃ cl suf', suf = cl :: suf' ∧ StateB k f n N (pre ++ [cl]) suf' (run (clauseB k) c) ∧
      (run (clauseB k) c).reg Reg.m + 1 = c.reg Reg.m := by
  cases suf with
  | nil => exact absurd h.hm (by simpa using hm)
  | cons cl suf =>
    suffices hS' : AddrOK S (clauseB k) c ∧ StateB k f n N (pre ++ [cl]) suf (run (clauseB k) c) from
      ⟨hS'.1, cl, suf, rfl, hS'.2, by rw [hS'.2.hm, h.hm]; simp⟩
    have hcl : cl ∈ f := by rw [← h.hsplit]; simp
    have hlen := hf cl hcl
    have hv : ∀ l ∈ cl, l.var < n := hvars cl hcl
    have hL := h.lit
    simp only [List.flatMap_cons, clauseCode, List.cons_append] at hL
    -- the clause header
    have hA₀ : AddrOK S (seqs [Stmt.sub Reg.m Reg.m Reg.one, Stmt.load Reg.len Reg.p,
        Stmt.add Reg.p Reg.p Reg.one]) c := by
      have := hL.hpN; simp only [List.length_cons] at this; simp +decide [run]; omega
    rw [clauseB_split, run_seqs_append, addrOK_seqs_append]
    refine and_assoc.mpr ⟨hA₀, ?_⟩
    generalize hd₀ : run (seqs [Stmt.sub Reg.m Reg.m Reg.one, Stmt.load Reg.len Reg.p,
      Stmt.add Reg.p Reg.p Reg.one]) c = c₀
    have hlenv : c.mem (c.reg Reg.p) = cl.length := hL.hAt.head
    have r₀ : ∀ r, r ≠ Reg.m → r ≠ Reg.len → r ≠ Reg.p → c₀.reg r = c.reg r := by
      intro r a1 a2 a3; rw [← hd₀]; simp [run, a1, a2, a3]
    have m₀ : c₀.mem = c.mem := by rw [← hd₀]; simp [run]
    have o₀ : c₀.out = c.out := by rw [← hd₀]; simp [run]
    have p₀ : c₀.reg Reg.p = c.reg Reg.p + 1 := by rw [← hd₀]; simp +decide [run, hL.hone]
    have hm₀ : c₀.reg Reg.m = suf.length := by rw [← hd₀]; simp +decide [run, hL.hone, h.hm]
    have hlen₀ : c₀.reg Reg.len = cl.length := by rw [← hd₀]; simp +decide [run, hlenv]
    have L₀ : LitPre k n N pre.flatten (cl.flatMap litCode ++ suf.flatMap clauseCode) c₀ := by
      refine ⟨hL.hAt.tail m₀ p₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [p₀]; have := hL.hpN; simp only [List.length_cons] at this; omega
      · rw [r₀ _ (by decide) (by decide) (by decide)]; exact hL.hN
      · rw [r₀ _ (by decide) (by decide) (by decide)]; exact hL.hB
      · rw [r₀ _ (by decide) (by decide) (by decide)]; exact hL.hW
      · rw [r₀ _ (by decide) (by decide) (by decide)]; exact hL.hone
      · intro v hv' s hs; rw [m₀]; exact hL.hcount v hv' s hs
      · intro u hu; rw [m₀]; exact hL.htable u hu
    have hcb₀ : c₀.reg Reg.cb = gadgetWidth k * (n + pre.length) := by
      rw [r₀ _ (by decide) (by decide) (by decide), h.hcb]
    have hout₀ : c₀.out = f.length :: edgeWord (varPairs k 0 n ++ clausePairsFrom k n 0 [] pre) := by
      rw [o₀, h.hout]
    have hsplit : pre ++ cl :: suf = f := h.hsplit
    have hnot₁ : ∀ i, i < 3 → ∀ r, r ∈ [Reg.m, Reg.len, Reg.cb] → r ∉ litRegs i := by
      intro i hi r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [litRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      rcases hr with rfl | rfl | rfl <;> simp +decide [hi]
    simp only [run_seqs_cons, run_seqs_nil, addrOK_seqs_cons, addrOK_seqs_nil, addrOK_const, addrOK_sub,
      addrOK_add, and_true, true_and]
    match cl, hlen, hv, L₀, hlen₀, hsplit with
    | [l₀, l₁], _, hv, L₀, hlen₀, hsplit =>
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc] at L₀
      obtain ⟨L₁, E₁, B₁, o₁, -, f₁, A₀⟩ := readLit_step k n N 0 (by decide) c₀ l₀ _ _ L₀ (hv l₀ (by simp)) hS
      generalize hd₁ : run (readLit 0) c₀ = c₁ at L₁ E₁ B₁ o₁ f₁
      obtain ⟨L₂, E₂, B₂, o₂, -, f₂, A₁⟩ := readLit_step k n N 1 (by decide) c₁ l₁ _ _ L₁ (hv l₁ (by simp)) hS
      generalize hd₂ : run (readLit 1) c₁ = c₂ at L₂ E₂ B₂ o₂ f₂
      generalize hd₃ : run (Stmt.sub Reg.t Reg.len Reg.t) (run (Stmt.const Reg.t 2) c₂) = c₃
      have r₃ : ∀ r, r ≠ Reg.t → c₃.reg r = c₂.reg r := by intro r hr; rw [← hd₃]; simp [run, hr]
      have m₃ : c₃.mem = c₂.mem := by rw [← hd₃]; simp [run]
      have o₃ : c₃.out = c₂.out := by rw [← hd₃]; simp [run]
      have t₃ : c₃.reg Reg.t = 0 := by
        rw [← hd₃]; simp +decide [run]
        rw [f₂ _ (hnot₁ 1 (by decide) _ (by simp)), f₁ _ (hnot₁ 0 (by decide) _ (by simp)), hlen₀]; rfl
      have hif : run (Stmt.ifz Reg.t (seqs (clauseEmit k 2)) (Stmt.seq (readLit 2) (seqs (clauseEmit k 3)))) c₃ =
          run (seqs (clauseEmit k 2)) c₃ := by simp [run, t₃]
      rw [hif]
      have hP : pre.flatten ++ [l₀] ++ [l₁] = pre.flatten ++ [l₀, l₁] := by simp
      rw [hP] at L₂
      refine ⟨⟨A₀, A₁, AddrOK.ifz (fun _ => AddrOK.of_memFree (memFree_clauseEmit k 2)) (fun h => absurd t₃ h)⟩, ?_⟩
      refine emit_finish (by rfl) c₃ (L₂.of_eq (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact r₃ _ (by decide)) m₃) ⟨?_, ?_⟩ ?_ ?_ ?_ hsplit
      · intro i hi
        simp only [placeLiterals_two', List.length_cons, List.length_nil] at hi ⊢
        match i, hi with
        | 0, _ =>
          rw [r₃ _ (bReg_ne_t _ (by decide)), f₂ _ (slot_not_mem 0 1 (by decide) (by decide) (by decide)).1, B₁]; rfl
        | 1, _ => rw [r₃ _ (bReg_ne_t _ (by decide)), B₂]; rfl
      · intro i hi b
        simp only [placeLiterals_two', List.length_cons, List.length_nil] at hi ⊢
        match i, hi with
        | 0, _ =>
          rw [r₃ _ (eReg_ne_t _ _ (by decide)), f₂ _ ((slot_not_mem 0 1 (by decide) (by decide) (by decide)).2 b),
            E₁]; rfl
        | 1, _ => rw [r₃ _ (eReg_ne_t _ _ (by decide)), E₂]; rfl
      · rw [r₃ _ (by decide), f₂ _ (hnot₁ 1 (by decide) _ (by simp)), f₁ _ (hnot₁ 0 (by decide) _ (by simp)), hcb₀]
      · rw [r₃ _ (by decide), f₂ _ (hnot₁ 1 (by decide) _ (by simp)), f₁ _ (hnot₁ 0 (by decide) _ (by simp)), hm₀]
      · rw [o₃, o₂, o₁, hout₀]
    | [l₀, l₁, l₂], _, hv, L₀, hlen₀, hsplit =>
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc] at L₀
      obtain ⟨L₁, E₁, B₁, o₁, -, f₁, A₀⟩ := readLit_step k n N 0 (by decide) c₀ l₀ _ _ L₀ (hv l₀ (by simp)) hS
      generalize hd₁ : run (readLit 0) c₀ = c₁ at L₁ E₁ B₁ o₁ f₁
      obtain ⟨L₂, E₂, B₂, o₂, -, f₂, A₁⟩ := readLit_step k n N 1 (by decide) c₁ l₁ _ _ L₁ (hv l₁ (by simp)) hS
      generalize hd₂ : run (readLit 1) c₁ = c₂ at L₂ E₂ B₂ o₂ f₂
      generalize hd₃ : run (Stmt.sub Reg.t Reg.len Reg.t) (run (Stmt.const Reg.t 2) c₂) = c₃
      have r₃ : ∀ r, r ≠ Reg.t → c₃.reg r = c₂.reg r := by intro r hr; rw [← hd₃]; simp [run, hr]
      have m₃ : c₃.mem = c₂.mem := by rw [← hd₃]; simp [run]
      have o₃ : c₃.out = c₂.out := by rw [← hd₃]; simp [run]
      have t₃ : c₃.reg Reg.t = 1 := by
        rw [← hd₃]; simp +decide [run]
        rw [f₂ _ (hnot₁ 1 (by decide) _ (by simp)), f₁ _ (hnot₁ 0 (by decide) _ (by simp)), hlen₀]; rfl
      have hif : run (Stmt.ifz Reg.t (seqs (clauseEmit k 2)) (Stmt.seq (readLit 2) (seqs (clauseEmit k 3)))) c₃ =
          run (seqs (clauseEmit k 3)) (run (readLit 2) c₃) := by simp [run, t₃]
      rw [hif]
      have L₃ : LitPre k n N (pre.flatten ++ [l₀] ++ [l₁]) (litCode l₂ ++ suf.flatMap clauseCode) c₃ :=
        L₂.of_eq (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact r₃ _ (by decide)) m₃
      obtain ⟨L₄, E₄, B₄, o₄, -, f₄, A₂⟩ := readLit_step k n N 2 (by decide) c₃ l₂ _ _ L₃ (hv l₂ (by simp)) hS
      refine ⟨⟨A₀, A₁, AddrOK.ifz (fun h => absurd h (by omega))
        (fun _ => AddrOK.seq A₂ (AddrOK.of_memFree (memFree_clauseEmit k 3)))⟩, ?_⟩
      generalize hd₄ : run (readLit 2) c₃ = c₄ at L₄ E₄ B₄ o₄ f₄
      have hP : pre.flatten ++ [l₀] ++ [l₁] ++ [l₂] = pre.flatten ++ [l₀, l₁, l₂] := by simp
      rw [hP] at L₄
      refine emit_finish (by rfl) c₄ L₄ ⟨?_, ?_⟩ ?_ ?_ ?_ hsplit
      · intro i hi
        simp only [placeLiterals_three', List.length_cons, List.length_nil] at hi ⊢
        match i, hi with
        | 0, _ =>
          rw [f₄ _ (slot_not_mem 0 2 (by decide) (by decide) (by decide)).1, r₃ _ (bReg_ne_t _ (by decide)),
            f₂ _ (slot_not_mem 0 1 (by decide) (by decide) (by decide)).1, B₁]; rfl
        | 1, _ => rw [f₄ _ (slot_not_mem 1 2 (by decide) (by decide) (by decide)).1, r₃ _ (bReg_ne_t _ (by decide)), B₂]; rfl
        | 2, _ => rw [B₄]; rfl
      · intro i hi b
        simp only [placeLiterals_three', List.length_cons, List.length_nil] at hi ⊢
        match i, hi with
        | 0, _ =>
          rw [f₄ _ ((slot_not_mem 0 2 (by decide) (by decide) (by decide)).2 b), r₃ _ (eReg_ne_t _ _ (by decide)),
            f₂ _ ((slot_not_mem 0 1 (by decide) (by decide) (by decide)).2 b), E₁]; rfl
        | 1, _ =>
          rw [f₄ _ ((slot_not_mem 1 2 (by decide) (by decide) (by decide)).2 b), r₃ _ (eReg_ne_t _ _ (by decide)),
            E₂]; rfl
        | 2, _ => rw [E₄]; rfl
      · rw [f₄ _ (hnot₁ 2 (by decide) _ (by simp)), r₃ _ (by decide), f₂ _ (hnot₁ 1 (by decide) _ (by simp)),
          f₁ _ (hnot₁ 0 (by decide) _ (by simp)), hcb₀]
      · rw [f₄ _ (hnot₁ 2 (by decide) _ (by simp)), r₃ _ (by decide), f₂ _ (hnot₁ 1 (by decide) _ (by simp)),
          f₁ _ (hnot₁ 0 (by decide) _ (by simp)), hm₀]
      · rw [o₄, o₃, o₂, o₁, hout₀]

end STACS2027.RAM
