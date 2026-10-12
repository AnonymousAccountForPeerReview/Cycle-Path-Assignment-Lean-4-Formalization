module

public import ApproximationHardness.RAM.PassA
import Lean.Elab.Tactic.Omega

/-!
# The second pass of the RAM program: the variable gadgets

`passV k` emits the edges of the `n` variable gadgets, writes the block start
`W · v` of every variable `v < n` to the table at `B + v`, and leaves `W · n` (the
first clause block) in `Reg.cb`, within `O(n)` steps for fixed `k`.
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT

theorem run_seqs_append (A B : List Stmt) (c : Config) : run (seqs (A ++ B)) c = run (seqs B) (run (seqs A) c) := by
  induction A generalizing c with
  | nil => rfl
  | cons s A ih => simp [ih]

theorem loopFree_seqs_append {A B : List Stmt} (hA : LoopFree (seqs A)) (hB : LoopFree (seqs B)) :
    LoopFree (seqs (A ++ B)) := by
  induction A with
  | nil => exact hB
  | cons s A ih => exact ⟨hA.1, ih hA.2⟩

theorem loopFree_edgeConst (base a b : Nat) : LoopFree (seqs (edgeConst base a b)) := by
  simp [edgeConst, seqs, LoopFree]

theorem loopFree_flatMap {α : Type} (es : List α) (F : α → List Stmt) (h : ∀ e, LoopFree (seqs (F e))) :
    LoopFree (seqs (es.flatMap F)) := by
  induction es with
  | nil => trivial
  | cons e es ih => exact loopFree_seqs_append (h e) ih

/-- Emitting edges with constant offsets from the base register `vb`. -/
theorem varEmit_run (es : List (Nat × Nat)) (c : Config) :
    (run (seqs (es.flatMap fun e => edgeConst Reg.vb e.1 e.2)) c).out =
        c.out ++ edgeWord (es.map fun e => (c.reg Reg.vb + e.1, c.reg Reg.vb + e.2)) ∧
      (run (seqs (es.flatMap fun e => edgeConst Reg.vb e.1 e.2)) c).mem = c.mem ∧
      ∀ r, r ≠ Reg.t → r ≠ Reg.x → (run (seqs (es.flatMap fun e => edgeConst Reg.vb e.1 e.2)) c).reg r = c.reg r := by
  induction es generalizing c with
  | nil => exact ⟨by simp [edgeWord], rfl, fun _ _ _ => rfl⟩
  | cons e es ih =>
    rw [List.flatMap_cons, run_seqs_append]
    have hvb : (run (seqs (edgeConst Reg.vb e.1 e.2)) c).reg Reg.vb = c.reg Reg.vb := by
      simp +decide [edgeConst, run]
    obtain ⟨o, m, r⟩ := ih (run (seqs (edgeConst Reg.vb e.1 e.2)) c)
    refine ⟨?_, ?_, ?_⟩
    · rw [o, hvb]
      simp +decide [edgeConst, run, edgeWord]
    · rw [m]; rfl
    · intro x h1 h2
      rw [r x h1 h2]
      simp only [edgeConst, run_seqs_cons, run_seqs_nil, run, setReg_reg, emit_reg, h1, h2, ↓reduceIte]

/-- The prefix and the suffix of the variable loop's body. -/
def varBodyPre : List Stmt := [Stmt.sub Reg.cv Reg.cv Reg.one, Stmt.add Reg.addr Reg.B Reg.vi, Stmt.store Reg.addr Reg.vb]
def varBodyPost : List Stmt := [Stmt.add Reg.vb Reg.vb Reg.W, Stmt.add Reg.vi Reg.vi Reg.one]

theorem varBody_eq (k : Nat) : varBody k = seqs (varBodyPre ++ varEmit k ++ varBodyPost) := rfl

theorem loopFree_varBody (k : Nat) : LoopFree (varBody k) := by
  rw [varBody_eq]
  refine loopFree_seqs_append (loopFree_seqs_append (by simp [varBodyPre, seqs, LoopFree]) ?_)
    (by simp [varBodyPost, seqs, LoopFree])
  exact loopFree_flatMap _ _ (fun e => loopFree_edgeConst _ _ _)

/-- The invariant of the variable loop, for `n` variables, input length `N` and table start `B`. -/
structure InvV (k : Nat) (m n N B : Nat) (mem₀ : Nat → Nat) (c : Config) : Prop where
  hv : c.reg Reg.vi + c.reg Reg.cv = n
  hvb : c.reg Reg.vb = gadgetWidth k * c.reg Reg.vi
  hW : c.reg Reg.W = gadgetWidth k
  hB : c.reg Reg.B = B
  hN : c.reg Reg.N = N
  hn : c.reg Reg.n = n
  hone : c.reg Reg.one = 1
  hzero : c.reg Reg.zero = 0
  hout : c.out = m :: edgeWord (varPairs k 0 (c.reg Reg.vi))
  hlow : ∀ i, i < B → c.mem i = mem₀ i
  htable : ∀ u, u < c.reg Reg.vi → c.mem (B + u) = gadgetWidth k * u

theorem varPairs_succ (k v : Nat) :
    varPairs k 0 (v + 1) = varPairs k 0 v ++ rawPairs (blockVertex (gadgetWidth k) v) (variableGraph k) := by
  simp only [varPairs]
  rw [← List.range'_append (s := 0) (m := v) (n := 1)]
  simp

theorem edgeWord_append (A B : List (Nat × Nat)) : edgeWord (A ++ B) = edgeWord A ++ edgeWord B := by
  simp [edgeWord]

theorem InvV.step {k m n N B : Nat} {mem₀ : Nat → Nat} {c : Config} (h : InvV k m n N B mem₀ c)
    (hc : c.reg Reg.cv ≠ 0) :
    InvV k m n N B mem₀ (run (varBody k) c) ∧ (run (varBody k) c).reg Reg.cv + 1 = c.reg Reg.cv := by
  rw [varBody_eq, run_seqs_append, run_seqs_append]
  generalize hd₁ : run (seqs varBodyPre) c = c₁
  have hc₁ : ∀ r, r ≠ Reg.cv → r ≠ Reg.addr → c₁.reg r = c.reg r := by
    intro r a1 a2; rw [← hd₁]; simp [varBodyPre, run, a1, a2]
  have hm₁ : c₁.mem = fun i => if i = B + c.reg Reg.vi then c.reg Reg.vb else c.mem i := by
    rw [← hd₁]; funext i; simp +decide [varBodyPre, run, h.hB]
  have hcv₁ : c₁.reg Reg.cv = c.reg Reg.cv - 1 := by rw [← hd₁]; simp +decide [varBodyPre, run, h.hone]
  have ho₁ : c₁.out = c.out := by rw [← hd₁]; simp [varBodyPre, run]
  obtain ⟨o₂, m₂, r₂⟩ := varEmit_run (variableGraph k) c₁
  generalize hd₂ : run (seqs (varEmit k)) c₁ = c₂
  rw [show run (seqs (varEmit k)) c₁ = run (seqs ((variableGraph k).flatMap fun e => edgeConst Reg.vb e.1 e.2)) c₁
    from rfl] at hd₂
  rw [hd₂] at o₂ m₂ r₂
  have hrd : ∀ r, r ≠ Reg.t → r ≠ Reg.x → r ≠ Reg.cv → r ≠ Reg.addr → c₂.reg r = c.reg r := by
    intro r a1 a2 a3 a4; rw [r₂ r a1 a2, hc₁ r a3 a4]
  generalize hd₃ : run (seqs varBodyPost) c₂ = c₃
  have hvi : c₃.reg Reg.vi = c.reg Reg.vi + 1 := by
    rw [← hd₃]; simp +decide [varBodyPost, run]
    rw [hrd _ (by decide) (by decide) (by decide) (by decide), hrd _ (by decide) (by decide) (by decide) (by decide),
      h.hone]
  have hvb : c₃.reg Reg.vb = c.reg Reg.vb + gadgetWidth k := by
    rw [← hd₃]; simp +decide [varBodyPost, run]
    rw [hrd _ (by decide) (by decide) (by decide) (by decide), hrd _ (by decide) (by decide) (by decide) (by decide),
      h.hW]
  have hpost : ∀ r, r ≠ Reg.vb → r ≠ Reg.vi → c₃.reg r = c₂.reg r := by
    intro r a1 a2; rw [← hd₃]; simp [varBodyPost, run, a1, a2]
  have hpostm : c₃.mem = c₂.mem := by rw [← hd₃]; simp [varBodyPost, run]
  have hposto : c₃.out = c₂.out := by rw [← hd₃]; simp [varBodyPost, run]
  have hvb₁ : c₁.reg Reg.vb = c.reg Reg.vb := hc₁ _ (by decide) (by decide)
  have hcv₃ : c₃.reg Reg.cv = c.reg Reg.cv - 1 := by
    rw [hpost _ (by decide) (by decide), r₂ _ (by decide) (by decide), hcv₁]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hvi, hcv₃]; have := h.hv; omega
  · rw [hvi, hvb, h.hvb, Nat.mul_succ]
  · rw [hpost _ (by decide) (by decide), hrd _ (by decide) (by decide) (by decide) (by decide), h.hW]
  · rw [hpost _ (by decide) (by decide), hrd _ (by decide) (by decide) (by decide) (by decide), h.hB]
  · rw [hpost _ (by decide) (by decide), hrd _ (by decide) (by decide) (by decide) (by decide), h.hN]
  · rw [hpost _ (by decide) (by decide), hrd _ (by decide) (by decide) (by decide) (by decide), h.hn]
  · rw [hpost _ (by decide) (by decide), hrd _ (by decide) (by decide) (by decide) (by decide), h.hone]
  · rw [hpost _ (by decide) (by decide), hrd _ (by decide) (by decide) (by decide) (by decide), h.hzero]
  · rw [hposto, hvi, o₂, varPairs_succ, edgeWord_append, ho₁, h.hout, hvb₁, h.hvb]
    have hmap : (variableGraph k).map (fun e => (gadgetWidth k * c.reg Reg.vi + e.1, gadgetWidth k * c.reg Reg.vi + e.2))
        = rawPairs (blockVertex (gadgetWidth k) (c.reg Reg.vi)) (variableGraph k) := by
      simp only [rawPairs, blockVertex, Nat.mul_comm]
    rw [hmap, List.cons_append]
  · intro i hi
    rw [hpostm, m₂, hm₁]
    have : i ≠ B + c.reg Reg.vi := by omega
    simp only [this, ↓reduceIte]
    exact h.hlow i hi
  · intro u hu
    rw [hvi] at hu
    rw [hpostm, m₂, hm₁]
    by_cases hu' : u = c.reg Reg.vi
    · subst hu'; simp [h.hvb]
    · have : B + u ≠ B + c.reg Reg.vi := by omega
      simp only [this, ↓reduceIte]
      exact h.htable u (by omega)
  · rw [hcv₃]; omega

theorem InvV.cv_le {k m n N B : Nat} {mem₀ : Nat → Nat} {c : Config} (h : InvV k m n N B mem₀ c) :
    c.reg Reg.cv ≤ n := by have := h.hv; omega

theorem memFree_varEmit (k : Nat) : memFree (seqs (varEmit k)) = true := memFree_flatMap _ _ (fun _ => rfl)

/-- The only memory access of the variable loop's body is the table entry `B + v`, `v < n`. -/
theorem InvV.addrOK {k m n N B : Nat} {mem₀ : Nat → Nat} {c : Config} (h : InvV k m n N B mem₀ c)
    (hc : c.reg Reg.cv ≠ 0) {S : Nat} (hS : B + n ≤ S) : AddrOK S (varBody k) c := by
  rw [varBody_eq]
  refine AddrOK.append_memFree (AddrOK.append_memFree ?_ (memFree_varEmit k)) rfl
  have := h.hv
  simp +decide [varBodyPre, run, h.hB]; omega

/-- The prefix and suffix of the second pass. -/
def passVpre (k : Nat) : Stmt :=
  seqs [Stmt.const Reg.W (gadgetWidth k), Stmt.const Reg.vb 0, Stmt.const Reg.vi 0, Stmt.add Reg.cv Reg.n Reg.zero]
def passVpost : Stmt := seqs [Stmt.add Reg.cb Reg.vb Reg.zero]

theorem passV_eq (k : Nat) : passV k = Stmt.seq (passVpre k) (Stmt.seq (Stmt.loop Reg.cv (varBody k)) passVpost) := rfl

def passVModel (k : Nat) (c : Config) : Config :=
  run passVpost (iterate (run (varBody k)) ((run (passVpre k) c).reg Reg.cv) (run (passVpre k) c))

def passVCost (k n : Nat) : Nat := size (passVpre k) + (n * (size (varBody k) + 1) + 1 + size passVpost)

/-- The state after the first pass, as needed by the second. -/
structure AfterA (m n N B : Nat) (mem₀ : Nat → Nat) (c : Config) : Prop where
  hn : c.reg Reg.n = n
  hN : c.reg Reg.N = N
  hB : c.reg Reg.B = B
  hone : c.reg Reg.one = 1
  hzero : c.reg Reg.zero = 0
  hout : c.out = [m]
  hmem : c.mem = mem₀

theorem InvV.start {k m n N B : Nat} {mem₀ : Nat → Nat} {c : Config} (h : AfterA m n N B mem₀ c) :
    InvV k m n N B mem₀ (run (passVpre k) c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp +decide [passVpre, run, h.hn, h.hN, h.hB, h.hone, h.hzero, h.hout, h.hmem, varPairs, edgeWord]

/-- The second pass writes the table `[B, B + n)`: it runs within every space bound `S ≥ B + n`
(and reads nothing). -/
theorem sat_passV (k m n N B : Nat) (mem₀ : Nat → Nat) {S : Nat} (hS : B + n ≤ S) :
    SatB S (passV k) (AfterA m n N B mem₀) (passVModel k) (passVCost k n) := by
  have h₁ := SatB.ofLoopFree (S := S) (s := passVpre k) (by simp [passVpre, seqs, LoopFree]) (P := AfterA m n N B mem₀)
    (fun _ _ => AddrOK.of_memFree rfl)
  have h₂ := SatB.loop (a := Reg.cv) (body := varBody k) (P := InvV k m n N B mem₀) (m := run (varBody k)) (L := n)
    (SatB.ofLoopFree (loopFree_varBody k) (fun c hc => hc.1.addrOK hc.2 hS)) (fun c hc hcv => (hc.step hcv).1)
    (fun c hc hcv => (hc.step hcv).2) (fun c hc => hc.cv_le)
  have h₃ := SatB.ofLoopFree (S := S) (s := passVpost) (by simp [passVpost, seqs, LoopFree]) (P := fun _ => True)
    (fun _ _ => AddrOK.of_memFree rfl)
  have h := h₁.seq (Q := InvV k m n N B mem₀) (fun c hc => InvV.start hc) (h₂.seq (fun _ _ => trivial) h₃)
  rw [passV_eq]
  exact (h.mono (fun c hc => hc) (by simp only [passVCost]; omega)).congr (fun c _ => rfl)

/-- After the second pass: the variable gadgets are emitted and the block table is written. -/
theorem passVModel_spec {k m n N B : Nat} {mem₀ : Nat → Nat} {c : Config} (h : AfterA m n N B mem₀ c) :
    let c' := passVModel k c
    c'.out = m :: edgeWord (varPairs k 0 n) ∧ c'.reg Reg.cb = gadgetWidth k * n ∧
      c'.reg Reg.W = gadgetWidth k ∧ c'.reg Reg.N = N ∧ c'.reg Reg.B = B ∧ c'.reg Reg.n = n ∧
      c'.reg Reg.one = 1 ∧ c'.reg Reg.zero = 0 ∧
      (∀ i, i < B → c'.mem i = mem₀ i) ∧ (∀ u, u < n → c'.mem (B + u) = gadgetWidth k * u) := by
  obtain ⟨hI, hcv0⟩ := iterate_invariant (a := Reg.cv) (P := InvV k m n N B mem₀) (m := run (varBody k))
    (fun c hc hcv => (hc.step hcv).1) (fun c hc hcv => (hc.step hcv).2) _ _ (InvV.start h) rfl
  have hvi : (iterate (run (varBody k)) ((run (passVpre k) c).reg Reg.cv) (run (passVpre k) c)).reg Reg.vi = n := by
    have := hI.hv; omega
  intro c'
  have hpost : ∀ r, r ≠ Reg.cb → c'.reg r =
      (iterate (run (varBody k)) ((run (passVpre k) c).reg Reg.cv) (run (passVpre k) c)).reg r := by
    intro r hr; simp [c', passVModel, passVpost, run, hr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [c', passVModel, passVpost, run_seqs_cons, run_seqs_nil, run, setReg_out]
    rw [hI.hout, hvi]
  · simp +decide only [c', passVModel, passVpost, run_seqs_cons, run_seqs_nil, run, setReg_reg, ↓reduceIte]
    rw [hI.hzero, hI.hvb, hvi]; rfl
  · rw [hpost _ (by decide)]; exact hI.hW
  · rw [hpost _ (by decide)]; exact hI.hN
  · rw [hpost _ (by decide)]; exact hI.hB
  · rw [hpost _ (by decide)]; exact hI.hn
  · rw [hpost _ (by decide)]; exact hI.hone
  · rw [hpost _ (by decide)]; exact hI.hzero
  · intro i hi
    simp only [c', passVModel, passVpost, run_seqs_cons, run_seqs_nil, run, setReg_mem]
    exact hI.hlow i hi
  · intro u hu
    simp only [c', passVModel, passVpost, run_seqs_cons, run_seqs_nil, run, setReg_mem]
    exact hI.htable u (by rw [hvi]; exact hu)

end STACS2027.RAM
