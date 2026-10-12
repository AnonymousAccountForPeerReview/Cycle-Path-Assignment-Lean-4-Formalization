module

public import ApproximationHardness.Embed.SolverRAM
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

/-! Constant-time bounded RAM steps of the linked embedding solver. -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

/-- The head key of a class, with the empty-class convention. -/
def headKey (dst pointer : Nat) : Stmt :=
  .ifz pointer (.const dst 0)
    (seqs [.sub 41 pointer 1, loadCell dst 12 41, .add dst dst 1])

/-- Snapshot the five fields of the group indexed by register 20. -/
def groupRead : Stmt := seqs [loadCell 21 1 20, loadCell 22 2 20,
  loadCell 23 3 20, loadCell 24 4 20, loadCell 28 5 20]

/-- Record a consumed group and advance its stack pointer. -/
def consumeRecord (pointer : Nat) : Stmt := seqs [.add 29 9 1,
  storeCell 8 20 29, storeCell 9 20 30, .add pointer 28 0]

/-- Append the two classes of a popped group to the upper accumulators. -/
def popClasses (positive : Bool) : Stmt :=
  if positive then seqs [appendInto 14 15 21 22, appendInto 16 17 23 24, .const 30 0]
  else seqs [appendInto 14 15 23 24, appendInto 16 17 21 22, .const 30 1]

/-- One linked-machine pop step, with no traversal hidden in an instruction. -/
def popStepProgram : Stmt :=
  .ifz 12 (.const 7 2) (seqs [.sub 20 12 1, groupRead,
    headKey 25 21, headKey 26 23, .sub 25 25 10, .sub 26 26 10,
    .ifz 25 (.ifz 26 (.const 7 2)
      (.seq (popClasses false) (consumeRecord 12)))
      (.seq (popClasses true) (consumeRecord 12))])

/-- One nonempty lower-stack consumption. -/
def consumeGroupProgram : Stmt := seqs [.sub 20 13 1, groupRead,
  appendInto 18 19 21 22, appendInto 18 19 23 24,
  .ifz 21 (.const 30 0) (.const 30 1), consumeRecord 13]

/-- Close a merge after its lower stack has been consumed. -/
def finishMergeProgram : Stmt := seqs [.add 21 18 0, .add 22 19 0,
  appendInto 21 22 16 17, storeCell 1 9 14, storeCell 2 9 15,
  storeCell 3 9 21, storeCell 4 9 22, storeCell 5 9 12,
  .add 29 9 1, storeCell 6 8 29, storeCell 7 8 11, .const 7 0]

/-- One linked-machine consume step. -/
def consStepProgram : Stmt := .ifz 13 finishMergeProgram consumeGroupProgram

theorem headKey_loopFree (dst pointer : Nat) : LoopFree (headKey dst pointer) := by
  simp [headKey, loadCell, LoopFree, seqs]

theorem popStepProgram_loopFree : LoopFree popStepProgram := by
  simp [popStepProgram, groupRead, headKey, popClasses, consumeRecord,
    appendInto, loadCell, storeCell, LoopFree, seqs]

theorem consStepProgram_loopFree : LoopFree consStepProgram := by
  simp [consStepProgram, finishMergeProgram, consumeGroupProgram, groupRead,
    consumeRecord, appendInto, loadCell, storeCell, LoopFree, seqs]

theorem popStepProgram_size : size popStepProgram ≤ 200 := by decide

theorem consStepProgram_size : size consStepProgram ≤ 200 := by decide

/-- Exact memory footprint of an append, including cells outside the linked block. -/
theorem appendInto_memory (c : Config) {head tail otherHead otherTail : Nat}
    (hh : head < 30) (ht : tail < 30) (hu : otherHead < 30) (hv : otherTail < 30)
    (hhz : head ≠ 0) (htz : tail ≠ 0) (hne : head ≠ tail)
    (hz : c.reg 0 = 0) (ho : c.reg 1 = 1) :
    (run (appendInto head tail otherHead otherTail) c).mem =
      if c.reg head = 0 ∨ c.reg otherHead = 0 then c.mem
      else upd c.mem (c.reg 50 + (c.reg tail - 1)) (c.reg otherHead) := by
  have haux : head ≠ 32 ∧ head ≠ 33 ∧ head ≠ 34 ∧ head ≠ 35 ∧ head ≠ 40 ∧
      tail ≠ 32 ∧ tail ≠ 33 ∧ tail ≠ 34 ∧ tail ≠ 35 ∧ tail ≠ 40 ∧
      otherHead ≠ 32 ∧ otherHead ≠ 33 ∧ otherHead ≠ 34 ∧ otherHead ≠ 35 ∧
      otherTail ≠ 32 ∧ otherTail ≠ 33 ∧ otherTail ≠ 34 ∧ otherTail ≠ 35 := by omega
  rcases haux with ⟨ha, hb, hc, hd, he, hf, hg, hi, hj, hk, hl, hm, hn, hp, hq, hr, hs, ht'⟩
  by_cases h₁ : c.reg head = 0
  · simp [appendInto, seqs, run, Ne.symm hd, Ne.symm hhz, *]
  · by_cases h₂ : c.reg otherHead = 0
    · simp [appendInto, seqs, run, *]
    · funext i
      simp [appendInto, seqs, run, upd, *]

/-- Appending preserves every register other than its output pair and fixed scratch cells. -/
theorem appendInto_frame (c : Config) {head tail otherHead otherTail i : Nat}
    (hh : head < 30) (ht : tail < 30) (hu : otherHead < 30) (hv : otherTail < 30)
    (hhz : head ≠ 0) (htz : tail ≠ 0) (hne : head ≠ tail)
    (hz : c.reg 0 = 0) (ho : c.reg 1 = 1)
    (hi : i ≠ head ∧ i ≠ tail ∧ i ≠ 32 ∧ i ≠ 33 ∧ i ≠ 34 ∧ i ≠ 35 ∧ i ≠ 40) :
    (run (appendInto head tail otherHead otherTail) c).reg i = c.reg i := by
  have haux : head ≠ 32 ∧ head ≠ 33 ∧ head ≠ 34 ∧ head ≠ 35 ∧ head ≠ 40 ∧
      tail ≠ 32 ∧ tail ≠ 33 ∧ tail ≠ 34 ∧ tail ≠ 35 ∧ tail ≠ 40 ∧
      otherHead ≠ 32 ∧ otherHead ≠ 33 ∧ otherHead ≠ 34 ∧ otherHead ≠ 35 ∧
      otherTail ≠ 32 ∧ otherTail ≠ 33 ∧ otherTail ≠ 34 ∧ otherTail ≠ 35 := by omega
  rcases haux with ⟨ha, hb, hc, hd, he, hf, hg, hj, hk, hl, hm, hn, hp, hq, hr, hs, ht', hu'⟩
  rcases hi with ⟨hih, hit, hia, hib, hic, hid, hie⟩
  by_cases h₁ : c.reg head = 0
  · simp [appendInto, seqs, run, Ne.symm hd, Ne.symm hhz, *]
  · by_cases h₂ : c.reg otherHead = 0
    · simp [appendInto, seqs, run, *]
    · simp [appendInto, seqs, run, *]

/-- An append is bounded whenever its possible tail address is bounded. -/
theorem appendInto_addrOK (c : Config) {head tail otherHead otherTail bound : Nat}
    (hh : head < 30) (ht : tail < 30) (hu : otherHead < 30) (hv : otherTail < 30)
    (hhz : head ≠ 0) (htz : tail ≠ 0) (hne : head ≠ tail)
    (hz : c.reg 0 = 0) (ho : c.reg 1 = 1)
    (ha : c.reg head ≠ 0 → c.reg otherHead ≠ 0 →
      c.reg 50 + (c.reg tail - 1) < bound) :
    AddrOK bound (appendInto head tail otherHead otherTail) c := by
  have haux : head ≠ 32 ∧ head ≠ 33 ∧ head ≠ 34 ∧ head ≠ 35 ∧ head ≠ 40 ∧
      tail ≠ 32 ∧ tail ≠ 33 ∧ tail ≠ 34 ∧ tail ≠ 35 ∧ tail ≠ 40 ∧
      otherHead ≠ 32 ∧ otherHead ≠ 33 ∧ otherHead ≠ 34 ∧ otherHead ≠ 35 ∧
      otherTail ≠ 32 ∧ otherTail ≠ 33 ∧ otherTail ≠ 34 ∧ otherTail ≠ 35 := by omega
  rcases haux with ⟨ha', hb, hc, hd, he, hf, hg, hi, hj, hk, hl, hm, hn, hp, hq, hr, hs, ht'⟩
  by_cases h₁ : c.reg head = 0
  · simp [appendInto, seqs, run, Ne.symm hd, Ne.symm hhz, *]
  · by_cases h₂ : c.reg otherHead = 0
    · simp [appendInto, seqs, run, *]
    · simpa [appendInto, seqs, run, *] using ha h₁ h₂

/-- The full-memory update of one linked append. -/
def appendMem (m : Nat → Nat) (base head tail other : Nat) : Nat → Nat :=
  if head = 0 ∨ other = 0 then m else upd m (base + (tail - 1)) other

/-- The raw key of an address-loaded class head. -/
def rawHeadKey (c : Config) (pointer : Nat) : Nat :=
  if pointer = 0 then 0 else c.mem (c.reg 62 + (pointer - 1)) + 1

/-- Only the linked pointer array changes during the append primitive. -/
theorem appendMem_slice (m : Nat → Nat) (base head tail other i : Nat) :
    appendMem m base head tail other (base + i) =
      (if head = 0 ∨ other = 0 then m (base + i)
       else upd (fun a => m (base + a)) (tail - 1) other i) := by
  by_cases h : head = 0 ∨ other = 0 <;> simp [appendMem, upd, h]

/-- Every register outside the documented scratch set is left untouched by a load. -/
theorem loadCell_frame (c : Config) (dst block index i : Nat)
    (hi : i ≠ dst ∧ i ≠ 40) :
    (run (loadCell dst block index) c).reg i = c.reg i := by
  simp [loadCell, seqs, run, hi.1, hi.2]

/-- A cell write has exactly one full-memory update. -/
theorem storeCell_memory (c : Config) (block index src : Nat)
    (hs : src ≠ 40) :
    (run (storeCell block index src) c).mem =
      upd c.mem (c.reg (50 + block) + c.reg index) (c.reg src) := by
  funext i
  simp [storeCell, seqs, run, hs, upd]

/-- Full operational effect of consuming one snapshotted group. -/
theorem consumeGroupProgram_raw (c : Config) (hz : c.reg 0 = 0) (ho : c.reg 1 = 1) :
    let g := c.reg 13 - 1
    let ph := c.mem (c.reg 51 + g)
    let pt := c.mem (c.reg 52 + g)
    let mh := c.mem (c.reg 53 + g)
    let mt := c.mem (c.reg 54 + g)
    let a := appL (fun i => c.mem (c.reg 50 + i)) (c.reg 18) (c.reg 19) ph pt
    let b := appL a.2.2 a.1 a.2.1 mh mt
    let m₁ := appendMem c.mem (c.reg 50) (c.reg 18) (c.reg 19) ph
    let m₂ := appendMem m₁ (c.reg 50) a.1 a.2.1 mh
    let out := run consumeGroupProgram c
    (∀ i, i < 20 → out.reg i =
      if i = 13 then c.mem (c.reg 55 + g)
      else if i = 18 then b.1 else if i = 19 then b.2.1 else c.reg i) ∧
    out.mem = upd (upd m₂ (c.reg 58 + g) (c.reg 9 + 1))
      (c.reg 59 + g) (if ph = 0 then 0 else 1) ∧
    (∀ i, 50 ≤ i → out.reg i = c.reg i) ∧ out.out = c.out := by
  dsimp only
  by_cases hp : c.mem (c.reg 51 + (c.reg 13 - 1)) = 0 <;>
    by_cases hm : c.mem (c.reg 53 + (c.reg 13 - 1)) = 0 <;>
    by_cases hc : c.reg 18 = 0
  all_goals
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      have hin : i ≠ 20 ∧ i ≠ 21 ∧ i ≠ 22 ∧ i ≠ 23 ∧ i ≠ 24 ∧
        i ≠ 28 ∧ i ≠ 29 ∧ i ≠ 30 ∧ i ≠ 32 ∧ i ≠ 33 ∧ i ≠ 34 ∧ i ≠ 35 ∧ i ≠ 40 := by omega
      rcases hin with ⟨ha, hb, hd, he, hf, hg, hh, hi', hj, hk, hl, hm', hn⟩
      by_cases h₁ : i = 13 <;> by_cases h₂ : i = 18 <;> by_cases h₃ : i = 19
      all_goals simp_all [consumeGroupProgram, groupRead, consumeRecord, loadCell, storeCell,
        appendInto, appL, appendMem, run, seqs]
    · funext i
      simp [consumeGroupProgram, groupRead, consumeRecord, loadCell, storeCell,
        appendInto, appL, appendMem, run, seqs, upd, hz, ho, hp, hm, hc]
    · intro i hi
      have hin : i ≠ 13 ∧ i ≠ 18 ∧ i ≠ 19 ∧ i ≠ 20 ∧ i ≠ 21 ∧ i ≠ 22 ∧ i ≠ 23 ∧ i ≠ 24 ∧
        i ≠ 28 ∧ i ≠ 29 ∧ i ≠ 30 ∧ i ≠ 32 ∧ i ≠ 33 ∧ i ≠ 34 ∧ i ≠ 35 ∧ i ≠ 40 := by omega
      rcases hin with ⟨ha, hb, hd, he, hf, hg, hh, hi', hj, hk, hl, hm', hn, hp', hq, hr⟩
      simp [consumeGroupProgram, groupRead, consumeRecord, loadCell, storeCell,
        appendInto, run, seqs, hz, ho, hp, hm, hc, *]
    · simp [consumeGroupProgram, groupRead, consumeRecord, loadCell, storeCell,
        appendInto, run, seqs, hz, ho, hp, hm, hc]

/-- Full operational effect of finishing a merge. -/
theorem finishMergeProgram_raw (c : Config) (hz : c.reg 0 = 0) (ho : c.reg 1 = 1) :
    let y := appL (fun i => c.mem (c.reg 50 + i)) (c.reg 18) (c.reg 19)
      (c.reg 16) (c.reg 17)
    let m₀ := appendMem c.mem (c.reg 50) (c.reg 18) (c.reg 19) (c.reg 16)
    let m₁ := upd m₀ (c.reg 51 + c.reg 9) (c.reg 14)
    let m₂ := upd m₁ (c.reg 52 + c.reg 9) (c.reg 15)
    let m₃ := upd m₂ (c.reg 53 + c.reg 9) y.1
    let m₄ := upd m₃ (c.reg 54 + c.reg 9) y.2.1
    let m₅ := upd m₄ (c.reg 55 + c.reg 9) (c.reg 12)
    let m₆ := upd m₅ (c.reg 56 + c.reg 8) (c.reg 9 + 1)
    let m₇ := upd m₆ (c.reg 57 + c.reg 8) (c.reg 11)
    let out := run finishMergeProgram c
    (∀ i, i < 20 → out.reg i = if i = 7 then 0 else c.reg i) ∧
    out.mem = m₇ ∧ (∀ i, 50 ≤ i → out.reg i = c.reg i) ∧ out.out = c.out := by
  dsimp only
  by_cases hc : c.reg 18 = 0 <;> by_cases hb : c.reg 16 = 0
  all_goals
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      have hin : i ≠ 21 ∧ i ≠ 22 ∧ i ≠ 29 ∧ i ≠ 32 ∧ i ≠ 33 ∧
        i ≠ 34 ∧ i ≠ 35 ∧ i ≠ 40 := by omega
      rcases hin with ⟨ha, hd, he, hf, hg, hh, hi', hj⟩
      simp [finishMergeProgram, loadCell, storeCell, appendInto, appL, appendMem,
        run, seqs, hz, ho, hc, hb, *]
    · funext i
      simp [finishMergeProgram, loadCell, storeCell, appendInto, appL, appendMem,
        run, seqs, upd, hz, ho, hc, hb]
    · intro i hi
      have hin : i ≠ 7 ∧ i ≠ 21 ∧ i ≠ 22 ∧ i ≠ 29 ∧ i ≠ 32 ∧ i ≠ 33 ∧
        i ≠ 34 ∧ i ≠ 35 ∧ i ≠ 40 := by omega
      rcases hin with ⟨ha, hb', hd, he, hf, hg, hh, hi', hj⟩
      simp [finishMergeProgram, loadCell, storeCell, appendInto, run, seqs, hz, ho, hc, hb, *]
    · simp [finishMergeProgram, loadCell, storeCell, appendInto, run, seqs, hz, ho, hc, hb]

/-- Disjoint fixed-width blocks reduce an address equality to index equality. -/
theorem Layout.cell_eq_iff {L : Layout} {j k i a : Nat}
    (hi : i < L.width) (ha : a < L.width) :
    L.cell j i = L.cell k a ↔ j = k ∧ i = a := by
  constructor
  · exact L.cell_injective hi ha
  · rintro ⟨rfl, rfl⟩; rfl

/-- A single write changes only the selected array block and index. -/
theorem update_cell (L : Layout) (m : Nat → Nat) (j k i a value : Nat)
    (hi : i < L.width) (ha : a < L.width) :
    upd m (L.cell k a) value (L.cell j i) =
      if j = k ∧ i = a then value else m (L.cell j i) := by
  simp [upd, L.cell_eq_iff hi ha]

/-- Pointer and tail bounds needed by an actual solver RAM step. -/
structure StepBounds (L : Layout) (s : SMS) (dartBound : Nat) : Prop where
  width : 0 < L.width
  group : s.G < L.width
  node : s.v < L.width
  upper : s.rxp ≤ L.width
  lower : s.ryp ≤ L.width
  positive : s.at' ≤ L.width
  negative : s.bt ≤ L.width
  lowerClass : s.ct ≤ L.width
  positiveHeads : ∀ g, g < L.width → s.m.ph g ≤ dartBound
  negativeHeads : ∀ g, g < L.width → s.m.mh g ≤ dartBound
  positiveTails : ∀ g, g < L.width → s.m.pt g ≤ L.width
  negativeTails : ∀ g, g < L.width → s.m.mt g ≤ L.width

/-- Appending cannot change a foreign block in the solver layout. -/
theorem appendMem_foreign (L : Layout) (m : Nat → Nat) (head tail other j i : Nat)
    (ht : tail ≤ L.width) (hw : 0 < L.width) (hi : i < L.width) (hj : j ≠ 0) :
    appendMem m (L.block 0) head tail other (L.cell j i) = m (L.cell j i) := by
  by_cases h : head = 0 ∨ other = 0
  · simp [appendMem, h]
  · have ha : tail - 1 < L.width := by omega
    have hn : L.cell j i ≠ L.block 0 + (tail - 1) := by
      intro he
      have := L.cell_injective hi ha (show L.cell j i = L.cell 0 (tail - 1) from he)
      exact hj this.1
    simp [appendMem, h, upd, hn]

/-- The linked block of a full-memory append agrees with `appL`. -/
theorem appendMem_linked (L : Layout) (m : Nat → Nat) (head tail other otherTail i : Nat) :
    appendMem m (L.block 0) head tail other (L.cell 0 i) =
      (appL (fun a => m (L.cell 0 a)) head tail other otherTail).2.2 i := by
  by_cases hh : head = 0 <;> by_cases hu : other = 0 <;>
    simp [appendMem, appL, Layout.cell, upd, hh, hu]

@[simp] theorem appL_head (nx : Nat → Nat) (h t u v : Nat) :
    (appL nx h t u v).1 = if h = 0 then u else h := by
  by_cases hh : h = 0 <;> by_cases hu : u = 0 <;> simp [appL, hh, hu]

@[simp] theorem appL_tail (nx : Nat → Nat) (h t u v : Nat) :
    (appL nx h t u v).2.1 = if h = 0 then v else if u = 0 then t else v := by
  by_cases hh : h = 0 <;> by_cases hu : u = 0 <;> simp [appL, hh, hu]

/-- Finite linked blocks suffice to refine an append. -/
theorem appendMem_rep (L : Layout) (m nx : Nat → Nat) (h t u v i : Nat)
    (ht : t ≤ L.width) (hw : 0 < L.width) (hi : i < L.width)
    (hm : ∀ a, a < L.width → m (L.cell 0 a) = nx a) :
    appendMem m (L.block 0) h t u (L.cell 0 i) = (appL nx h t u v).2.2 i := by
  have ha : t - 1 < L.width := by omega
  have hm' : m (L.block 0 + i) = nx i := hm i hi
  by_cases hh : h = 0 <;> by_cases hu : u = 0 <;>
    simp [appendMem, appL, Layout.cell, upd, hh, hu, hm']

end STACS2027.Embed.RAMSolver
