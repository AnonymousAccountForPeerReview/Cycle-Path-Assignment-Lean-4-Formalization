module

public import ApproximationHardness.Embed.PlanHeader
public import ApproximationHardness.Embed.PlanItemRAM
public import ApproximationHardness.Embed.SolverTempRAM
import Lean.Elab.Tactic.Omega

/-! Finite stores and preserved forest caches during plan compilation. -/

@[expose] public section

namespace STACS2027.Embed.PlanRAM

open RAM

attribute [local simp] zBase vertex degree vertexParent dart opposite child childParent
  itemType itemValue distinguished vertexBound partCount topVertex remaining slot
  address test otherTest

/-- Write one solver-plan cell without using the solver's live scratch registers. -/
def planStore (block index src : Nat) : Stmt := seqs [
  .add address (50 + block) index, .store address src]

/-- Write one distinguished-dart cache entry. -/
def zStore (index src : Nat) : Stmt := seqs [.add address zBase index, .store address src]

/-- Exact memory effect and register frame of a plan-table store. -/
theorem planStore_raw (c : Config) (block index src : Nat) (hs : src ≠ address) :
    (run (planStore block index src) c).mem =
      upd c.mem (c.reg (50 + block) + c.reg index) (c.reg src) ∧
    (∀ r, r ≠ address → (run (planStore block index src) c).reg r = c.reg r) ∧
    (run (planStore block index src) c).out = c.out := by
  refine ⟨?_, ?_, ?_⟩
  · funext a; simp [planStore, seqs, run, Config.setMem, upd, hs]
  · intro r hr; simp [planStore, seqs, run, hr]
  · simp [planStore, seqs, run]

/-- Exact memory effect and register frame of a distinguished-dart store. -/
theorem zStore_raw (c : Config) (index src : Nat) (hs : src ≠ address) :
    (run (zStore index src) c).mem = upd c.mem (c.reg zBase + c.reg index) (c.reg src) ∧
    (∀ r, r ≠ address → (run (zStore index src) c).reg r = c.reg r) ∧
    (run (zStore index src) c).out = c.out := by
  refine ⟨?_, ?_, ?_⟩
  · funext a; simp [zStore, seqs, run, Config.setMem, upd, hs]
  · intro r hr; simp [zStore, seqs, run, hr]
  · simp [zStore, seqs, run]

/-- The immutable forest and installed solver layout used throughout plan construction. -/
structure Context (L : DFSRAM.Layout) (G : DG) (s : DS) (c : Config) : Prop where
  forest : DFSRAM.Rep L G c s
  tables : DFSRAM.Tables L G c
  solver : RAMSolver.Bases (solverLayout L) c
  zbase : c.reg zBase = (solverLayout L).limit
  postCapacity : s.post.length ≤ L.width
  dartCapacity : 2 * G.E ≤ L.width
  postLength : c.reg 4 = s.post.length
  infinity : c.reg 5 = s.H + 2

/-- A scratch-register update preserves the complete compilation context. -/
theorem Context.temp {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (r value : Nat) (hr : 281 ≤ r) :
    Context L G s (c.setReg r value) := by
  have hf (i : Nat) (hi : i < 281) : (c.setReg r value).reg i = c.reg i := by simp [show i ≠ r by omega]
  have hb : DFSRAM.Bases L G (c.setReg r value) := hc.forest.bases.frame (by
    intro i hi; simp only [DFSRAM.dartCount, DFSRAM.baseRegister, DFSRAM.widthRegister] at hi
    apply hf; rcases hi with hi | hi | hi | hi | hi | hi <;> omega)
  have hfr : DFSRAM.Rep L G (c.setReg r value) s := by
    refine hc.forest.memory.of_regs rfl hb ?_ ?_ ?_ ?_ ?_
    · exact (hf _ (by decide)).trans hc.forest.scan
    · exact (hf _ (by decide)).trans hc.forest.current
    · exact (hf _ (by decide)).trans hc.forest.inner
    · exact (hf _ (by decide)).trans hc.forest.height
    · exact (hf _ (by decide)).trans hc.forest.postLength
  have hbs : RAMSolver.Bases (solverLayout L) (c.setReg r value) := by
    rcases hc.solver with ⟨hz, ho, hb, hw, hblocks⟩
    refine ⟨(hf _ (by decide)).trans hz, (hf _ (by decide)).trans ho,
      (hf _ (by decide)).trans hb, (hf _ (by decide)).trans hw, ?_⟩
    intro j hj; exact (hf _ (by omega)).trans (hblocks j hj)
  exact ⟨hfr, hc.tables.mem_congr rfl, hbs, (hf _ (by decide)).trans hc.zbase,
    hc.postCapacity, hc.dartCapacity, (hf _ (by decide)).trans hc.postLength, (hf _ (by decide)).trans hc.infinity⟩

/-- Read-only code in the plan scratch interval preserves every installed cache and scalar. -/
theorem Context.readOnly {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config} {p : Stmt}
    (hc : Context L G s c) (hm : hasStore p = false)
    (hw : ∀ r, r ∈ regsW p → 281 ≤ r) : Context L G s (run p c) := by
  have hf (i : Nat) (hi : i < 281) : (run p c).reg i = c.reg i := by
    apply run_reg_frame; intro hn; have := hw i hn; omega
  have hmem := run_mem_frame p c hm
  have hb : DFSRAM.Bases L G (run p c) := hc.forest.bases.frame (by
    intro i hi; simp only [DFSRAM.dartCount, DFSRAM.baseRegister, DFSRAM.widthRegister] at hi
    apply hf; rcases hi with hi | hi | hi | hi | hi | hi <;> omega)
  have hfr : DFSRAM.Rep L G (run p c) s := by
    refine hc.forest.memory.of_regs hmem hb ?_ ?_ ?_ ?_ ?_
    · exact (hf _ (by decide)).trans hc.forest.scan
    · exact (hf _ (by decide)).trans hc.forest.current
    · exact (hf _ (by decide)).trans hc.forest.inner
    · exact (hf _ (by decide)).trans hc.forest.height
    · exact (hf _ (by decide)).trans hc.forest.postLength
  have hbs : RAMSolver.Bases (solverLayout L) (run p c) := by
    rcases hc.solver with ⟨hz, ho, hb, hw, hblocks⟩
    refine ⟨(hf _ (by decide)).trans hz, (hf _ (by decide)).trans ho,
      (hf _ (by decide)).trans hb, (hf _ (by decide)).trans hw, ?_⟩
    intro j hj; exact (hf _ (by omega)).trans (hblocks j hj)
  exact ⟨hfr, hc.tables.mem_congr hmem, hbs, (hf _ (by decide)).trans hc.zbase,
    hc.postCapacity, hc.dartCapacity, (hf _ (by decide)).trans hc.postLength, (hf _ (by decide)).trans hc.infinity⟩

/-- Any memory write after the forest layout preserves its complete cached state. -/
theorem Context.memory {L : DFSRAM.Layout} {G : DG} {s : DS} {c d : Config}
    (hc : Context L G s c) (hr : ∀ r, r < 281 → d.reg r = c.reg r)
    (hm : ∀ a, a < L.limit → d.mem a = c.mem a) : Context L G s d := by
  have hb : DFSRAM.Bases L G d := hc.forest.bases.frame (by
    intro i hi; simp only [DFSRAM.dartCount, DFSRAM.baseRegister, DFSRAM.widthRegister] at hi
    apply hr; rcases hi with hi | hi | hi | hi | hi | hi <;> omega)
  have hcell (j i : Nat) (hj : j < 11) (hi : i < 2 * G.E) : d.mem (L.cell j i) = c.mem (L.cell j i) :=
    hm _ (DFSRAM.Layout.cell_lt hj (hi.trans_le hc.dartCapacity))
  have hfr : DFSRAM.Rep L G d s := by
    refine ⟨hb, (hr _ (by decide)).trans hc.forest.scan, (hr _ (by decide)).trans hc.forest.current,
      (hr _ (by decide)).trans hc.forest.inner, (hr _ (by decide)).trans hc.forest.height,
      (hr _ (by decide)).trans hc.forest.postLength, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi; exact (hcell 6 i (by decide) hi).trans (hc.forest.parents i hi)
    · intro i hi; exact (hcell 7 i (by decide) hi).trans (hc.forest.depths i hi)
    · intro i hi; exact (hcell 8 i (by decide) hi).trans (hc.forest.pointers i hi)
    · intro i hi; exact (hcell 9 i (by decide) hi).trans (hc.forest.states i hi)
    · intro i hi; exact (hm _ (DFSRAM.Layout.cell_lt (by decide) (hi.trans_le hc.postCapacity))).trans (hc.forest.post i hi)
  have ht : DFSRAM.Tables L G d := by
    constructor
    · intro i hi; exact (hcell 0 i (by decide) hi).trans (hc.tables.representatives i hi)
    · intro i hi; exact (hcell 1 i (by decide) hi).trans (hc.tables.partners i hi)
    · intro i hi; exact (hcell 2 i (by decide) hi).trans (hc.tables.degrees i hi)
    · intro k hk i hi; exact (hcell (3+k) i (by omega) hi).trans (hc.tables.adjacent k hk i hi)
  have hbs : RAMSolver.Bases (solverLayout L) d := by
    rcases hc.solver with ⟨hz, ho, hb, hw, hblocks⟩
    refine ⟨(hr _ (by decide)).trans hz, (hr _ (by decide)).trans ho,
      (hr _ (by decide)).trans hb, (hr _ (by decide)).trans hw, ?_⟩
    intro j hj; exact (hr _ (by omega)).trans (hblocks j hj)
  exact ⟨hfr, ht, hbs, (hr _ (by decide)).trans hc.zbase, hc.postCapacity, hc.dartCapacity,
    (hr _ (by decide)).trans hc.postLength, (hr _ (by decide)).trans hc.infinity⟩

/-- A plan-table store preserves the full DFS cache and compilation metadata. -/
theorem Context.planStore {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (j index src : Nat) (hj : j < 22) (hs : src ≠ address) :
    Context L G s (run (planStore j index src) c) := by
  obtain ⟨hm, hf, _⟩ := planStore_raw c j index src hs
  apply hc.memory (fun r hr => hf r (by simp only [address]; omega))
  intro a ha
  rw [hm]
  have hlo : L.limit ≤ c.reg (50+j) + c.reg index := by
    rw [hc.solver.2.2.2.2 j hj]
    dsimp [solverLayout, RAMSolver.Layout.block]
    omega
  simp [upd, show a ≠ c.reg (50+j) + c.reg index by omega]


/-- A distinguished-dart store preserves all cached forest fields and metadata. -/
theorem Context.zStore {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (index src : Nat) (hs : src ≠ address) :
    Context L G s (run (zStore index src) c) := by
  obtain ⟨hm, hf, _⟩ := zStore_raw c index src hs
  apply hc.memory (fun r hr => hf r (by simp only [address]; omega))
  intro a ha
  rw [hm, hc.zbase]
  have hlo : L.limit ≤ (solverLayout L).limit + c.reg index := by
    dsimp [solverLayout, RAMSolver.Layout.limit]; omega
  simp [upd, show a ≠ (solverLayout L).limit + c.reg index by omega]

/-- A plan-cell store is an actual bounded instruction in the combined layout. -/
theorem planStore_exec {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (j index src : Nat) (hj : j < 22) (hi : c.reg index < L.width) :
    ∃ t, ExecB (zLimit L) (planStore j index src) c t (run (planStore j index src) c) ∧ t ≤ 4 := by
  have ha : c.reg (50+j) + c.reg index < zLimit L := by
    rw [hc.solver.2.2.2.2 j hj]
    have hcell := (solverLayout L).cell_lt hj hi
    dsimp only [RAMSolver.Layout.cell] at hcell
    dsimp [zLimit]
    omega
  have hlp : LoopFree (planStore j index src) := by simp [planStore, seqs, LoopFree]
  have haddr : AddrOK (zLimit L) (planStore j index src) c := by simp [planStore, seqs, AddrOK, run, ha]
  have hsize : size (planStore j index src) ≤ 4 := by simp [planStore, seqs, size]
  exact ⟨_, execB_run _ hlp c haddr, (cost_le_size _ _).trans hsize⟩

/-- Distinguished-dart stores stay inside the additional width-sized block. -/
theorem zStore_exec {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (index src : Nat) (hi : c.reg index < L.width) :
    ∃ t, ExecB (zLimit L) (zStore index src) c t (run (zStore index src) c) ∧ t ≤ 4 := by
  have ha : c.reg zBase + c.reg index < zLimit L := by rw [hc.zbase]; dsimp [zLimit]; omega
  have hlp : LoopFree (zStore index src) := by simp [zStore, seqs, LoopFree]
  have haddr : AddrOK (zLimit L) (zStore index src) c := by simp [zStore, seqs, AddrOK, run, ha]
  have hsize : size (zStore index src) ≤ 4 := by simp [zStore, seqs, size]
  exact ⟨_, execB_run _ hlp c haddr, (cost_le_size _ _).trans hsize⟩

/-- The mutable solver arrays are zero before its own execution starts. -/
def MutableZero (L : DFSRAM.Layout) (c : Config) : Prop :=
  ∀ j, j < 12 → ∀ i, i < L.width → c.mem ((solverLayout L).cell j i) = 0

/-- Plan-table writes preserve the solver's initially zero mutable arrays. -/
theorem MutableZero.planStore {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hz : MutableZero L c) (hc : Context L G s c) (j index src : Nat)
    (hlo : 12 ≤ j) (hj : j < 22) (hi : c.reg index < L.width) (hs : src ≠ address) :
    MutableZero L (run (planStore j index src) c) := by
  intro k hk i hindex
  rw [(planStore_raw c j index src hs).1, hc.solver.2.2.2.2 j hj]
  change upd c.mem ((solverLayout L).cell j (c.reg index)) (c.reg src) ((solverLayout L).cell k i) = 0
  rw [RAMSolver.update_cell (solverLayout L) _ k j i (c.reg index) _ hindex hi]
  simp only [show ¬ (k = j ∧ i = c.reg index) by omega, ↓reduceIte]
  exact hz k hk i hindex

/-- Distinguished-cache writes also preserve all initially zero mutable solver arrays. -/
theorem MutableZero.zStore {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hz : MutableZero L c) (hc : Context L G s c) (index src : Nat) (hs : src ≠ address) :
    MutableZero L (run (zStore index src) c) := by
  intro k hk i hi
  rw [(zStore_raw c index src hs).1, hc.zbase]
  have hlt := (solverLayout L).cell_lt (by omega : k < 22) hi
  simp only [upd, show (solverLayout L).cell k i ≠ (solverLayout L).limit + c.reg index by omega, ↓reduceIte]
  exact hz k hk i hi


/-- A cached forest-cell read preserves the full plan-compilation context. -/
theorem Context.readForest {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (dst block index : Nat) (hdst : 281 ≤ dst) :
    Context L G s (run (readForest dst block index) c) := by
  apply hc.readOnly (p := PlanRAM.readForest dst block index) (by simp [PlanRAM.readForest, seqs, hasStore])
  intro r hn
  simp [PlanRAM.readForest, seqs, regsW] at hn
  rcases hn with hn | hn <;> omega

/-- Decoding a dart into its plan item preserves every cached forest field. -/
theorem Context.cachedItem {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) : Context L G s (run cachedItem c) := by
  apply hc.readOnly (p := PlanRAM.cachedItem) (by decide)
  intro r hn
  simp [PlanRAM.cachedItem, PlanRAM.readForest, seqs, regsW] at hn
  omega

end STACS2027.Embed.PlanRAM
