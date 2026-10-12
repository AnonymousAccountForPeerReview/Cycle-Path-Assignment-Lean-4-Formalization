module

public import ApproximationHardness.Embed.SolverLoop
public import ApproximationHardness.Embed.SolverRecords
public import ApproximationHardness.Embed.SolverBits
public import ApproximationHardness.Embed.SolverMstepRAM

/-! # Uniform RAM execution of the complete linked embedding solver -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

/-- The preserved input register contains the number of directed darts, twice the edge count. -/
def solverBudgetProgram : Stmt := seqs [.add 80 140 140, .add 81 80 80,
  .add 81 81 81, .add 80 81 80]

def solverProgram : Stmt := .seq solverBudgetProgram solverLoop

theorem solverBudgetProgram_raw (c : Config) :
    (run solverBudgetProgram c).reg 80 = 10 * c.reg 140 ∧
      (∀ r, r ≠ 80 → r ≠ 81 → (run solverBudgetProgram c).reg r = c.reg r) ∧
      (run solverBudgetProgram c).mem = c.mem ∧ (run solverBudgetProgram c).out = c.out := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · simp [solverBudgetProgram, seqs, run]; omega
  · intro r hr hs; simp [solverBudgetProgram, seqs, run, hr, hs]

theorem solverBudgetProgram_rep {L : Layout} {c : Config} {s : SMS} {S : Sol}
    {post : List Nat} {vertices darts : Nat}
    (hr : Rep L c s) (ht : Tables L c S post vertices darts) :
    Rep L (run solverBudgetProgram c) s ∧
      Tables L (run solverBudgetProgram c) S post vertices darts := by
  have H := (solverBudgetProgram_raw c).2
  have Hbase : Bases L (run solverBudgetProgram c) := by
    rcases hr.bases with ⟨hz, ho, hb, hw, hblocks⟩
    refine ⟨(H.1 0 (by decide) (by decide)).trans hz,
      (H.1 1 (by decide) (by decide)).trans ho,
      (H.1 2 (by decide) (by decide)).trans hb,
      (H.1 3 (by decide) (by decide)).trans hw, ?_⟩
    intro j hj; rw [H.1 (50 + j) (by omega) (by omega)]; exact hblocks j hj
  have Hr : Rep L (run solverBudgetProgram c) s := by
    refine ⟨Hbase, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [H.2.1]; exact hr.arrays
    all_goals rw [H.1 _ (by decide) (by decide)]
    all_goals first | exact hr.index | exact hr.mode | exact hr.node | exact hr.group |
      exact hr.upperLow | exact hr.resultLow | exact hr.upperHead | exact hr.lowerHead |
      exact hr.positiveHead | exact hr.positiveTail | exact hr.negativeHead |
      exact hr.negativeTail | exact hr.lowerClassHead | exact hr.lowerClassTail
  refine ⟨Hr, ht.frame (H.1 4 (by decide) (by decide))
    (H.1 5 (by decide) (by decide)) ?_⟩
  rw [H.2.1]; exact TableMemEq.refl _ _

theorem solverBudgetProgram_exec (bound : Nat) (c : Config) :
    ExecB bound solverBudgetProgram c 5 (run solverBudgetProgram c) := by
  have Hl : LoopFree solverBudgetProgram := by simp [solverBudgetProgram, LoopFree, seqs]
  have Ha : AddrOK bound solverBudgetProgram c := AddrOK.of_memFree (by decide)
  simpa [solverBudgetProgram, RAM.cost, seqs] using execB_run solverBudgetProgram Hl c Ha

/-- The actual uniform program supplies the complete records and the Boolean instructions. -/
theorem solverProgram_refines {L : Layout} {F : ForestData} (hF : F.Valid)
    {post : List Nat} {vertices darts : Nat}
    {sides : Nat → Bool}
    (hfork : ∀ v p q, (F.sol hF).P.IsFork (F.sol hF).α (F.sol hF).key v p q →
      (F.sol hF).P.ForkOK (F.sol hF).α (F.sol hF).key sides p q)
    (hpost : F.PostOrder hF post) (init : SMS) (c : Config)
    (hr : Rep L c init) (ht : Tables L c (F.sol hF) post vertices darts)
    (hb : StateBounds L init darts) (hm : init.mode = 0) (hk : init.k = 0)
    (hzero : ∀ g, init.m.gp g = 0) (hedges : c.reg 140 = 2 * F.E) :
    let final := (F.sol hF).runPrefix post init post.length
    ∃ t c', ExecB L.limit solverProgram c t c' ∧ t ≤ 40040 * F.E + 6 ∧
      Rep L c' final ∧ Tables L c' (F.sol hF) post vertices darts ∧
      ForestData.Records F hF final.m.gp final.m.gf ∧
      (∀ v ∈ post, ∀ o, final.m.evalBit (F.sol hF).gid o v = (F.sol hF).bit o v) ∧
      c'.out = c.out ∧ (∀ r, 81 < r → c'.reg r = c.reg r) ∧
      (∀ a, L.limit ≤ a → c'.mem a = c.mem a) := by
  let d := run solverBudgetProgram c
  obtain ⟨Hdr, Hdt⟩ := solverBudgetProgram_rep hr ht
  have Hbudget : d.reg 80 = 20 * F.E := by
    rw [(solverBudgetProgram_raw c).1, hedges]; omega
  obtain ⟨t, c', He, Ht, Hr, Htb, Hout, Hreg, Hmem⟩ :=
    solverLoop_refines (fun _ _ hr ht hb hk => mstepProgram_simulation hr ht hb hk)
      (20 * F.E) init d Hdr Hdt hb (by omega) Hbudget
  rw [ForestData.solver_fixedBudget hF hfork hpost init hm hk] at Hr
  refine ⟨5 + t, c', .seq (solverBudgetProgram_exec L.limit c) He, by omega, Hr, Htb,
    ForestData.solver_records hF hfork hpost init hm hk hzero, ?_, ?_, ?_, ?_⟩
  · intro v hv o
    have H := (F.sol hF).runPrefix_bits (ForestData.tree hF) (ForestData.good hF)
      hfork hpost.solver init hm hk post.length (Nat.le_refl _) v
      (by simpa only [List.take_length] using hv) o
    exact H
  · exact Hout.trans (solverBudgetProgram_raw c).2.2.2
  · intro r hrr; rw [Hreg r (by omega)]
    exact (solverBudgetProgram_raw c).2.1 r (by omega) (by omega)
  · intro a ha; exact (Hmem a ha).trans (congrFun (solverBudgetProgram_raw c).2.2.1 a)

end STACS2027.Embed.RAMSolver
