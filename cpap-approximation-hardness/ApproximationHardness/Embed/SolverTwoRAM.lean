module

public import ApproximationHardness.Embed.SolverForkSimulation
public import ApproximationHardness.Embed.SolverTargetRAM
public import ApproximationHardness.Embed.SolverTempRAM
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Actual two-part dispatch between target closing and linked forks. -/

@[expose] public section

set_option maxHeartbeats 1500000

namespace STACS2027.Embed.RAMSolver

open RAM

/-- The four formula cells read before choosing the two-part branch. -/
def twoReadProgram : Stmt := seqs [loadCell 22 17 20, loadCell 23 18 20,
  loadCell 26 19 20, loadCell 27 20 20]

/-- Dispatch on the represented kinds and target bit. -/
def twoBranchProgram : Stmt := .ifz 22
    (.ifz 26 forkNodeProgram
      (seqs [loadCell 28 14 27, .ifz 28 forkNodeProgram
        (seqs [.add 21 23 0, .add 23 27 0, .const 34 1, targetNodeProgram])]))
    (.ifz 26
      (seqs [loadCell 28 14 23, .ifz 28 forkNodeProgram
        (seqs [.add 21 27 0, .const 34 2, targetNodeProgram])])
      forkNodeProgram)

/-- The branch's fork case inherits the checked item results and finite address bounds. -/
theorem forkBranch_rep_addr {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertices darts v : Nat} (hr : Rep L c s) (ht : Tables L c S post vertices darts)
    (p q : Item) (hp : match p with | .node w => w < vertices | .dart e => e < darts)
    (hq : match q with | .node w => w < vertices | .dart e => e < darts)
    (hv : v < vertices) (hnode : c.reg 20 = v)
    (hpt : c.reg 22 = itemType p) (hpv : c.reg 23 = itemValue p)
    (hqt : c.reg 26 = itemType q) (hqv : c.reg 27 = itemValue q)
    (hnt : S.tgtOf p q = none) :
    Rep L (run forkNodeProgram c) (S.twoStep s v p q) ∧
    Tables L (run forkNodeProgram c) S post vertices darts ∧ AddrOK L.limit forkNodeProgram c := by
  obtain ⟨hr', ht'⟩ := forkNodeProgram_rep hr ht p q hp hq hv hnode hpt hpv hqt hqv hnt
  exact ⟨hr', ht', forkNodeProgram_addrOK hr ht p q hp hq hv hnode hpt hpv hqt hqv⟩

/-- Target preparation with a node on the left refines the semantic target branch. -/
theorem leftTarget_rep_addr {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertices darts v w d : Nat} (hr : Rep L c s) (ht : Tables L c S post vertices darts)
    (hb : MemoryBounds s.m L.width darts) (hv : v < vertices) (hw : w < vertices) (hd : d < darts)
    (hnode : c.reg 20 = v) (hpv : c.reg 23 = w) (hqv : c.reg 27 = d) (hin : S.isIn d) :
    let p := seqs [.add 21 23 0, .add 23 27 0, .const 34 1, targetNodeProgram]
    Rep L (run p c) (S.twoStep s v (.node w) (.dart d)) ∧
    Tables L (run p c) S post vertices darts ∧ AddrOK L.limit p c := by
  let c₁ := c.setReg 21 (c.reg 23 + c.reg 0)
  let c₂ := c₁.setReg 23 (c₁.reg 27 + c₁.reg 0)
  let c₃ := c₂.setReg 34 1
  have hr₃ := ((hr.temp 21 (c.reg 23 + c.reg 0) (by decide) (by decide)).temp
    23 (c₁.reg 27 + c₁.reg 0) (by decide) (by decide)).temp 34 1 (by decide) (by decide)
  have ht₃ := ((ht.temp 21 (c.reg 23 + c.reg 0) (by decide)).temp
    23 (c₁.reg 27 + c₁.reg 0) (by decide)).temp 34 1 (by decide)
  have hn₃ : c₃.reg 20 = v := by simp [c₃, c₂, c₁, hnode]
  have hw₃ : c₃.reg 21 = w := by simp [c₃, c₂, c₁, hpv, hr.bases.1]
  have hd₃ : c₃.reg 23 = d := by simp [c₃, c₂, c₁, hqv, hr.bases.1]
  obtain ⟨hr', ht'⟩ := targetNodeProgram_rep (code := 1) hr₃ ht₃ hb hv hw hd hn₃ hw₃ hd₃ (by simp [c₃])
  obtain ⟨t, he, _⟩ := targetNodeProgram_exec hr₃ ht₃ hb hv hw hd hn₃ hw₃ hd₃
  have hlp : LoopFree targetNodeProgram := by
    simp [targetNodeProgram, closeResultProgram, closePositiveProgram, closeNegativeProgram,
      loadCell, storeCell, LoopFree, seqs]
  have ha := (boundedRun_addr he hlp).2
  have hr'' : Rep L (run targetNodeProgram c₃) (S.twoStep s v (.node w) (.dart d)) := by
    simpa only [Sol.twoStep, Sol.tgtOf, if_pos hin, Sol.tcode] using hr'
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simpa only [run_seqs_cons, run_seqs_nil, run, c₁, c₂, c₃] using hr''
  · simpa only [run_seqs_cons, run_seqs_nil, run, c₁, c₂, c₃] using ht'
  · simpa only [addrOK_seqs_cons, addrOK_seqs_nil, AddrOK, run, and_true, true_and, c₁, c₂, c₃] using ha

/-- Target preparation with a dart on the left refines the semantic target branch. -/
theorem rightTarget_rep_addr {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertices darts v w d : Nat} (hr : Rep L c s) (ht : Tables L c S post vertices darts)
    (hb : MemoryBounds s.m L.width darts) (hv : v < vertices) (hw : w < vertices) (hd : d < darts)
    (hnode : c.reg 20 = v) (hpv : c.reg 23 = d) (hqv : c.reg 27 = w) (hin : S.isIn d) :
    let p := seqs [.add 21 27 0, .const 34 2, targetNodeProgram]
    Rep L (run p c) (S.twoStep s v (.dart d) (.node w)) ∧
    Tables L (run p c) S post vertices darts ∧ AddrOK L.limit p c := by
  let c₁ := c.setReg 21 (c.reg 27 + c.reg 0)
  let c₂ := c₁.setReg 34 2
  have hr₂ := (hr.temp 21 (c.reg 27 + c.reg 0) (by decide) (by decide)).temp 34 2 (by decide) (by decide)
  have ht₂ := (ht.temp 21 (c.reg 27 + c.reg 0) (by decide)).temp 34 2 (by decide)
  have hn₂ : c₂.reg 20 = v := by simp [c₂, c₁, hnode]
  have hw₂ : c₂.reg 21 = w := by simp [c₂, c₁, hqv, hr.bases.1]
  have hd₂ : c₂.reg 23 = d := by simp [c₂, c₁, hpv]
  obtain ⟨hr', ht'⟩ := targetNodeProgram_rep (code := 2) hr₂ ht₂ hb hv hw hd hn₂ hw₂ hd₂ (by simp [c₂])
  obtain ⟨t, he, _⟩ := targetNodeProgram_exec hr₂ ht₂ hb hv hw hd hn₂ hw₂ hd₂
  have hlp : LoopFree targetNodeProgram := by
    simp [targetNodeProgram, closeResultProgram, closePositiveProgram, closeNegativeProgram,
      loadCell, storeCell, LoopFree, seqs]
  have ha := (boundedRun_addr he hlp).2
  have hr'' : Rep L (run targetNodeProgram c₂) (S.twoStep s v (.dart d) (.node w)) := by
    simpa only [Sol.twoStep, Sol.tgtOf, if_pos hin, Sol.tcode] using hr'
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simpa only [run_seqs_cons, run_seqs_nil, run, c₁, c₂] using hr''
  · simpa only [run_seqs_cons, run_seqs_nil, run, c₁, c₂] using ht'
  · simpa only [addrOK_seqs_cons, addrOK_seqs_nil, AddrOK, run, and_true, true_and, c₁, c₂] using ha


/-- Select the operational two-part branch from the formula's actual kinds and target bit. -/
theorem twoBranchProgram_rep_addr {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertices darts v : Nat} (hr : Rep L c s) (ht : Tables L c S post vertices darts)
    (hb : MemoryBounds s.m L.width darts)
    (p q : Item) (hp : match p with | .node w => w < vertices | .dart e => e < darts)
    (hq : match q with | .node w => w < vertices | .dart e => e < darts)
    (hv : v < vertices) (hnode : c.reg 20 = v)
    (hpt : c.reg 22 = itemType p) (hpv : c.reg 23 = itemValue p)
    (hqt : c.reg 26 = itemType q) (hqv : c.reg 27 = itemValue q) :
    Rep L (run twoBranchProgram c) (S.twoStep s v p q) ∧
    Tables L (run twoBranchProgram c) S post vertices darts ∧ AddrOK L.limit twoBranchProgram c := by
  cases p with
  | node w =>
    cases q with
    | node z =>
      have hs := forkBranch_rep_addr hr ht (.node w) (.node z) hp hq hv hnode hpt hpv hqt hqv (by rfl)
      simpa [twoBranchProgram, run, AddrOK, hpt, hqt, itemType] using hs
    | dart d =>
      simp only [itemType, itemValue] at hpt hpv hqt hqv
      let c₁ := run (loadCell 28 14 27) c
      have hr₁ := hr.loadTemp 28 14 27 (by decide) (by decide)
      have ht₁ := ht.loadTemp 28 14 27 (by decide)
      have hn₁ : c₁.reg 20 = v := (loadCell_frame c 28 14 27 20 (by decide)).trans hnode
      have hpv₁ : c₁.reg 23 = w := (loadCell_frame c 28 14 27 23 (by decide)).trans hpv
      have hqv₁ : c₁.reg 27 = d := (loadCell_frame c 28 14 27 27 (by decide)).trans hqv
      have hpt₁ : c₁.reg 22 = itemType (.node w) := (loadCell_frame c 28 14 27 22 (by decide)).trans hpt
      have hqt₁ : c₁.reg 26 = itemType (.dart d) := (loadCell_frame c 28 14 27 26 (by decide)).trans hqt
      have hbit : c₁.reg 28 = if S.isIn d then 1 else 0 := by
        have hx := ht.target d hq
        simpa [c₁, loadCell, run, seqs, hqv, hr.bases.2.2.2.2 14 (by decide), Layout.cell] using hx
      have haLoad : AddrOK L.limit (loadCell 28 14 27) c := by
        have hx : c.reg 64 + c.reg 27 < L.limit := by
          rw [hr.bases.2.2.2.2 14 (by decide), hqv]
          exact L.cell_lt (by decide) (hq.trans_le ht.darts)
        simpa [loadCell, AddrOK, run, seqs] using hx
      by_cases hin : S.isIn d
      · have hs := leftTarget_rep_addr hr₁ ht₁ hb hv hp hq hn₁ hpv₁ hqv₁ hin
        obtain ⟨hsr, hst, hsa⟩ := hs
        have hr' : Rep L (run twoBranchProgram c) (S.twoStep s v (.node w) (.dart d)) := by
          simpa [twoBranchProgram, run, seqs, hpt, hqt, c₁, hbit, hin] using hsr
        have ht' : Tables L (run twoBranchProgram c) S post vertices darts := by
          simpa [twoBranchProgram, run, seqs, hpt, hqt, c₁, hbit, hin] using hst
        refine ⟨hr', ht', ?_⟩
        simpa [twoBranchProgram, AddrOK, run, seqs, hpt, hqt, c₁, hbit, hin] using And.intro haLoad hsa
      · have hs := forkBranch_rep_addr hr₁ ht₁ (.node w) (.dart d) hp hq hv hn₁ hpt₁ hpv₁ hqt₁ hqv₁
          (by simp [Sol.tgtOf, hin])
        obtain ⟨hsr, hst, hsa⟩ := hs
        have hr' : Rep L (run twoBranchProgram c) (S.twoStep s v (.node w) (.dart d)) := by
          simpa [twoBranchProgram, run, seqs, hpt, hqt, c₁, hbit, hin] using hsr
        have ht' : Tables L (run twoBranchProgram c) S post vertices darts := by
          simpa [twoBranchProgram, run, seqs, hpt, hqt, c₁, hbit, hin] using hst
        refine ⟨hr', ht', ?_⟩
        simpa [twoBranchProgram, AddrOK, run, seqs, hpt, hqt, c₁, hbit, hin] using And.intro haLoad hsa
  | dart d =>
    cases q with
    | dart e =>
      have hs := forkBranch_rep_addr hr ht (.dart d) (.dart e) hp hq hv hnode hpt hpv hqt hqv (by rfl)
      simpa [twoBranchProgram, run, AddrOK, hpt, hqt, itemType] using hs
    | node w =>
      simp only [itemType, itemValue] at hpt hpv hqt hqv
      let c₁ := run (loadCell 28 14 23) c
      have hr₁ := hr.loadTemp 28 14 23 (by decide) (by decide)
      have ht₁ := ht.loadTemp 28 14 23 (by decide)
      have hn₁ : c₁.reg 20 = v := (loadCell_frame c 28 14 23 20 (by decide)).trans hnode
      have hpv₁ : c₁.reg 23 = d := (loadCell_frame c 28 14 23 23 (by decide)).trans hpv
      have hqv₁ : c₁.reg 27 = w := (loadCell_frame c 28 14 23 27 (by decide)).trans hqv
      have hpt₁ : c₁.reg 22 = itemType (.dart d) := (loadCell_frame c 28 14 23 22 (by decide)).trans hpt
      have hqt₁ : c₁.reg 26 = itemType (.node w) := (loadCell_frame c 28 14 23 26 (by decide)).trans hqt
      have hbit : c₁.reg 28 = if S.isIn d then 1 else 0 := by
        have hx := ht.target d hp
        simpa [c₁, loadCell, run, seqs, hpv, hr.bases.2.2.2.2 14 (by decide), Layout.cell] using hx
      have haLoad : AddrOK L.limit (loadCell 28 14 23) c := by
        have hx : c.reg 64 + c.reg 23 < L.limit := by
          rw [hr.bases.2.2.2.2 14 (by decide), hpv]
          exact L.cell_lt (by decide) (hp.trans_le ht.darts)
        simpa [loadCell, AddrOK, run, seqs] using hx
      by_cases hin : S.isIn d
      · have hs := rightTarget_rep_addr hr₁ ht₁ hb hv hq hp hn₁ hpv₁ hqv₁ hin
        obtain ⟨hsr, hst, hsa⟩ := hs
        have hr' : Rep L (run twoBranchProgram c) (S.twoStep s v (.dart d) (.node w)) := by
          simpa [twoBranchProgram, run, seqs, hpt, hqt, c₁, hbit, hin] using hsr
        have ht' : Tables L (run twoBranchProgram c) S post vertices darts := by
          simpa [twoBranchProgram, run, seqs, hpt, hqt, c₁, hbit, hin] using hst
        refine ⟨hr', ht', ?_⟩
        simpa [twoBranchProgram, AddrOK, run, seqs, hpt, hqt, c₁, hbit, hin] using And.intro haLoad hsa
      · have hs := forkBranch_rep_addr hr₁ ht₁ (.dart d) (.node w) hp hq hv hn₁ hpt₁ hpv₁ hqt₁ hqv₁
          (by simp [Sol.tgtOf, hin])
        obtain ⟨hsr, hst, hsa⟩ := hs
        have hr' : Rep L (run twoBranchProgram c) (S.twoStep s v (.dart d) (.node w)) := by
          simpa [twoBranchProgram, run, seqs, hpt, hqt, c₁, hbit, hin] using hsr
        have ht' : Tables L (run twoBranchProgram c) S post vertices darts := by
          simpa [twoBranchProgram, run, seqs, hpt, hqt, c₁, hbit, hin] using hst
        refine ⟨hr', ht', ?_⟩
        simpa [twoBranchProgram, AddrOK, run, seqs, hpt, hqt, c₁, hbit, hin] using And.intro haLoad hsa


/-- Two-part table reads protect the current node and all live solver registers. -/
theorem twoReadProgram_raw (c : Config) :
    let out := run twoReadProgram c
    out.reg 22 = c.mem (c.reg 67 + c.reg 20) ∧
    out.reg 23 = c.mem (c.reg 68 + c.reg 20) ∧
    out.reg 26 = c.mem (c.reg 69 + c.reg 20) ∧
    out.reg 27 = c.mem (c.reg 70 + c.reg 20) ∧ out.mem = c.mem ∧
    (∀ i, i ≠ 22 → i ≠ 23 → i ≠ 26 → i ≠ 27 → i ≠ 40 → out.reg i = c.reg i) := by
  simp [twoReadProgram, loadCell, run, seqs]
  intro i h₁ h₂ h₃ h₄ h₅; simp [h₁, h₂, h₃, h₄, h₅]

/-- Two-part execution is table reads followed by the actual kind dispatcher. -/
theorem twoNodeProgram_run (c : Config) : run twoNodeProgram c = run twoBranchProgram (run twoReadProgram c) := by
  simp only [twoNodeProgram, twoBranchProgram, twoReadProgram, run_seqs_cons, run_seqs_nil]

/-- The two-part memory bound splits at its actual table-read stage. -/
theorem twoNodeProgram_addr_decomp (bound : Nat) (c : Config) :
    AddrOK bound twoNodeProgram c ↔ AddrOK bound twoReadProgram c ∧
      AddrOK bound twoBranchProgram (run twoReadProgram c) := by
  simp only [twoNodeProgram, twoBranchProgram, twoReadProgram, addrOK_seqs_cons, addrOK_seqs_nil,
    run_seqs_cons, run_seqs_nil, and_true, and_assoc]

/-- A two-part node refines its semantic target or fork and has only bounded accesses. -/
theorem twoNodeProgram_rep_addr {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertices darts v : Nat} (hr : Rep L c s) (ht : Tables L c S post vertices darts)
    (hb : MemoryBounds s.m L.width darts) (hv : v < vertices) (hnode : c.reg 20 = v)
    (p q : Item) (hparts : S.P.parts v = [p, q]) :
    Rep L (run twoNodeProgram c) (S.twoStep s v p q) ∧
    Tables L (run twoNodeProgram c) S post vertices darts ∧ AddrOK L.limit twoNodeProgram c := by
  let c₁ := run twoReadProgram c
  obtain ⟨hpt, hpv, hqt, hqv, hm, hf⟩ := twoReadProgram_raw c
  have hr₁ : Rep L c₁ s := hr.frame
    (fun i hi => hf i (by omega) (by omega) (by omega) (by omega) (by omega))
    (fun i hi => hf i (by omega) (by omega) (by omega) (by omega) (by omega)) hm
  have ht₁ : Tables L c₁ S post vertices darts := ht.frame
    (hf 4 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hf 5 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hm]; exact TableMemEq.refl L c.mem)
  have hn₁ : c₁.reg 20 = v := (hf 20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hnode
  have hpt₁ : c₁.reg 22 = itemType p := by
    have hx := ht.leftType v hv
    simp [hparts] at hx
    simpa only [c₁, hnode, hr.bases.2.2.2.2 17 (by decide), ← hx, Layout.cell] using hpt
  have hpv₁ : c₁.reg 23 = itemValue p := by
    have hx := ht.leftValue v hv
    simp [hparts] at hx
    simpa only [c₁, hnode, hr.bases.2.2.2.2 18 (by decide), ← hx, Layout.cell] using hpv
  have hqt₁ : c₁.reg 26 = itemType q := by
    have hx := ht.rightType v hv
    simp [hparts] at hx
    simpa only [c₁, hnode, hr.bases.2.2.2.2 19 (by decide), ← hx, Layout.cell] using hqt
  have hqv₁ : c₁.reg 27 = itemValue q := by
    have hx := ht.rightValue v hv
    simp [hparts] at hx
    simpa only [c₁, hnode, hr.bases.2.2.2.2 20 (by decide), ← hx, Layout.cell] using hqv
  have hp := ht.children v hv p (by simp [hparts])
  have hq := ht.children v hv q (by simp [hparts])
  obtain ⟨hr', ht', ha'⟩ := twoBranchProgram_rep_addr hr₁ ht₁ hb p q hp hq hv hn₁ hpt₁ hpv₁ hqt₁ hqv₁
  have haRead : AddrOK L.limit twoReadProgram c := by
    have hc (j : Nat) (hj : j < 22) : c.reg (50 + j) + c.reg 20 < L.limit := by
      rw [hr.bases.2.2.2.2 j hj, hnode]; exact L.cell_lt hj (hv.trans_le ht.vertices)
    have h₁₇ := hc 17 (by decide)
    have h₁₈ := hc 18 (by decide)
    have h₁₉ := hc 19 (by decide)
    have h₂₀ := hc 20 (by decide)
    simp [twoReadProgram, loadCell, AddrOK, run, seqs, h₁₇, h₁₈, h₁₉, h₂₀]
  refine ⟨?_, ?_, (twoNodeProgram_addr_decomp L.limit c).mpr ⟨haRead, ha'⟩⟩
  · rw [twoNodeProgram_run]; exact hr'
  · rw [twoNodeProgram_run]; exact ht'

end STACS2027.Embed.RAMSolver
