module

public import ApproximationHardness.Embed.SolverForkRAM
public import ApproximationHardness.Embed.SolverTempRAM
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Empty and singleton branches of the actual node dispatcher. -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

/-- The empty-node program writes the empty represented result and advances the index. -/
theorem leafNodeProgram_rep {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound v : Nat} (hr : Rep L c s)
    (ht : Tables L c S post vertexBound dartBound) (hv : v < vertexBound) (hnode : c.reg 20 = v) :
    Rep L (run leafNodeProgram c)
      {s with m := {SMem.store s.m v 0 S.INF with inf := upd s.m.inf v 0}, k := s.k + 1} ∧
    Tables L (run leafNodeProgram c) S post vertexBound dartBound := by
  let c₁ := c.setReg 24 0
  let c₂ := c₁.setReg 25 (c.reg 5 + c.reg 0)
  have hr₂ := (hr.temp 24 0 (by decide) (by decide)).temp 25 (c.reg 5 + c.reg 0) (by decide) (by decide)
  have ht₂ := (ht.temp 24 0 (by decide)).temp 25 (c.reg 5 + c.reg 0) (by decide)
  have hs := storeNodeResult_rep hr₂ ht₂ (hv.trans_le ht.vertices)
    (by simpa [c₁, c₂] using hnode) (head := 24) (low := 25) (by decide) (by decide)
  simpa [leafNodeProgram, run, seqs, c₁, c₂, hr.bases.1, ht.infinity] using hs

/-- Empty-node execution uses only its three result cells. -/
theorem leafNodeProgram_exec {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound v : Nat} (hr : Rep L c s)
    (ht : Tables L c S post vertexBound dartBound) (hv : v < vertexBound) (hnode : c.reg 20 = v) :
    ∃ t, ExecB L.limit leafNodeProgram c t (run leafNodeProgram c) ∧ t ≤ 100 := by
  let c₂ := (c.setReg 24 0).setReg 25 (c.reg 5 + c.reg 0)
  have hr₂ := (hr.temp 24 0 (by decide) (by decide)).temp 25 (c.reg 5 + c.reg 0) (by decide) (by decide)
  obtain ⟨t, he, hb⟩ := storeNodeResult_exec hr₂ (hv.trans_le ht.vertices)
    (by simpa [c₂] using hnode) (head := 24) (low := 25) (by decide) (by decide)
  have hlp : LoopFree (storeNodeResult 24 25) := by simp [storeNodeResult, storeCell, LoopFree, seqs]
  have ha := (boundedRun_addr he hlp).2
  have ha' : AddrOK L.limit leafNodeProgram c := by simpa [leafNodeProgram, AddrOK, run, seqs] using ha
  have hlp' : LoopFree leafNodeProgram := by simp [leafNodeProgram, storeNodeResult, storeCell, LoopFree, seqs]
  have hs : size leafNodeProgram ≤ 100 := by decide
  exact ⟨_, execB_run _ hlp' c ha', Nat.le_trans (cost_le_size _ _) hs⟩

/-- Singleton initialization protects the current node register. -/
theorem singleItem_node_frame (c : Config) : (run (itemResultInto 22 23 24 25) c).reg 20 = c.reg 20 := by
  by_cases ht : c.reg 22 = 0 <;> simp [itemResultInto, loadCell, storeCell, run, seqs, ht]

/-- The singleton node program refines its actual item-result read and store. -/
theorem singleNodeProgram_rep {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound v : Nat} (hr : Rep L c s)
    (ht : Tables L c S post vertexBound dartBound) (hv : v < vertexBound)
    (hnode : c.reg 20 = v) (it : Item) (hparts : S.P.parts v = [it]) :
    let r := S.itRes s.m it
    Rep L (run singleNodeProgram c)
      {s with m := {SMem.store r.1 v r.2.1 r.2.2 with inf := upd r.1.inf v 0}, k := s.k + 1} ∧
    Tables L (run singleNodeProgram c) S post vertexBound dartBound := by
  let c₁ := run (loadCell 22 17 20) c
  let c₂ := run (loadCell 23 18 20) c₁
  let c₃ := run (itemResultInto 22 23 24 25) c₂
  have hr₂ := (hr.loadTemp 22 17 20 (by decide) (by decide)).loadTemp 23 18 20 (by decide) (by decide)
  have ht₂ := (ht.loadTemp 22 17 20 (by decide)).loadTemp 23 18 20 (by decide)
  have hnode₂ : c₂.reg 20 = v := by simp [c₂, c₁, loadCell, run, seqs, hnode]
  have htyp : c₂.reg 22 = itemType it := by
    have hx := ht.leftType v hv
    simp only [hparts, List.getD_cons_zero] at hx
    simpa [c₂, c₁, loadCell, run, seqs, hnode, hr.bases.2.2.2.2 17 (by decide), Layout.cell] using hx
  have hval : c₂.reg 23 = itemValue it := by
    have hx := ht.leftValue v hv
    simp only [hparts, List.getD_cons_zero] at hx
    simpa [c₂, c₁, loadCell, run, seqs, hnode, hr.bases.2.2.2.2 18 (by decide), Layout.cell] using hx
  have hit := ht.children v hv it (by simp [hparts])
  obtain ⟨hh₃, hl₃, hr₃, ht₃⟩ := itemResultInto_rep hr₂ ht₂ it hit
    (head := 24) (low := 25) (typ := 22) (value := 23)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) htyp hval
  have hnode₃ : c₃.reg 20 = v := (singleItem_node_frame c₂).trans hnode₂
  have hs := storeNodeResult_rep hr₃ ht₃ (hv.trans_le ht.vertices) hnode₃
    (head := 24) (low := 25) (by decide) (by decide)
  simpa only [singleNodeProgram, run_seqs_cons, run_seqs_nil, c₁, c₂, c₃, hh₃, hl₃] using hs


/-- Singleton node execution has a fixed instruction bound and bounded real addresses. -/
theorem singleNodeProgram_exec {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound v : Nat} (hr : Rep L c s)
    (ht : Tables L c S post vertexBound dartBound) (hv : v < vertexBound)
    (hnode : c.reg 20 = v) (it : Item) (hparts : S.P.parts v = [it]) :
    ∃ t, ExecB L.limit singleNodeProgram c t (run singleNodeProgram c) ∧ t ≤ 200 := by
  let c₁ := run (loadCell 22 17 20) c
  let c₂ := run (loadCell 23 18 20) c₁
  let c₃ := run (itemResultInto 22 23 24 25) c₂
  have hr₁ := hr.loadTemp 22 17 20 (by decide) (by decide)
  have hr₂ := hr₁.loadTemp 23 18 20 (by decide) (by decide)
  have ht₂ := (ht.loadTemp 22 17 20 (by decide)).loadTemp 23 18 20 (by decide)
  have hnode₂ : c₂.reg 20 = v := by simp [c₂, c₁, loadCell, run, seqs, hnode]
  have htyp : c₂.reg 22 = itemType it := by
    have hx := ht.leftType v hv
    simp only [hparts, List.getD_cons_zero] at hx
    simpa [c₂, c₁, loadCell, run, seqs, hnode, hr.bases.2.2.2.2 17 (by decide), Layout.cell] using hx
  have hval : c₂.reg 23 = itemValue it := by
    have hx := ht.leftValue v hv
    simp only [hparts, List.getD_cons_zero] at hx
    simpa [c₂, c₁, loadCell, run, seqs, hnode, hr.bases.2.2.2.2 18 (by decide), Layout.cell] using hx
  have hit := ht.children v hv it (by simp [hparts])
  obtain ⟨hh₃, hl₃, hr₃, ht₃⟩ := itemResultInto_rep hr₂ ht₂ it hit
    (head := 24) (low := 25) (typ := 22) (value := 23)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) htyp hval
  obtain ⟨ti, hei, _⟩ := itemResultInto_exec hr₂ ht₂ it hit
    (head := 24) (low := 25) (typ := 22) (value := 23)
    (by decide) (by decide) (by decide) (by decide) (by decide) htyp hval
  have hai := (boundedRun_addr hei (itemResultInto_loopFree _ _ _ _)).2
  have hnode₃ : c₃.reg 20 = v := (singleItem_node_frame c₂).trans hnode₂
  obtain ⟨ts, hes, _⟩ := storeNodeResult_exec hr₃ (hv.trans_le ht.vertices) hnode₃
    (head := 24) (low := 25) (by decide) (by decide)
  have hlps : LoopFree (storeNodeResult 24 25) := by simp [storeNodeResult, storeCell, LoopFree, seqs]
  have has := (boundedRun_addr hes hlps).2
  have ha₁ : AddrOK L.limit (loadCell 22 17 20) c := by
    have hx : c.reg 67 + c.reg 20 < L.limit := by
      rw [hr.bases.2.2.2.2 17 (by decide), hnode]; exact L.cell_lt (by decide) (hv.trans_le ht.vertices)
    simpa [loadCell, AddrOK, run, seqs] using hx
  have ha₂ : AddrOK L.limit (loadCell 23 18 20) c₁ := by
    have hx : c₁.reg 68 + c₁.reg 20 < L.limit := by
      rw [hr₁.bases.2.2.2.2 18 (by decide)]
      have hn : c₁.reg 20 = v := by simp [c₁, loadCell, run, seqs, hnode]
      rw [hn]; exact L.cell_lt (by decide) (hv.trans_le ht.vertices)
    simpa [loadCell, AddrOK, run, seqs] using hx
  have ha : AddrOK L.limit singleNodeProgram c := by
    simp only [singleNodeProgram, addrOK_seqs_cons, addrOK_seqs_nil,
      run_seqs_cons, run_seqs_nil]
    exact ⟨ha₁, ha₂, hai, has, trivial⟩
  have hlp : LoopFree singleNodeProgram := by
    simp [singleNodeProgram, itemResultInto_loopFree, storeNodeResult, storeCell, loadCell, LoopFree, seqs]
  have hs : size singleNodeProgram ≤ 200 := by decide
  exact ⟨_, execB_run _ hlp c ha, Nat.le_trans (cost_le_size _ _) hs⟩

end STACS2027.Embed.RAMSolver
