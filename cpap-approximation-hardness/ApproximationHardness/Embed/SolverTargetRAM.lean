module

public import ApproximationHardness.Embed.SolverCloseRefine
public import ApproximationHardness.Embed.SolverCloseBounds
public import ApproximationHardness.Embed.SolverNodeBounds
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Actual target-node reads and stores in the finite linked layout. -/

@[expose] public section

set_option maxHeartbeats 1500000

namespace STACS2027.Embed.RAMSolver

open RAM

/-- Read the partner and child result for a target. -/
def targetReadProgram : Stmt := seqs [loadCell 23 13 23, loadCell 24 6 21, loadCell 25 7 21]

/-- Commit the closed target result and its orientation code. -/
def targetStoreProgram : Stmt := seqs [storeCell 6 20 24, storeCell 7 20 25,
  storeCell 10 20 34, storeCell 11 20 23, .add 6 6 1]

/-- The target read has no memory effect and protects the current node and orientation code. -/
theorem targetReadProgram_raw (c : Config) :
    let out := run targetReadProgram c
    out.reg 23 = c.mem (c.reg 63 + c.reg 23) ∧
    out.reg 24 = c.mem (c.reg 56 + c.reg 21) ∧
    out.reg 25 = c.mem (c.reg 57 + c.reg 21) ∧ out.mem = c.mem ∧
    (∀ i, i ≠ 23 → i ≠ 24 → i ≠ 25 → i ≠ 40 → out.reg i = c.reg i) ∧ out.out = c.out := by
  simp [targetReadProgram, loadCell, run, seqs]
  intro i h₁ h₂ h₃ h₄
  simp [h₁, h₂, h₃, h₄]

/-- Exact four-cell commit and scalar frame for a target result. -/
theorem targetStoreProgram_raw (c : Config) (hz : c.reg 0 = 0) (ho : c.reg 1 = 1) :
    let m₁ := upd c.mem (c.reg 56 + c.reg 20) (c.reg 24)
    let m₂ := upd m₁ (c.reg 57 + c.reg 20) (c.reg 25)
    let m₃ := upd m₂ (c.reg 60 + c.reg 20) (c.reg 34)
    let m₄ := upd m₃ (c.reg 61 + c.reg 20) (c.reg 23)
    let out := run targetStoreProgram c
    out.reg 6 = c.reg 6 + 1 ∧ out.mem = m₄ ∧
    (∀ i, i ≠ 6 → i ≠ 40 → out.reg i = c.reg i) ∧ out.out = c.out := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [targetStoreProgram, storeCell, run, seqs, hz, ho]
  · funext i; simp [targetStoreProgram, storeCell, run, seqs, upd]
  · intro i h₁ h₂; simp [targetStoreProgram, storeCell, run, seqs, h₁, h₂]
  · simp [targetStoreProgram, storeCell, run, seqs]

/-- A target store refines its finite mutable-array update. -/
theorem targetStoreProgram_rep {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound v code e h l : Nat} (hr : Rep L c s)
    (ht : Tables L c S post vertexBound dartBound) (hv : v < L.width)
    (hnode : c.reg 20 = v) (hhead : c.reg 24 = h) (hlow : c.reg 25 = l)
    (hcode : c.reg 34 = code) (he : c.reg 23 = e) :
    Rep L (run targetStoreProgram c)
      {s with
        m := {SMem.store s.m v h l with
          inf := upd s.m.inf v code
          ia := upd s.m.ia v e}
        k := s.k + 1} ∧
    Tables L (run targetStoreProgram c) S post vertexBound dartBound := by
  obtain ⟨hk, hm, hf, hout⟩ := targetStoreProgram_raw c hr.bases.1 hr.bases.2.1
  have hbase := hr.bases.2.2.2.2
  let m₁ := upd c.mem (L.cell 6 v) h
  let m₂ := upd m₁ (L.cell 7 v) l
  let m₃ := upd m₂ (L.cell 10 v) code
  let m₄ := upd m₃ (L.cell 11 v) e
  have hm' : (run targetStoreProgram c).mem = m₄ := by
    simpa only [hnode, hhead, hlow, hcode, he, hbase 6 (by decide), hbase 7 (by decide),
      hbase 10 (by decide), hbase 11 (by decide), m₄, m₃, m₂, m₁, Layout.cell] using hm
  refine ⟨?_, ?_⟩
  · constructor
    · refine ⟨(hf 0 (by decide) (by decide)).trans hr.bases.1,
        (hf 1 (by decide) (by decide)).trans hr.bases.2.1,
        (hf 2 (by decide) (by decide)).trans hr.bases.2.2.1,
        (hf 3 (by decide) (by decide)).trans hr.bases.2.2.2.1, ?_⟩
      intro j hj; exact (hf _ (by omega) (by omega)).trans (hbase j hj)
    · intro j hj i hi
      rw [hm']
      dsimp only [m₄, m₃, m₂, m₁]
      simp only [update_cell L _ j 11 i v _ hi hv, update_cell L _ j 10 i v _ hi hv,
        update_cell L _ j 7 i v _ hi hv, update_cell L _ j 6 i v _ hi hv]
      have harr := hr.arrays j hj i hi
      interval_cases j <;> simp [SMem.store, memField, upd, eq_comm, harr]
    · exact hk.trans (congrArg (· + 1) hr.index)
    · exact (hf 7 (by decide) (by decide)).trans hr.mode
    · exact (hf 8 (by decide) (by decide)).trans hr.node
    · exact (hf 9 (by decide) (by decide)).trans hr.group
    · exact (hf 10 (by decide) (by decide)).trans hr.upperLow
    · exact (hf 11 (by decide) (by decide)).trans hr.resultLow
    · exact (hf 12 (by decide) (by decide)).trans hr.upperHead
    · exact (hf 13 (by decide) (by decide)).trans hr.lowerHead
    · exact (hf 14 (by decide) (by decide)).trans hr.positiveHead
    · exact (hf 15 (by decide) (by decide)).trans hr.positiveTail
    · exact (hf 16 (by decide) (by decide)).trans hr.negativeHead
    · exact (hf 17 (by decide) (by decide)).trans hr.negativeTail
    · exact (hf 18 (by decide) (by decide)).trans hr.lowerClassHead
    · exact (hf 19 (by decide) (by decide)).trans hr.lowerClassTail
  · have h₁ := TableMemEq.update L c.mem 6 v h (by decide) hv
    have h₂ := (TableMemEq.update L m₁ 7 v l (by decide) hv).trans h₁
    have h₃ := (TableMemEq.update L m₂ 10 v code (by decide) hv).trans h₂
    have h₄ := (TableMemEq.update L m₃ 11 v e (by decide) hv).trans h₃
    apply ht.frame (hf 4 (by decide) (by decide)) (hf 5 (by decide) (by decide))
    rw [hm']; exact h₄

/-- The target-node instruction is exactly read, close, and commit. -/
theorem targetNodeProgram_run (c : Config) : run targetNodeProgram c =
    run targetStoreProgram (run closeResultProgram (run targetReadProgram c)) := by
  simp [targetNodeProgram, targetReadProgram, targetStoreProgram, run, seqs]


/-- The target-node instruction refines closing the partner in a child result. -/
theorem targetNodeProgram_rep {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound v w d code : Nat} (hr : Rep L c s)
    (ht : Tables L c S post vertexBound dartBound) (hb : MemoryBounds s.m L.width dartBound)
    (hv : v < vertexBound) (hw : w < vertexBound) (hd : d < dartBound)
    (hnode : c.reg 20 = v) (hchild : c.reg 21 = w) (hdart : c.reg 23 = d)
    (hcode : c.reg 34 = code) :
    let r := S.closeM s.m (S.α d) (s.m.rs w) (s.m.rl w)
    Rep L (run targetNodeProgram c)
      {s with
        m := {SMem.store r.1 v r.2.1 r.2.2 with
          inf := upd r.1.inf v code
          ia := upd r.1.ia v (S.α d)}
        k := s.k + 1} ∧
    Tables L (run targetNodeProgram c) S post vertexBound dartBound := by
  dsimp only
  let c₁ := run targetReadProgram c
  let c₂ := run closeResultProgram c₁
  obtain ⟨he₁, hh₁, hl₁, hm₁, hf₁, hout₁⟩ := targetReadProgram_raw c
  have hbase := hr.bases.2.2.2.2
  have hr₁ : Rep L c₁ s := hr.frame (fun i hi => hf₁ i (by omega) (by omega) (by omega) (by omega))
    (fun i hi => hf₁ i (by omega) (by omega) (by omega) (by omega)) hm₁
  have ht₁ : Tables L c₁ S post vertexBound dartBound := ht.frame
    (hf₁ 4 (by decide) (by decide) (by decide) (by decide))
    (hf₁ 5 (by decide) (by decide) (by decide) (by decide))
    (by rw [hm₁]; exact TableMemEq.refl L c.mem)
  have he₁' : c₁.reg 23 = S.α d := by
    simpa only [c₁, hbase 13 (by decide), hdart, ← ht.partners d hd, Layout.cell] using he₁
  have hh₁' : c₁.reg 24 = s.m.rs w := by
    have hx : c₁.reg 24 = c.mem (L.cell 6 w) := by
      simpa only [c₁, hbase 6 (by decide), hchild, Layout.cell] using hh₁
    exact hx.trans (hr.arrays 6 (by decide) w (hw.trans_le ht.vertices))
  have hl₁' : c₁.reg 25 = s.m.rl w := by
    have hx : c₁.reg 25 = c.mem (L.cell 7 w) := by
      simpa only [c₁, hbase 7 (by decide), hchild, Layout.cell] using hl₁
    exact hx.trans (hr.arrays 7 (by decide) w (hw.trans_le ht.vertices))
  obtain ⟨hh₂, hl₂, hr₂, ht₂⟩ := closeResultProgram_rep hr₁ ht₁ (ht.partnersBound d hd)
    (hb.resultHead w) he₁' hh₁' hl₁'
  obtain ⟨_, _, _, hf₂, _⟩ := closeResultProgram_raw c₁ hr₁.bases.1 hr₁.bases.2.1
  have hnode₂ : c₂.reg 20 = v :=
    (hf₂ 20 (Or.inr (Or.inl rfl))).trans ((hf₁ 20 (by decide) (by decide) (by decide) (by decide)).trans hnode)
  have hcode₂ : c₂.reg 34 = code :=
    (hf₂ 34 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).trans
      ((hf₁ 34 (by decide) (by decide) (by decide) (by decide)).trans hcode)
  have he₂ : c₂.reg 23 = S.α d :=
    (hf₂ 23 (Or.inr (Or.inr (Or.inl rfl)))).trans he₁'
  have hs := targetStoreProgram_rep hr₂ ht₂ (hv.trans_le ht.vertices) hnode₂ hh₂ hl₂ hcode₂ he₂
  rw [targetNodeProgram_run]
  exact hs


/-- The target node's address condition separates into its three actual instruction stages. -/
theorem targetNodeProgram_addr_decomp (bound : Nat) (c : Config) :
    AddrOK bound targetNodeProgram c ↔
      AddrOK bound targetReadProgram c ∧
      AddrOK bound closeResultProgram (run targetReadProgram c) ∧
      AddrOK bound targetStoreProgram (run closeResultProgram (run targetReadProgram c)) := by
  simp only [targetNodeProgram, targetReadProgram, targetStoreProgram, addrOK_seqs_cons,
    addrOK_seqs_nil, run_seqs_cons, run_seqs_nil, and_true, and_assoc]

/-- Bounded execution of a target node, including all partner, child, and commit accesses. -/
theorem targetNodeProgram_exec {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound v w d : Nat} (hr : Rep L c s)
    (ht : Tables L c S post vertexBound dartBound) (hb : MemoryBounds s.m L.width dartBound)
    (hv : v < vertexBound) (hw : w < vertexBound) (hd : d < dartBound)
    (hnode : c.reg 20 = v) (hchild : c.reg 21 = w) (hdart : c.reg 23 = d) :
    ∃ t, ExecB L.limit targetNodeProgram c t (run targetNodeProgram c) ∧ t ≤ 200 := by
  let c₁ := run targetReadProgram c
  let c₂ := run closeResultProgram c₁
  obtain ⟨he₁, hh₁, hl₁, hm₁, hf₁, hout₁⟩ := targetReadProgram_raw c
  have hbase := hr.bases.2.2.2.2
  have hr₁ : Rep L c₁ s := hr.frame (fun i hi => hf₁ i (by omega) (by omega) (by omega) (by omega))
    (fun i hi => hf₁ i (by omega) (by omega) (by omega) (by omega)) hm₁
  have ht₁ : Tables L c₁ S post vertexBound dartBound := ht.frame
    (hf₁ 4 (by decide) (by decide) (by decide) (by decide))
    (hf₁ 5 (by decide) (by decide) (by decide) (by decide))
    (by rw [hm₁]; exact TableMemEq.refl L c.mem)
  have he₁' : c₁.reg 23 = S.α d := by
    simpa only [c₁, hbase 13 (by decide), hdart, ← ht.partners d hd, Layout.cell] using he₁
  have hh₁' : c₁.reg 24 = s.m.rs w := by
    have hx : c₁.reg 24 = c.mem (L.cell 6 w) := by
      simpa only [c₁, hbase 6 (by decide), hchild, Layout.cell] using hh₁
    exact hx.trans (hr.arrays 6 (by decide) w (hw.trans_le ht.vertices))
  have hl₁' : c₁.reg 25 = s.m.rl w := by
    have hx : c₁.reg 25 = c.mem (L.cell 7 w) := by
      simpa only [c₁, hbase 7 (by decide), hchild, Layout.cell] using hl₁
    exact hx.trans (hr.arrays 7 (by decide) w (hw.trans_le ht.vertices))
  obtain ⟨_, _, hr₂, ht₂⟩ := closeResultProgram_rep hr₁ ht₁ (ht.partnersBound d hd)
    (hb.resultHead w) he₁' hh₁' hl₁'
  obtain ⟨_, _, _, hf₂, _⟩ := closeResultProgram_raw c₁ hr₁.bases.1 hr₁.bases.2.1
  have hnode₂ : c₂.reg 20 = v :=
    (hf₂ 20 (Or.inr (Or.inl rfl))).trans ((hf₁ 20 (by decide) (by decide) (by decide) (by decide)).trans hnode)
  have hread : AddrOK L.limit targetReadProgram c := by
    have he : c.reg 63 + c.reg 23 < L.limit := by
      rw [hbase 13 (by decide), hdart]; exact L.cell_lt (by decide) (hd.trans_le ht.darts)
    have h₆ : c.reg 56 + c.reg 21 < L.limit := by
      rw [hbase 6 (by decide), hchild]; exact L.cell_lt (by decide) (hw.trans_le ht.vertices)
    have h₇ : c.reg 57 + c.reg 21 < L.limit := by
      rw [hbase 7 (by decide), hchild]; exact L.cell_lt (by decide) (hw.trans_le ht.vertices)
    simp [targetReadProgram, loadCell, AddrOK, run, seqs, he, h₆, h₇]
  have hclose : AddrOK L.limit closeResultProgram c₁ :=
    closeResultProgram_addrOK hr₁.bases.1 hr₁.bases.2.1
      (CloseAddressOK.ofRep hr₁ ht₁ (ht.partnersBound d hd) (hb.resultHead w) he₁' hh₁')
  have hstore : AddrOK L.limit targetStoreProgram c₂ := by
    have hbase₂ := hr₂.bases.2.2.2.2
    have hc (j : Nat) (hj : j < 22) : c₂.reg (50 + j) + c₂.reg 20 < L.limit := by
      rw [hbase₂ j hj, hnode₂]; exact L.cell_lt hj (hv.trans_le ht.vertices)
    have h₆ := hc 6 (by decide)
    have h₇ := hc 7 (by decide)
    have h₁₀ := hc 10 (by decide)
    have h₁₁ := hc 11 (by decide)
    simp [targetStoreProgram, storeCell, AddrOK, run, seqs, h₆, h₇, h₁₀, h₁₁]
  have ha := (targetNodeProgram_addr_decomp L.limit c).mpr ⟨hread, hclose, hstore⟩
  have hlp : LoopFree targetNodeProgram := by
    simp [targetNodeProgram, closeResultProgram, closePositiveProgram, closeNegativeProgram,
      loadCell, storeCell, LoopFree, seqs]
  have hsize : size targetNodeProgram ≤ 200 := by decide
  exact ⟨_, execB_run _ hlp c ha, Nat.le_trans (cost_le_size _ _) hsize⟩

end STACS2027.Embed.RAMSolver
