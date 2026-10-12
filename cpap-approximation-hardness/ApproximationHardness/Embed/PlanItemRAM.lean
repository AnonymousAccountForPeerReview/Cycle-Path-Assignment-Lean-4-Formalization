module

public import ApproximationHardness.Embed.PlanCache
public import ApproximationHardness.Embed.DFSStepProof
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-! # Constant-time decoding of a cached forest-plan item -/

@[expose] public section

namespace STACS2027.Embed.PlanRAM

open RAM

abbrev zBase := 280
abbrev vertex := 281
abbrev degree := 282
abbrev vertexParent := 283
abbrev dart := 284
abbrev opposite := 285
abbrev child := 286
abbrev childParent := 287
abbrev itemType := 288
abbrev itemValue := 289
abbrev distinguished := 290
abbrev vertexBound := 291
abbrev partCount := 292
abbrev topVertex := 293
abbrev remaining := 294
abbrev slot := 295
abbrev address := 300
abbrev test := 301
abbrev otherTest := 302

attribute [local simp] zBase vertex degree vertexParent dart opposite child childParent
  itemType itemValue distinguished vertexBound partCount topVertex remaining slot
  address test otherTest

def readForest (dst block index : Nat) : Stmt := seqs [
  .add address (160 + block) index, .load dst address]

def cachedItem : Stmt := seqs [readForest opposite 1 dart,
  readForest child 0 opposite, readForest childParent 6 child,
  .sub test childParent opposite, .sub otherTest opposite childParent,
  .const itemType 1, .add itemValue dart 0,
  .ifz test (.ifz otherTest (seqs [.const itemType 0, .add itemValue child 0]) .skip) .skip]

theorem cachedItem_loopFree : LoopFree cachedItem := by
  simp [cachedItem, readForest, seqs, LoopFree]

theorem cachedItem_size : size cachedItem ≤ 30 := by decide

theorem cachedItem_values {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hr : DFSRAM.Rep L G c s) (ht : DFSRAM.Tables L G c) (hG : G.Ok)
    {d : Nat} (hd : d < 2 * G.E) (hreg : c.reg dart = d) :
    (run cachedItem c).reg opposite = pair d ∧
    (run cachedItem c).reg child = G.rep (pair d) ∧
    (run cachedItem c).reg childParent = s.par (G.rep (pair d)) ∧
    (run cachedItem c).reg itemType = RAMSolver.itemType ((G.fd s).item d) ∧
    (run cachedItem c).reg itemValue = RAMSolver.itemValue ((G.fd s).item d) := by
  have hb (j : Nat) (hj : j < 11) := hr.bases.2.2.2.2.2 j hj
  have hp := ht.partners d hd
  have hv := ht.representatives (pair d) (pair_lt hd)
  have hw := hG.rep_lt (pair d) (pair_lt hd)
  have hpar := hr.parents _ hw
  simp only [DFSRAM.Layout.cell] at hp hv hpar
  have he := PlanCache.item_cached (G.fd s) d
  simp only [DG.fd] at he
  have hpair : pair d < 2 * G.E := pair_lt hd
  by_cases heq : s.par (G.rep (pair d)) = pair d
  · simp [cachedItem, readForest, seqs, run, hreg, hb 1 (by decide), hb 0 (by decide),
      hb 6 (by decide), hr.bases.1, hp, hv, hpar, heq, he, DG.fd, hpair,
      RAMSolver.itemType, RAMSolver.itemValue]
  · have hdiff : s.par (G.rep (pair d)) - pair d ≠ 0 ∨
        pair d - s.par (G.rep (pair d)) ≠ 0 := by omega
    rcases hdiff with hdiff | hdiff
    · simp [cachedItem, readForest, seqs, run, hreg, hb 1 (by decide), hb 0 (by decide),
        hb 6 (by decide), hr.bases.1, hp, hv, hpar, hdiff, heq, he, DG.fd,
        RAMSolver.itemType, RAMSolver.itemValue]
    · simp [cachedItem, readForest, seqs, run, hreg, hb 1 (by decide), hb 0 (by decide),
        hb 6 (by decide), hr.bases.1, hp, hv, hpar, hdiff, heq, he, DG.fd,
        RAMSolver.itemType, RAMSolver.itemValue]

theorem cachedItem_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hr : DFSRAM.Rep L G c s) (ht : DFSRAM.Tables L G c) (hG : G.Ok)
    {d : Nat} (hd : d < 2 * G.E) (hreg : c.reg dart = d) (hw : 2 * G.E ≤ L.width) :
    AddrOK L.limit cachedItem c := by
  have hb (j : Nat) (hj : j < 11) := hr.bases.2.2.2.2.2 j hj
  have hp := ht.partners d hd
  have hv := ht.representatives (pair d) (pair_lt hd)
  have hwv := hG.rep_lt (pair d) (pair_lt hd)
  have h1 := DFSRAM.Layout.cell_lt (L := L) (j := 1) (by decide) (i := d) (by omega)
  have h0 := DFSRAM.Layout.cell_lt (L := L) (j := 0) (by decide) (i := pair d) (by have := pair_lt hd; omega)
  have h6 := DFSRAM.Layout.cell_lt (L := L) (j := 6) (by decide) (i := G.rep (pair d)) (by omega)
  simp only [DFSRAM.Layout.cell] at hp hv h1 h0 h6
  simp [cachedItem, readForest, seqs, AddrOK, run, hreg, hb 1 (by decide), hb 0 (by decide),
    hb 6 (by decide), hp, hv, h1, h0, h6]

theorem cachedItem_spec {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hr : DFSRAM.Rep L G c s) (ht : DFSRAM.Tables L G c) (hG : G.Ok)
    {d : Nat} (hd : d < 2 * G.E) (hreg : c.reg dart = d) (hw : 2 * G.E ≤ L.width) :
    ∃ t, ExecB L.limit cachedItem c t (run cachedItem c) ∧ t ≤ 30 ∧
      (run cachedItem c).reg itemType = RAMSolver.itemType ((G.fd s).item d) ∧
      (run cachedItem c).reg itemValue = RAMSolver.itemValue ((G.fd s).item d) ∧
      (run cachedItem c).mem = c.mem ∧ (run cachedItem c).out = c.out := by
  have hv := cachedItem_values hr ht hG hd hreg
  exact ⟨_, execB_run _ cachedItem_loopFree c (cachedItem_addrOK hr ht hG hd hreg hw),
    (cost_le_size cachedItem c).trans cachedItem_size, hv.2.2.2.1, hv.2.2.2.2,
    run_mem_frame _ _ (by decide), run_out_frame _ _ (by decide)⟩

theorem cachedItem_frame (c : Config) (r : Nat)
    (hr : r ∉ [285,286,287,288,289,300,301,302]) :
    (run cachedItem c).reg r = c.reg r := by
  apply run_reg_frame
  simp_all [cachedItem,readForest,seqs,regsW]

theorem cachedItem_rep {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hr : DFSRAM.Rep L G c s) : DFSRAM.Rep L G (run cachedItem c) s := by
  apply hr.memory.of_regs (c := run cachedItem c) (run_mem_frame _ _ (by decide))
  · apply hr.bases.frame
    intro r hb
    apply cachedItem_frame
    simp only [DFSRAM.dartCount,DFSRAM.baseRegister,DFSRAM.widthRegister] at hb
    intro hm
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hm
    rcases hb with hb | hb | hb | hb | hb | hb <;> omega
  · rw [cachedItem_frame c 141 (by decide)];exact hr.scan
  · rw [cachedItem_frame c 142 (by decide)];exact hr.current
  · rw [cachedItem_frame c 143 (by decide)];exact hr.inner
  · rw [cachedItem_frame c 144 (by decide)];exact hr.height
  · rw [cachedItem_frame c 145 (by decide)];exact hr.postLength

theorem cachedItem_tables {L : DFSRAM.Layout} {G : DG} {c : Config}
    (ht : DFSRAM.Tables L G c) : DFSRAM.Tables L G (run cachedItem c) :=
  ht.mem_congr (run_mem_frame _ _ (by decide))

end STACS2027.Embed.PlanRAM
