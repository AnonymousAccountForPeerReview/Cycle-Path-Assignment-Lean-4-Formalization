module

public import ApproximationHardness.Embed.PlanVertexRAM
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-! The distinguished-dart scan realizes the forest plan's exact three-slot choice. -/

@[expose] public section

set_option maxHeartbeats 1500000

namespace STACS2027.Embed.PlanRAM

open RAM

theorem distinguishedRAM_run_skip (c : Config) : run .skip c = c := rfl

attribute [local simp] zBase vertex degree vertexParent dart opposite child childParent
  itemType itemValue distinguished vertexBound partCount topVertex remaining slot
  address test otherTest exclusion representative constant

/-- For a dart at a fixed vertex, cached item type and parent equality identify tree darts. -/
theorem tree_cached {G : DG} {s : DS} {r d : Nat} (hd : d ∈ G.darts r) :
    (G.fd s).IsTree d ↔ RAMSolver.itemType ((G.fd s).item d) = 0 ∨ d = s.par r := by
  obtain ⟨hdb, hdr⟩ := DG.mem_darts.mp hd
  have hup : (G.fd s).IsUp d ↔ d = s.par r := by
    simp only [ForestData.IsUp, ForestData.IsRoot, DG.fd, hdr]
    omega
  have hdown : RAMSolver.itemType ((G.fd s).item d) = 0 ↔ (G.fd s).IsDown d := by
    unfold ForestData.item
    split <;> simp_all [RAMSolver.itemType]
  simp only [ForestData.IsTree, hup, hdown]
  exact or_comm

/-- A single valid adjacency slot updates the remembered choice exactly for back darts. -/
theorem distinguishedSlot_value {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) {r k : Nat} (hr : r < 2 * G.E)
    (hk : k < 3) (hvalid : k < (G.darts r).length)
    (hv : c.reg vertex = r) (hp : c.reg vertexParent = s.par r) :
    let d := (G.darts r).getD k 0
    (run (distinguishedSlot k) c).reg distinguished =
      if (G.fd s).IsTree d then c.reg distinguished else d := by
  let d := (G.darts r).getD k 0
  have hmem : d ∈ G.darts r := DG.getD_mem hvalid
  have hdb : d < 2 * G.E := (DG.mem_darts.mp hmem).1
  let c₁ := run (readForest dart (3+k) vertex) c
  let c₂ := run cachedItem c₁
  have hc₁ := hc.readForest dart (3+k) vertex (by decide)
  have hc₂ := hc₁.cachedItem
  have hd₁ : c₁.reg dart = d := by
    have hx := hc.tables.adjacent k hk r hr
    simpa [c₁, readForest, run, seqs, hv, hc.forest.bases.2.2.2.2.2 (3+k) (by omega), DFSRAM.Layout.cell, d] using hx
  obtain ⟨_, _, _, ht₂, _⟩ := cachedItem_values hc₁.forest hc₁.tables hG hdb hd₁
  have hd₂ : c₂.reg dart = d := (cachedItem_frame c₁ dart (by decide)).trans hd₁
  have hp₂ : c₂.reg vertexParent = s.par r := by
    rw [show c₂.reg vertexParent = c₁.reg vertexParent from cachedItem_frame c₁ vertexParent (by decide)]
    simpa [c₁, readForest, run, seqs] using hp
  have hz₂ : c₂.reg distinguished = c.reg distinguished := by
    rw [show c₂.reg distinguished = c₁.reg distinguished from cachedItem_frame c₁ distinguished (by decide)]
    simp [c₁, readForest, run, seqs]
  have htree := tree_cached (s := s) hmem
  change (run (.ifz itemType .skip (seqs [.sub test dart vertexParent, .sub otherTest vertexParent dart,
    .add test test otherTest, .ifz test .skip (.add distinguished dart 0)])) c₂).reg distinguished =
    if (G.fd s).IsTree d then c.reg distinguished else d
  change c₂.reg itemType = RAMSolver.itemType ((G.fd s).item d) at ht₂
  have hzero : c₂.reg 0 = 0 := hc₂.forest.bases.1
  by_cases ht : RAMSolver.itemType ((G.fd s).item d) = 0
  · have hT : (G.fd s).IsTree d := htree.mpr (Or.inl ht)
    simp [run, seqs, ht₂, ht, hT, hz₂]
  · by_cases he : d = s.par r
    · have hT : (G.fd s).IsTree d := htree.mpr (Or.inr he)
      rw [if_pos hT]
      simp [run, seqs, ht₂, ht, hd₂, hp₂, hz₂, he]
    · have hT : ¬ (G.fd s).IsTree d := by intro h; rcases htree.mp h with h | h <;> contradiction
      have hdiff : ¬ (d - s.par r = 0 ∧ s.par r - d = 0) := by omega
      simp [run, seqs, ht₂, ht, hd₂, hp₂, hz₂, hzero, hT, hdiff]



/-- A distinguished-slot scan protects the fixed vertex and its parent value. -/
theorem distinguishedSlot_frame (c : Config) (k r : Nat)
    (hr : r ∉ [284,285,286,287,288,289,290,300,301,302]) :
    (run (distinguishedSlot k) c).reg r = c.reg r := by
  apply run_reg_frame
  have hw : (regsW (distinguishedSlot k)).all
      (fun q => decide (q ∈ [284,285,286,287,288,289,290,300,301,302])) = true := by
    simp [distinguishedSlot, cachedItem, readForest, seqs, regsW]
  intro hn
  exact hr (of_decide_eq_true ((List.all_eq_true.mp hw) r hn))

/-- Slot scanning is read-only and preserves the forest compilation context. -/
theorem Context.distinguishedSlot {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (k : Nat) : Context L G s (run (distinguishedSlot k) c) := by
  apply hc.readOnly (p := PlanRAM.distinguishedSlot k) (by simp [PlanRAM.distinguishedSlot, PlanRAM.cachedItem, PlanRAM.readForest, seqs, hasStore])
  have hw : (regsW (PlanRAM.distinguishedSlot k)).all (fun r => decide (281 ≤ r)) = true := by
    simp [PlanRAM.distinguishedSlot, PlanRAM.cachedItem, PlanRAM.readForest, seqs, regsW]
  intro r hn
  exact of_decide_eq_true ((List.all_eq_true.mp hw) r hn)

/-- The complete three-slot scan follows the forest's last-back-dart rule exactly. -/
theorem distinguishedScan_value {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) {r : Nat} (hr : r < 2 * G.E)
    (hthree : (G.darts r).length = 3) (hv : c.reg vertex = r) (hp : c.reg vertexParent = s.par r) :
    let p := seqs [readForest distinguished 5 vertex, distinguishedSlot 0, distinguishedSlot 1, distinguishedSlot 2]
    (run p c).reg distinguished = PlanCache.distinguished (G.fd s)
      ((G.darts r).getD 0 0) ((G.darts r).getD 1 0) ((G.darts r).getD 2 0) := by
  generalize he₀ : run (readForest distinguished 5 vertex) c = c₀
  have hc₀ : Context L G s c₀ := he₀ ▸ hc.readForest distinguished 5 vertex (by decide)
  have hinit : c₀.reg distinguished = (G.darts r).getD 2 0 := by
    rw [← he₀]
    have hx := hc.tables.adjacent 2 (by decide) r hr
    simpa [readForest, run, seqs, hv, hc.forest.bases.2.2.2.2.2 5 (by decide), DFSRAM.Layout.cell] using hx
  have hv₀ : c₀.reg vertex = r := by rw [← he₀]; simpa [readForest, run, seqs] using hv
  have hp₀ : c₀.reg vertexParent = s.par r := by rw [← he₀]; simpa [readForest, run, seqs] using hp
  have h₀ := distinguishedSlot_value hc₀ hG hr (k := 0) (by decide) (by omega) hv₀ hp₀
  generalize he₁ : run (distinguishedSlot 0) c₀ = c₁
  rw [he₁] at h₀
  have hc₁ : Context L G s c₁ := he₁ ▸ hc₀.distinguishedSlot 0
  have hv₁ : c₁.reg vertex = r := by rw [← he₁]; exact (distinguishedSlot_frame c₀ 0 vertex (by decide)).trans hv₀
  have hp₁ : c₁.reg vertexParent = s.par r := by rw [← he₁]; exact (distinguishedSlot_frame c₀ 0 vertexParent (by decide)).trans hp₀
  have h₁ := distinguishedSlot_value hc₁ hG hr (k := 1) (by decide) (by omega) hv₁ hp₁
  generalize he₂ : run (distinguishedSlot 1) c₁ = c₂
  rw [he₂] at h₁
  have hc₂ : Context L G s c₂ := he₂ ▸ hc₁.distinguishedSlot 1
  have hv₂ : c₂.reg vertex = r := by rw [← he₂]; exact (distinguishedSlot_frame c₁ 1 vertex (by decide)).trans hv₁
  have hp₂ : c₂.reg vertexParent = s.par r := by rw [← he₂]; exact (distinguishedSlot_frame c₁ 1 vertexParent (by decide)).trans hp₁
  have h₂ := distinguishedSlot_value hc₂ hG hr (k := 2) (by decide) (by omega) hv₂ hp₂
  simp only [seqs, run_seq, distinguishedRAM_run_skip] at ⊢
  rw [he₀, he₁, he₂, h₂, h₁, h₀, hinit]
  by_cases ha : (G.fd s).IsTree ((G.darts r).getD 0 0) <;>
    by_cases hb : (G.fd s).IsTree ((G.darts r).getD 1 0) <;>
    by_cases hd : (G.fd s).IsTree ((G.darts r).getD 2 0)
  all_goals simp [PlanCache.distinguished, ha, hb, hd]

/-- Read-only prefix of the distinguished-dart program. -/
def distinguishedRead : Stmt := seqs [readForest degree 2 vertex,
  readForest vertexParent 6 vertex, .const constant 3,
  .sub test degree constant, .sub otherTest constant degree, .add test test otherTest,
  .ifz test (seqs [readForest distinguished 5 vertex,
    distinguishedSlot 0, distinguishedSlot 1, distinguishedSlot 2])
    (.add distinguished DFSRAM.dartCount 0)]

theorem distinguishedProgram_run (c : Config) :
    run distinguishedProgram c = run (zStore vertex distinguished) (run distinguishedRead c) := by
  simp [distinguishedProgram, distinguishedRead, seqs, run]

theorem distinguishedRead_frame (c : Config) (r : Nat)
    (hr : r ∉ [282,283,284,285,286,287,288,289,290,300,301,302,305]) :
    (run distinguishedRead c).reg r = c.reg r := by
  apply run_reg_frame
  have hw : (regsW distinguishedRead).all
      (fun q => decide (q ∈ [282,283,284,285,286,287,288,289,290,300,301,302,305])) = true := by decide
  intro hn
  exact hr (of_decide_eq_true ((List.all_eq_true.mp hw) r hn))

theorem Context.distinguishedRead {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) : Context L G s (run distinguishedRead c) := by
  apply hc.readOnly (p := PlanRAM.distinguishedRead)
    (by simp [PlanRAM.distinguishedRead, PlanRAM.distinguishedSlot, PlanRAM.cachedItem, PlanRAM.readForest, seqs, hasStore])
  have hw : (regsW PlanRAM.distinguishedRead).all (fun r => decide (281 ≤ r)) = true := by decide
  intro r hn
  exact of_decide_eq_true ((List.all_eq_true.mp hw) r hn)

/-- The scan computes the plan's distinguished dart, including the sentinel at all lower degrees. -/
theorem distinguishedRead_value {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) (hF : (G.fd s).Valid) {r : Nat}
    (hr : r < 2 * G.E) (hv : c.reg vertex = r) :
    (run distinguishedRead c).reg distinguished = (G.fd s).zOf r := by
  let init := seqs [readForest degree 2 vertex, readForest vertexParent 6 vertex,
    .const constant 3, .sub test degree constant, .sub otherTest constant degree,
    .add test test otherTest]
  let c₀ := run init c
  have hc₀ : Context L G s c₀ := by
    apply hc.readOnly (p := init) (by simp [init, readForest, seqs, hasStore])
    intro i hi
    simp [init, readForest, seqs, regsW] at hi
    omega
  have hv₀ : c₀.reg vertex = r := by simp [c₀, init, readForest, seqs, run, hv]
  have hp₀ : c₀.reg vertexParent = s.par r := by
    have hp := hc.forest.parents r hr
    simpa [c₀, init, readForest, seqs, run, hv, hc.forest.bases.2.2.2.2.2 6 (by decide), DFSRAM.Layout.cell] using hp
  have ht₀ : c₀.reg test = ((G.darts r).length - 3) + (3 - (G.darts r).length) := by
    have hd := hc.tables.degrees r hr
    simp only [DFSRAM.Layout.cell] at hd
    simp [c₀, init, readForest, seqs, run, hv, hc.forest.bases.2.2.2.2.2 2 (by decide), DFSRAM.Layout.cell, hd]
  have hzero : c₀.reg 0 = 0 := hc₀.forest.bases.1
  have hD : c₀.reg DFSRAM.dartCount = 2 * G.E := hc₀.forest.bases.2.2.1
  rw [PlanCache.zOf_from_slots hF]
  change (run (.ifz test
    (seqs [readForest distinguished 5 vertex, distinguishedSlot 0, distinguishedSlot 1, distinguishedSlot 2])
    (.add distinguished DFSRAM.dartCount 0)) c₀).reg distinguished =
    if (G.darts r).length = 3 then PlanCache.distinguished (G.fd s)
      ((G.darts r).getD 0 0) ((G.darts r).getD 1 0) ((G.darts r).getD 2 0) else 2 * G.E
  by_cases hthree : (G.darts r).length = 3
  · have ht : c₀.reg test = 0 := by simp [ht₀, hthree]
    simp only [run_ifz, ht, ↓reduceIte, hthree]
    exact distinguishedScan_value hc₀ hG hr hthree hv₀ hp₀
  · have ht : c₀.reg test ≠ 0 := by rw [ht₀]; omega
    simp [run_ifz, ht, hthree, run, hD, hzero]

/-- The distinguished scan writes precisely its cache entry. -/
theorem distinguishedProgram_mem {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) (hF : (G.fd s).Valid) {r : Nat}
    (hr : r < 2 * G.E) (hv : c.reg vertex = r) :
    (run distinguishedProgram c).mem =
      upd c.mem ((solverLayout L).limit + r) ((G.fd s).zOf r) := by
  rw [distinguishedProgram_run, (zStore_raw _ vertex distinguished (by decide)).1,
    distinguishedRead_value hc hG hF hr hv]
  rw [distinguishedRead_frame c zBase (by decide), hc.zbase,
    distinguishedRead_frame c vertex (by decide), hv]
  congr 1
  exact run_mem_frame _ _ (by simp [distinguishedRead, distinguishedSlot, cachedItem, readForest, seqs, hasStore])

/-- Computing and storing a distinguished dart preserves the installed forest context. -/
theorem Context.distinguishedProgram {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) : Context L G s (run distinguishedProgram c) := by
  rw [distinguishedProgram_run]
  exact hc.distinguishedRead.zStore vertex distinguished (by decide)

/-- The distinguished scan leaves every mutable solver array initially zero. -/
theorem MutableZero.distinguishedProgram {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hz : MutableZero L c) (hc : Context L G s c) :
    MutableZero L (run distinguishedProgram c) := by
  rw [distinguishedProgram_run]
  have hz' : MutableZero L (run distinguishedRead c) := by
    intro j hj i hi
    rw [run_mem_frame _ _ (by simp [distinguishedRead, distinguishedSlot, cachedItem, readForest, seqs, hasStore])]
    exact hz j hj i hi
  exact hz'.zStore hc.distinguishedRead vertex distinguished (by decide)

end STACS2027.Embed.PlanRAM
