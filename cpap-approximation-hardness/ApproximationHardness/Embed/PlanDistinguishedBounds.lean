module

public import ApproximationHardness.Embed.PlanDistinguishedRAM
public import ApproximationHardness.Embed.PlanAddressRAM
import Lean.Elab.Tactic.Omega

/-! Bounded RAM execution of the distinguished-dart cache compiler. -/

@[expose] public section

namespace STACS2027.Embed.PlanRAM
open RAM

attribute [local simp] zBase vertex degree vertexParent dart opposite child childParent
  itemType itemValue distinguished vertexBound partCount topVertex remaining slot
  address test otherTest exclusion representative constant

theorem distinguishedBounds_run_skip (c : Config) : run .skip c = c := rfl

theorem distinguishedBounds_addr_append {S : Nat} (A B : List Stmt) (c : Config) :
    AddrOK S (seqs (A ++ B)) c ↔
      AddrOK S (seqs A) c ∧ AddrOK S (seqs B) (run (seqs A) c) := by
  induction A generalizing c with
  | nil => simp [seqs, run]
  | cons a A ih => simp only [List.cons_append, addrOK_seqs_cons, run_seq, seqs, addrOK_seq, ih, and_assoc]

/-- All three slots of a degree-three adjacency list are actual bounded reads. -/
theorem distinguishedScan_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) {r : Nat} (hr : r < 2 * G.E)
    (hthree : (G.darts r).length = 3) (hv : c.reg vertex = r) :
    AddrOK (zLimit L) (seqs [readForest distinguished 5 vertex,
      distinguishedSlot 0, distinguishedSlot 1, distinguishedSlot 2]) c := by
  generalize he₀ : run (readForest distinguished 5 vertex) c = c₀
  have hc₀ : Context L G s c₀ := he₀ ▸ hc.readForest distinguished 5 vertex (by decide)
  have hv₀ : c₀.reg vertex = r := by rw [← he₀]; simpa [readForest, run, seqs] using hv
  generalize he₁ : run (distinguishedSlot 0) c₀ = c₁
  have hc₁ : Context L G s c₁ := he₁ ▸ hc₀.distinguishedSlot 0
  have hv₁ : c₁.reg vertex = r := by rw [← he₁]; exact (distinguishedSlot_frame c₀ 0 vertex (by decide)).trans hv₀
  generalize he₂ : run (distinguishedSlot 1) c₁ = c₂
  have hc₂ : Context L G s c₂ := he₂ ▸ hc₁.distinguishedSlot 1
  have hv₂ : c₂.reg vertex = r := by rw [← he₂]; exact (distinguishedSlot_frame c₁ 1 vertex (by decide)).trans hv₁
  simp only [addrOK_seqs_cons, addrOK_seqs_nil, he₀, he₁, he₂, and_true]
  exact ⟨readForest_addrOK hc _ _ _ (by decide) (by simpa [hv] using hr),
    distinguishedSlot_addrOK hc₀ hG hr (by decide) (by omega) hv₀,
    distinguishedSlot_addrOK hc₁ hG hr (by decide) (by omega) hv₁,
    distinguishedSlot_addrOK hc₂ hG hr (by decide) (by omega) hv₂⟩

/-- The degree test only executes the three-slot branch when all three slots exist. -/
theorem distinguishedRead_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) {r : Nat} (hr : r < 2 * G.E)
    (hv : c.reg vertex = r) : AddrOK (zLimit L) distinguishedRead c := by
  let A := [readForest degree 2 vertex, readForest vertexParent 6 vertex,
    .const constant 3, .sub test degree constant, .sub otherTest constant degree,
    .add test test otherTest]
  let branch : Stmt := .ifz test (seqs [readForest distinguished 5 vertex,
    distinguishedSlot 0, distinguishedSlot 1, distinguishedSlot 2])
    (.add distinguished DFSRAM.dartCount 0)
  change AddrOK (zLimit L) (seqs (A ++ [branch])) c
  rw [distinguishedBounds_addr_append]
  refine ⟨?_, ?_⟩
  · have htwo := DFSRAM.Layout.cell_lt (L := L) (j := 2) (by decide) (i := r) (hr.trans_le hc.dartCapacity)
    have hsix := DFSRAM.Layout.cell_lt (L := L) (j := 6) (by decide) (i := r) (hr.trans_le hc.dartCapacity)
    have hlim : L.limit ≤ zLimit L := by dsimp [zLimit, solverLayout, RAMSolver.Layout.limit]; omega
    simp only [DFSRAM.Layout.cell] at htwo hsix
    simp [A, readForest, seqs, AddrOK, run, hv, hc.forest.bases.2.2.2.2.2 2 (by decide),
      hc.forest.bases.2.2.2.2.2 6 (by decide), htwo.trans_le hlim, hsix.trans_le hlim]
  · generalize he : run (seqs A) c = c₀
    have hc₀ : Context L G s c₀ := by
      rw [← he]
      apply hc.readOnly (p := seqs A) (by simp [A, readForest, seqs, hasStore])
      have hw : (regsW (seqs A)).all (fun r => decide (281 ≤ r)) = true := by decide
      intro r hn; exact of_decide_eq_true ((List.all_eq_true.mp hw) r hn)
    have hv₀ : c₀.reg vertex = r := by rw [← he]; simp [A, readForest, seqs, run, hv]
    have ht : c₀.reg test = ((G.darts r).length - 3) + (3 - (G.darts r).length) := by
      rw [← he]
      have hd := hc.tables.degrees r hr
      simp only [DFSRAM.Layout.cell] at hd
      simp [A, readForest, seqs, run, hv, hc.forest.bases.2.2.2.2.2 2 (by decide), hd]
    simp only [addrOK_seqs_cons, addrOK_seqs_nil, and_true, branch, addrOK_ifz]
    refine ⟨?_, ?_⟩
    · intro h
      have hs := distinguishedScan_addrOK hc₀ hG hr (by rw [ht] at h; omega) hv₀
      simpa only [addrOK_seqs_cons, addrOK_seqs_nil, and_true] using hs
    · simp [AddrOK]

/-- The entire distinguished cache instruction is bounded in the extended layout. -/
theorem distinguishedProgram_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) {r : Nat} (hr : r < 2 * G.E)
    (hv : c.reg vertex = r) : AddrOK (zLimit L) distinguishedProgram c := by
  let A := [readForest degree 2 vertex, readForest vertexParent 6 vertex, .const constant 3,
    .sub test degree constant, .sub otherTest constant degree, .add test test otherTest,
    .ifz test (seqs [readForest distinguished 5 vertex,
      distinguishedSlot 0, distinguishedSlot 1, distinguishedSlot 2])
      (.add distinguished DFSRAM.dartCount 0)]
  change AddrOK (zLimit L) (seqs (A ++ [zStore vertex distinguished])) c
  rw [distinguishedBounds_addr_append]
  refine ⟨distinguishedRead_addrOK hc hG hr hv, ?_⟩
  change AddrOK (zLimit L) (seqs [zStore vertex distinguished]) (run distinguishedRead c)
  simp only [addrOK_seqs_cons, addrOK_seqs_nil, and_true]
  apply zStore_addrOK hc.distinguishedRead
  rw [distinguishedRead_frame c vertex (by decide), hv]
  exact hr.trans_le hc.dartCapacity

/-- A fixed constant bounds the actual distinguished-dart cache execution. -/
theorem distinguishedProgram_exec {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) {r : Nat} (hr : r < 2 * G.E)
    (hv : c.reg vertex = r) :
    ∃ t, ExecB (zLimit L) distinguishedProgram c t (run distinguishedProgram c) ∧ t ≤ 200 := by
  have hlp : LoopFree distinguishedProgram := by simp [distinguishedProgram, distinguishedSlot, cachedItem, readForest, zStore, seqs, LoopFree]
  have hs : size distinguishedProgram ≤ 200 := by decide
  exact ⟨_, execB_run _ hlp c (distinguishedProgram_addrOK hc hG hr hv), (cost_le_size _ _).trans hs⟩

end STACS2027.Embed.PlanRAM
