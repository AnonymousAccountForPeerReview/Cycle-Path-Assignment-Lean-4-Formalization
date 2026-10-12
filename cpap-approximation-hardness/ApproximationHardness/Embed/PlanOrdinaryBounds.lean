module

public import ApproximationHardness.Embed.PlanVertexHeaderBounds
import Lean.Elab.Tactic.Omega

/-! Actual bounded adjacency-slot and ordinary-node table construction. -/

@[expose] public section
namespace STACS2027.Embed.PlanRAM
open RAM

attribute [local simp] zBase vertex degree vertexParent dart opposite child childParent
  itemType itemValue distinguished vertexBound partCount topVertex remaining slot
  address test otherTest exclusion representative constant

theorem ordinaryBounds_run_skip (c : Config) : run .skip c=c := rfl
theorem ordinaryBounds_addr_append {S : Nat} (A B : List Stmt) (c : Config) :
    AddrOK S (seqs (A++B)) c ↔ AddrOK S (seqs A) c ∧ AddrOK S (seqs B) (run (seqs A) c) := by
  induction A generalizing c with
  | nil => simp [seqs,run]
  | cons a A ih => simp only [List.cons_append,seqs,addrOK_seq,run_seq,ih,and_assoc]

/-- Retaining either the first or second item always writes the same bounded node index. -/
theorem retainItem_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hv : c.reg vertex<L.width) : AddrOK (zLimit L) retainItem c := by
  have hlim : (solverLayout L).limit≤zLimit L := by dsimp [zLimit]; omega
  have hb (j : Nat) (hj : j<22) := hc.solver.2.2.2.2 j hj
  have ha (j : Nat) (hj : j<22) : (solverLayout L).cell j (c.reg vertex)<zLimit L :=
    ((solverLayout L).cell_lt hj hv).trans_le hlim
  simp only [RAMSolver.Layout.cell] at ha
  simp [retainItem,planStore,seqs,AddrOK,run,hb 17 (by decide),hb 18 (by decide),
    hb 19 (by decide),hb 20 (by decide),ha 17 (by decide),ha 18 (by decide),
    ha 19 (by decide),ha 20 (by decide)]

/-- A slot header protects the whole installed forest context. -/
theorem Context.slotHeader {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (k : Nat) : Context L G s (run (slotHeader k) c) := by
  apply hc.readOnly (p:=PlanRAM.slotHeader k) (by simp [PlanRAM.slotHeader,seqs,hasStore])
  intro r hr; simp [PlanRAM.slotHeader,seqs,regsW] at hr; omega

/-- Reading and comparing one cached dart protects every forest cache field. -/
theorem Context.slotCompare {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (k : Nat) : Context L G s (run (slotCompare k) c) := by
  apply hc.readOnly (p:=PlanRAM.slotCompare k) (by simp [PlanRAM.slotCompare,PlanRAM.readForest,seqs,hasStore])
  intro r hr; simp [PlanRAM.slotCompare,PlanRAM.readForest,seqs,regsW] at hr; omega

/-- A guarded slot protects the compilation context even when it appends an item. -/
theorem Context.partSlot {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (k : Nat) : Context L G s (run (partSlot k) c) := partSlot_context hc k

/-- The degree guard prevents decoding a nonexistent cached adjacency slot. -/
theorem partSlot_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) {r k : Nat} (hr : r<2*G.E) (hk : k<3)
    (hv : c.reg vertex=r) (hd : c.reg degree=(G.darts r).length) :
    AddrOK (zLimit L) (partSlot k) c := by
  let A : List Stmt := [.const constant k,.sub test degree constant]
  let B := [readForest dart (3+k) vertex,.sub test dart exclusion,
    .sub otherTest exclusion dart,.add test test otherTest]
  let tail : Stmt := .ifz test .skip (seqs [cachedItem,retainItem])
  change AddrOK (zLimit L) (seqs (A++[.ifz test .skip (seqs (B++[tail]))])) c
  rw [ordinaryBounds_addr_append]
  refine ⟨by simp [A,seqs,AddrOK],?_⟩
  generalize he₁ : run (seqs A) c=c₁
  have hc₁ : Context L G s c₁ := by change Context L G s c₁; rw [←he₁]; exact hc.slotHeader k
  have hv₁ : c₁.reg vertex=r := by rw [←he₁]; simp [A,seqs,run,hv]
  have ht₁ : c₁.reg test=(G.darts r).length-k := by rw [←he₁]; simp [A,seqs,run,hd]
  simp only [addrOK_seqs_cons,addrOK_seqs_nil,and_true,addrOK_ifz,addrOK_skip,implies_true,true_and]
  intro hn
  have hvalid : k<(G.darts r).length := by rw [ht₁] at hn; omega
  rw [ordinaryBounds_addr_append]
  refine ⟨?_,?_⟩
  · simp only [B,addrOK_seqs_cons]
    refine ⟨readForest_addrOK hc₁ _ _ _ (by omega) (by simpa [hv₁] using hr),?_⟩
    simp [seqs,AddrOK]
  · generalize he₂ : run (seqs B) c₁=c₂
    have hc₂ : Context L G s c₂ := by rw [←he₂]; exact hc₁.slotCompare k
    have hv₂ : c₂.reg vertex=r := by rw [←he₂]; simp [B,readForest,seqs,run,hv₁]
    have hd₂ : c₂.reg dart=(G.darts r).getD k 0 := by
      rw [←he₂]
      have hx := hc₁.tables.adjacent k hk r hr
      simp only [DFSRAM.Layout.cell] at hx
      simp [B,readForest,seqs,run,hv₁,hc₁.forest.bases.2.2.2.2.2 (3+k) (by omega),hx]
    have hdb : (G.darts r).getD k 0<2*G.E := (DG.mem_darts.mp (DG.getD_mem hvalid)).1
    simp only [addrOK_seqs_cons,addrOK_seqs_nil,and_true,tail,addrOK_ifz,addrOK_skip,implies_true,true_and]
    intro _
    refine ⟨cachedItem_plan_addrOK hc₂ hG hdb hd₂,?_⟩
    apply retainItem_addrOK hc₂.cachedItem
    rw [cachedItem_frame c₂ vertex (by decide),hv₂]
    exact hr.trans_le hc.dartCapacity

/-- The ordinary prefix only initializes a bounded node and then changes scratch scalars. -/
theorem ordinaryPrefix_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hv : c.reg vertex<L.width) :
    AddrOK (zLimit L) ordinaryPrefix c := by
  simp only [ordinaryPrefix,addrOK_seqs_cons]
  refine ⟨clearParts_plan_addrOK hc vertex (by decide) hv,?_⟩
  simp [seqs,AddrOK]

theorem Context.ordinaryPrefix {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) : Context L G s (run ordinaryPrefix c) := by
  let p := seqs [.const partCount 0,.sub test DFSRAM.dartCount vertexParent,
    .ifz test (.add exclusion distinguished 0) (.add exclusion vertexParent 0)]
  have hctx : Context L G s (run p (run (clearParts vertex) c)) := by
    apply (clearParts_context hc vertex (by decide)).readOnly (p:=p) (by decide)
    intro r hr; simp [p,seqs,regsW] at hr; omega
  exact hctx

theorem ordinaryPrefix_reg (c : Config) (r : Nat) (hr : r∉[292,300,301,303]) :
    (run ordinaryPrefix c).reg r=c.reg r := by
  apply run_reg_frame
  have hw : (regsW ordinaryPrefix).all (fun q => decide (q∈[292,300,301,303]))=true := by decide
  intro hn; exact hr (of_decide_eq_true ((List.all_eq_true.mp hw) r hn))

/-- All three guarded slots and the final count store are actual bounded accesses. -/
theorem ordinaryParts_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) {r : Nat} (hr : r<2*G.E)
    (hv : c.reg vertex=r) (hd : c.reg degree=(G.darts r).length) :
    AddrOK (zLimit L) ordinaryParts c := by
  let A := [clearParts vertex,.const partCount 0,.sub test DFSRAM.dartCount vertexParent,
    .ifz test (.add exclusion distinguished 0) (.add exclusion vertexParent 0)]
  let B := [partSlot 0,partSlot 1,partSlot 2,planStore 16 vertex partCount]
  change AddrOK (zLimit L) (seqs (A++B)) c
  rw [ordinaryBounds_addr_append]
  refine ⟨ordinaryPrefix_addrOK hc (by rw [hv];exact hr.trans_le hc.dartCapacity),?_⟩
  generalize he₀ : run (seqs A) c=c₀
  have hc₀ : Context L G s c₀ := he₀ ▸ hc.ordinaryPrefix
  have hv₀ : c₀.reg vertex=r := by rw [←he₀];exact (ordinaryPrefix_reg c vertex (by decide)).trans hv
  have hd₀ : c₀.reg degree=(G.darts r).length := by rw [←he₀];exact (ordinaryPrefix_reg c degree (by decide)).trans hd
  generalize he₁ : run (partSlot 0) c₀=c₁
  have hc₁ : Context L G s c₁ := he₁ ▸ hc₀.partSlot 0
  have hv₁ : c₁.reg vertex=r := by rw [←he₁];exact (partSlot_reg c₀ 0 vertex (by decide)).trans hv₀
  have hd₁ : c₁.reg degree=(G.darts r).length := by rw [←he₁];exact (partSlot_reg c₀ 0 degree (by decide)).trans hd₀
  generalize he₂ : run (partSlot 1) c₁=c₂
  have hc₂ : Context L G s c₂ := he₂ ▸ hc₁.partSlot 1
  have hv₂ : c₂.reg vertex=r := by rw [←he₂];exact (partSlot_reg c₁ 1 vertex (by decide)).trans hv₁
  have hd₂ : c₂.reg degree=(G.darts r).length := by rw [←he₂];exact (partSlot_reg c₁ 1 degree (by decide)).trans hd₁
  generalize he₃ : run (partSlot 2) c₂=c₃
  have hc₃ : Context L G s c₃ := he₃ ▸ hc₂.partSlot 2
  have hv₃ : c₃.reg vertex=r := by rw [←he₃];exact (partSlot_reg c₂ 2 vertex (by decide)).trans hv₂
  simp only [B,addrOK_seqs_cons,addrOK_seqs_nil,and_true,he₁,he₂,he₃]
  exact ⟨partSlot_addrOK hc₀ hG hr (by decide) hv₀ hd₀,
    partSlot_addrOK hc₁ hG hr (by decide) hv₁ hd₁,
    partSlot_addrOK hc₂ hG hr (by decide) hv₂ hd₂,
    planStore_addrOK hc₃ 16 vertex partCount (by decide) (by rw [hv₃];exact hr.trans_le hc.dartCapacity)⟩

/-- A fixed constant bounds the complete actual ordinary-node compilation. -/
theorem ordinaryParts_exec {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) {r : Nat} (hr : r<2*G.E)
    (hv : c.reg vertex=r) (hd : c.reg degree=(G.darts r).length) :
    ∃t,ExecB (zLimit L) ordinaryParts c t (run ordinaryParts c) ∧ t≤500 := by
  have hlp : LoopFree ordinaryParts := by
    simp [ordinaryParts,partSlot,cachedItem,retainItem,clearParts,planStore,readForest,seqs,LoopFree]
  have hs : size ordinaryParts≤500 := by decide
  exact ⟨_,execB_run _ hlp c (ordinaryParts_addrOK hc hG hr hv hd),(cost_le_size _ _).trans hs⟩

end STACS2027.Embed.PlanRAM
