module

public import ApproximationHardness.Embed.PlanPartsRAM
public import ApproximationHardness.Embed.PlanAddressRAM
import Lean.Elab.Tactic.Omega

/-! # Actual top-node plan-table refinement -/

@[expose] public section

namespace STACS2027.Embed.PlanRAM

open RAM

attribute [local simp] zBase vertex degree vertexParent dart opposite child childParent
  itemType itemValue distinguished vertexBound partCount topVertex remaining slot
  address test otherTest exclusion representative constant
attribute [local simp] DFSRAM.dartCount

def topPrepare : Stmt := seqs [clearParts topVertex,
  .sub test DFSRAM.dartCount vertexParent]

def topHead : Stmt := seqs [.const itemType 0,.add itemValue vertex 0,
  planStore 17 topVertex itemType,planStore 18 topVertex itemValue,
  .const partCount 1,.sub test DFSRAM.dartCount distinguished]

def topExtra : Stmt := seqs [.add dart distinguished 0,cachedItem,
  planStore 19 topVertex itemType,planStore 20 topVertex itemValue,.const partCount 2]

theorem run_topParts (c : Config) :
    run topParts c =
      let d := run topPrepare c
      if d.reg test=0 then
        let e := run topHead d
        run (planStore 16 topVertex partCount)
          (if e.reg test=0 then e else run topExtra e)
      else d := by
  simp [topParts,topPrepare,topHead,topExtra,seqs,run]

theorem topPrepare_regs (c : Config) :
    (run topPrepare c).reg test=c.reg DFSRAM.dartCount-c.reg vertexParent ∧
      ∀ r,r≠address → r≠test → (run topPrepare c).reg r=c.reg r := by
  constructor
  · simp [topPrepare,seqs,run,clearParts_reg]
  · intro r ha ht
    apply run_reg_frame
    simp [topPrepare,clearParts,planStore,seqs,regsW,ha,ht]

theorem topPrepare_mem (c : Config) :
    (run topPrepare c).mem=(run (clearParts topVertex) c).mem := by
  simp [topPrepare,seqs,run]

theorem topPrepare_context {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) : Context L G s (run topPrepare c) := by
  simpa [topPrepare,seqs,run] using
    (clearParts_context hc topVertex (by decide)).temp test
      ((run (clearParts topVertex) c).reg DFSRAM.dartCount-
        (run (clearParts topVertex) c).reg vertexParent) (by decide)

theorem topHead_regs (c : Config) (hz : c.reg 0=0) :
    (run topHead c).reg test=c.reg DFSRAM.dartCount-c.reg distinguished ∧
    (run topHead c).reg partCount=1 ∧
    ∀ r,r≠itemType → r≠itemValue → r≠address → r≠partCount → r≠test →
      (run topHead c).reg r=c.reg r := by
  refine ⟨?_,?_,?_⟩
  · simp [topHead,planStore,seqs,run]
  · simp [topHead,planStore,seqs,run]
  · intro r ht hv ha hn he
    simp [topHead,planStore,seqs,run,ht,hv,ha,hn,he,hz]

theorem topHead_mem {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) :
    (run topHead c).mem=
      upd (upd c.mem ((solverLayout L).cell 17 (c.reg topVertex)) 0)
        ((solverLayout L).cell 18 (c.reg topVertex)) (c.reg vertex) := by
  have hb (j : Nat) (hj : j<22) := hc.solver.2.2.2.2 j hj
  funext a
  simp [topHead,planStore,seqs,run,hc.solver.1,hb 17 (by decide),hb 18 (by decide),
    RAMSolver.Layout.cell,Config.setMem,upd]
  rfl

theorem topHead_context {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) : Context L G s (run topHead c) := by
  apply hc.memory
  · intro r hr
    apply run_reg_frame
    simp [topHead,planStore,seqs,regsW]
    omega
  · intro a ha
    rw [topHead_mem hc]
    have hn (j : Nat) : a≠(solverLayout L).cell j (c.reg topVertex) := by
      have := part_cell_after_forest L j (c.reg topVertex);omega
    simp [upd,hn]

theorem topExtra_regs (c : Config) :
    (run topExtra c).reg partCount=2 ∧
    ∀ r,r∉[dart,opposite,child,childParent,itemType,itemValue,partCount,address,test,otherTest] →
      (run topExtra c).reg r=c.reg r := by
  constructor
  · simp [topExtra,planStore,seqs,run]
  · intro r hr
    apply run_reg_frame
    simp_all [topExtra,cachedItem,readForest,planStore,seqs,regsW]

theorem topExtra_mem {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) (hd : c.reg distinguished<2*G.E) :
    (run topExtra c).mem=
      upd (upd c.mem ((solverLayout L).cell 19 (c.reg topVertex))
        (RAMSolver.itemType ((G.fd s).item (c.reg distinguished))))
        ((solverLayout L).cell 20 (c.reg topVertex))
        (RAMSolver.itemValue ((G.fd s).item (c.reg distinguished))) := by
  let d := c.setReg dart (c.reg distinguished)
  have hctx : Context L G s d := hc.temp dart _ (by decide)
  have hreg : d.reg dart=c.reg distinguished := by simp [d]
  have hv := cachedItem_values hctx.forest hctx.tables hG hd hreg
  have hm := run_mem_frame cachedItem d (by decide : hasStore cachedItem=false)
  have ht := cachedItem_frame d topVertex (by decide)
  have hb (j : Nat) (hj : j<22) := (hctx.cachedItem).solver.2.2.2.2 j hj
  funext a
  simp only [topExtra,seqs,run,hc.solver.1,Nat.add_zero]
  change (run (planStore 20 topVertex itemValue)
    (run (planStore 19 topVertex itemType) (run cachedItem d))).mem a=_
  simp [planStore,seqs,run,hb 19 (by decide),hb 20 (by decide),hv.2.2.2.1,
    hv.2.2.2.2,hm,ht,d,RAMSolver.Layout.cell,Config.setMem,upd]
  rfl

theorem topExtra_context {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) : Context L G s (run topExtra c) := by
  have h := ((hc.temp dart (c.reg distinguished) (by decide)).cachedItem).planStore
    19 topVertex itemType (by decide) (by decide)
  have h' := h.planStore 20 topVertex itemValue (by decide) (by decide)
  simpa [topExtra,seqs,run,hc.solver.1] using h'.temp partCount 2 (by decide)

theorem topHead_slots {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hv : c.reg topVertex<L.width)
    (hs : PartSlots (solverLayout L) c.mem (c.reg topVertex) []) :
    PartSlots (solverLayout L) (run topHead c).mem (c.reg topVertex)
      [.node (c.reg vertex)] := by
  rw [topHead_mem hc]
  simp only [PartSlots] at hs ⊢
  simpa [update_part_cell (solverLayout L) _ _ _ _ _ hv,
    RAMSolver.itemType,RAMSolver.itemValue] using hs.2.2

theorem topExtra_slots {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) (hv : c.reg topVertex<L.width)
    (hd : c.reg distinguished<2*G.E) (r : Nat)
    (hs : PartSlots (solverLayout L) c.mem (c.reg topVertex) [.node r]) :
    PartSlots (solverLayout L) (run topExtra c).mem (c.reg topVertex)
      [.node r,(G.fd s).item (c.reg distinguished)] := by
  rw [topExtra_mem hc hG hd]
  simp only [PartSlots] at hs ⊢
  simpa [update_part_cell (solverLayout L) _ _ _ _ _ hv] using And.intro hs.1 hs.2.1

theorem topCompletion_slots {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hv : c.reg topVertex<L.width) (xs : List Item)
    (hs : PartSlots (solverLayout L) c.mem (c.reg topVertex) xs)
    (hn : c.reg partCount=xs.length) :
    PartSlots (solverLayout L) (run (planStore 16 topVertex partCount) c).mem
        (c.reg topVertex) xs ∧
      (run (planStore 16 topVertex partCount) c).mem
        ((solverLayout L).cell 16 (c.reg topVertex))=xs.length := by
  rw [(planStore_raw _ 16 topVertex partCount (by decide)).1,
    hc.solver.2.2.2.2 16 (by decide)]
  change PartSlots (solverLayout L)
    (upd c.mem ((solverLayout L).cell 16 (c.reg topVertex)) (c.reg partCount))
    (c.reg topVertex) xs ∧ _
  constructor
  · simpa [PartSlots,update_part_cell (solverLayout L) _ _ _ _ _ hv] using hs
  · change upd c.mem ((solverLayout L).cell 16 (c.reg topVertex)) (c.reg partCount)
      ((solverLayout L).cell 16 (c.reg topVertex))=xs.length
    rw [upd_same,hn]

theorem topParts_reg (c : Config) (r : Nat)
    (hr : r∉[284,285,286,287,288,289,292,300,301,302]) :
    (run topParts c).reg r=c.reg r := by
  apply run_reg_frame
  simp_all [topParts,clearParts,cachedItem,readForest,planStore,seqs,regsW]

theorem topParts_context {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) : Context L G s (run topParts c) := by
  rw [run_topParts]
  dsimp only
  split
  · have h := topHead_context (topPrepare_context hc)
    split
    · exact h.planStore 16 topVertex partCount (by decide) (by decide)
    · exact (topExtra_context h).planStore 16 topVertex partCount (by decide) (by decide)
  · exact topPrepare_context hc

theorem ForestData.parts_top_nonroot {F : ForestData} {r : Nat}
    (hr : ¬F.IsRoot r) : F.parts (F.top r)=[] := by
  have hv : ¬F.IsVertex (F.top r) := by
    simp only [ForestData.IsVertex,ForestData.top]
    omega
  have ht : ¬F.IsTop (F.top r) := by
    simpa [ForestData.IsTop,ForestData.top] using
      (show ¬(F.IsVertex r ∧ F.IsRoot r) from fun h=>hr h.2)
  exact ForestData.parts_other hv ht

set_option maxHeartbeats 1200000 in
theorem topParts_values {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) {r : Nat}
    (hr : c.reg vertex=r) (hp : c.reg vertexParent=s.par r)
    (hz : c.reg distinguished=(G.fd s).zOf r)
    (ht : c.reg topVertex=2*G.E+r) (hv : (G.fd s).IsVertex r)
    (hwidth : 2*G.E+r<L.width) :
    PartSlots (solverLayout L) (run topParts c).mem (2*G.E+r)
        ((G.fd s).parts ((G.fd s).top r)) ∧
      (run topParts c).mem ((solverLayout L).cell 16 (2*G.E+r))=
        ((G.fd s).parts ((G.fd s).top r)).length := by
  let d := run topPrepare c
  have hd : Context L G s d := topPrepare_context hc
  have hdtop : d.reg topVertex=2*G.E+r := (topPrepare_regs c).2 _ (by decide) (by decide) |>.trans ht
  have hdvertex : d.reg vertex=r := (topPrepare_regs c).2 _ (by decide) (by decide) |>.trans hr
  have hdz : d.reg distinguished=(G.fd s).zOf r := (topPrepare_regs c).2 _ (by decide) (by decide) |>.trans hz
  have hdtest : d.reg test=2*G.E-s.par r := by
    rw [(topPrepare_regs c).1,hc.forest.bases.2.2.1,hp]
  have hs : PartSlots (solverLayout L) d.mem (2*G.E+r) [] ∧
      d.mem ((solverLayout L).cell 16 (2*G.E+r))=0 := by
    dsimp only [d]
    rw [topPrepare_mem]
    simpa only [ht] using clearParts_slots hc topVertex (by decide) (by rw [ht];exact hwidth)
  rw [run_topParts]
  dsimp only
  by_cases hroot : (G.fd s).IsRoot r
  · have htest : d.reg test=0 := by
      rw [hdtest];simp only [ForestData.IsRoot,DG.fd] at hroot;omega
    change (run topPrepare c).reg test=0 at htest
    simp only [htest,↓reduceIte]
    let e := run topHead d
    have he : Context L G s e := topHead_context hd
    have hetop : e.reg topVertex=2*G.E+r := (topHead_regs d hd.solver.1).2.2 _
      (by decide) (by decide) (by decide) (by decide) (by decide) |>.trans hdtop
    have hez : e.reg distinguished=(G.fd s).zOf r := (topHead_regs d hd.solver.1).2.2 _
      (by decide) (by decide) (by decide) (by decide) (by decide) |>.trans hdz
    have hetest : e.reg test=2*G.E-(G.fd s).zOf r := by
      rw [(topHead_regs d hd.solver.1).1,hdz,hd.forest.bases.2.2.1]
    have hes : PartSlots (solverLayout L) e.mem (2*G.E+r) [.node r] := by
      have := topHead_slots hd (by rw [hdtop];exact hwidth) (by rw [hdtop];exact hs.1)
      simpa only [hdtop,hdvertex] using this
    have hfe : (G.fd s).E=G.E := rfl
    rw [ForestData.parts_top hv hroot,hfe]
    by_cases hsmall : (G.fd s).zOf r<2*G.E
    · have hn : e.reg test≠0 := by rw [hetest];omega
      change (run topHead (run topPrepare c)).reg test≠0 at hn
      simp only [hn,↓reduceIte,hsmall]
      have hex : Context L G s (run topExtra e) := topExtra_context he
      have hxtop : (run topExtra e).reg topVertex=2*G.E+r :=
        (topExtra_regs e).2 _ (by decide) |>.trans hetop
      have hxs := topExtra_slots he hG (by rw [hetop];exact hwidth)
        (by rw [hez];exact hsmall) r (by rw [hetop];exact hes)
      have hout := topCompletion_slots hex (by rw [hxtop];exact hwidth)
        [.node r,(G.fd s).item ((G.fd s).zOf r)] (by simpa only [hxtop,hetop,hez] using hxs)
        (by simp only [(topExtra_regs e).1,List.length_cons,List.length_nil])
      simpa only [hxtop] using hout
    · have hezero : e.reg test=0 := by rw [hetest];omega
      change (run topHead (run topPrepare c)).reg test=0 at hezero
      simp only [hezero,↓reduceIte,hsmall]
      have hout := topCompletion_slots he (by rw [hetop];exact hwidth) [.node r]
        (by rw [hetop];exact hes) (by simpa only [List.length_cons,List.length_nil] using (topHead_regs d hd.solver.1).2.1)
      simpa only [hetop] using hout
  · have hn : d.reg test≠0 := by
      rw [hdtest];simp only [ForestData.IsRoot,DG.fd] at hroot;omega
    change (run topPrepare c).reg test≠0 at hn
    simp only [hn,↓reduceIte,ForestData.parts_top_nonroot hroot,List.length_nil]
    exact hs

theorem planStore_partFrame {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (j : Nat) (hj : 16≤j) (hj' : j≤20)
    (src : Nat) (hs : src≠address) :
    PartMemFrame (solverLayout L) (c.reg topVertex)
      (run (planStore j topVertex src) c).mem c.mem := by
  intro a ha
  rw [(planStore_raw c j topVertex src hs).1,hc.solver.2.2.2.2 j (by omega)]
  change upd c.mem ((solverLayout L).cell j (c.reg topVertex)) (c.reg src) a=c.mem a
  simp [upd,ha j hj hj']

theorem topPrepare_frame {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) :
    PartMemFrame (solverLayout L) (c.reg topVertex) (run topPrepare c).mem c.mem := by
  rw [topPrepare_mem]
  exact clearParts_memFrame hc topVertex (by decide)

theorem topHead_frame {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) :
    PartMemFrame (solverLayout L) (c.reg topVertex) (run topHead c).mem c.mem := by
  intro a ha
  rw [topHead_mem hc]
  simp [upd,ha 17 (by decide) (by decide),ha 18 (by decide) (by decide)]

theorem topExtra_frame {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) :
    PartMemFrame (solverLayout L) (c.reg topVertex) (run topExtra c).mem c.mem := by
  let d := c.setReg dart (c.reg distinguished)
  let e := run cachedItem d
  have he : Context L G s e := (hc.temp dart (c.reg distinguished) (by decide)).cachedItem
  have htop : e.reg topVertex=c.reg topVertex := by
    rw [cachedItem_frame d topVertex (by decide)]
    simp [d]
  have hf1 := planStore_partFrame he 19 (by decide) (by decide) itemType (by decide)
  have he' : Context L G s (run (planStore 19 topVertex itemType) e) :=
    he.planStore 19 topVertex itemType (by decide) (by decide)
  have hf2 := planStore_partFrame he' 20 (by decide) (by decide) itemValue (by decide)
  have htop' : (run (planStore 19 topVertex itemType) e).reg topVertex=c.reg topVertex :=
    (planStore_raw e 19 topVertex itemType (by decide)).2.1 _ (by decide) |>.trans htop
  have hm : e.mem=c.mem := by
    rw [run_mem_frame cachedItem d (by decide)]
    rfl
  intro a ha
  simp only [topExtra,seqs,run,hc.solver.1,Nat.add_zero]
  change (run (planStore 20 topVertex itemValue)
    (run (planStore 19 topVertex itemType) e)).mem a=c.mem a
  rw [hf2 a (by simpa only [htop'] using ha),hf1 a (by simpa only [htop] using ha),hm]

theorem topParts_frame {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) :
    PartMemFrame (solverLayout L) (c.reg topVertex) (run topParts c).mem c.mem := by
  rw [run_topParts]
  dsimp only
  have h0 := topPrepare_context hc
  have hf0 := topPrepare_frame hc
  have ht0 : (run topPrepare c).reg topVertex=c.reg topVertex :=
    (topPrepare_regs c).2 _ (by decide) (by decide)
  split
  · have h1 := topHead_context h0
    have hf1 : PartMemFrame (solverLayout L) (c.reg topVertex)
        (run topHead (run topPrepare c)).mem c.mem := by
      have h : PartMemFrame (solverLayout L) (c.reg topVertex)
          (run topHead (run topPrepare c)).mem (run topPrepare c).mem := by
        simpa only [ht0] using topHead_frame h0
      exact h.trans hf0
    have ht1 : (run topHead (run topPrepare c)).reg topVertex=c.reg topVertex :=
      (topHead_regs _ h0.solver.1).2.2 _ (by decide) (by decide) (by decide)
        (by decide) (by decide) |>.trans ht0
    split
    · have h : PartMemFrame (solverLayout L) (c.reg topVertex)
          (run (planStore 16 topVertex partCount) (run topHead (run topPrepare c))).mem
          (run topHead (run topPrepare c)).mem := by
        simpa only [ht1] using
          planStore_partFrame h1 16 (by decide) (by decide) partCount (by decide)
      exact h.trans hf1
    · have h2 := topExtra_context h1
      have hf2 : PartMemFrame (solverLayout L) (c.reg topVertex)
          (run topExtra (run topHead (run topPrepare c))).mem c.mem := by
        have h : PartMemFrame (solverLayout L) (c.reg topVertex)
            (run topExtra (run topHead (run topPrepare c))).mem
            (run topHead (run topPrepare c)).mem := by
          simpa only [ht1] using topExtra_frame h1
        exact h.trans hf1
      have ht2 : (run topExtra (run topHead (run topPrepare c))).reg topVertex=c.reg topVertex :=
        (topExtra_regs _).2 _ (by decide) |>.trans ht1
      have h : PartMemFrame (solverLayout L) (c.reg topVertex)
          (run (planStore 16 topVertex partCount)
            (run topExtra (run topHead (run topPrepare c)))).mem
          (run topExtra (run topHead (run topPrepare c))).mem := by
        simpa only [ht2] using
          planStore_partFrame h2 16 (by decide) (by decide) partCount (by decide)
      exact h.trans hf2
  · exact hf0

theorem topParts_mutable {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hz : MutableZero L c) (hv : c.reg topVertex<L.width) :
    MutableZero L (run topParts c) := by
  intro j hj i hi
  rw [topParts_frame hc]
  · exact hz j hj i hi
  · intro k hk hk' he
    have := (solverLayout L).cell_injective hi hv he
    omega

theorem topParts_out (c : Config) : (run topParts c).out=c.out :=
  run_out_frame _ _ (by decide)

theorem clearTop_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hv : c.reg topVertex<L.width) :
    AddrOK (zLimit L) (clearParts topVertex) c := by
  have hb (j : Nat) (hj : j<22) := hc.solver.2.2.2.2 j hj
  have ha (j : Nat) (hj : j<22) : (solverLayout L).block j+c.reg topVertex<zLimit L := by
    have hcell := (solverLayout L).cell_lt hj hv
    change (solverLayout L).block j+c.reg topVertex<(solverLayout L).limit at hcell
    change (solverLayout L).block j+c.reg topVertex<(solverLayout L).limit+L.width
    omega
  simp [clearParts,planStore,seqs,AddrOK,run,hb 16 (by decide),hb 17 (by decide),
    hb 18 (by decide),hb 19 (by decide),hb 20 (by decide),ha 16 (by decide),
    ha 17 (by decide),ha 18 (by decide),ha 19 (by decide),ha 20 (by decide)]

theorem topPrepare_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hv : c.reg topVertex<L.width) :
    AddrOK (zLimit L) topPrepare c := by
  simpa only [topPrepare,addrOK_seqs_cons,addrOK_seqs_nil,addrOK_sub,true_and,and_true]
    using clearTop_addrOK hc hv

theorem topHead_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hv : c.reg topVertex<L.width) :
    AddrOK (zLimit L) topHead c := by
  have hb (j : Nat) (hj : j<22) := hc.solver.2.2.2.2 j hj
  have ha (j : Nat) (hj : j<22) : (solverLayout L).block j+c.reg topVertex<zLimit L := by
    have hcell := (solverLayout L).cell_lt hj hv
    change (solverLayout L).block j+c.reg topVertex<(solverLayout L).limit at hcell
    change (solverLayout L).block j+c.reg topVertex<(solverLayout L).limit+L.width
    omega
  simp [topHead,planStore,seqs,AddrOK,run,hb 17 (by decide),hb 18 (by decide),
    ha 17 (by decide),ha 18 (by decide)]

theorem topExtra_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) (hv : c.reg topVertex<L.width)
    (hd : c.reg distinguished<2*G.E) : AddrOK (zLimit L) topExtra c := by
  let d := c.setReg dart (c.reg distinguished)
  let e := run cachedItem d
  have hctx : Context L G s d := hc.temp dart _ (by decide)
  have hreg : d.reg dart=c.reg distinguished := by simp [d]
  have hlim : L.limit≤zLimit L := by
    dsimp [zLimit,solverLayout,RAMSolver.Layout.limit]
    omega
  have hcache := (cachedItem_addrOK hctx.forest hctx.tables hG hd hreg hc.dartCapacity).mono hlim
  have he : Context L G s e := hctx.cachedItem
  have hetop : e.reg topVertex=c.reg topVertex := by
    rw [cachedItem_frame d topVertex (by decide)]
    simp [d]
  have hs1 := planStore_addrOK he 19 topVertex itemType (by decide) (by rw [hetop];exact hv)
  have he' : Context L G s (run (planStore 19 topVertex itemType) e) :=
    he.planStore 19 topVertex itemType (by decide) (by decide)
  have htop' : (run (planStore 19 topVertex itemType) e).reg topVertex=c.reg topVertex :=
    (planStore_raw e 19 topVertex itemType (by decide)).2.1 _ (by decide) |>.trans hetop
  have hs2 := planStore_addrOK he' 20 topVertex itemValue (by decide) (by rw [htop'];exact hv)
  simp only [topExtra,addrOK_seqs_cons,addrOK_seqs_nil,addrOK_add,addrOK_const,true_and,and_true]
  change AddrOK (zLimit L) cachedItem (c.setReg dart (c.reg distinguished+c.reg 0)) ∧
    AddrOK (zLimit L) (planStore 19 topVertex itemType)
      (run cachedItem (c.setReg dart (c.reg distinguished+c.reg 0))) ∧
    AddrOK (zLimit L) (planStore 20 topVertex itemValue)
      (run (planStore 19 topVertex itemType)
        (run cachedItem (c.setReg dart (c.reg distinguished+c.reg 0))))
  simp only [hc.solver.1,Nat.add_zero]
  exact ⟨hcache,hs1,hs2⟩

theorem topParts_loopFree : LoopFree topParts := by
  simp [topParts,clearParts,cachedItem,readForest,planStore,seqs,LoopFree]

theorem topParts_size : size topParts≤100 := by decide

set_option maxHeartbeats 1200000 in
theorem topParts_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) (hv : c.reg topVertex<L.width) :
    AddrOK (zLimit L) topParts c := by
  unfold topParts
  refine AddrOK.seq (clearTop_addrOK hc hv) ?_
  refine AddrOK.seq (AddrOK.of_memFree (by decide)) ?_
  refine AddrOK.seq ?_ (by trivial)
  apply AddrOK.ifz
  swap
  · intro _;trivial
  intro _
  let d := run topPrepare c
  have hd : Context L G s d := topPrepare_context hc
  have hdtop : d.reg topVertex=c.reg topVertex := (topPrepare_regs c).2 _ (by decide) (by decide)
  change AddrOK (zLimit L)
    (seqs ([.const itemType 0,.add itemValue vertex 0,
      planStore 17 topVertex itemType,planStore 18 topVertex itemValue,
      .const partCount 1,.sub test DFSRAM.dartCount distinguished] ++
      [.ifz test .skip topExtra,planStore 16 topVertex partCount])) d
  rw [addrOK_seqs_append]
  refine ⟨topHead_addrOK hd (by rw [hdtop];exact hv),?_⟩
  let e := run topHead d
  have he : Context L G s e := topHead_context hd
  have hetop : e.reg topVertex=c.reg topVertex := (topHead_regs d hd.solver.1).2.2 _
    (by decide) (by decide) (by decide) (by decide) (by decide) |>.trans hdtop
  have hez : e.reg distinguished=d.reg distinguished := (topHead_regs d hd.solver.1).2.2 _
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have hetest : e.reg test=2*G.E-e.reg distinguished := by
    rw [(topHead_regs d hd.solver.1).1,hd.forest.bases.2.2.1,hez]
  simp only [addrOK_seqs_cons,addrOK_seqs_nil,and_true]
  change AddrOK (zLimit L) (.ifz test .skip topExtra) e ∧
    AddrOK (zLimit L) (planStore 16 topVertex partCount) (run (.ifz test .skip topExtra) e)
  constructor
  · apply AddrOK.ifz
    · intro _;trivial
    · intro hn
      apply topExtra_addrOK he hG (by rw [hetop];exact hv)
      rw [hetest] at hn
      omega
  · by_cases hn : e.reg test=0
    · simpa only [run,hn,↓reduceIte] using
        planStore_addrOK he 16 topVertex partCount (by decide) (by rw [hetop];exact hv)
    · have htop : (run topExtra e).reg topVertex=c.reg topVertex :=
        (topExtra_regs e).2 _ (by decide) |>.trans hetop
      simpa only [run,hn,↓reduceIte] using
        planStore_addrOK (topExtra_context he) 16 topVertex partCount
          (by decide) (by rw [htop];exact hv)

theorem topParts_spec {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) (hv : c.reg topVertex<L.width) :
    ∃ t,ExecB (zLimit L) topParts c t (run topParts c) ∧ t≤100 := by
  exact ⟨_,execB_run _ topParts_loopFree c (topParts_addrOK hc hG hv),
    (cost_le_size _ _).trans topParts_size⟩

end STACS2027.Embed.PlanRAM
