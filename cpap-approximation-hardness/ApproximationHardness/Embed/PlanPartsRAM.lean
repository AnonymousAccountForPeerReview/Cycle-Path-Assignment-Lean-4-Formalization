module

public import ApproximationHardness.Embed.PlanVertexRAM
public import ApproximationHardness.Embed.DefaultReadyHelpers
import Mathlib.Data.List.GetD
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-! # Ordered at-most-two-item plan tables on the actual RAM -/

@[expose] public section

namespace STACS2027.Embed.PlanRAM

open RAM

attribute [local simp] zBase vertex degree vertexParent dart opposite child childParent
  itemType itemValue distinguished vertexBound partCount topVertex remaining slot
  address test otherTest exclusion representative constant

/-- The four item cells, with the specified empty-slot encoding. -/
def PartSlots (L : RAMSolver.Layout) (m : Nat → Nat) (v : Nat) (xs : List Item) : Prop :=
  m (L.cell 17 v)=RAMSolver.itemType (xs.getD 0 (.node 0)) ∧
  m (L.cell 18 v)=RAMSolver.itemValue (xs.getD 0 (.node 0)) ∧
  m (L.cell 19 v)=RAMSolver.itemType (xs.getD 1 (.node 0)) ∧
  m (L.cell 20 v)=RAMSolver.itemValue (xs.getD 1 (.node 0))

theorem update_part_cell (L : RAMSolver.Layout) (m : Nat → Nat) (j k v a : Nat)
    (hv : v<L.width) :
    upd m (L.cell j v) a (L.cell k v) = if k=j then a else m (L.cell k v) := by
  rw [RAMSolver.update_cell L m k j v v a hv hv]
  simp

theorem clearParts_mem {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (index : Nat) (hi : index≠address) :
    (run (clearParts index) c).mem =
      upd (upd (upd (upd (upd c.mem ((solverLayout L).cell 16 (c.reg index)) 0)
        ((solverLayout L).cell 17 (c.reg index)) 0)
        ((solverLayout L).cell 18 (c.reg index)) 0)
        ((solverLayout L).cell 19 (c.reg index)) 0)
        ((solverLayout L).cell 20 (c.reg index)) 0 := by
  have hb (j : Nat) (hj : j<22) := hc.solver.2.2.2.2 j hj
  funext a
  simp [clearParts,planStore,seqs,run,hi,hc.solver.1,hb 16 (by decide),
    hb 17 (by decide),hb 18 (by decide),hb 19 (by decide),hb 20 (by decide),
    RAMSolver.Layout.cell,Config.setMem,upd]
  rfl

theorem clearParts_slots {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (index : Nat) (hi : index≠address)
    (hv : c.reg index<L.width) :
    PartSlots (solverLayout L) (run (clearParts index) c).mem (c.reg index) [] ∧
      (run (clearParts index) c).mem ((solverLayout L).cell 16 (c.reg index))=0 := by
  rw [clearParts_mem hc index hi]
  simp [PartSlots,update_part_cell (solverLayout L) _ _ _ _ _ hv,RAMSolver.itemType,RAMSolver.itemValue]

theorem retainItem_mem {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) :
    (run retainItem c).mem =
      if c.reg partCount=0 then
        upd (upd c.mem ((solverLayout L).cell 17 (c.reg vertex)) (c.reg itemType))
          ((solverLayout L).cell 18 (c.reg vertex)) (c.reg itemValue)
      else
        upd (upd c.mem ((solverLayout L).cell 19 (c.reg vertex)) (c.reg itemType))
          ((solverLayout L).cell 20 (c.reg vertex)) (c.reg itemValue) := by
  have hb (j : Nat) (hj : j<22) := hc.solver.2.2.2.2 j hj
  by_cases hn : c.reg partCount=0
  all_goals funext a; simp [retainItem,planStore,seqs,run,hn,hb 17 (by decide),hb 18 (by decide),
    hb 19 (by decide),hb 20 (by decide),RAMSolver.Layout.cell,Config.setMem,upd]
  all_goals rfl

theorem retainItem_count {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) :
    (run retainItem c).reg partCount=c.reg partCount+1 := by
  by_cases hn : c.reg partCount=0
  all_goals simp [retainItem,planStore,seqs,run,hn,hc.solver.2.1]

theorem retainItem_slots {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) {xs : List Item} (hxs : xs.length≤1)
    (hv : c.reg vertex<L.width) (hn : c.reg partCount=xs.length)
    (hs : PartSlots (solverLayout L) c.mem (c.reg vertex) xs)
    (it : Item) (ht : c.reg itemType=RAMSolver.itemType it)
    (he : c.reg itemValue=RAMSolver.itemValue it) :
    PartSlots (solverLayout L) (run retainItem c).mem (c.reg vertex) (xs++[it]) := by
  rw [retainItem_mem hc,hn]
  cases xs with
  | nil =>
    simp only [PartSlots] at hs ⊢
    simpa [update_part_cell (solverLayout L) _ _ _ _ _ hv,ht,he,RAMSolver.itemType,RAMSolver.itemValue] using hs.2.2
  | cons x xs =>
    cases xs with
    | nil =>
      simp only [PartSlots] at hs ⊢
      simpa [update_part_cell (solverLayout L) _ _ _ _ _ hv,ht,he] using (And.intro hs.1 hs.2.1)
    | cons y ys => simp at hxs


theorem part_cell_after_forest (L : DFSRAM.Layout) (j v : Nat) :
    L.limit≤(solverLayout L).cell j v := by
  dsimp [solverLayout,RAMSolver.Layout.cell,RAMSolver.Layout.block]
  omega

theorem clearParts_context {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (index : Nat) (hi : index≠address) :
    Context L G s (run (clearParts index) c) := by
  apply hc.memory
  · intro r hr
    apply run_reg_frame
    simp [clearParts,planStore,seqs,regsW]
    omega
  · intro a ha
    rw [clearParts_mem hc index hi]
    have hn (j : Nat) : a≠(solverLayout L).cell j (c.reg index) := by
      have := part_cell_after_forest L j (c.reg index);omega
    simp [upd,hn]

theorem retainItem_context {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) : Context L G s (run retainItem c) := by
  apply hc.memory
  · intro r hr
    apply run_reg_frame
    simp [retainItem,planStore,seqs,regsW]
    omega
  · intro a ha
    rw [retainItem_mem hc]
    have hn (j : Nat) : a≠(solverLayout L).cell j (c.reg vertex) := by
      have := part_cell_after_forest L j (c.reg vertex);omega
    split <;> simp [upd,hn]

theorem clearParts_reg (c : Config) (index r : Nat) (hr : r≠address) :
    (run (clearParts index) c).reg r=c.reg r := by
  apply run_reg_frame
  simp [clearParts,planStore,seqs,regsW,hr]

theorem retainItem_reg (c : Config) (r : Nat) (hr : r≠address) (hn : r≠partCount) :
    (run retainItem c).reg r=c.reg r := by
  apply run_reg_frame
  simp [retainItem,planStore,seqs,regsW,hr,hn]

theorem clearParts_mutable {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hz : MutableZero L c) (index : Nat)
    (hi : index≠address) (hv : c.reg index<L.width) :
    MutableZero L (run (clearParts index) c) := by
  intro j hj i hindex
  rw [clearParts_mem hc index hi]
  simp only [RAMSolver.update_cell (solverLayout L) _ _ _ _ _ _ hindex hv]
  have hne : j≠16 ∧ j≠17 ∧ j≠18 ∧ j≠19 ∧ j≠20 := by omega
  simp only [hne.1,hne.2.1,hne.2.2.1,hne.2.2.2.1,hne.2.2.2.2,false_and,↓reduceIte]
  exact hz j hj i hindex

theorem retainItem_mutable {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hz : MutableZero L c) (hv : c.reg vertex<L.width) :
    MutableZero L (run retainItem c) := by
  intro j hj i hindex
  rw [retainItem_mem hc]
  have hne : j≠17 ∧ j≠18 ∧ j≠19 ∧ j≠20 := by omega
  split
  all_goals simp only [RAMSolver.update_cell (solverLayout L) _ _ _ _ _ _ hindex hv,
    hne.1,hne.2.1,hne.2.2.1,hne.2.2.2,false_and,↓reduceIte]
  all_goals exact hz j hj i hindex


/-- The scan state of an ordered part-list compiler. -/
structure PartsState (L : DFSRAM.Layout) (G : DG) (s : DS) (c : Config)
    (v excluded : Nat) (xs : List Item) : Prop where
  context : Context L G s c
  vreg : c.reg PlanRAM.vertex=v
  dreg : c.reg PlanRAM.degree=(G.darts v).length
  xreg : c.reg PlanRAM.exclusion=excluded
  count : c.reg partCount=xs.length
  slots : PartSlots (solverLayout L) c.mem v xs

theorem PartsState.readOnly {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    {v excluded : Nat} {xs : List Item} (h : PartsState L G s c v excluded xs)
    (p : Stmt) (hm : hasStore p=false)
    (hw : ∀ r,r∈regsW p → 281≤r)
    (hf : ∀ r,r∈[vertex,degree,exclusion,partCount] → r∉regsW p) :
    PartsState L G s (run p c) v excluded xs := by
  have hreg (r : Nat) (hr : r∈[vertex,degree,exclusion,partCount]) := run_reg_frame p c r (hf r hr)
  refine ⟨h.context.readOnly hm hw,
    (hreg _ (by simp)).trans h.vreg,(hreg _ (by simp)).trans h.dreg,
    (hreg _ (by simp)).trans h.xreg,(hreg _ (by simp)).trans h.count,?_⟩
  rw [run_mem_frame p c hm]
  exact h.slots

theorem PartsState.retain {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    {v excluded : Nat} {xs : List Item} (h : PartsState L G s c v excluded xs)
    (hv : v<L.width) (hn : xs.length≤1) (it : Item)
    (ht : c.reg itemType=RAMSolver.itemType it)
    (he : c.reg itemValue=RAMSolver.itemValue it) :
    PartsState L G s (run retainItem c) v excluded (xs++[it]) := by
  refine ⟨retainItem_context h.context,
    (retainItem_reg c _ (by decide) (by decide)).trans h.vreg,
    (retainItem_reg c _ (by decide) (by decide)).trans h.dreg,
    (retainItem_reg c _ (by decide) (by decide)).trans h.xreg,?_,?_⟩
  · rw [retainItem_count h.context,h.count,List.length_append]
    rfl
  · have hs : PartSlots (solverLayout L) c.mem (c.reg vertex) xs := by rw [h.vreg];exact h.slots
    have := retainItem_slots h.context hn (by rw [h.vreg];exact hv) h.count hs it ht he
    simpa only [h.vreg] using this

def slotHeader (k : Nat) : Stmt := seqs [.const constant k,.sub test degree constant]
def slotCompare (k : Nat) : Stmt := seqs [readForest dart (3+k) vertex,
  .sub test dart exclusion,.sub otherTest exclusion dart,.add test test otherTest]

theorem run_partSlot (k : Nat) (c : Config) :
    run (partSlot k) c =
      if c.reg degree-k=0 then run (slotHeader k) c else
        let d := run (slotCompare k) (run (slotHeader k) c)
        if d.reg test=0 then d else run retainItem (run cachedItem d) := by
  simp [partSlot,slotHeader,slotCompare,seqs,run]

theorem slotHeader_state {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    {v excluded : Nat} {xs : List Item} (h : PartsState L G s c v excluded xs) (k : Nat) :
    PartsState L G s (run (slotHeader k) c) v excluded xs := by
  apply h.readOnly (slotHeader k) (by simp [slotHeader,seqs,hasStore])
  · intro r hr;simp [slotHeader,seqs,regsW] at hr;omega
  · intro r hr;simp [slotHeader,seqs,regsW];simp only [List.mem_cons,List.mem_nil_iff,or_false,vertex,degree,exclusion,partCount] at hr;omega

theorem slotCompare_state {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    {v excluded : Nat} {xs : List Item} (h : PartsState L G s c v excluded xs) (k : Nat) :
    PartsState L G s (run (slotCompare k) c) v excluded xs := by
  apply h.readOnly (slotCompare k) (by simp [slotCompare,readForest,seqs,hasStore])
  · intro r hr;simp [slotCompare,readForest,seqs,regsW] at hr;omega
  · intro r hr;simp [slotCompare,readForest,seqs,regsW];simp only [List.mem_cons,List.mem_nil_iff,or_false,vertex,degree,exclusion,partCount] at hr;omega

theorem slotCompare_values {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    {v excluded : Nat} {xs : List Item} (h : PartsState L G s c v excluded xs)
    (k : Nat) (hk : k<3) (hv : v<2*G.E) :
    (run (slotCompare k) c).reg dart=(G.darts v).getD k 0 ∧
    (run (slotCompare k) c).reg test=
      (G.darts v).getD k 0-excluded+(excluded-(G.darts v).getD k 0) := by
  have hb := h.context.forest.bases.2.2.2.2.2 (3+k) (by omega)
  have ha := h.context.tables.adjacent k hk v hv
  simp only [DFSRAM.Layout.cell] at ha
  simp [slotCompare,readForest,seqs,run,h.vreg,h.xreg,hb,ha]

theorem cachedItem_state {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    {v excluded : Nat} {xs : List Item} (h : PartsState L G s c v excluded xs) :
    PartsState L G s (run cachedItem c) v excluded xs := by
  apply h.readOnly cachedItem (by decide)
  · intro r hr;simp [cachedItem,readForest,seqs,regsW] at hr;omega
  · intro r hr;simp [cachedItem,readForest,seqs,regsW];simp only [List.mem_cons,List.mem_nil_iff,or_false,vertex,degree,exclusion,partCount] at hr;omega

theorem partSlot_state {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    {v excluded : Nat} {xs : List Item} (h : PartsState L G s c v excluded xs)
    (hG : G.Ok) (k : Nat) (hk : k<3) (hv : v<2*G.E)
    (happend : k<(G.darts v).length → (G.darts v).getD k 0≠excluded → xs.length≤1) :
    PartsState L G s (run (partSlot k) c) v excluded
      (if k<(G.darts v).length ∧ (G.darts v).getD k 0≠excluded then
        xs++[(G.fd s).item ((G.darts v).getD k 0)] else xs) := by
  rw [run_partSlot,h.dreg]
  by_cases hklen : k<(G.darts v).length
  · have hn : (G.darts v).length-k≠0 := by omega
    rw [ite_eq_right hn]
    have h0 := slotHeader_state h k
    have h1 := slotCompare_state h0 k
    have hd := slotCompare_values h0 k hk hv
    by_cases he : (G.darts v).getD k 0=excluded
    · have hz : (run (slotCompare k) (run (slotHeader k) c)).reg test=0 := by rw [hd.2,he];omega
      rw [ite_eq_left hz]
      simpa only [hklen,he,ne_self_iff_false,and_false,ite_false] using h1
    · have hn' : (run (slotCompare k) (run (slotHeader k) c)).reg test≠0 := by rw [hd.2];omega
      rw [ite_eq_right hn']
      have hdl : (G.darts v).getD k 0<2*G.E :=
        ((DG.mem_darts (G:=G) (u:=v) (d:=(G.darts v).getD k 0)).mp (by
          rw [List.getD_eq_getElem (G.darts v) 0 hklen]
          exact List.getElem_mem hklen)).1
      have hvals := cachedItem_values h1.context.forest h1.context.tables hG hdl hd.1
      have h2 := cachedItem_state h1
      have hnew := h2.retain (hv.trans_le h.context.dartCapacity) (happend hklen he)
        ((G.fd s).item ((G.darts v).getD k 0)) hvals.2.2.2.1 hvals.2.2.2.2
      simpa only [ite_eq_left (And.intro hklen he)] using hnew
  · have hz : (G.darts v).length-k=0 := by omega
    rw [ite_eq_left hz]
    simpa [hklen] using slotHeader_state h k


/-- The ordered retained items in the first `k` cached adjacency slots. -/
def scanPrefix (F : ForestData) (ds : List Nat) (excluded k : Nat) : List Item :=
  ((ds.take k).filter (· != excluded)).map F.item

theorem scanPrefix_next (F : ForestData) (ds : List Nat) (excluded k : Nat) :
    scanPrefix F ds excluded (k+1) =
      if k<ds.length ∧ ds.getD k 0≠excluded then
        scanPrefix F ds excluded k++[F.item (ds.getD k 0)] else
        scanPrefix F ds excluded k := by
  by_cases hk : k<ds.length
  · by_cases he : ds.getD k 0=excluded
    · have he' : ds[k]=excluded := by simpa only [List.getD_eq_getElem ds 0 hk] using he
      rw [ite_eq_right (show ¬(k<ds.length ∧ ds.getD k 0≠excluded) by intro h;exact h.2 he)]
      rw [scanPrefix,List.take_succ_eq_append_getElem hk,List.filter_append,List.map_append]
      rw [he',List.filter_cons_of_neg (p:=fun x => x != excluded) (a:=excluded) (by simp),
        List.filter_nil,List.map_nil,List.append_nil]
      rfl
    · have he' : ds[k]≠excluded := by simpa only [List.getD_eq_getElem ds 0 hk] using he
      rw [ite_eq_left ⟨hk,he⟩,List.getD_eq_getElem ds 0 hk]
      rw [scanPrefix,List.take_succ_eq_append_getElem hk,List.filter_append,List.map_append]
      have hb : (ds[k] != excluded)=true := by simp only [bne_iff_ne];exact he'
      rw [List.filter_cons_of_pos (p:=fun x => x != excluded) (a:=ds[k]) hb,List.filter_nil,List.map_cons,List.map_nil]
      rfl
  · have hlen : ds.length≤k := by omega
    rw [ite_eq_right (by intro h;exact hk h.1)]
    unfold scanPrefix
    rw [List.take_of_length_le hlen,List.take_of_length_le (show ds.length≤k+1 by omega)]

theorem scanPrefix_bound (F : ForestData) (ds : List Nat) (excluded k : Nat)
    (h : ((ds.filter (· !=excluded)).map F.item).length≤2) :
    (scanPrefix F ds excluded k).length≤2 := by
  exact (((List.take_sublist k ds).filter _).map _).length_le.trans h

def ordinaryPrefix : Stmt := seqs [clearParts vertex,.const partCount 0,
  .sub test DFSRAM.dartCount vertexParent,
  .ifz test (.add exclusion distinguished 0) (.add exclusion vertexParent 0)]

theorem run_ordinaryParts (c : Config) : run ordinaryParts c =
    run (planStore 16 vertex partCount)
      (run (partSlot 2) (run (partSlot 1) (run (partSlot 0) (run ordinaryPrefix c)))) := by
  simp [ordinaryParts,ordinaryPrefix,seqs,run]

theorem ordinaryPrefix_state {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) {v : Nat} (hr : c.reg vertex=v)
    (hd : c.reg degree=(G.darts v).length) (hp : c.reg vertexParent=s.par v)
    (hz : c.reg distinguished=(G.fd s).zOf v) (hv : v<L.width) :
    PartsState L G s (run ordinaryPrefix c) v
      (if (G.fd s).IsRoot v then (G.fd s).zOf v else s.par v) [] := by
  let q := seqs [.const partCount 0,.sub test DFSRAM.dartCount vertexParent,
    .ifz test (.add exclusion distinguished 0) (.add exclusion vertexParent 0)]
  have hc' := clearParts_context hc vertex (by decide)
  have hq : Context L G s (run q (run (clearParts vertex) c)) := by
    apply hc'.readOnly (by decide)
    intro r hn;simp [q,seqs,regsW] at hn;omega
  have he : run ordinaryPrefix c=run q (run (clearParts vertex) c) := by
    simp [ordinaryPrefix,q,seqs,run]
  have hreg (r : Nat) (h : r≠300 ∧ r≠292 ∧ r≠301 ∧ r≠303) :
      (run ordinaryPrefix c).reg r=c.reg r := by
    apply run_reg_frame
    simp [ordinaryPrefix,clearParts,planStore,seqs,regsW]
    omega
  refine ⟨he.symm ▸ hq,(hreg _ (by decide)).trans hr,
    (hreg _ (by decide)).trans hd,?_,?_,?_⟩
  · have hD := hc.forest.bases.2.2.1
    simp only [DFSRAM.dartCount] at hD
    have hroot : (G.fd s).IsRoot v ↔ 2*G.E≤s.par v := by rfl
    by_cases ht : 2*G.E≤s.par v
    · have heq : 2*G.E-s.par v=0 := by omega
      simp [ordinaryPrefix,clearParts,planStore,seqs,run,DFSRAM.dartCount,hp,hD,heq,hroot,ht,hz,hc.solver.1]
    · have hne : 2*G.E-s.par v≠0 := by omega
      simp [ordinaryPrefix,clearParts,planStore,seqs,run,DFSRAM.dartCount,hp,hD,hne,hroot,ht,hc.solver.1]
  · simp [ordinaryPrefix,clearParts,planStore,seqs,run]
  · have hm : (run ordinaryPrefix c).mem=(run (clearParts vertex) c).mem := by
      rw [he];exact run_mem_frame _ _ (by decide)
    rw [hm,←hr]
    exact (clearParts_slots hc vertex (by decide) (by rw [hr];exact hv)).1

theorem ordinaryParts_scan {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) (hF : (G.fd s).Valid)
    {v : Nat} (hr : c.reg vertex=v) (hd : c.reg degree=(G.darts v).length)
    (hp : c.reg vertexParent=s.par v) (hz : c.reg distinguished=(G.fd s).zOf v)
    (hv : v<2*G.E) (hver : (G.fd s).IsVertex v) :
    PartsState L G s
      (run (partSlot 2) (run (partSlot 1) (run (partSlot 0) (run ordinaryPrefix c)))) v
      (if (G.fd s).IsRoot v then (G.fd s).zOf v else s.par v) ((G.fd s).parts v) := by
  let X := if (G.fd s).IsRoot v then (G.fd s).zOf v else s.par v
  let ds := G.darts v
  let F := G.fd s
  have hparts : F.parts v=((ds.filter (· !=X)).map F.item) := by
    rw [ForestData.parts_vertex hver]
    change ((G.darts v).erase X).map F.item=((ds.filter (· !=X)).map F.item)
    rw [DG.darts_nodup v |>.erase_eq_filter X]
  have hb : ((ds.filter (· !=X)).map F.item).length≤2 := by
    rw [←hparts];exact ForestData.real_parts_bound hF hv
  have h0 := ordinaryPrefix_state hc hr hd hp hz (hv.trans_le hc.dartCapacity)
  have hstep (k : Nat) (hk : k<3) {d : Config}
      (hs : PartsState L G s d v X (scanPrefix F ds X k)) :
      PartsState L G s (run (partSlot k) d) v X (scanPrefix F ds X (k+1)) := by
    rw [scanPrefix_next]
    apply partSlot_state hs hG k hk hv
    intro hlen hne
    have hn := scanPrefix_bound F ds X (k+1) hb
    rw [scanPrefix_next,ite_eq_left ⟨hlen,hne⟩,List.length_append,List.length_singleton] at hn
    omega
  have hs0 : PartsState L G s (run ordinaryPrefix c) v X (scanPrefix F ds X 0) := by
    simpa [scanPrefix] using h0
  have hs := hstep 2 (by decide) (hstep 1 (by decide) (hstep 0 (by decide) hs0))
  have hdeg : ds.length≤3 := hG.deg v
  have he : scanPrefix F ds X 3=F.parts v := by
    unfold scanPrefix
    rw [List.take_of_length_le hdeg,←hparts]
  simpa only [he] using hs


theorem ordinaryParts_values {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) (hF : (G.fd s).Valid)
    {v : Nat} (hr : c.reg vertex=v) (hd : c.reg degree=(G.darts v).length)
    (hp : c.reg vertexParent=s.par v) (hz : c.reg distinguished=(G.fd s).zOf v)
    (hv : v<2*G.E) (hver : (G.fd s).IsVertex v) :
    Context L G s (run ordinaryParts c) ∧
      PartSlots (solverLayout L) (run ordinaryParts c).mem v ((G.fd s).parts v) ∧
      (run ordinaryParts c).mem ((solverLayout L).cell 16 v)=((G.fd s).parts v).length := by
  have hs := ordinaryParts_scan hc hG hF hr hd hp hz hv hver
  rw [run_ordinaryParts]
  refine ⟨hs.context.planStore 16 vertex partCount (by decide) (by decide),?_,?_⟩
  · rw [(planStore_raw _ 16 vertex partCount (by decide)).1,
      hs.context.solver.2.2.2.2 16 (by decide),hs.vreg]
    change PartSlots (solverLayout L)
      (upd _ ((solverLayout L).cell 16 v) _) v ((G.fd s).parts v)
    simpa [PartSlots,update_part_cell (solverLayout L) _ _ _ _ _ (hv.trans_le hc.dartCapacity)] using hs.slots
  · rw [(planStore_raw _ 16 vertex partCount (by decide)).1,
      hs.context.solver.2.2.2.2 16 (by decide),hs.vreg]
    change upd _ ((solverLayout L).cell 16 v) _ ((solverLayout L).cell 16 v)=_
    rw [upd_same,hs.count]

/-- Agreement away from the five cells allocated to one node's parts. -/
def PartMemFrame (L : RAMSolver.Layout) (v : Nat) (m n : Nat → Nat) : Prop :=
  ∀ a,(∀ j,16≤j → j≤20 → a≠L.cell j v) → m a=n a

theorem PartMemFrame.trans {L : RAMSolver.Layout} {v : Nat} {m n p : Nat → Nat}
    (h : PartMemFrame L v m n) (h' : PartMemFrame L v n p) :
    PartMemFrame L v m p := fun a ha=>(h a ha).trans (h' a ha)

theorem clearParts_memFrame {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (index : Nat) (hi : index≠address) :
    PartMemFrame (solverLayout L) (c.reg index) (run (clearParts index) c).mem c.mem := by
  intro a ha
  rw [clearParts_mem hc index hi]
  simp [upd,ha 16 (by decide) (by decide),ha 17 (by decide) (by decide),
    ha 18 (by decide) (by decide),ha 19 (by decide) (by decide),ha 20 (by decide) (by decide)]

theorem retainItem_memFrame {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) :
    PartMemFrame (solverLayout L) (c.reg vertex) (run retainItem c).mem c.mem := by
  intro a ha
  rw [retainItem_mem hc]
  split
  all_goals simp [upd,ha 17 (by decide) (by decide),ha 18 (by decide) (by decide),
    ha 19 (by decide) (by decide),ha 20 (by decide) (by decide)]

theorem partSlot_memFrame {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    {v X : Nat} {xs : List Item} (hs : PartsState L G s c v X xs) (k : Nat) :
    PartMemFrame (solverLayout L) v (run (partSlot k) c).mem c.mem := by
  rw [run_partSlot]
  have h0 := slotHeader_state hs k
  have h1 := slotCompare_state h0 k
  have h2 := cachedItem_state h1
  have hm0 : (run (slotHeader k) c).mem=c.mem := run_mem_frame _ _ (by simp [slotHeader,seqs,hasStore])
  have hm1 : (run (slotCompare k) (run (slotHeader k) c)).mem=c.mem :=
    (run_mem_frame _ _ (by simp [slotCompare,readForest,seqs,hasStore])).trans hm0
  have hm2 : (run cachedItem (run (slotCompare k) (run (slotHeader k) c))).mem=c.mem :=
    (run_mem_frame _ _ (by decide)).trans hm1
  split
  · intro a _;exact congrFun hm0 a
  · dsimp only
    split
    · intro a _;exact congrFun hm1 a
    · have := retainItem_memFrame h2.context
      simpa only [h2.vreg,hm2] using this

theorem partSlot_mutable {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    {v X : Nat} {xs : List Item} (hs : PartsState L G s c v X xs)
    (hz : MutableZero L c) (hv : v<L.width) (k : Nat) :
    MutableZero L (run (partSlot k) c) := by
  intro j hj i hi
  have hf := partSlot_memFrame hs k
  rw [hf]
  · exact hz j hj i hi
  · intro b hb hb' he
    have := (solverLayout L).cell_injective hi hv he
    omega


theorem partSlot_context {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (k : Nat) : Context L G s (run (partSlot k) c) := by
  rw [run_partSlot]
  have h0 : Context L G s (run (slotHeader k) c) := by
    apply hc.readOnly (by simp [slotHeader,seqs,hasStore])
    intro r hr;simp [slotHeader,seqs,regsW] at hr;omega
  have h1 : Context L G s (run (slotCompare k) (run (slotHeader k) c)) := by
    apply h0.readOnly (by simp [slotCompare,readForest,seqs,hasStore])
    intro r hr;simp [slotCompare,readForest,seqs,regsW] at hr;omega
  split
  · exact h0
  · dsimp only
    split
    · exact h1
    · exact retainItem_context h1.cachedItem

theorem partSlot_reg (c : Config) (k r : Nat)
    (hr : r∉[284,285,286,287,288,289,292,300,301,302,305]) :
    (run (partSlot k) c).reg r=c.reg r := by
  apply run_reg_frame
  simp_all [partSlot,cachedItem,retainItem,planStore,readForest,seqs,regsW]

theorem partSlot_frame {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) {v : Nat} (hv : c.reg vertex=v) (k : Nat) :
    PartMemFrame (solverLayout L) v (run (partSlot k) c).mem c.mem := by
  rw [run_partSlot]
  have h0 : Context L G s (run (slotHeader k) c) := by
    apply hc.readOnly (by simp [slotHeader,seqs,hasStore])
    intro r hr;simp [slotHeader,seqs,regsW] at hr;omega
  have h1 : Context L G s (run (slotCompare k) (run (slotHeader k) c)) := by
    apply h0.readOnly (by simp [slotCompare,readForest,seqs,hasStore])
    intro r hr;simp [slotCompare,readForest,seqs,regsW] at hr;omega
  have hm0 : (run (slotHeader k) c).mem=c.mem := run_mem_frame _ _ (by simp [slotHeader,seqs,hasStore])
  have hm1 : (run (slotCompare k) (run (slotHeader k) c)).mem=c.mem :=
    (run_mem_frame _ _ (by simp [slotCompare,readForest,seqs,hasStore])).trans hm0
  have hm2 : (run cachedItem (run (slotCompare k) (run (slotHeader k) c))).mem=c.mem :=
    (run_mem_frame _ _ (by decide)).trans hm1
  split
  · intro a _;exact congrFun hm0 a
  · dsimp only
    split
    · intro a _;exact congrFun hm1 a
    · have hv2 : (run cachedItem (run (slotCompare k) (run (slotHeader k) c))).reg vertex=v := by
        rw [cachedItem_frame _ vertex (by decide)]
        simpa [slotCompare,slotHeader,readForest,seqs,run] using hv
      have := retainItem_memFrame h1.cachedItem
      simpa only [hv2,hm2] using this

theorem ordinaryParts_reg (c : Config) (r : Nat)
    (hr : r∉[284,285,286,287,288,289,292,300,301,302,303,305]) :
    (run ordinaryParts c).reg r=c.reg r := by
  apply run_reg_frame
  simp_all [ordinaryParts,partSlot,cachedItem,retainItem,clearParts,planStore,readForest,seqs,regsW]

theorem ordinaryParts_frame {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) {v : Nat} (hr : c.reg vertex=v)
    (hd : c.reg degree=(G.darts v).length) (hp : c.reg vertexParent=s.par v)
    (hz : c.reg distinguished=(G.fd s).zOf v) (hv : v<L.width) :
    PartMemFrame (solverLayout L) v (run ordinaryParts c).mem c.mem := by
  have hs0 := ordinaryPrefix_state hc hr hd hp hz hv
  have hc1 := partSlot_context hs0.context 0
  have hc2 := partSlot_context hc1 1
  have hc3 := partSlot_context hc2 2
  have hr1 := (partSlot_reg _ 0 vertex (by decide)).trans hs0.vreg
  have hr2 := (partSlot_reg _ 1 vertex (by decide)).trans hr1
  have hr3 := (partSlot_reg _ 2 vertex (by decide)).trans hr2
  have hf1 := partSlot_frame hs0.context hs0.vreg 0
  have hf2 := partSlot_frame hc1 hr1 1
  have hf3 := partSlot_frame hc2 hr2 2
  intro a ha
  rw [run_ordinaryParts,(planStore_raw _ 16 vertex partCount (by decide)).1,
    hc3.solver.2.2.2.2 16 (by decide),hr3]
  change upd _ ((solverLayout L).cell 16 v) _ a=c.mem a
  rw [upd,ite_eq_right (ha 16 (by decide) (by decide)),hf3 a ha,hf2 a ha,hf1 a ha]
  have hm : (run ordinaryPrefix c).mem=(run (clearParts vertex) c).mem := by
    let q := seqs [.const partCount 0,.sub test DFSRAM.dartCount vertexParent,
      .ifz test (.add exclusion distinguished 0) (.add exclusion vertexParent 0)]
    have he : run ordinaryPrefix c=run q (run (clearParts vertex) c) := by
      simp [ordinaryPrefix,q,seqs,run]
    rw [he]
    exact run_mem_frame _ _ (by decide)
  rw [hm]
  exact clearParts_memFrame hc vertex (by decide) a (by simpa only [hr] using ha)

theorem ordinaryParts_mutable {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hm : MutableZero L c) {v : Nat} (hr : c.reg vertex=v)
    (hd : c.reg degree=(G.darts v).length) (hp : c.reg vertexParent=s.par v)
    (hz : c.reg distinguished=(G.fd s).zOf v) (hv : v<L.width) :
    MutableZero L (run ordinaryParts c) := by
  intro j hj i hi
  rw [ordinaryParts_frame hc hr hd hp hz hv]
  · exact hm j hj i hi
  · intro k hk hk' he
    have := (solverLayout L).cell_injective hi hv he
    omega

end STACS2027.Embed.PlanRAM
