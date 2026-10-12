module

public import ApproximationHardness.Embed.PlanStoreRAM
public import ApproximationHardness.Embed.PlanAddressRAM
public import ApproximationHardness.RAM.Pass
import Lean.Elab.Tactic.Omega

/-! # A bounded RAM scan compiling partner, target, and key tables -/

@[expose] public section

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace STACS2027.Embed.PlanRAM

open RAM

abbrev scanDart := 306
abbrev otherDart := 307
abbrev thisVertex := 308
abbrev otherVertex := 309
abbrev thisDepth := 310
abbrev otherDepth := 311
abbrev otherParent := 312
abbrev otherDistinguished := 313
abbrev targetValue := 314
abbrev keyValue := 315
abbrev comparison := 316
abbrev dartRemaining := 317
abbrev secondComparison := 319

attribute [local simp] scanDart otherDart thisVertex otherVertex thisDepth otherDepth
  otherParent otherDistinguished targetValue keyValue comparison dartRemaining secondComparison
  address zBase
  DFSRAM.dartCount

def dartProbe : Stmt := seqs [readForest otherDart 1 scanDart,
  readForest thisVertex 0 scanDart, readForest otherVertex 0 otherDart,
  readForest thisDepth 7 thisVertex, readForest otherDepth 7 otherVertex,
  readForest otherParent 6 otherVertex,
  .add address zBase otherVertex, .load otherDistinguished address]

def dartValues : Stmt := seqs [.sub comparison otherDepth thisDepth,
  .ifz comparison (.const targetValue 0) (.const targetValue 1),
  .add keyValue otherDepth 1, .sub comparison DFSRAM.dartCount otherParent,
  .ifz comparison (seqs [.sub comparison otherDart otherDistinguished,
    .sub secondComparison otherDistinguished otherDart,
    .add comparison comparison secondComparison,
    .ifz comparison (.const keyValue 0) .skip]) .skip]

def dartCommits : Stmt := seqs [planStore 13 scanDart otherDart,
  planStore 14 scanDart targetValue, planStore 12 scanDart keyValue]

def dartTableStep : Stmt := .seq dartProbe (.seq dartValues dartCommits)

def dartTableBody : Stmt := .seq dartTableStep
  (seqs [.add scanDart scanDart 1, .sub dartRemaining dartRemaining 1])

def dartTablesProgram : Stmt := .seq
  (seqs [.const scanDart 0, .add dartRemaining DFSRAM.dartCount 0])
  (.loop dartRemaining dartTableBody)

theorem Context.dartProbe_context {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) : Context L G s (run dartProbe c) := by
  apply hc.readOnly (by decide)
  intro r hr; simp [dartProbe, PlanRAM.readForest, seqs, regsW] at hr; omega

theorem Context.dartValues_context {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) : Context L G s (run dartValues c) := by
  apply hc.readOnly (by decide)
  intro r hr; simp [dartValues, seqs, regsW] at hr; omega

theorem dartProbe_raw {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) {d : Nat} (hd : d < 2 * G.E)
    (hreg : c.reg scanDart = d)
    (hz : ∀ r, r < 2 * G.E → c.mem (c.reg zBase + r) = (G.fd s).zOf r) :
    let out := run dartProbe c
    out.reg scanDart = d ∧ out.reg otherDart = pair d ∧
      out.reg thisDepth = s.depth (G.rep d) ∧
      out.reg otherDepth = s.depth (G.rep (pair d)) ∧
      out.reg otherParent = s.par (G.rep (pair d)) ∧
      out.reg otherDistinguished = (G.fd s).zOf (G.rep (pair d)) ∧
      out.mem = c.mem ∧ out.out = c.out := by
  have hb (j : Nat) (hj : j < 11) := hc.forest.bases.2.2.2.2.2 j hj
  have hp := hc.tables.partners d hd
  have hv := hc.tables.representatives d hd
  have hw := hc.tables.representatives (pair d) (pair_lt hd)
  have hvl := hG.rep_lt d hd
  have hwl := hG.rep_lt (pair d) (pair_lt hd)
  have hdp := hc.forest.depths _ hvl
  have hdq := hc.forest.depths _ hwl
  have hpar := hc.forest.parents _ hwl
  have hzz := hz _ hwl
  simp only [DFSRAM.Layout.cell] at hp hv hw hdp hdq hpar
  simp [dartProbe, readForest, seqs, run, hreg, hb 1 (by decide), hb 0 (by decide),
    hb 7 (by decide), hb 6 (by decide), hp, hv, hw, hdp, hdq, hpar, hzz]

theorem dartValues_raw (c : Config) :
    let out := run dartValues c
    out.reg targetValue = (if c.reg thisDepth < c.reg otherDepth then 1 else 0) ∧
      out.reg keyValue = (if c.reg DFSRAM.dartCount ≤ c.reg otherParent ∧
        c.reg otherDart = c.reg otherDistinguished then 0 else c.reg otherDepth + c.reg 1) ∧
      (∀ r, r ≠ comparison → r ≠ secondComparison → r ≠ targetValue → r ≠ keyValue →
        out.reg r = c.reg r) ∧ out.mem = c.mem ∧ out.out = c.out := by
  by_cases hlt : c.reg thisDepth < c.reg otherDepth
  all_goals by_cases hroot : c.reg DFSRAM.dartCount ≤ c.reg otherParent
  all_goals by_cases heq : c.reg otherDart = c.reg otherDistinguished
  all_goals
    have ht : c.reg otherDepth - c.reg thisDepth = 0 ↔ ¬ c.reg thisDepth < c.reg otherDepth := by omega
    have hp : c.reg DFSRAM.dartCount - c.reg otherParent = 0 ↔
      c.reg DFSRAM.dartCount ≤ c.reg otherParent := by omega
    have hb : (c.reg otherDart - c.reg otherDistinguished = 0 ∧
      c.reg otherDistinguished - c.reg otherDart = 0) ↔
        c.reg otherDart = c.reg otherDistinguished := by omega
    simp [dartValues, seqs, run, ht, hp, hb, hlt, hroot, heq]
    intro r h₁ h₂ h₃ h₄; simp [h₁,h₂,h₃,h₄]

theorem dartTableStep_context {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) : Context L G s (run dartTableStep c) := by
  simp only [dartTableStep, run, dartCommits, run_seqs_cons, run_seqs_nil]
  exact (((hc.dartProbe_context.dartValues_context).planStore 13 scanDart otherDart
    (by decide) (by decide)).planStore 14 scanDart targetValue (by decide) (by decide)).planStore
      12 scanDart keyValue (by decide) (by decide)

theorem dartTableStep_reg (c : Config) (r : Nat) (hr : r < 306 ∨ 319 < r)
    (ha : r ≠ address) : (run dartTableStep c).reg r = c.reg r := by
  apply run_reg_frame
  have h : (regsW dartTableStep).all (fun r => decide (r = 300 ∨ 306 ≤ r ∧ r ≤ 319)) = true := by decide
  intro hm; have := of_decide_eq_true ((List.all_eq_true.mp h) r hm); simp only [address] at ha; omega

theorem dartCommits_raw (c : Config) :
    (run dartCommits c).mem =
      upd (upd (upd c.mem (c.reg 63 + c.reg scanDart) (c.reg otherDart))
        (c.reg 64 + c.reg scanDart) (c.reg targetValue))
        (c.reg 62 + c.reg scanDart) (c.reg keyValue) ∧
      (∀ r, r ≠ address → (run dartCommits c).reg r = c.reg r) ∧
      (run dartCommits c).out = c.out := by
  refine ⟨?_, ?_, ?_⟩
  · funext a; simp [dartCommits, planStore, seqs, run, Config.setMem, upd]
  · intro r hr; simp [dartCommits, planStore, seqs, run, hr]
  · simp [dartCommits, planStore, seqs, run]

theorem dartTableStep_memory {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) {d : Nat} (hd : d < 2 * G.E)
    (hreg : c.reg scanDart = d)
    (hz : ∀ r, r < 2 * G.E → c.mem (c.reg zBase + r) = (G.fd s).zOf r) :
    (run dartTableStep c).mem =
      upd (upd (upd c.mem ((solverLayout L).cell 13 d) (pair d))
        ((solverLayout L).cell 14 d) (if (G.fd s).isIn d then 1 else 0))
        ((solverLayout L).cell 12 d) ((G.fd s).key d) := by
  let p := run dartProbe c
  let q := run dartValues p
  obtain ⟨Hscan, Hother, Hdepth, HotherDepth, Hpar, Hz, Hmem, _⟩ := dartProbe_raw hc hG hd hreg hz
  obtain ⟨Ht, Hkey, Hframe, Hqmem, _⟩ := dartValues_raw p
  have Hctx : Context L G s q := hc.dartProbe_context.dartValues_context
  have Hscanq : q.reg scanDart = d := (Hframe scanDart (by decide) (by decide) (by decide) (by decide)).trans Hscan
  have Hotherq : q.reg otherDart = pair d := (Hframe otherDart (by decide) (by decide) (by decide) (by decide)).trans Hother
  have Hcount : p.reg DFSRAM.dartCount = 2 * G.E := hc.dartProbe_context.forest.bases.2.2.1
  have Hone : p.reg 1 = 1 := hc.dartProbe_context.forest.bases.2.1
  have Htarget : q.reg targetValue = if (G.fd s).isIn d then 1 else 0 := by
    rw [Ht, Hdepth, HotherDepth]
    by_cases h : s.depth (G.rep d) < s.depth (G.rep (pair d)) <;>
      simp [ForestData.isIn, DG.fd, h]
  have Hkeyq : q.reg keyValue = (G.fd s).key d := by
    rw [Hkey, Hcount, Hpar, Hother, Hz, HotherDepth, Hone]
    rfl
  rw [show run dartTableStep c = run dartCommits q by rfl, (dartCommits_raw q).1,
    Hqmem, Hmem, Hctx.solver.2.2.2.2 13 (by decide),
    Hctx.solver.2.2.2.2 14 (by decide), Hctx.solver.2.2.2.2 12 (by decide),
    Hscanq, Hotherq, Htarget, Hkeyq]
  rfl

theorem dartTableStep_out (c : Config) : (run dartTableStep c).out = c.out :=
  run_out_frame _ _ (by decide)

theorem dartTableStep_loopFree : LoopFree dartTableStep := by
  simp [dartTableStep, dartProbe, dartValues, dartCommits, planStore, readForest, seqs, LoopFree]

theorem dartTableStep_size : size dartTableStep ≤ 100 := by decide

theorem dartProbe_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) {d : Nat} (hd : d < 2 * G.E)
    (hreg : c.reg scanDart = d) : AddrOK (zLimit L) dartProbe c := by
  have hb (j : Nat) (hj : j < 11) := hc.forest.bases.2.2.2.2.2 j hj
  have hp := hc.tables.partners d hd
  have hv := hc.tables.representatives d hd
  have hw := hc.tables.representatives (pair d) (pair_lt hd)
  have hvl := hG.rep_lt d hd
  have hwl := hG.rep_lt (pair d) (pair_lt hd)
  have hdp := hc.forest.depths _ hvl
  have hdq := hc.forest.depths _ hwl
  have hpar := hc.forest.parents _ hwl
  have hlim : L.limit ≤ zLimit L := by dsimp [zLimit,solverLayout,RAMSolver.Layout.limit]; omega
  have hcell (j i : Nat) (hj : j < 11) (hi : i < 2 * G.E) : L.block j + i < zLimit L :=
    (DFSRAM.Layout.cell_lt hj (hi.trans_le hc.dartCapacity)).trans_le hlim
  have hz : c.reg zBase + G.rep (pair d) < zLimit L := by
    rw [hc.zbase]; dsimp [zLimit]; have := hc.dartCapacity; omega
  simp only [DFSRAM.Layout.cell] at hp hv hw hdp hdq hpar
  simp [dartProbe, readForest, seqs, AddrOK, run, hreg, hb 1 (by decide), hb 0 (by decide),
    hb 7 (by decide), hb 6 (by decide), hp,hv,hw,hdp,hdq,hpar,hz,
    hcell 1 d (by decide) hd,hcell 0 d (by decide) hd,
    hcell 0 (pair d) (by decide) (pair_lt hd),
    hcell 7 (G.rep d) (by decide) hvl,hcell 7 (G.rep (pair d)) (by decide) hwl,
    hcell 6 (G.rep (pair d)) (by decide) hwl]

theorem dartCommits_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hi : c.reg scanDart < L.width) :
    AddrOK (zLimit L) dartCommits c := by
  let p := run (planStore 13 scanDart otherDart) c
  let q := run (planStore 14 scanDart targetValue) p
  have Hcp := hc.planStore 13 scanDart otherDart (by decide) (by decide)
  have Hcq := Hcp.planStore 14 scanDart targetValue (by decide) (by decide)
  have Hp : p.reg scanDart = c.reg scanDart := (planStore_raw c 13 scanDart otherDart (by decide)).2.1 _ (by decide)
  have Hq : q.reg scanDart = c.reg scanDart :=
    ((planStore_raw p 14 scanDart targetValue (by decide)).2.1 _ (by decide)).trans Hp
  simp only [dartCommits,addrOK_seqs_cons,addrOK_seqs_nil]
  exact ⟨planStore_addrOK hc _ _ _ (by decide) hi,
    planStore_addrOK Hcp _ _ _ (by decide) (by rw [Hp]; exact hi),
    planStore_addrOK Hcq _ _ _ (by decide) (by rw [Hq]; exact hi),trivial⟩

theorem dartTableStep_addrOK {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) {d : Nat} (hd : d < 2 * G.E)
    (hreg : c.reg scanDart = d) : AddrOK (zLimit L) dartTableStep c := by
  have Hscan : (run dartValues (run dartProbe c)).reg scanDart = d := by
    rw [(dartValues_raw _).2.2.1 scanDart (by decide) (by decide) (by decide) (by decide)]
    have H : (run dartProbe c).reg scanDart = c.reg scanDart := run_reg_frame _ _ _ (by decide)
    exact H.trans hreg
  exact ⟨dartProbe_addrOK hc hG hd hreg, AddrOK.of_memFree (by decide),
    dartCommits_addrOK hc.dartProbe_context.dartValues_context
      (by rw [Hscan]; exact hd.trans_le hc.dartCapacity)⟩

theorem dartTableStep_exec {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) {d : Nat} (hd : d < 2 * G.E)
    (hreg : c.reg scanDart = d) :
    ∃ t, ExecB (zLimit L) dartTableStep c t (run dartTableStep c) ∧ t ≤ 100 :=
  ⟨_,execB_run _ dartTableStep_loopFree c (dartTableStep_addrOK hc hG hd hreg),
    (cost_le_size _ _).trans dartTableStep_size⟩

structure DartPrefix (L : DFSRAM.Layout) (F : ForestData) (c : Config) (n : Nat) : Prop where
  keys : ∀ d,d<n → c.mem ((solverLayout L).cell 12 d)=F.key d
  partners : ∀ d,d<n → c.mem ((solverLayout L).cell 13 d)=pair d
  targets : ∀ d,d<n → c.mem ((solverLayout L).cell 14 d)=(if F.isIn d then 1 else 0)

def DartFrame (L : DFSRAM.Layout) (c d : Config) : Prop :=
  ∀ a,(∀ i,i<L.width → a≠(solverLayout L).cell 12 i ∧
    a≠(solverLayout L).cell 13 i ∧ a≠(solverLayout L).cell 14 i) → d.mem a=c.mem a

theorem dartTableStep_frame {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) {d : Nat} (hd : d < 2 * G.E)
    (hreg : c.reg scanDart = d)
    (hz : ∀ r,r<2*G.E → c.mem (c.reg zBase+r)=(G.fd s).zOf r) :
    DartFrame L c (run dartTableStep c) := by
  intro a ha
  obtain ⟨h₁,h₂,h₃⟩ := ha d (hd.trans_le hc.dartCapacity)
  rw [dartTableStep_memory hc hG hd hreg hz]
  simp [upd,h₁,h₂,h₃]

theorem dartTableStep_cell {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) {d : Nat} (hd : d < 2 * G.E)
    (hreg : c.reg scanDart = d)
    (hz : ∀ r,r<2*G.E → c.mem (c.reg zBase+r)=(G.fd s).zOf r)
    (j i : Nat) (hi : i<L.width) :
    (run dartTableStep c).mem ((solverLayout L).cell j i)=
      if j=12 ∧ i=d then (G.fd s).key d else
      if j=14 ∧ i=d then (if (G.fd s).isIn d then 1 else 0) else
      if j=13 ∧ i=d then pair d else c.mem ((solverLayout L).cell j i) := by
  rw [dartTableStep_memory hc hG hd hreg hz]
  rw [RAMSolver.update_cell (solverLayout L) _ j 12 i d _ hi (hd.trans_le hc.dartCapacity)]
  split
  · rfl
  · rw [RAMSolver.update_cell (solverLayout L) _ j 14 i d _ hi (hd.trans_le hc.dartCapacity)]
    split
    · rfl
    · rw [RAMSolver.update_cell (solverLayout L) _ j 13 i d _ hi (hd.trans_le hc.dartCapacity)]

theorem dartTableStep_prefix {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) {d : Nat} (hd : d < 2 * G.E)
    (hreg : c.reg scanDart = d)
    (hz : ∀ r,r<2*G.E → c.mem (c.reg zBase+r)=(G.fd s).zOf r)
    (hp : DartPrefix L (G.fd s) c d) : DartPrefix L (G.fd s) (run dartTableStep c) (d+1) := by
  refine ⟨?_,?_,?_⟩
  all_goals
    intro i hi
    have hwidth : i<L.width := by have := hc.dartCapacity; omega
    rw [dartTableStep_cell hc hG hd hreg hz _ i hwidth]
    by_cases he : i=d
    · simp [he]
    · simp only [show ¬(i=d) from he, and_false, ↓reduceIte]
      first | exact hp.keys i (by omega) | exact hp.partners i (by omega) | exact hp.targets i (by omega)

theorem dartTableStep_zero {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hG : G.Ok) {d : Nat} (hd : d < 2 * G.E)
    (hreg : c.reg scanDart = d)
    (hz : ∀ r,r<2*G.E → c.mem (c.reg zBase+r)=(G.fd s).zOf r)
    (hm : MutableZero L c) : MutableZero L (run dartTableStep c) := by
  intro j hj i hi
  rw [dartTableStep_cell hc hG hd hreg hz j i hi]
  simp only [show ¬(j=12) by omega,show ¬(j=13) by omega,show ¬(j=14) by omega,
    false_and, ↓reduceIte]
  exact hm j hj i hi

end STACS2027.Embed.PlanRAM
