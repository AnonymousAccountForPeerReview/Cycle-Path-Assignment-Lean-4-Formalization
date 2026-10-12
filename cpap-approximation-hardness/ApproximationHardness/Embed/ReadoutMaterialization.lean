module

public import ApproximationHardness.Embed.BufferHeaders
public import ApproximationHardness.Embed.SolverIndexBounds
import Lean.Elab.Tactic.Omega

/-! # The constructed finite arrays satisfy the final rotation reader -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

theorem readoutHeader_ready {D : DFSRAM.Layout} {G : DG} {c : Config} {m : SMS}
    {S : Sol} {post : List Nat} {vertices darts : Nat} {o : Nat→Bool}
    (hG : G.Ok) (hb : DFSRAM.Bases D G c) (hd : DFSRAM.Tables D G c)
    (hr : Rep (PlanRAM.solverLayout D) c m)
    (ht : Tables (PlanRAM.solverLayout D) c S post vertices darts)
    (hvertices : 2*G.E≤vertices)
    (hwidth : 2*G.E≤D.width)
    (hia : ∀ v,v<2*G.E → m.m.ia v<D.width)
    (horient : c.reg 100=orientationBase (PlanRAM.solverLayout D))
    (hnext : c.reg 261=nextBase (PlanRAM.solverLayout D))
    (hprev : c.reg 262=predBase (PlanRAM.solverLayout D))
    (hoval : ∀ v,v<D.width → c.mem (orientationBase (PlanRAM.solverLayout D)+v)=boolWord (o v)) :
    ReadoutReady (bufferLimit (PlanRAM.solverLayout D)) (2*G.E)
      (run readoutHeader c) o := by
  let L := PlanRAM.solverLayout D
  let e := run readoutHeader c
  have hmem : e.mem=c.mem := (readoutHeader_frame c).1
  have hreg (r : Nat) (h : r<125 ∨ 130<r) : e.reg r=c.reg r :=
    (readoutHeader_frame c).2.2 r h
  have hh := readoutHeader_values c hr.bases.1
  have hrepBase : e.reg 127=D.block 0 := hh.2.2.1.trans (hb.2.2.2.2.2 0 (by decide))
  have hnextBase : e.reg 128=nextBase L := hh.2.2.2.1.trans hnext
  have hprevBase : e.reg 129=predBase L := hh.2.2.2.2.1.trans hprev
  have horientBase : e.reg 130=orientationBase L := hh.2.2.2.2.2.trans horient
  have hinfoBase : e.reg 60=L.block 10 := (hreg 60 (by decide)).trans (hr.bases.2.2.2.2 10 (by decide))
  have hindexBase : e.reg 61=L.block 11 := (hreg 61 (by decide)).trans (hr.bases.2.2.2.2 11 (by decide))
  have hgroupBase : e.reg 65=L.block 15 := (hreg 65 (by decide)).trans (hr.bases.2.2.2.2 15 (by decide))
  have hrep (d : Nat) (hlt : d<2*G.E) : e.mem (e.reg 127+d)=G.rep d := by
    rw [hmem,hrepBase]
    exact hd.representatives d hlt
  have hindex (v : Nat) (hlt : v<2*G.E) : e.mem (e.reg 61+v)=m.m.ia v := by
    rw [hmem,hindexBase]
    simpa only [memField,Layout.cell,L] using hr.arrays 11 (by decide) v (hlt.trans_le hwidth)
  have hgroup (v : Nat) (hlt : v<2*G.E) : e.mem (e.reg 65+v)=S.gid v := by
    rw [hmem,hgroupBase]
    exact ht.groupIds v (hlt.trans_le hvertices)
  have hsolverBelow : L.limit≤bufferLimit L := by
    dsimp [bufferLimit,predBase,nextBase,keyBase,orientationBase]
    omega
  have hforestBelow : D.limit≤bufferLimit L := by
    have hl : D.limit≤L.limit := by dsimp [L,PlanRAM.solverLayout,Layout.limit];omega
    exact hl.trans hsolverBelow
  have horientBound (v : Nat) (hv : v<D.width) : orientationBase L+v<bufferLimit L := by
    dsimp [bufferLimit,predBase,nextBase,keyBase,orientationBase,L,PlanRAM.solverLayout]
    omega
  refine ⟨(hreg 1 (by decide)).trans hr.bases.2.1,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro d hlt
    rw [hrepBase]
    exact (DFSRAM.Layout.cell_lt (L:=D) (j:=0) (by decide) (hlt.trans_le hwidth)).trans_le hforestBelow
  · intro d hlt
    rw [hrep d hlt,hinfoBase]
    exact (Layout.cell_lt (L:=L) (j:=10) (by decide) ((hG.rep_lt d hlt).trans_le hwidth)).trans_le hsolverBelow
  · intro d hlt
    rw [hrep d hlt,hindexBase]
    exact (Layout.cell_lt (L:=L) (j:=11) (by decide) ((hG.rep_lt d hlt).trans_le hwidth)).trans_le hsolverBelow
  · intro d hlt
    rw [hrep d hlt,hgroupBase]
    exact (Layout.cell_lt (L:=L) (j:=15) (by decide) ((hG.rep_lt d hlt).trans_le hwidth)).trans_le hsolverBelow
  · intro d hlt
    rw [hrep d hlt,hindex _ (hG.rep_lt d hlt),horientBase]
    exact horientBound _ (hia _ (hG.rep_lt d hlt))
  · intro d hlt
    rw [hrep d hlt,hgroup _ (hG.rep_lt d hlt),horientBase]
    exact horientBound _ (ht.groupsBound _ ((hG.rep_lt d hlt).trans_le hvertices))
  · intro d hlt
    rw [hnextBase]
    dsimp [bufferLimit,predBase,nextBase,keyBase,orientationBase,L,PlanRAM.solverLayout]
    omega
  · intro d hlt
    rw [hprevBase]
    dsimp [bufferLimit,predBase]
    change nextBase L+L.width+d<nextBase L+L.width+L.width
    exact Nat.add_lt_add_left (hlt.trans_le hwidth) _
  · intro d hlt
    rw [hrep d hlt,hindex _ (hG.rep_lt d hlt),horientBase,hmem]
    exact hoval _ (hia _ (hG.rep_lt d hlt))
  · intro d hlt
    rw [hrep d hlt,hgroup _ (hG.rep_lt d hlt),horientBase,hmem]
    exact hoval _ (ht.groupsBound _ ((hG.rep_lt d hlt).trans_le hvertices))

theorem encodedBit_evalBit (m : SMem) (gid : Nat→Nat) (o : Nat→Bool) (v : Nat) :
    encodedBit (m.inf v) (m.ia v) (gid v) o=m.evalBit gid o v := by
  rfl

theorem readoutHeader_rotationValue {D : DFSRAM.Layout} {G : DG} {s : DS}
    {c : Config} {m : SMS} {post : List Nat} {vertices darts : Nat}
    (hF : (G.fd s).Valid) (o β : Nat→Bool)
    (hb : DFSRAM.Bases D G c) (hd : DFSRAM.Tables D G c)
    (hr : Rep (PlanRAM.solverLayout D) c m)
    (ht : Tables (PlanRAM.solverLayout D) c ((G.fd s).sol hF) post vertices darts)
    (hvertices : 2*G.E≤vertices) (hwidth : 2*G.E≤D.width)
    (hnext : c.reg 261=nextBase (PlanRAM.solverLayout D))
    (hprev : c.reg 262=predBase (PlanRAM.solverLayout D))
    (hn : ∀ d,d<2*G.E → c.mem (nextBase (PlanRAM.solverLayout D)+d)=ForestData.rotN hF (fun _=>false) d)
    (hp : ∀ d,d<2*G.E → c.mem (predBase (PlanRAM.solverLayout D)+d)=ForestData.rotInvN hF (fun _=>false) d)
    (hbit : ∀ d,d<2*G.E → m.m.evalBit ((G.fd s).sol hF).gid o ((G.fd s).rep d)=β ((G.fd s).rep d)) :
    ∀ d,d<2*G.E → rotationValue (run readoutHeader c) o d=ForestData.rotInvN hF β d := by
  intro d hlt
  let e := run readoutHeader c
  have hmem : e.mem=c.mem := (readoutHeader_frame c).1
  have hreg (r : Nat) (h : r<125 ∨ 130<r) : e.reg r=c.reg r :=
    (readoutHeader_frame c).2.2 r h
  have hh := readoutHeader_values c hr.bases.1
  have hrepBase : e.reg 127=D.block 0 := hh.2.2.1.trans (hb.2.2.2.2.2 0 (by decide))
  have hnextBase : e.reg 128=nextBase (PlanRAM.solverLayout D) := hh.2.2.2.1.trans hnext
  have hprevBase : e.reg 129=predBase (PlanRAM.solverLayout D) := hh.2.2.2.2.1.trans hprev
  have hv : (G.fd s).rep d<2*G.E := hF.rep_lt d hlt
  apply rotationValue_correct hF e o β hlt
  · rw [hmem,hrepBase]
    exact hd.representatives d hlt
  · have hb10 := (hreg 60 (by decide)).trans (hr.bases.2.2.2.2 10 (by decide))
    have hb11 := (hreg 61 (by decide)).trans (hr.bases.2.2.2.2 11 (by decide))
    have hb15 := (hreg 65 (by decide)).trans (hr.bases.2.2.2.2 15 (by decide))
    rw [hmem,hb10,hb11,hb15]
    have hi := hr.arrays 10 (by decide) ((G.fd s).rep d) (hv.trans_le hwidth)
    have ha := hr.arrays 11 (by decide) ((G.fd s).rep d) (hv.trans_le hwidth)
    have hg := ht.groupIds ((G.fd s).rep d) (hv.trans_le hvertices)
    change encodedBit (c.mem ((PlanRAM.solverLayout D).cell 10 ((G.fd s).rep d)))
      (c.mem ((PlanRAM.solverLayout D).cell 11 ((G.fd s).rep d)))
      (c.mem ((PlanRAM.solverLayout D).cell 15 ((G.fd s).rep d))) o=β ((G.fd s).rep d)
    rw [hi,ha,hg]
    exact hbit d hlt
  · rw [hmem,hnextBase]
    exact hn d hlt
  · rw [hmem,hprevBase]
    exact hp d hlt

end STACS2027.Embed.RAMSolver
