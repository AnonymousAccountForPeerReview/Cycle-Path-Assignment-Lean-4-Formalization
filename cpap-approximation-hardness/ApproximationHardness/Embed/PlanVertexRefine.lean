module

public import ApproximationHardness.Embed.PlanVertexFrame
public import ApproximationHardness.Embed.PlanTopPartsRAM
import Lean.Elab.Tactic.Omega

/-! Exact RAM construction of each representative and synthetic top plan node. -/

@[expose] public section
namespace STACS2027.Embed.PlanRAM
open RAM

attribute [local simp] zBase vertex degree vertexParent dart opposite child childParent
  itemType itemValue distinguished vertexBound partCount topVertex remaining slot
  address test otherTest exclusion representative constant

theorem vertexRefine_run_skip (c : Config) : run .skip c=c := rfl

/-- Parts stores protect every group-id cell. -/
theorem PartMemFrame.groupCell {L : RAMSolver.Layout} {m n : Nat → Nat} {v i : Nat}
    (hf : PartMemFrame L v m n) (hi : i<L.width) (hv : v<L.width) :
    m (L.cell 15 i)=n (L.cell 15 i) := by
  apply hf
  intro j hj hj' he
  have hinj := L.cell_injective hi hv he
  omega

/-- Parts stores protect every distinguished-cache address. -/
theorem PartMemFrame.cacheCell {L : RAMSolver.Layout} {m n : Nat → Nat} {v i : Nat}
    (hf : PartMemFrame L v m n) (hv : v<L.width) : m (L.limit+i)=n (L.limit+i) := by
  apply hf
  intro j hj hj' he
  have hlt := L.cell_lt (by omega : j<22) hv
  omega

/-- Parts stores at a distinct node protect each earlier node cell. -/
theorem PartMemFrame.otherCell {L : RAMSolver.Layout} {m n : Nat → Nat} {v i : Nat}
    (hf : PartMemFrame L v m n) (hi : i<L.width) (hv : v<L.width) (hne : i≠v) (j : Nat) :
    m (L.cell j i)=n (L.cell j i) := by
  apply hf
  intro k hk hk' he
  have hinj := L.cell_injective hi hv he
  exact hne hinj.2

/-- Parts stores at a distinct node protect the complete item-slot encoding. -/
theorem PartMemFrame.otherSlots {L : RAMSolver.Layout} {m n : Nat → Nat} {v i : Nat}
    (hf : PartMemFrame L v m n) (hi : i<L.width) (hv : v<L.width) (hne : i≠v)
    (xs : List Item) (hs : PartSlots L n i xs) : PartSlots L m i xs := by
  simpa only [PartSlots,hf.otherCell hi hv hne 17,hf.otherCell hi hv hne 18,
    hf.otherCell hi hv hne 19,hf.otherCell hi hv hne 20] using hs

/-- One actual vertex instruction constructs the exact two plan entries and has a finite write frame. -/
theorem vertexTableStep_values {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hz : MutableZero L c) (hG : G.Ok) (hF : (G.fd s).Valid)
    {r : Nat} (hr : r<2*G.E) (hv : c.reg vertex=r)
    (hb : c.reg vertexBound=4*G.E) (hw : 4*G.E≤L.width) :
    Context L G s (run vertexTableStep c) ∧ MutableZero L (run vertexTableStep c) ∧
      VertexEntry L (G.fd s) (run vertexTableStep c) r ∧
      VertexMemFrame L G r (run vertexTableStep c).mem c.mem := by
  have hrw : r<(solverLayout L).width := by dsimp [solverLayout];omega
  have htw : 2*G.E+r<(solverLayout L).width := by dsimp [solverLayout];omega
  have hne : r≠2*G.E+r := by omega
  generalize heD : run distinguishedProgram c=d
  have hd : Context L G s d := heD ▸ hc.distinguishedProgram
  have hdz : MutableZero L d := heD ▸ hz.distinguishedProgram hc
  have hdInputs := distinguishedProgram_inputs hc hG hF hr hv
  rw [heD] at hdInputs
  obtain ⟨hvd,hdd,hpd,hzd⟩ := hdInputs
  have hbd : d.reg vertexBound=4*G.E := by
    rw [←heD]
    exact (run_reg_frame distinguishedProgram c vertexBound (by decide)).trans hb
  generalize heH : run vertexHeader d=e
  have he : Context L G s e := heH ▸ hd.vertexHeader
  have hez : MutableZero L e := heH ▸ hdz.vertexHeader hd (by rw [hvd];exact hrw) (by rw [hvd];exact htw)
  have hve : e.reg vertex=r := by rw [←heH];exact (vertexHeader_reg d vertex (by decide)).trans hvd
  have hde : e.reg degree=(G.darts r).length := by rw [←heH];exact (vertexHeader_reg d degree (by decide)).trans hdd
  have hpe : e.reg vertexParent=s.par r := by rw [←heH];exact (vertexHeader_reg d vertexParent (by decide)).trans hpd
  have hze : e.reg distinguished=(G.fd s).zOf r := by rw [←heH];exact (vertexHeader_reg d distinguished (by decide)).trans hzd
  have hte : e.reg topVertex=2*G.E+r := by rw [←heH,vertexHeader_top hd,hvd]
  have htest := vertexHeader_test hd hr hvd
  rw [heH] at htest
  have hgroups := vertexHeader_groups hd hr hvd hbd hw
  rw [heH] at hgroups
  have hempty := vertexHeader_empty hd hr hvd hw
  rw [heH] at hempty
  have hDframe (a : Nat) (ha : a≠(solverLayout L).limit+r) : d.mem a=c.mem a := by
    rw [←heD,distinguishedProgram_mem hc hG hF hr hv]
    simp [upd,ha]
  have hHframe (a : Nat) (hn : ∀j,j∈[15,16,17,18,19,20] →
      a≠(solverLayout L).cell j r ∧ a≠(solverLayout L).cell j (2*G.E+r)) : e.mem a=d.mem a := by
    rw [←heH]
    exact vertexHeader_mem_frame hd a (by simpa only [hvd] using hn)
  have hcache : e.mem ((solverLayout L).limit+r)=(G.fd s).zOf r := by
    rw [hHframe _ (by
      intro j hj
      have hjb : j<22 := by simp only [List.mem_cons,List.mem_nil_iff,or_false] at hj;omega
      have h₁ := (solverLayout L).cell_lt hjb hrw
      have h₂ := (solverLayout L).cell_lt hjb htw
      constructor <;> omega)]
    rw [←heD,distinguishedProgram_mem hc hG hF hr hv,upd_same]
  rw [run_vertexTableStep,heD,heH]
  by_cases hrep : G.rep r=r
  · have hzero : e.reg test=0 := htest.mpr hrep
    simp only [vertexFinish,run_ifz,hzero,↓reduceIte,seqs,run_seq,vertexRefine_run_skip]
    have hver : (G.fd s).IsVertex r := ⟨hr,hrep⟩
    generalize heO : run ordinaryParts e=o
    obtain ⟨ho,hos, hon⟩ := ordinaryParts_values he hG hF hve hde hpe hze hr hver
    rw [heO] at ho hos hon
    have hom : MutableZero L o := by
      rw [←heO];exact ordinaryParts_mutable he hez hve hde hpe hze hrw
    have hvo : o.reg vertex=r := by rw [←heO];exact (ordinaryParts_reg e vertex (by decide)).trans hve
    have hpo : o.reg vertexParent=s.par r := by rw [←heO];exact (ordinaryParts_reg e vertexParent (by decide)).trans hpe
    have hzo : o.reg distinguished=(G.fd s).zOf r := by rw [←heO];exact (ordinaryParts_reg e distinguished (by decide)).trans hze
    have hto : o.reg topVertex=2*G.E+r := by rw [←heO];exact (ordinaryParts_reg e topVertex (by decide)).trans hte
    have hfo : PartMemFrame (solverLayout L) r o.mem e.mem := by
      have hf := ordinaryParts_frame he hve hde hpe hze hrw
      rw [heO] at hf;exact hf
    generalize heT : run topParts o=t
    have ht : Context L G s t := heT ▸ topParts_context ho
    have htm : MutableZero L t := by rw [←heT];exact topParts_mutable ho hom (by rw [hto];exact htw)
    obtain ⟨hts,htn⟩ := topParts_values ho hG hvo hpo hzo hto hver htw
    rw [heT] at hts htn
    have hft : PartMemFrame (solverLayout L) (2*G.E+r) t.mem o.mem := by
      have hf := topParts_frame ho
      rw [heT,hto] at hf;exact hf
    refine ⟨ht,htm,?_,?_⟩
    · refine ⟨?_,?_,?_,?_,?_,htn,hts⟩
      · exact (hft.cacheCell htw).trans ((hfo.cacheCell hrw).trans hcache)
      · exact (hft.groupCell hrw htw).trans ((hfo.groupCell hrw hrw).trans hgroups.1)
      · exact (hft.otherCell hrw htw hne 16).trans hon
      · exact hft.otherSlots hrw htw hne _ hos
      · exact (hft.groupCell htw htw).trans ((hfo.groupCell htw hrw).trans hgroups.2)
    · intro a ha hn
      have hjs (j : Nat) (hj : 16≤j) (hj' : j≤20) : j∈[15,16,17,18,19,20] := by simp;omega
      exact (hft a (fun j hj hj' => (hn j (hjs j hj hj')).2)).trans
        ((hfo a (fun j hj hj' => (hn j (hjs j hj hj')).1)).trans ((hHframe a hn).trans (hDframe a ha)))
  · have hnzero : e.reg test≠0 := by intro h;exact hrep (htest.mp h)
    simp only [vertexFinish,run_ifz,hnzero,↓reduceIte,vertexRefine_run_skip]
    have hparts := parts_nonrepresentative (s:=s) hr hrep
    refine ⟨he,hez,?_,?_⟩
    · refine ⟨hcache,hgroups.1,?_,?_,hgroups.2,?_,?_⟩
      · simpa only [hparts.1,List.length_nil] using hempty.2.1
      · simpa only [hparts.1] using hempty.1
      · change e.mem ((solverLayout L).cell 16 (2*G.E+r))=((G.fd s).parts (2*G.E+r)).length
        simpa only [hparts.2,List.length_nil] using hempty.2.2.2
      · change PartSlots (solverLayout L) e.mem (2*G.E+r) ((G.fd s).parts (2*G.E+r))
        simpa only [hparts.2] using hempty.2.2.1
    · intro a ha hn; exact (hHframe a hn).trans (hDframe a ha)

end STACS2027.Embed.PlanRAM
