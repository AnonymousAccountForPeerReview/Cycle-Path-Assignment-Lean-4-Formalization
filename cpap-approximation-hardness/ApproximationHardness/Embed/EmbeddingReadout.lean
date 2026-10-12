module

public import ApproximationHardness.Embed.ReadoutMaterialization
public import ApproximationHardness.Embed.EmbeddingRuntime
public import ApproximationHardness.Embed.SolverBits
public import ApproximationHardness.Embed.PlanExecution
public import ApproximationHardness.Embed.RotationOutput
import Lean.Elab.Tactic.Omega

/-! The actual final scan emits a planar rotation from the computed solver arrays. -/

@[expose] public section
namespace STACS2027.Embed
open Complexity Complexity.SAT Complexity.Planar STACS2027.PlanarGluing STACS2027.PlanarAssembly RAM

/-- Planarity gives the consistency witness used to verify the deterministic solver. -/
theorem incidence_forkWitness {f : CNF} (hf : BoundedOccurrence f)
    (hp : PlanarGraph (incidenceGraph f)) :
    ∃ sides : Nat→Bool,∀ v p q,((incF f).sol (incF_valid hf)).P.IsFork
      ((incF f).sol (incF_valid hf)).α ((incF f).sol (incF_valid hf)).key v p q →
      ((incF f).sol (incF_valid hf)).P.ForkOK ((incF f).sol (incF_valid hf)).α
        ((incF f).sol (incF_valid hf)).key sides p q := by
  have hex : ∃ G : Hypermap (2*(incF f).E),IsGraphEdge G.edge ∧
      (∀ d d',Reaches G.node d d' ↔ (incF f).rep d'.val=(incF f).rep d.val) ∧ G.Planar := by
    unfold PlanarGraph at hp
    rw [incidence_length f] at hp
    obtain ⟨G,he,hn,hpl⟩ := hp
    refine ⟨G,he,fun d d'=>?_,hpl⟩
    rw [←incidence_reaches_iff hf d.isLt d'.isLt]
    exact hn d d'
  exact (ForestData.exists_planar_iff (incF_valid hf)).mp hex

namespace RAMSolver

def readoutProgram : Stmt := .seq readoutHeader rotationLoop

/-- The actual header and scan consume only computed arrays and write the exact planar rotation. -/
theorem readoutProgram_spec {f : CNF} (hf : BoundedOccurrence f)
    (hp : PlanarGraph (incidenceGraph f)) {c : Config} {o : Nat→Bool}
    (h : EmbeddingRuntime (IncidenceRAM.cacheLayout f) (incDG f) (incDG f).final
      (incF_valid hf) c)
    (hoval : ∀ i,i<(IncidenceRAM.cacheLayout f).width →
      c.mem (orientationBase (PlanRAM.solverLayout (IncidenceRAM.cacheLayout f))+i)=boolWord (o i))
    (hconsistent : ((incF f).sol (incF_valid hf)).Consistent o) :
    ∃ t d,ExecB (bufferLimit (PlanRAM.solverLayout (IncidenceRAM.cacheLayout f)))
      readoutProgram c t d ∧ t≤1000*(f.flatten.length+1) ∧
      d.out=rotOut hf o ∧ IsPlanarRotation f d.out := by
  have hG := incOk hf
  have hpost := DG.postOrder_final hG
  obtain ⟨sides,hfork⟩ := incidence_forkWitness hf hp
  have hw : 2*(incDG f).E≤(IncidenceRAM.cacheLayout f).width := by
    dsimp [incDG,IncidenceRAM.cacheLayout];omega
  have hpositive : 0<(IncidenceRAM.cacheLayout f).width := by
    dsimp [IncidenceRAM.cacheLayout];omega
  have hia := solver_final_ia_bound (incF_valid hf) h.tables hpositive hfork hpost
  have hready := readoutHeader_ready hG h.forestBases h.forestTables h.solver h.tables
    (by omega) hw (fun v _=>hia v) h.orientation h.nextBase h.previousBase hoval
  have hbit (d : Nat) (hd : d<2*(incDG f).E) :
      (completedSolver (incDG f) (incDG f).final (incF_valid hf)).m.evalBit
        ((incF f).sol (incF_valid hf)).gid o ((incF f).rep d)=incBits hf o ((incF f).rep d) := by
    have hmem : (incF f).rep d∈(incDG f).final.post := by
      apply ((DG.post_final hG).2.1 _).mpr
      left
      exact ⟨hG.rep_lt d hd,hG.rep_rep d hd⟩
    apply ((incF f).sol (incF_valid hf)).runPrefix_bits
      (ForestData.tree (incF_valid hf)) (ForestData.good (incF_valid hf)) hfork hpost.solver
      initialState rfl rfl (incDG f).final.post.length (by omega)
    simpa only [List.take_length] using hmem
  have hvalues := readoutHeader_rotationValue (incF_valid hf) o (incBits hf o)
    h.forestBases h.forestTables h.solver h.tables (by omega) hw h.nextBase h.previousBase
    h.next h.previous hbit
  have hheader := readoutHeader_values c h.solver.bases.1
  have hout : (run readoutHeader c).out=[] := (readoutHeader_frame c).2.1.trans h.output
  obtain ⟨t,d,et,bt,ho,hpl⟩ := rotationLoop_planar hf hp (run readoutHeader c) o hready
    (hheader.1.trans h.forestBases.2.2.1) hheader.2.1 hout hvalues hconsistent
  obtain ⟨th,eh,bh⟩ := readoutHeader_spec
    (bufferLimit (PlanRAM.solverLayout (IncidenceRAM.cacheLayout f))) c
  have hs : size rotationStep+1≤400 := by decide
  have hs' : (size rotationStep+1)*(2*f.flatten.length)≤800*f.flatten.length := by
    calc
      _≤400*(2*f.flatten.length) := Nat.mul_le_mul_right _ hs
      _=800*f.flatten.length := by omega
  exact ⟨th+t,d,.seq eh et,by omega,ho,hpl⟩

end RAMSolver
end STACS2027.Embed
