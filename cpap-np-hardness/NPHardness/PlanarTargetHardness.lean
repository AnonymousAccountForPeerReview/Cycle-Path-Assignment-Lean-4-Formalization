module
public import NPHardness.PlanarSourceGraphOutput
public import NPHardness.PlanarSourceGraphPlanarity

/-! Unconditional planar target hardness through the concrete polynomial
source-and-graph constructor. Planarity concerns the decoded target graph;
there is no assumed source hardness, rotation oracle, or hidden reduction in
the target language. -/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter Complexity.Planar.Emit

/-- The concrete output graph is planar for every input word. -/
theorem graphOutput_planar (k : Nat) (P : ClauseProgram 1) (w : SAT.Word) :
    PlanarGraph (instructionGraph (graphOutput k P w)) := by
  rw [(graphOutput_spec k P w).2.1,output_ringFormula,gridOut_eq]
  exact ringGrid_graph_planar _ _ _ _

/-- Complete encoded planar-target correctness for the fixed-k constructor. -/
theorem graphOutput_planar_iff (k : Nat) (hk : 5≤k) (P : ClauseProgram 1) (w : SAT.Word) :
    PlanarCPAP k (encode (graphOutput k P w)) ↔
      Satisfiable (P.emit w (fun _ => w.length)) := by
  rw [planarCPAP_encode_iff]
  constructor
  · intro h
    exact (graphOutput_assignment_iff k hk P w).mp h.2.2
  · intro hs
    exact ⟨(graphOutput_spec k P w).1,graphOutput_planar k P w,
      (graphOutput_assignment_iff k hk P w).mpr hs⟩

end STACS2027.PlanarSource.Packed

namespace STACS2027
open Complexity Complexity.SAT

/-- For every fixed k≥5, the planar cycle-path assignment language is
NP-hard in the registered single-tape polynomial-reduction model. -/
theorem planarCPAP_np_hard {k : Nat} (hk : 5≤k) : NPHard (PlanarCPAP k) := by
  intro L hL
  obtain ⟨P,hP⟩ := CookLevinEmitter.inNP_emitter hL
  refine ⟨fun x => encode (PlanarSource.Packed.graphOutput k P x),
    PlanarSource.Packed.graphOutput_polyTime k P,?_⟩
  intro x
  rw [hP x,SAT_encode_iff]
  exact (PlanarSource.Packed.graphOutput_planar_iff k hk P x).symm

end STACS2027
