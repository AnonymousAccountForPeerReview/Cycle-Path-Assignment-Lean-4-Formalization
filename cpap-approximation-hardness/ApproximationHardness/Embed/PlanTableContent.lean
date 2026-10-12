module

public import ApproximationHardness.Embed.PlanTableBounds
import Lean.Elab.Tactic.Omega

/-! Assemble the actual compiled cells into the solver's complete finite-table interface. -/

@[expose] public section
namespace STACS2027.Embed.PlanRAM
open RAM

/-- Exact compiled node, dart, and postorder cells satisfy the entire solver table contract. -/
theorem compiled_tables {L : DFSRAM.Layout} {G : DG} {s : DS} {c : Config}
    (hc : Context L G s c) (hF : (G.fd s).Valid) (hI : G.Inv s)
    (hw : 8*G.E≤L.width) (hd : DartPrefix L (G.fd s) c (2*G.E))
    (hn : ∀v,v<4*G.E →
      c.mem ((solverLayout L).cell 15 v)=(G.fd s).gid v ∧
      c.mem ((solverLayout L).cell 16 v)=((G.fd s).parts v).length ∧
      PartSlots (solverLayout L) c.mem v ((G.fd s).parts v))
    (hp : ∀i,i<s.post.length →c.mem ((solverLayout L).cell 21 i)=s.post.getD i 0) :
    RAMSolver.Tables (solverLayout L) c ((G.fd s).sol hF) s.post (4*G.E) (2*G.E) := by
  refine ⟨(show 4*G.E≤L.width by omega),hc.dartCapacity,hc.postLength,hc.infinity,
    hd.keys,hd.partners,hd.targets,?_,?_,?_,?_,?_,?_,?_,hc.postCapacity,
    forest_post_bound hI,?_,?_,?_,?_⟩
  · intro v hv;exact (hn v hv).1
  · intro v hv;exact (hn v hv).2.1
  · intro v hv;exact (hn v hv).2.2.1
  · intro v hv;exact (hn v hv).2.2.2.1
  · intro v hv;exact (hn v hv).2.2.2.2.1
  · intro v hv;exact (hn v hv).2.2.2.2.2
  · intro i hi
    rw [hp i hi]
    exact DG.getD_of_lt hi
  · intro v _;exact forest_parts_bound hF v
  · intro v _ it hi
    cases it with
    | node w => exact forest_item_bound (it:=.node w) hF hi
    | dart d => exact forest_item_bound (it:=.dart d) hF hi
  · intro e he;exact pair_lt he
  · intro v hv
    change 4*G.E+v<L.width
    omega

end STACS2027.Embed.PlanRAM
