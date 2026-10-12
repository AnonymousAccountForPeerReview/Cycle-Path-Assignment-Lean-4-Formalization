module

public import NPHardness.PlanarAssemblyQuotient
public import NPHardness.PlanarAssemblyInactive

/-!
Convert the actual assembled dart rotation to the precise oriented formula
edge list. This theorem retains both copies of every attachment edge and
uses canonical undirected normalization only after proving the full endpoint
orbit condition for the selected vertex quotient.
-/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.SAT Complexity.Planar PlanarGluing

/-- A planar rotation whose nodes are exactly the fibers of a vertex map
embeds the corresponding actual mapped graph. No injectivity of the vertex
map is required; the node-orbit equivalence is proved by port assembly. -/
theorem planar_mapGraph_of_rotation (es : Graph) (q : Nat→Nat)
    (G : Hypermap (2*es.length))
    (hE : ∀d,(G.edge d).val=ed d.val)
    (hN : ∀a b,(∃r,iterate G.node r a=b) ↔
      Option.map q (halfEdgeEnd es a.val)=Option.map q (halfEdgeEnd es b.val))
    (hG : G.Planar) : PlanarGraph (mapGraph q es) := by
  have hraw : PlanarGraph (es.map fun e=>(q e.1,q e.2)) := by
    unfold PlanarGraph
    rw [List.length_map]
    refine ⟨G,hE,?_,hG⟩
    intro a b
    simpa only [halfEdgeEnd_relabel] using hN a b
  have h := (planarGraph_canonical (es.map fun e=>(q e.1,q e.2))).mpr hraw
  change PlanarGraph (es.map fun e=>(min (q e.1) (q e.2),max (q e.1) (q e.2)))
  simpa only [List.map_map,canonicalEdge,Function.comp_def] using h

namespace LocalPortChoices
variable {k : Nat} {f : CNF} (C : LocalPortChoices k f) (hf : BoundedOccurrence f)

/-- Exact global graph planarity from ordered local boundary darts on the
source incidence rotation. The flips in the conclusion are constructed from
the actual chosen local dart directions. -/
theorem orientedFormulaGraph_planar_of_orderedPorts
    (G : Hypermap (2*(ungluedFormulaPieces k f).flatten.length))
    (hG : IsGraphEmbedding (ungluedFormulaPieces k f).flatten G)
    (hstrict : 2*G.componentCount+2*(ungluedFormulaPieces k f).flatten.length≤G.eulerRhs)
    {m : Nat} (I : Hypermap m) (hI : I.Planar)
    (O : OrderedIncidencePorts (C.geometricPairing hf G hG) I)
    (hseparate : O.SourceNodesSeparate) :
    PlanarGraph (orientedFormulaGraph (C.assemblyFlips hf) k f) := by
  let P := C.geometricPairing hf G hG
  let es := (ungluedFormulaPieces k f).flatten
  let q := assemblyVertex (C.assemblyFlips hf) k f
  have he : ∀d,G.edge d=graphEdge d := fun d=>Fin.ext (hG.1 d)
  have he2 : ∀d,G.edge (G.edge d)=d := by intro d; rw [he,he,graphEdge_twice]
  have hn : ∀a b,Reaches G.node a b ↔ halfEdgeEnd es a.val=halfEdgeEnd es b.val := hG.2.1
  have hend : ∀d,Option.map q (halfEdgeEnd es (G.node d).val)=Option.map q (halfEdgeEnd es d.val) := by
    intro d
    exact congrArg (Option.map q) (((hn d (G.node d)).mp (Reaches.step G.node d)).symm)
  have hdisj : P.DisjointNodeSwitches := C.geometricPairing_disjoint hf G hG
  have hfib := P.endpoint_fibers (fun d=>halfEdgeEnd es d.val) (Option.map q) he2 hn
    (C.geometricPairing_fibers hf G hG)
  have hp : P.assembled.Planar := O.assembled_planar_of_separation hdisj he2 hstrict hI hseparate
  have hgraph := planar_mapGraph_of_rotation es q P.assembled (hG.1)
    (fun a b=>P.assembled_node_orbit_iff (fun d=>Option.map q (halfEdgeEnd es d.val))
      hdisj he2 hend (C.geometricPairing_glue hf G hG) hfib a b) hp
  change PlanarGraph (mapGraph (assemblyVertex (C.assemblyFlips hf) k f)
    (ungluedFormulaPieces k f).flatten) at hgraph
  rw [ungluedFormulaPieces_flatten,assemblyVertex_formulaGraph] at hgraph
  exact hgraph

end LocalPortChoices
end STACS2027.PlanarAssembly
