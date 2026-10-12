module

public import NPHardness.PlanarAssemblyEuler

/-!
The unused-component bookkeeping of port assembly is derived from the actual
old components and source-node separation. No separately supplied list of
inactive gadgets or numerical component inequality is needed.
-/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.Planar PlanarGluing

namespace OrderedIncidencePorts
variable {n m : Nat} {G : Hypermap n} {P : PortPairing G} {I : Hypermap m}
  (O : OrderedIncidencePorts P I)

/-- An old component is inactive when it contains no selected source port. -/
def Inactive (d : Fin n) : Prop := ∀ i, ¬ Connected G d (O.port i)

/-- One actual old component root for each inactive component. This list is
proof bookkeeping and is not an operation of the graph-construction machine. -/
noncomputable def inactiveRoots : List (Fin n) := by
  classical
  exact ((List.finRange n).filter (ComponentRoot G)).filter
    (fun d => decide (O.Inactive d))

theorem mem_inactiveRoots (d : Fin n) :
    d ∈ O.inactiveRoots ↔ ComponentRoot G d = true ∧ O.Inactive d := by
  classical
  simp only [inactiveRoots,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]

theorem inactiveRoots_nodup : O.inactiveRoots.Nodup := by
  classical
  exact ((List.nodup_finRange n).filter _).filter _

theorem inactiveRoots_cover (d : Fin n) :
    (∃ r ∈ O.inactiveRoots, Connected G d r) ∨ ∃ i, Connected G d (O.port i) := by
  classical
  by_cases h : ∃ i, Connected G d (O.port i)
  · exact Or.inr h
  · refine Or.inl ⟨componentRep G d, (O.mem_inactiveRoots _).mpr ⟨componentRep_root G d, ?_⟩,
      ⟨n,componentRep_linked G d⟩⟩
    intro i hi
    exact h ⟨i,(show Connected G d (componentRep G d) from
      ⟨n,componentRep_linked G d⟩).trans hi⟩

/-- Distinct source-node cycles occupy distinct old gadget components. -/
def SourceNodesSeparate : Prop :=
  ∀ i j, Connected G (O.port i) (O.port j) → Reaches I.node i j

/-- The inactive component roots together with the old representatives of
source-node roots form a duplicate-free sublist of all old component roots. -/
theorem inactiveRoots_count (hsep : O.SourceNodesSeparate) :
    O.inactiveRoots.length + cycleCount I.node ≤ G.componentCount := by
  let active := (cycleRoots I.node).map (fun i => componentRep G (O.port i))
  have hactive : active.Nodup := by
    apply nodup_map_of_injOn' _ (cycleRoots_nodup I.node)
    intro i hi j hj he
    exact cycleRoots_eq_of_reaches (hm_node_inj I) hi hj
      (hsep i j (linked_of_componentRep_eq G he))
  have hnd : (O.inactiveRoots ++ active).Nodup := by
    rw [List.nodup_append]
    refine ⟨O.inactiveRoots_nodup,hactive,?_⟩
    intro a ha b hb he
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hb
    have ha' := ((O.mem_inactiveRoots a).mp ha).2
    rw [he] at ha'
    exact ha' i (Connected.symm ⟨n,componentRep_linked G (O.port i)⟩)
  have hcount := length_le_countP (ComponentRoot G) (O.inactiveRoots ++ active) hnd (by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact ((O.mem_inactiveRoots d).mp hd).1
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hd
      exact componentRep_root G (O.port i))
  change _ ≤ (List.finRange n).countP (ComponentRoot G)
  simpa only [List.length_append,List.length_map,active,cycleRoots_length] using hcount

/-- The actual simultaneous assembly is planar once local pieces are
spherical, the source rotation is planar, and source nodes lie in separate
old components. All inactive-piece accounting is proved internally. -/
theorem assembled_planar_of_separation (hdisj : P.DisjointNodeSwitches)
    (hE : ∀ d, G.edge (G.edge d) = d)
    (hG : 2*G.componentCount+n ≤ G.eulerRhs) (hI : I.Planar)
    (hsep : O.SourceNodesSeparate) : P.assembled.Planar :=
  O.assembled_planar hdisj hE hG hI O.inactiveRoots
    O.inactiveRoots_cover (O.inactiveRoots_count hsep)

end OrderedIncidencePorts
end STACS2027.PlanarAssembly
