module

public import NPHardness.PlanarSphericalGadgets
public import NPHardness.PlanarAssemblyIndexPorts

/-! The exact placed gadget graphs retain the same spherical embedding and
common port face under their injective, order-preserving block labels. -/

@[expose] public section
namespace STACS2027
open Complexity Complexity.SAT Complexity.Planar PlanarGluing

theorem HasSphericalCofacialPorts.relabel {V W : Type} {es ports : List (V×V)}
    (h : HasSphericalCofacialPorts es ports) (f : V → W)
    (hf : ∀ a b, f a = f b → a=b) :
    HasSphericalCofacialPorts (es.map (fun e => (f e.1,f e.2)))
      (ports.map (fun e => (f e.1,f e.2))) := by
  unfold HasSphericalCofacialPorts IsGraphEmbedding
  rw [List.length_map]
  obtain ⟨G,hG,hEuler,r,hports⟩ := h
  refine ⟨G,⟨hG.1,?_,hG.2.2⟩,hEuler,r,?_⟩
  · intro d e
    rw [halfEdgeEnd_relabel,halfEdgeEnd_relabel,hG.2.1]
    constructor
    · exact congrArg (Option.map f)
    · intro he
      generalize ha : halfEdgeEnd es d.val = a at he ⊢
      generalize hb : halfEdgeEnd es e.val = b at he ⊢
      cases a with
      | none => cases b <;> simp_all
      | some a =>
        cases b with
        | none => simp at he
        | some b => exact congrArg some (hf a b (Option.some.inj he))
  · intro e he
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
    obtain ⟨d,k,hk,hd⟩ := hports a ha
    exact ⟨d,k,hk,by simp only [List.getElem?_map,hd,Option.map_some]⟩

def EdgesOrdered (g : Graph) : Prop := ∀ e ∈ g, e.1 ≤ e.2

theorem subdividedEdge_ordered (a b next s : Nat) : EdgesOrdered (subdividedEdge a b next s) := by
  induction s generalizing a next with
  | zero => intro e he; have he' : e=edge a b := by simpa [subdividedEdge] using he
            subst e; change min _ _ ≤ max _ _; omega
  | succ s ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · change min _ _ ≤ max _ _; omega
    · exact ih next (next+1) e he

theorem realizeLinks_ordered (next : Nat) (ls : List Link) : EdgesOrdered (realizeLinks next ls) := by
  induction ls generalizing next with
  | nil => intro e he; simp [realizeLinks] at he
  | cons l ls ih =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact subdividedEdge_ordered _ _ _ _ e he
    · exact ih _ e he

theorem mapEdge_block_eq {width tag : Nat} {e : Edge} (h : e.1≤e.2) :
    mapEdge (blockVertex width tag) e =
      (blockVertex width tag e.1,blockVertex width tag e.2) := by
  have hh : blockVertex width tag e.1≤blockVertex width tag e.2 := by unfold blockVertex; omega
  exact Prod.ext (Nat.min_eq_left hh) (Nat.max_eq_right hh)

theorem mapGraph_block_eq {g : Graph} (h : EdgesOrdered g) (width tag : Nat) :
    mapGraph (blockVertex width tag) g =
      g.map (fun e => (blockVertex width tag e.1,blockVertex width tag e.2)) := by
  apply List.map_congr_left
  intro e he
  exact mapEdge_block_eq (h e he)

theorem HasSphericalCofacialPorts.block {g ports : Graph}
    (h : HasSphericalCofacialPorts g ports) (hg : EdgesOrdered g) (hp : EdgesOrdered ports)
    (width tag : Nat) :
    HasSphericalCofacialPorts (mapGraph (blockVertex width tag) g)
      (mapGraph (blockVertex width tag) ports) := by
  rw [mapGraph_block_eq hg,mapGraph_block_eq hp]
  exact h.relabel _ (fun _ _ he => Nat.add_left_cancel he)

theorem mapGraph_block_nodup {g : Graph} (hn : g.Nodup) (ho : EdgesOrdered g) (width tag : Nat) :
    (mapGraph (blockVertex width tag) g).Nodup := by
  rw [mapGraph_block_eq ho]
  apply nodup_map_of_injOn' _ hn
  intro a _ b _ he
  exact Prod.ext (Nat.add_left_cancel (congrArg Prod.fst he))
    (Nat.add_left_cancel (congrArg Prod.snd he))

namespace PlanarAssembly

def placedVariablePorts (k v : Nat) : Graph :=
  mapGraph (blockVertex (gadgetWidth k) v) variablePorts

def ungluedClausePorts (k n j : Nat) (c : List PlacedLiteral) : Graph :=
  mapGraph (blockVertex (gadgetWidth k) (n+j)) (clausePorts.take c.length)

theorem placedVariableGraph_sphericalPorts (k v : Nat) :
    HasSphericalCofacialPorts (placedVariableGraph k v) (placedVariablePorts k v) :=
  (variableGraph_sphericalPorts k).block (realizeLinks_ordered _ _) (by simp [EdgesOrdered,variablePorts]) _ _

theorem clauseGraph_sphericalPorts (k : Nat) (c : List PlacedLiteral)
    (hc : c.length=2 ∨ c.length=3) :
    HasSphericalCofacialPorts (clauseGraph k c) (clausePorts.take c.length) := by
  rcases hc with hc | hc
  · simpa only [clauseGraph,hc,↓reduceIte] using clauseTwoGraph_sphericalPorts k
  · simpa only [clauseGraph,hc,show ¬3=2 by decide,↓reduceIte,
      show clausePorts.take 3=clausePorts by rfl] using clauseThreeGraph_sphericalPorts k

theorem clauseGraph_ordered (k : Nat) (c : List PlacedLiteral) : EdgesOrdered (clauseGraph k c) := by
  unfold clauseGraph
  split <;> exact realizeLinks_ordered _ _

theorem ungluedClauseGraph_sphericalPorts (k n j : Nat) (c : List PlacedLiteral)
    (hc : c.length=2 ∨ c.length=3) :
    HasSphericalCofacialPorts (ungluedClauseGraph k n j c) (ungluedClausePorts k n j c) :=
  (clauseGraph_sphericalPorts k c hc).block (clauseGraph_ordered k c)
    (fun e he => (show EdgesOrdered clausePorts by simp [EdgesOrdered,clausePorts]) e (List.mem_of_mem_take he)) _ _

theorem placedVariablePorts_nodup (k v : Nat) : (placedVariablePorts k v).Nodup :=
  mapGraph_block_nodup (by decide) (by simp [EdgesOrdered,variablePorts]) _ _

theorem ungluedClausePorts_nodup (k n j : Nat) (c : List PlacedLiteral) :
    (ungluedClausePorts k n j c).Nodup :=
  mapGraph_block_nodup ((show clausePorts.Nodup by decide).take)
    (fun e he => (show EdgesOrdered clausePorts by simp [EdgesOrdered,clausePorts]) e (List.mem_of_mem_take he)) _ _

@[simp] theorem placedVariablePorts_length (k v : Nat) : (placedVariablePorts k v).length=3 := by
  simp [placedVariablePorts,mapGraph,variablePorts]

@[simp] theorem ungluedClausePorts_length (k n j : Nat) (c : List PlacedLiteral)
    (hc : c.length≤3) : (ungluedClausePorts k n j c).length=c.length := by
  simp only [ungluedClausePorts,mapGraph,List.length_map,List.length_take]
  exact Nat.min_eq_left hc

theorem variablePorts_getElem (i : Fin 3) :
    variablePorts[i.val] = edge (variableEndpoint i.val false) (variableEndpoint i.val true) :=
  (by decide : ∀ i : Fin 3, variablePorts[i.val] =
    edge (variableEndpoint i.val false) (variableEndpoint i.val true)) i

theorem clausePorts_getElem (i : Fin 3) :
    clausePorts[i.val] = edge (clauseEndpoint i.val false) (clauseEndpoint i.val true) :=
  (by decide : ∀ i : Fin 3, clausePorts[i.val] =
    edge (clauseEndpoint i.val false) (clauseEndpoint i.val true)) i

theorem placedVariablePorts_getElem (k v : Nat) (i : Fin 3) :
    (placedVariablePorts k v)[i.val]'(by rw [placedVariablePorts_length]; exact i.isLt) =
      mapEdge (blockVertex (gadgetWidth k) v)
        (edge (variableEndpoint i.val false) (variableEndpoint i.val true)) := by
  have hi : i.val < (variablePorts.map (mapEdge (blockVertex (gadgetWidth k) v))).length := by
    simpa only [List.length_map,show variablePorts.length=3 by rfl] using i.isLt
  change ((variablePorts.map (mapEdge (blockVertex (gadgetWidth k) v)))[i.val]) = _
  rw [List.getElem_map]
  exact congrArg _ (variablePorts_getElem i)

theorem ungluedClausePorts_getElem (k n j : Nat) (c : List PlacedLiteral) (hc : c.length≤3)
    (i : Fin c.length) :
    (ungluedClausePorts k n j c)[i.val]'(by rw [ungluedClausePorts_length _ _ _ _ hc]; exact i.isLt) =
      mapEdge (blockVertex (gadgetWidth k) (n+j))
        (edge (clauseEndpoint i.val false) (clauseEndpoint i.val true)) := by
  have hi : i.val < ((clausePorts.take c.length).map (mapEdge (blockVertex (gadgetWidth k) (n+j)))).length := by
    simpa only [List.length_map,List.length_take,show clausePorts.length=3 by rfl,Nat.min_eq_left hc] using i.isLt
  change (((clausePorts.take c.length).map (mapEdge (blockVertex (gadgetWidth k) (n+j))))[i.val]) = _
  rw [List.getElem_map,List.getElem_take]
  exact congrArg _ (clausePorts_getElem ⟨i.val,Nat.lt_of_lt_of_le i.isLt hc⟩)

end PlanarAssembly
end STACS2027
