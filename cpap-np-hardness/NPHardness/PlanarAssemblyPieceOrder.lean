module

public import NPHardness.PlanarAssemblyLocalOrder
public import NPHardness.PlanarAssemblyPieces
public import NPHardness.PlanarAssemblyPortEnds

/-! Transfer local first-hit orders through the actual prefix-offset dart
injections to the global ordered incidence-port interface. -/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.SAT Complexity.Planar PlanarGluing

/-- Local source-node enumerations coupled to actual gadget face walks. -/
structure PieceSourceOrders (gs : List Graph) (H : LocalMaps gs)
    {m : Nat} (I : Hypermap m) (port : Fin m → Fin (2*gs.flatten.length)) where
  count : Fin gs.length → Nat
  source : ∀ j, Fin (count j) → Fin m
  localPort : ∀ j, Fin (count j) → Fin (2*gs[j.val].length)
  next : ∀ j, Fin (count j) → Fin (count j)
  all_source : ∀ d, ∃ j, ∃ i, source j i=d
  match_port : ∀ j i, port (source j i)=blockDart gs j (localPort j i)
  covers_piece : ∀ j d e, port d=blockDart gs j e → ∃ i, source j i=d
  next_source : ∀ j i, source j (next j i)=I.face (I.edge (source j i))
  local_order : ∀ j i, NextSelected (H j).face (localPort j) i (next j i)

namespace PieceSourceOrders
variable {gs : List Graph} {H : LocalMaps gs} {m : Nat} {I : Hypermap m}
  {port : Fin m → Fin (2*gs.flatten.length)} (O : PieceSourceOrders gs H I port)

theorem nextSelected (j : Fin gs.length) (i : Fin (O.count j)) :
    NextSelected (piecesMap gs H).face port (O.source j i) (O.source j (O.next j i)) := by
  obtain ⟨k,hk,hend,hinside⟩ := O.local_order j i
  refine ⟨k,hk,?_,?_⟩
  · rw [O.match_port,O.match_port]
    exact (piecesMap_iterate .face gs H j k (O.localPort j i)).trans (congrArg (blockDart gs j) hend)
  · intro r hr hrk t ht
    rw [O.match_port] at ht
    rw [show iterate (piecesMap gs H).face r (blockDart gs j (O.localPort j i)) =
        blockDart gs j (iterate (H j).face r (O.localPort j i)) from
      piecesMap_iterate .face gs H j r (O.localPort j i)] at ht
    obtain ⟨s,hs⟩ := O.covers_piece j t _ ht.symm
    rw [← hs,O.match_port] at ht
    exact hinside r hr hrk s (blockDart_injective gs j ht)

include O in
theorem source_nextSelected (d : Fin m) :
    NextSelected (piecesMap gs H).face port d (I.face (I.edge d)) := by
  obtain ⟨j,i,rfl⟩ := O.all_source d
  rw [← O.next_source]
  exact O.nextSelected j i

include O in
theorem nextPort (P : PortPairing (piecesMap gs H))
    (hm : ∀ i, P.marked (port i)=true)
    (hcover : ∀ d, P.marked d=true → ∃ i, port i=d) (d : Fin m) :
    NextPort P port ((piecesMap gs H).face (port d)) (I.face (I.edge d)) :=
  (O.source_nextSelected d).to_nextPort hm (fun _ _ hd => hcover _ hd)

end PieceSourceOrders

/-- Local gadget choices satisfying their source-node cyclic orders construct
the complete global ordered-port object consumed by the assembly theorem. -/
noncomputable def LocalPortChoices.orderedFromPieces {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f)
    (H : LocalMaps (ungluedFormulaPieces k f))
    (hG : IsGraphEmbedding (ungluedFormulaPieces k f).flatten
      (piecesMap (ungluedFormulaPieces k f) H))
    (I : Hypermap (2*(placeFormula [] f).flatten.length))
    (hIedge : ∀ d, I.edge d=graphEdge d)
    (O : PieceSourceOrders (ungluedFormulaPieces k f) H I (C.sourcePort hf)) :
    OrderedIncidencePorts (C.geometricPairing hf _ hG) I where
  port := C.sourcePort hf
  injective := C.sourcePort_injective hf
  marked_port i := (C.pairing_marked hf _ _ _).mpr ⟨i,rfl⟩
  every_marked d hd := (C.pairing_marked hf _ _ d).mp hd
  pair_port i := by rw [hIedge]; exact C.pairing_pair hf _ _ i
  edge_involution i := by rw [hIedge,hIedge,graphEdge_twice]
  order i := O.nextPort _ (fun j => (C.pairing_marked hf _ _ _).mpr ⟨j,rfl⟩)
    (fun d hd => (C.pairing_marked hf _ _ d).mp hd) i

end STACS2027.PlanarAssembly
