module

public import NPHardness.PlanarAssemblyIndex
public import NPHardness.PlanarOperationsPortsGadgets

/-! Prefix offsets inject every actual gadget dart into the concatenated
unglued formula edge list. Edge numbers, endpoint sides, and half-edge ends
are preserved exactly. -/

@[expose] public section
namespace STACS2027
open Complexity Complexity.SAT

def ungluedFormulaPieces (k : Nat) (f : CNF) : List Graph :=
  (List.range (variableBound f)).map (placedVariableGraph k) ++
    (placeFormula [] f).mapIdx (fun j c => ungluedClauseGraph k (variableBound f) j c)

theorem ungluedFormulaPieces_flatten (k : Nat) (f : CNF) :
    (ungluedFormulaPieces k f).flatten = ungluedFormulaGraph k f := by
  simp only [ungluedFormulaPieces, ungluedFormulaGraph, List.flatten_append, List.flatMap]

namespace PlanarAssembly

def pieceOffset (gs : List Graph) (i : Nat) : Nat := (gs.take i).flatten.length

theorem flatten_piece (gs : List Graph) (i : Fin gs.length) :
    gs.flatten = (gs.take i.val).flatten ++ gs[i.val] ++ (gs.drop (i.val+1)).flatten := by
  conv => lhs; rw [← List.take_append_drop i.val gs]
  rw [List.flatten_append, List.drop_eq_getElem_cons i.isLt, List.flatten_cons,
    List.append_assoc]

theorem pieceOffset_end_le (gs : List Graph) (i : Fin gs.length) :
    pieceOffset gs i.val + gs[i.val].length ≤ gs.flatten.length := by
  have h := congrArg List.length (flatten_piece gs i)
  simp only [List.length_append] at h
  unfold pieceOffset
  omega

theorem pieceOffset_mono_end (gs : List Graph) (i j : Fin gs.length) (hij : i.val < j.val) :
    pieceOffset gs i.val + gs[i.val].length ≤ pieceOffset gs j.val := by
  obtain ⟨tail,ht⟩ := List.take_prefix_take_left (l := gs) (show i.val+1 ≤ j.val by omega)
  have he : ((gs.take (i.val+1)).flatten).length ≤ (gs.take j.val).flatten.length := by
    rw [← ht, List.flatten_append, List.length_append]
    omega
  rw [List.take_succ_eq_append_getElem i.isLt, List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.length_append] at he
  exact he

def blockDart (gs : List Graph) (i : Fin gs.length) (d : Fin (2*gs[i.val].length)) :
    Fin (2*gs.flatten.length) :=
  ⟨2*pieceOffset gs i.val+d.val, by
    have h := pieceOffset_end_le gs i
    have hd := d.isLt
    omega⟩

theorem blockDart_index (gs : List Graph) (i : Fin gs.length) (d : Fin (2*gs[i.val].length)) :
    (blockDart gs i d).val / 2 = pieceOffset gs i.val+d.val/2 := by
  simp only [blockDart]
  omega

theorem blockDart_side (gs : List Graph) (i : Fin gs.length) (d : Fin (2*gs[i.val].length)) :
    (blockDart gs i d).val % 2 = d.val%2 := by
  simp only [blockDart, Nat.mul_add_mod]

theorem flatten_piece_getElem? (gs : List Graph) (i : Fin gs.length) {j : Nat}
    (hj : j < gs[i.val].length) :
    gs.flatten[pieceOffset gs i.val+j]? = gs[i.val][j]? := by
  rw [flatten_piece gs i, List.append_assoc, List.getElem?_append_right (by
    change (gs.take i.val).flatten.length ≤ (gs.take i.val).flatten.length+j
    omega)]
  simp only [pieceOffset, Nat.add_sub_cancel_left]
  exact List.getElem?_append_left hj

theorem blockDart_edge_lookup (gs : List Graph) (i : Fin gs.length)
    (d : Fin (2*gs[i.val].length)) :
    gs.flatten[(blockDart gs i d).val/2]? = gs[i.val][d.val/2]? := by
  rw [blockDart_index]
  exact flatten_piece_getElem? gs i (by have := d.isLt; omega)

theorem blockDart_end (gs : List Graph) (i : Fin gs.length)
    (d : Fin (2*gs[i.val].length)) :
    halfEdgeEnd gs.flatten (blockDart gs i d).val = halfEdgeEnd gs[i.val] d.val := by
  unfold halfEdgeEnd
  rw [blockDart_edge_lookup, blockDart_side]

theorem blockDart_graphEdge (gs : List Graph) (i : Fin gs.length)
    (d : Fin (2*gs[i.val].length)) :
    blockDart gs i (PlanarGluing.graphEdge d) = PlanarGluing.graphEdge (blockDart gs i d) := by
  apply Fin.ext
  simp only [blockDart, PlanarGluing.graphEdge]
  rcases Nat.mod_two_eq_zero_or_one d.val with h | h
  · simp [Complexity.Planar.ed, h]
    omega
  · simp [Complexity.Planar.ed, h]
    omega

theorem blockDart_block_injective (gs : List Graph) {i j : Fin gs.length}
    {d : Fin (2*gs[i.val].length)} {e : Fin (2*gs[j.val].length)}
    (h : blockDart gs i d = blockDart gs j e) : i = j := by
  have hv := congrArg Fin.val h
  change 2*pieceOffset gs i.val+d.val = 2*pieceOffset gs j.val+e.val at hv
  apply Fin.ext
  have hd := d.isLt
  have he := e.isLt
  by_cases hij : i.val < j.val
  · have ho := pieceOffset_mono_end gs i j hij
    omega
  · by_cases hji : j.val < i.val
    · have ho := pieceOffset_mono_end gs j i hji
      omega
    · omega

theorem blockDart_injective (gs : List Graph) (i : Fin gs.length)
    {d e : Fin (2*gs[i.val].length)} (h : blockDart gs i d = blockDart gs i e) : d=e := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 2*pieceOffset gs i.val+d.val = 2*pieceOffset gs i.val+e.val at hv
  omega

end PlanarAssembly
end STACS2027
