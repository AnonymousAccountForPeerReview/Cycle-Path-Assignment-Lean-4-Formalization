module

public import NPHardness.GlobalSeparation

/-! No edge between a variable copy and a clause copy is shared accidentally:
shared edges are exactly allocated literal ports. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

theorem subdividedEdge_fresh_source {a b next s bound : Nat} (ha : bound ≤ a)
    (hn : bound ≤ next) {e : Edge} (he : e ∈ subdividedEdge a b next s)
    (hb : e.1 < bound ∧ e.2 < bound) : False := by
  induction s generalizing a next with
  | zero =>
    have heq : e = edge a b := by simpa [subdividedEdge] using he
    rw [heq] at hb
    have h := (edge_below a b bound).mp hb
    omega
  | succ s ih =>
    rcases List.mem_cons.mp he with rfl | he
    · have h := (edge_below a next bound).mp hb
      omega
    · exact ih hn (by omega) he

theorem subdividedEdge_old {a b next s bound : Nat} (hn : bound ≤ next)
    {e : Edge} (he : e ∈ subdividedEdge a b next s) (hb : e.1 < bound ∧ e.2 < bound) :
    e = edge a b := by
  cases s with
  | zero => simpa [subdividedEdge] using he
  | succ s =>
    rcases List.mem_cons.mp he with rfl | he
    · have h := (edge_below a next bound).mp hb
      omega
    · exact False.elim (subdividedEdge_fresh_source hn (by omega) he hb)

theorem realizeLinks_old_edge (next : Nat) (ls : List Link) {bound : Nat} (hn : bound ≤ next)
    {e : Edge} (he : e ∈ realizeLinks next ls) (hb : e.1 < bound ∧ e.2 < bound) :
    e ∈ linkEdges ls := by
  induction ls generalizing next with
  | nil => simp [realizeLinks] at he
  | cons l ls ih =>
    rcases List.mem_append.mp he with he | he
    · have heq := subdividedEdge_old hn he hb
      simp [linkEdges, heq]
    · exact List.mem_cons_of_mem _ (ih (next + l.subdivisions) (by omega) he)

def clausePortVertices : List Nat := [0,1,4,5,10,11]

theorem attachmentAt_vertex {c : List PlacedLiteral} {v : Nat} {p : PlacedLiteral} {side : Bool}
    (h : attachmentAt c v = some (p,side)) : v ∈ clausePortVertices := by
  obtain ⟨i, hi, _, rfl⟩ := attachmentAt_spec.mp h
  exact (by decide : ∀ i : Fin 3, ∀ b : Bool, clauseEndpoint i.val b ∈ clausePortVertices) ⟨i,hi⟩ side

theorem clausePortVertices_bound : ∀ v ∈ clausePortVertices, v < 12 := by decide

theorem clauseSkeleton_port_edges : ∀ e ∈ clauseTwoSkeleton,
    e.1 ∈ clausePortVertices → e.2 ∈ clausePortVertices → e ∈ clausePorts := by decide

theorem clauseGraph_attachment_edge {k : Nat} {c : List PlacedLiteral} {e : Edge}
    (he : e ∈ clauseGraph k c) {p q : PlacedLiteral} {a b : Bool}
    (hp : attachmentAt c e.1 = some (p,a)) (hq : attachmentAt c e.2 = some (q,b)) : e ∈ clausePorts := by
  have h1 := attachmentAt_vertex hp
  have h2 := attachmentAt_vertex hq
  have heold : e ∈ clauseTwoSkeleton := by
    have hb : e.1 < 12 ∧ e.2 < 12 :=
      ⟨clausePortVertices_bound _ h1, clausePortVertices_bound _ h2⟩
    unfold clauseGraph at he
    split at he
    · exact realizeLinks_old_edge 24 (clauseTwoLinks k) (bound := 12) (by omega) he hb
    · have h := realizeLinks_old_edge 18 (clauseThreeLinks k) (bound := 12) (by omega) he hb
      exact (by decide : clauseThree5 ⊆ clauseTwoSkeleton) h
  exact clauseSkeleton_port_edges e heold h1 h2

theorem variable_clause_vertex_intersection {width n j v a b : Nat} {c : List PlacedLiteral}
    (hw : 7 ≤ width) (hv : v < n) (ha : a < width) (hb : b < width)
    (he : blockVertex width v a = clauseVertex width n j c b) :
    ∃ p side, attachmentAt c b = some (p,side) ∧ v = p.literal.var ∧ a = variableEndpoint p.port side := by
  cases h : attachmentAt c b with
  | none =>
    have ht := (blockVertex_injective ha hb (by simpa [clauseVertex, h] using he)).1
    omega
  | some ps =>
    obtain ⟨p, side⟩ := ps
    have hep := Nat.lt_of_lt_of_le (variableEndpoint_bound p.port side) hw
    have hx := blockVertex_injective ha hep (by simpa [clauseVertex, h] using he)
    exact ⟨p, side, rfl, hx⟩

theorem attachmentAt_endpoint {c : List PlacedLiteral} {i : Nat} (hi : i < 3) (side : Bool) :
    attachmentAt c (clauseEndpoint i side) = (c[i]?).map (fun p => (p,side)) := by
  simp [attachmentAt, clausePortAt_endpoint hi side]

theorem clauseGraph_ports (k : Nat) (c : List PlacedLiteral) {i : Nat} (hi : i < 3) :
    edge (clauseEndpoint i false) (clauseEndpoint i true) ∈ clauseGraph k c := by
  have hs : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hbase : ∀ l ∈ clauseThreeLinks k, l.subdivisions = 0 → edge l.source l.target ∈ clauseGraph k c := by
    intro l hl hz
    unfold clauseGraph
    split
    · exact realizeLinks_contains_zero 24 (clauseTwoLinks k) (List.mem_append_left _ hl) hz
    · exact realizeLinks_contains_zero 18 (clauseThreeLinks k) hl hz
  rcases hs with rfl | rfl | rfl
  · exact hbase ⟨0,1,0⟩ (by simp [clauseThreeLinks]) rfl
  · exact hbase ⟨4,5,0⟩ (by simp [clauseThreeLinks]) rfl
  · exact hbase ⟨10,11,0⟩ (by simp [clauseThreeLinks]) rfl

/-- A concrete inverse description of every shared variable/clause edge. -/
theorem formulaGraph_shared_edge {k : Nat} {f : CNF} {v j : Nat}
    (hv : v < variableBound f) (hj : j < (placeFormula [] f).length) {e : Edge}
    (heV : e ∈ placedVariableGraph k v)
    (heC : e ∈ placedClauseGraph k (variableBound f) j (placeFormula [] f)[j]) :
    ∃ i p, i < 3 ∧ (placeFormula [] f)[j][i]? = some p ∧ v = p.literal.var ∧
      e = mapEdge (blockVertex (gadgetWidth k) v)
        (edge (variableEndpoint p.port false) (variableEndpoint p.port true)) := by
  let c := (placeFormula [] f)[j]
  obtain ⟨de, hd, hde⟩ := List.mem_map.mp heV
  obtain ⟨ce, hc, hce⟩ := List.mem_map.mp heC
  have hbV := variableGraph_below k de hd
  have hbC := clauseGraph_below k c ce hc
  have hw : 7 ≤ gadgetWidth k := by have := gadgetWidth_ge k; omega
  have heq : edge (blockVertex (gadgetWidth k) v de.1) (blockVertex (gadgetWidth k) v de.2) =
      edge (clauseVertex (gadgetWidth k) (variableBound f) j c ce.1)
        (clauseVertex (gadgetWidth k) (variableBound f) j c ce.2) := hde.trans hce.symm
  have ha : ∃ p a, attachmentAt c ce.1 = some (p,a) ∧ v = p.literal.var := by
    rcases (edge_eq_iff ..).mp heq with ⟨h1, _⟩ | ⟨_, h1⟩
    · obtain ⟨p,a,hp,hvar,_⟩ := variable_clause_vertex_intersection hw hv hbV.1 hbC.1 h1
      exact ⟨p,a,hp,hvar⟩
    · obtain ⟨p,a,hp,hvar,_⟩ := variable_clause_vertex_intersection hw hv hbV.2 hbC.1 h1
      exact ⟨p,a,hp,hvar⟩
  have hb : ∃ q b, attachmentAt c ce.2 = some (q,b) := by
    rcases (edge_eq_iff ..).mp heq with ⟨_, h2⟩ | ⟨h2, _⟩
    · obtain ⟨q,b,hq,_,_⟩ := variable_clause_vertex_intersection hw hv hbV.2 hbC.2 h2
      exact ⟨q,b,hq⟩
    · obtain ⟨q,b,hq,_,_⟩ := variable_clause_vertex_intersection hw hv hbV.1 hbC.2 h2
      exact ⟨q,b,hq⟩
  obtain ⟨p,a,hp,hvar⟩ := ha
  obtain ⟨q,b,hq⟩ := hb
  have hm := clauseGraph_attachment_edge hc hp hq
  have hports : ∃ i : Fin 3, ce = edge (clauseEndpoint i.val false) (clauseEndpoint i.val true) ∧
      ce.1 = clauseEndpoint i.val false :=
    (by decide : ∀ e ∈ clausePorts, ∃ i : Fin 3,
      e = edge (clauseEndpoint i.val false) (clauseEndpoint i.val true) ∧ e.1 = clauseEndpoint i.val false) ce hm
  obtain ⟨i, heport, hleft⟩ := hports
  rw [hleft, attachmentAt_endpoint i.isLt false] at hp
  have hcp : c[i.val]? = some p := by
    cases h : c[i.val]? with
    | none => simp [h] at hp
    | some r =>
      have hsame : r = p := by simpa [h] using congrArg (Option.map Prod.fst) hp
      simp [hsame]
  refine ⟨i.val, p, i.isLt, hcp, hvar, ?_⟩
  rw [← hce, heport, mapped_attachment_edge i.isLt hcp, ← hvar]

end STACS2027
