module

public import NPHardness.PlanarAssemblySourcePortNumbers
public import Complexity.Planar.CombBasic

/-! The allocated occurrence position agrees with the registered arithmetic
clause/slot decoder. This removes all choice from source port coordinates. -/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.SAT Complexity.Planar Comb PlanarGluing

theorem placed_clause_length (f:CNF) (j:Nat) (hj:j<f.length)
    (hjp:j<(placeFormula [] f).length) :
    (placeFormula [] f)[j].length=f[j].length := by
  have h:=congrArg (fun ls:List Nat=>ls[j]?) (placed_clause_lengths f)
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hjp,
    List.getElem?_eq_getElem hj,Option.map_some,Option.some.injEq] using h

theorem occurrencePosition_decode (f:CNF) (i:OccurrenceIndex f) :
    (occurrencePosition f i).clause.val=oj f i.val ∧
    (occurrencePosition f i).slot.val=ot f i.val := by
  let p:=occurrencePosition f i
  have hj:p.clause.val<f.length:=by simpa only [placeFormula_length] using p.clause.isLt
  have hl:kl f p.clause.val=(placeFormula [] f)[p.clause.val].length:=by
    rw [kl_of_lt f _ hj]
    exact (placed_clause_length f _ hj p.clause.isLt).symm
  have ht:p.slot.val<kl f p.clause.val:=by rw [hl];exact p.slot.isLt
  have he:=occurrencePosition_offset f i
  rw [placed_clause_lengths] at he
  have hoff:off f p.clause.val+p.slot.val=i.val:=he
  have hd:=occ_eq f p.clause.val p.slot.val hj ht
  rw [hoff] at hd
  exact ⟨hd.1.symm,hd.2.symm⟩

theorem occurrencePosition_at_offset (f:CNF) (i:OccurrenceIndex f) (j t:Nat)
    (hj:j<f.length) (ht:t<kl f j) (hi:i.val=off f j+t) :
    (occurrencePosition f i).clause.val=j ∧ (occurrencePosition f i).slot.val=t := by
  have hd:=occurrencePosition_decode f i
  have he:=occ_eq f j t hj ht
  exact ⟨hd.1.trans ((congrArg (oj f) hi).trans he.1),
    hd.2.trans ((congrArg (ot f) hi).trans he.2)⟩

theorem odd_offset_port_data (signs:Nat→Bool) (f:CNF)
    (d:Fin (2*(placeFormula [] f).flatten.length)) (j t:Nat)
    (hj:j<f.length) (ht:t<kl f j) (hd:d.val=2*(off f j+t)+1) :
    sourcePortNumber f d=t ∧ sourcePortCount f d=kl f j ∧ sourceForward signs f d=false := by
  let i:OccurrenceIndex f:=⟨d.val/2,by have:=d.isLt;omega⟩
  have hi:i.val=off f j+t:=by dsimp [i];omega
  have he:=occurrencePosition_at_offset f i j t hj ht hi
  have hp:d.val%2≠0:=by omega
  have hv:occurrenceVertex f d=Sum.inr j:=by
    simp only [occurrenceVertex,hp,↓reduceIte]
    exact congrArg Sum.inr he.1
  refine ⟨?_,?_,?_⟩
  · simp only [sourcePortNumber,hp,↓reduceIte]
    exact he.2
  · unfold sourcePortCount
    rw [hv]
    have hjp:j<(placeFormula [] f).length:=by simpa only [placeFormula_length] using hj
    simp only [List.getElem?_eq_getElem hjp,Option.getD_some]
    rw [placed_clause_length f j hj hjp,kl_of_lt f j hj]
  · simp only [sourceForward,hv]

end STACS2027.PlanarAssembly
