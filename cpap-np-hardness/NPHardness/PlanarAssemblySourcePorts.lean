module

public import NPHardness.PlanarAssemblySourceNode
public import NPHardness.PlanarAssemblyPortEnds

/-!
Finite source-node enumerations for the actual occurrence ordering. A variable
uses only its allocated ports that occur in the formula; a clause uses its
actual literal slots. Both are complete enumerations of the corresponding
registered incidence vertex, with injective maps to at most three local ports.
-/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.SAT Complexity.Planar PlanarGluing

@[simp] theorem occurrenceVertex_even (f : CNF) (i : OccurrenceIndex f) :
    occurrenceVertex f (occurrenceDart i false)=Sum.inl (occurrence f i).literal.var := by
  simp only [occurrenceVertex,occurrenceDart,Bool.false_eq_true,↓reduceIte,Nat.add_zero,
    Nat.mul_mod_right,Nat.mul_div_right,show 0<2 by decide]

@[simp] theorem occurrenceVertex_odd (f : CNF) (i : OccurrenceIndex f) :
    occurrenceVertex f (occurrenceDart i true)=Sum.inr (occurrencePosition f i).clause.val := by
  have hd : (2*i.val+1)/2=i.val := by omega
  have hm : (2*i.val+1)%2=1 := by omega
  simp only [occurrenceVertex,occurrenceDart,↓reduceIte,hm,show ¬1=0 by decide,↓reduceIte]
  exact congrArg (fun j:OccurrenceIndex f=>Sum.inr (occurrencePosition f j).clause.val) (Fin.ext hd)

theorem occurrenceDart_injective {f : CNF} (side : Bool) {i j : OccurrenceIndex f}
    (h : occurrenceDart i side=occurrenceDart j side) : i=j := by
  have hv := congrArg Fin.val h
  apply Fin.ext
  cases side <;> simp only [occurrenceDart,Bool.false_eq_true,↓reduceIte,Nat.add_zero] at hv <;> omega

theorem occurrenceDart_cases {f : CNF} (d : Fin (2*(placeFormula [] f).flatten.length)) :
    ∃i:OccurrenceIndex f,∃s:Bool,d=occurrenceDart i s := by
  let i : OccurrenceIndex f := ⟨d.val/2,by have := d.isLt; omega⟩
  rcases Nat.mod_two_eq_zero_or_one d.val with h | h
  · exact ⟨i,false,Fin.ext (by simp only [occurrenceDart,Bool.false_eq_true,↓reduceIte,Nat.add_zero,i]; omega)⟩
  · exact ⟨i,true,Fin.ext (by simp only [occurrenceDart,↓reduceIte,i]; omega)⟩

def variableOccurrences (f : CNF) (v : Nat) : List (OccurrenceIndex f) :=
  (List.finRange (placeFormula [] f).flatten.length).filter fun i=>decide ((occurrence f i).literal.var=v)

noncomputable def clauseOccurrences (f : CNF) (j : Nat) : List (OccurrenceIndex f) :=
  (List.finRange (placeFormula [] f).flatten.length).filter fun i=>decide ((occurrencePosition f i).clause.val=j)

def variableOccurrenceIndex (f : CNF) (v : Nat) (i : Fin (variableOccurrences f v).length) :
    OccurrenceIndex f := (variableOccurrences f v)[i.val]

noncomputable def clauseOccurrenceIndex (f : CNF) (j : Nat) (i : Fin (clauseOccurrences f j).length) :
    OccurrenceIndex f := (clauseOccurrences f j)[i.val]

theorem variableOccurrenceIndex_vertex (f : CNF) (v : Nat) (i : Fin (variableOccurrences f v).length) :
    (occurrence f (variableOccurrenceIndex f v i)).literal.var=v := by
  have hm := List.getElem_mem i.isLt
  have h := (List.mem_filter.mp (show variableOccurrenceIndex f v i∈variableOccurrences f v from hm)).2
  exact of_decide_eq_true h

theorem clauseOccurrenceIndex_vertex (f : CNF) (j : Nat) (i : Fin (clauseOccurrences f j).length) :
    (occurrencePosition f (clauseOccurrenceIndex f j i)).clause.val=j := by
  have hm := List.getElem_mem i.isLt
  have h := (List.mem_filter.mp (show clauseOccurrenceIndex f j i∈clauseOccurrences f j from hm)).2
  exact of_decide_eq_true h

theorem variableOccurrenceIndex_injective (f : CNF) (v : Nat)
    {i j : Fin (variableOccurrences f v).length}
    (h : variableOccurrenceIndex f v i=variableOccurrenceIndex f v j) : i=j := by
  have hn : (variableOccurrences f v).Nodup := (List.nodup_finRange _).filter _
  exact Fin.ext ((hn.getElem_inj (hi:=i.isLt) (hj:=j.isLt)).mp h)

theorem clauseOccurrenceIndex_injective (f : CNF) (v : Nat)
    {i j : Fin (clauseOccurrences f v).length}
    (h : clauseOccurrenceIndex f v i=clauseOccurrenceIndex f v j) : i=j := by
  have hn : (clauseOccurrences f v).Nodup := (List.nodup_finRange _).filter _
  exact Fin.ext ((hn.getElem_inj (hi:=i.isLt) (hj:=j.isLt)).mp h)

/-- The source darts of one variable, including the empty case for unused variables. -/
noncomputable def variableNodeIndex (f : CNF) (v : Nat) :
    NodeDartIndex (occurrenceVertex f) (Sum.inl v) (variableOccurrences f v).length where
  dart i := occurrenceDart (variableOccurrenceIndex f v i) false
  injective i j h := variableOccurrenceIndex_injective f v (occurrenceDart_injective false h)
  vertex i := by rw [occurrenceVertex_even,variableOccurrenceIndex_vertex]
  complete d hd := by
    obtain ⟨i,s,rfl⟩ := occurrenceDart_cases d
    cases s
    · rw [occurrenceVertex_even] at hd
      have hm : i∈variableOccurrences f v :=
        List.mem_filter.mpr ⟨List.mem_finRange _,decide_eq_true (Sum.inl.inj hd)⟩
      obtain ⟨t,ht,he⟩ := List.mem_iff_getElem.mp hm
      exact ⟨⟨t,ht⟩,congrArg (fun i=>occurrenceDart i false) he⟩
    · rw [occurrenceVertex_odd] at hd
      contradiction

/-- The source darts of one clause in its actual list position. -/
noncomputable def clauseNodeIndex (f : CNF) (v : Nat) :
    NodeDartIndex (occurrenceVertex f) (Sum.inr v) (clauseOccurrences f v).length where
  dart i := occurrenceDart (clauseOccurrenceIndex f v i) true
  injective i j h := clauseOccurrenceIndex_injective f v (occurrenceDart_injective true h)
  vertex i := by rw [occurrenceVertex_odd,clauseOccurrenceIndex_vertex]
  complete d hd := by
    obtain ⟨i,s,rfl⟩ := occurrenceDart_cases d
    cases s
    · rw [occurrenceVertex_even] at hd
      contradiction
    · rw [occurrenceVertex_odd] at hd
      have hm : i∈clauseOccurrences f v :=
        List.mem_filter.mpr ⟨List.mem_finRange _,decide_eq_true (Sum.inr.inj hd)⟩
      obtain ⟨t,ht,he⟩ := List.mem_iff_getElem.mp hm
      exact ⟨⟨t,ht⟩,congrArg (fun i=>occurrenceDart i true) he⟩

def variableUsedPort {f : CNF} (hf : BoundedOccurrence f) (v : Nat)
    (i : Fin (variableOccurrences f v).length) : Fin 3 :=
  occurrenceLocalPort hf (variableOccurrenceIndex f v i)

theorem variableUsedPort_injective {f : CNF} (hf : BoundedOccurrence f) (v : Nat)
    (i j : Fin (variableOccurrences f v).length) (h : variableUsedPort hf v i=variableUsedPort hf v j) : i=j := by
  apply variableOccurrenceIndex_injective f v
  apply occurrence_injective f
  apply hf.placement_key_injective (occurrence_mem f _) (occurrence_mem f _)
  apply Prod.ext
  · exact (variableOccurrenceIndex_vertex f v i).trans (variableOccurrenceIndex_vertex f v j).symm
  · exact congrArg Fin.val h

noncomputable def clauseUsedPort (f : CNF) (j : Fin (placeFormula [] f).length)
    (i : Fin (clauseOccurrences f j.val).length) : Fin (placeFormula [] f)[j.val].length :=
  ⟨(occurrencePosition f (clauseOccurrenceIndex f j.val i)).slot.val,by
    have h := (occurrencePosition f (clauseOccurrenceIndex f j.val i)).slot.isLt
    simpa only [clauseOccurrenceIndex_vertex] using h⟩

theorem clauseUsedPort_injective (f : CNF) (j : Fin (placeFormula [] f).length)
    (a b : Fin (clauseOccurrences f j.val).length) (h : clauseUsedPort f j a=clauseUsedPort f j b) : a=b := by
  apply clauseOccurrenceIndex_injective f j.val
  apply occurrencePosition_injective
  · exact (clauseOccurrenceIndex_vertex f j.val a).trans (clauseOccurrenceIndex_vertex f j.val b).symm
  · exact congrArg Fin.val h

theorem finite_injection_card {m n : Nat} (f : Fin m→Fin n)
    (h : ∀i j,f i=f j→i=j) : m≤n := by
  have hn := nodup_map_of_injOn' f (List.nodup_finRange m) (fun a _ b _ he=>h a b he)
  have hb := List.Nodup.length_le_of_subset hn (l₂:=List.finRange n) (fun d _=>List.mem_finRange d)
  simpa only [List.length_map,List.length_finRange] using hb

theorem variableOccurrences_le_three {f : CNF} (hf : BoundedOccurrence f) (v : Nat) :
    (variableOccurrences f v).length≤3 :=
  finite_injection_card (variableUsedPort hf v) (variableUsedPort_injective hf v)

theorem clauseOccurrences_le_three {f : CNF} (hf : BoundedOccurrence f)
    (j : Fin (placeFormula [] f).length) : (clauseOccurrences f j.val).length≤3 := by
  have hi := finite_injection_card (clauseUsedPort f j) (clauseUsedPort_injective f j)
  have hs := hf.placed_clause_size (List.getElem_mem j.isLt)
  omega

/-- Registered incidence endpoint semantics give the node-orbit hypothesis
needed by every finite local desired-order construction. -/
theorem occurrence_node_semantics (f : CNF)
    (I : Hypermap (2*(placeFormula [] f).flatten.length))
    (hI : ∀a b,Reaches I.node a b ↔ halfEdgeEnd (incidenceGraph f) a.val=halfEdgeEnd (incidenceGraph f) b.val)
    (a b : Fin (2*(placeFormula [] f).flatten.length)) :
    Reaches I.node a b ↔ occurrenceVertex f a=occurrenceVertex f b := by
  rw [hI,occurrence_incidence_end,occurrence_incidence_end,Option.some.injEq]

end STACS2027.PlanarAssembly
