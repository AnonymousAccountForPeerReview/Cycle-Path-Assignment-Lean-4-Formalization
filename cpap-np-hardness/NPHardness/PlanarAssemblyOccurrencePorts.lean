module

public import NPHardness.PlanarAssemblyIndexPorts
public import NPHardness.PlanarGluingOrientation

/-! Inject the two ends of every actual formula occurrence into its allocated
variable and clause port darts. Local face choices stay parameters, allowing
the embedding and its reflection to be chosen before this exact indexing. -/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.SAT Complexity.Planar PlanarGluing

abbrev OccurrenceIndex (f : CNF) := Fin (placeFormula [] f).flatten.length

def occurrence (f : CNF) (i : OccurrenceIndex f) : PlacedLiteral :=
  (placeFormula [] f).flatten[i.val]

theorem occurrence_mem (f : CNF) (i : OccurrenceIndex f) :
    occurrence f i ∈ (placeFormula [] f).flatten := List.getElem_mem i.isLt

theorem occurrence_injective (f : CNF) {i j : OccurrenceIndex f}
    (h : occurrence f i=occurrence f j) : i=j :=
  Fin.ext (((placedOccurrences_nodup f).getElem_inj (hi := i.isLt) (hj := j.isLt)).mp h)

theorem occurrence_variable_lt {f : CNF} (_hf : BoundedOccurrence f) (i : OccurrenceIndex f) :
    (occurrence f i).literal.var < variableBound f := by
  obtain ⟨c,hc,hp⟩ := List.mem_flatten.mp (placement_literal_mem (occurrence_mem f i))
  exact literal_lt_variableBound hc hp

def occurrenceVariable {f : CNF} (hf : BoundedOccurrence f) (i : OccurrenceIndex f) :
    Fin (variableBound f) := ⟨(occurrence f i).literal.var,occurrence_variable_lt hf i⟩

def occurrenceLocalPort {f : CNF} (hf : BoundedOccurrence f) (i : OccurrenceIndex f) : Fin 3 :=
  ⟨(occurrence f i).port,hf.placement_port_lt (occurrence_mem f i)⟩

def LocalPortChoices.variableOccurrencePort {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f) (i : OccurrenceIndex f) :
    Fin (2*(ungluedFormulaPieces k f).flatten.length) :=
  variableGlobalDart k f (occurrenceVariable hf i)
    (C.varDart (occurrenceVariable hf i) (occurrenceLocalPort hf i))

noncomputable def LocalPortChoices.clauseOccurrencePort {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (i : OccurrenceIndex f) :
    Fin (2*(ungluedFormulaPieces k f).flatten.length) :=
  clauseGlobalDart k f (occurrencePosition f i).clause
    (C.clause (occurrencePosition f i).clause (occurrencePosition f i).slot)

theorem LocalPortChoices.variableOccurrencePort_injective {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f) {i j : OccurrenceIndex f}
    (h : C.variableOccurrencePort hf i=C.variableOccurrencePort hf j) : i=j := by
  have hv := variableGlobalDart_piece_injective k f h
  have hp : occurrenceLocalPort hf i=occurrenceLocalPort hf j := by
    unfold variableOccurrencePort at h
    rw [← hv] at h
    exact C.variable_injective _ _ _ (variableGlobalDart_injective k f _ h)
  have hk : (occurrence f i).key=(occurrence f j).key :=
    Prod.ext (congrArg Fin.val hv) (congrArg Fin.val hp)
  exact occurrence_injective f
    (hf.placement_key_injective (occurrence_mem f i) (occurrence_mem f j) hk)

theorem LocalPortChoices.clause_global_injective {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) {j j' : Fin (placeFormula [] f).length}
    {i : Fin (placeFormula [] f)[j.val].length}
    {i' : Fin (placeFormula [] f)[j'.val].length}
    (h : clauseGlobalDart k f j (C.clause j i)=clauseGlobalDart k f j' (C.clause j' i')) :
    j=j' ∧ i.val=i'.val := by
  have hj := clauseGlobalDart_piece_injective k f h
  subst j'
  have hi := C.clause_injective j i i' (clauseGlobalDart_injective k f j h)
  exact ⟨rfl,congrArg Fin.val hi⟩

theorem occurrencePosition_get (f : CNF) (i : OccurrenceIndex f) :
    ((placeFormula [] f)[(occurrencePosition f i).clause.val])[(occurrencePosition f i).slot.val]? =
      some (occurrence f i) := by
  rw [List.getElem?_eq_getElem (occurrencePosition f i).slot.isLt]
  exact congrArg some (occurrencePosition f i).value

theorem LocalPortChoices.clauseOccurrencePort_injective {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) {i j : OccurrenceIndex f}
    (h : C.clauseOccurrencePort i=C.clauseOccurrencePort j) : i=j := by
  obtain ⟨hc,hs⟩ := C.clause_global_injective h
  have hi := occurrencePosition_get f i
  have hj := occurrencePosition_get f j
  simp only [← hc,← hs] at hj
  exact occurrence_injective f (Option.some.inj (hi.symm.trans hj))

theorem LocalPortChoices.variableOccurrencePort_ne_clauseOccurrencePort
    {k : Nat} {f : CNF} (C : LocalPortChoices k f) (hf : BoundedOccurrence f)
    (i j : OccurrenceIndex f) : C.variableOccurrencePort hf i≠C.clauseOccurrencePort j :=
  variableGlobalDart_ne_clauseGlobalDart k f _ _ _ _

/-- Even source darts select variable ports and odd darts clause ports. -/
noncomputable def LocalPortChoices.sourcePort {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f)
    (d : Fin (2*(placeFormula [] f).flatten.length)) :
    Fin (2*(ungluedFormulaPieces k f).flatten.length) :=
  let i : OccurrenceIndex f := ⟨d.val/2,by have := d.isLt; omega⟩
  if d.val%2=0 then C.variableOccurrencePort hf i else C.clauseOccurrencePort i

theorem LocalPortChoices.sourcePort_injective {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f)
    (d e : Fin (2*(placeFormula [] f).flatten.length))
    (h : C.sourcePort hf d=C.sourcePort hf e) : d=e := by
  unfold sourcePort at h
  dsimp only at h
  split at h <;> split at h
  · have hi := congrArg Fin.val (C.variableOccurrencePort_injective hf h)
    apply Fin.ext
    dsimp only at hi
    omega
  · exact False.elim (C.variableOccurrencePort_ne_clauseOccurrencePort hf _ _ h)
  · exact False.elim (C.variableOccurrencePort_ne_clauseOccurrencePort hf _ _ h.symm)
  · have hi := congrArg Fin.val (C.clauseOccurrencePort_injective h)
    apply Fin.ext
    dsimp only at hi
    omega

def occurrenceDart {f : CNF} (i : OccurrenceIndex f) (side : Bool) :
    Fin (2*(placeFormula [] f).flatten.length) :=
  ⟨2*i.val+(if side then 1 else 0), by have := i.isLt; cases side <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega⟩

@[simp] theorem LocalPortChoices.sourcePort_even {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f) (i : OccurrenceIndex f) :
    C.sourcePort hf (occurrenceDart i false)=C.variableOccurrencePort hf i := by
  simp only [sourcePort,occurrenceDart,Bool.false_eq_true,↓reduceIte,Nat.add_zero,
    Nat.mul_mod_right,Nat.mul_div_right,show 0<2 by decide]

@[simp] theorem LocalPortChoices.sourcePort_odd {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f) (i : OccurrenceIndex f) :
    C.sourcePort hf (occurrenceDart i true)=C.clauseOccurrencePort i := by
  simp only [sourcePort,occurrenceDart,↓reduceIte]
  have hd : (2*i.val+1)/2=i.val := by omega
  have hm : (2*i.val+1)%2=1 := by omega
  simp only [hd,hm,show ¬1=0 by decide,↓reduceIte]

theorem occurrenceDart_graphEdge {f : CNF} (i : OccurrenceIndex f) (side : Bool) :
    graphEdge (occurrenceDart i side)=occurrenceDart i (!side) := by
  apply Fin.ext
  cases side <;> simp only [graphEdge,occurrenceDart,Bool.not_false,Bool.not_true,
    Bool.false_eq_true,↓reduceIte,Nat.add_zero]
  · have hm : (2*i.val)%2=0 := by omega
    simp [ed,hm]
  · have hm : (2*i.val+1)%2=1 := by omega
    simp [ed,hm]

end STACS2027.PlanarAssembly
