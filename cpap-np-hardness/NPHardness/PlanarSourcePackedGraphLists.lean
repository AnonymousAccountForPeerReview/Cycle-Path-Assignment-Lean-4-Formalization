module

public import NPHardness.PlanarSourceGraphSerialization
public import NPHardness.PlanarSourcePackedRingPhase

/-! Dense graph-record composition over packed source blocks. Both clause
and literal offsets are accumulated from the actual input lists. -/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.Planar Complexity.Planar.Emit Complexity.StackTableauEmitter

@[simp] theorem copiesAt_length (base : Nat) (f : CNF) : (copiesAt base f).length=f.length := by
  rw [copiesAt_tagSource]
  exact Formula.tagCopies_length base f

def copyGraphAt (flips : EndpointChoices) (k n cb lb : Nat) (f : CNF) : CNF :=
  orientedClauseRecordsAt flips k n cb
    ((copiesAt lb f).map (List.map (fun l => PlacedLiteral.mk l 0)))

theorem copyGraphAt_append (flips : EndpointChoices) (k n cb lb : Nat) (f g : CNF) :
    copyGraphAt flips k n cb lb (f++g)=
      copyGraphAt flips k n cb lb f ++
      copyGraphAt flips k n (cb+f.length) (lb+f.flatten.length) g := by
  simp only [copyGraphAt,copiesAt_append,List.map_append,orientedClauseRecordsAt_append,
    List.length_map,copiesAt_length]

/-- Exact dense offsets in the two independently counted coordinates. -/
theorem copyGraphAt_reverse_blocks (flips : EndpointChoices) (k n cb lb clauses literals N : Nat)
    (F : Nat→CNF) (hc : ∀i,i<N→(F i).length=clauses)
    (hl : ∀i,i<N→(F i).flatten.length=literals) :
    copyGraphAt flips k n cb lb ((List.range N).reverse.flatMap F)=
      (List.range N).reverse.flatMap (fun i =>
        copyGraphAt flips k n (cb+(N-1-i)*clauses) (lb+(N-1-i)*literals) (F i)) := by
  induction N generalizing cb lb with
  | zero => rfl
  | succ N ih =>
    rw [range_reverse_succ_flatMap,copyGraphAt_append,hc N (by omega),hl N (by omega),
      range_reverse_succ_flatMap,ih (cb+clauses) (lb+literals)
        (fun i hi => hc i (by omega)) (fun i hi => hl i (by omega))]
    simp only [Nat.add_sub_cancel,Nat.sub_self,Nat.zero_mul,Nat.add_zero]
    congr 1
    apply flatMap_congr_range
    intro i hi
    have hn : N-i=(N-1-i)+1 := by omega
    have hec : cb+clauses+(N-1-i)*clauses=cb+(N-i)*clauses := by rw [hn,Nat.add_mul]; omega
    have hel : lb+literals+(N-1-i)*literals=lb+(N-i)*literals := by rw [hn,Nat.add_mul]; omega
    rw [hec,hel]

/-- Expand each copied occurrence into an arbitrary list of graph records.
The result may contain both budget ticks and edge records. -/
def expandCopyRecords (records : Nat→CNF) (copies : CNF) : CNF :=
  copies.flatten.flatMap (fun l => records l.var)

@[simp] theorem expandCopyRecords_append (records : Nat→CNF) (f g : CNF) :
    expandCopyRecords records (f++g)=expandCopyRecords records f++expandCopyRecords records g := by
  simp only [expandCopyRecords,List.flatten_append,List.flatMap_append]

theorem expandCopyRecords_flatMap {α : Type} (records : Nat→CNF) (xs : List α) (F : α→CNF) :
    expandCopyRecords records (xs.flatMap F)=xs.flatMap (fun x => expandCopyRecords records (F x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,expandCopyRecords_append,ih]

theorem expandCopyRecords_copiesAt (records : Nat→CNF) (base : Nat) (f : CNF) :
    expandCopyRecords records (copiesAt base f)=(List.range' base f.flatten.length).flatMap records := by
  rw [copiesAt_tagSource]
  have he (ps : List (List SourceOccurrence)) :
      expandCopyRecords records (ps.map sourceCopies)=
        (ps.flatten.map Prod.snd).flatMap records := by
    have hf : (ps.map sourceCopies).flatten=
        ps.flatten.map (fun p => (⟨p.2,false⟩ : Literal)) := by
      induction ps with
      | nil => rfl
      | cons p ps ih => simp [sourceCopies,ih]
    simp only [expandCopyRecords,hf,List.flatMap_map]
  rw [he,tagSource_flatten]
  have hi : (f.flatten.zipIdx base).map Prod.snd=List.range' base f.flatten.length := by
    apply List.ext_getElem
    · simp
    · intro i hi hj; simp
  rw [hi]

/-- The global implication phase follows from local occurrence-record blocks
without recomputing or flattening the source formula in the emitter. -/
theorem ringGraphRecords_expandCopies (flips : EndpointChoices) (k n base : Nat)
    (next : Nat→Nat) (signs : Nat→Bool) (f : CNF) :
    expandCopyRecords (fun i => orientedClauseGraphRecords flips k n (base+i)
      [⟨⟨i,signs i⟩,if signs i then 0 else 1⟩,
       ⟨⟨next i,!(signs (next i))⟩,if !(signs (next i)) then 0 else 1⟩]) (copiesAt 0 f) =
      orientedClauseRecordsAt flips k n base (Formula.ringPlaced f.flatten.length next signs) := by
  rw [expandCopyRecords_copiesAt,Formula.ringClauseRecordsAt_explicit]
  rw [← List.range_eq_range']

end STACS2027.PlanarSource.Packed
