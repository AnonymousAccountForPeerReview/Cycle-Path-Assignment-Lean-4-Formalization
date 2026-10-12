module

public import NPHardness.PlanarSourceFormulaGraph
public import NPHardness.SourceSemantics
public import NPHardness.PlanarSourceCycles

/-!
SAT and exact Definition 7 restrictions for the rotation-ordered occurrence
formula. The order is a genuine finite permutation whose orbits are exactly
the occurrences of each source variable. The proof reuses the checked
occurrence-lifting/decoding reduction and the signed implication-cycle counts.
No planarity, complexity, or NP-hardness hypothesis is concealed in SAT.
-/

@[expose] public section
namespace STACS2027.PlanarSource.Formula
open Complexity Complexity.SAT STACS2027.PlanarGluing

def occurrence (f : CNF) (i : Fin f.flatten.length) : SourceOccurrence := (f.flatten[i.val],i.val)

theorem occurrence_mem (f : CNF) (i : Fin f.flatten.length) : occurrence f i ∈ f.flatten.zipIdx := by
  apply List.mem_zipIdx_iff_getElem?.mpr
  simp [occurrence,List.getElem?_eq_getElem i.isLt]

theorem occurrence_of_mem {f : CNF} {p : SourceOccurrence} (hp : p ∈ f.flatten.zipIdx) :
    ∃ i : Fin f.flatten.length, occurrence f i = p := by
  have he := List.mem_zipIdx_iff_getElem?.mp hp
  have hi := (List.getElem?_eq_some_iff.mp he).1
  refine ⟨⟨p.2,hi⟩,?_⟩
  apply Prod.ext
  · exact (List.getElem?_eq_some_iff.mp he).2
  · rfl

theorem successor_range_perm {E : Nat} (rot : DartEquiv E E) (next : Nat → Nat)
    (hn : ∀ i : Fin E, next i.val = (rot.toFun i).val) :
    ((List.range E).map next).Perm (List.range E) := by
  have hinj : ∀ a ∈ List.range E, ∀ b ∈ List.range E, next a = next b → a = b := by
    intro a ha b hb he
    have ha' := List.mem_range.mp ha
    have hb' := List.mem_range.mp hb
    rw [hn ⟨a,ha'⟩,hn ⟨b,hb'⟩] at he
    exact congrArg Fin.val (rot.injective (Fin.ext he))
  have hnd := Complexity.Planar.nodup_map_of_injOn' next (List.nodup_range) hinj
  apply (List.perm_ext_iff_of_nodup hnd (List.nodup_range)).mpr
  intro a
  constructor
  · rintro hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    rw [hn ⟨i,List.mem_range.mp hi⟩]
    exact List.mem_range.mpr (rot.toFun _).isLt
  · intro ha
    let i := rot.invFun ⟨a,List.mem_range.mp ha⟩
    refine List.mem_map.mpr ⟨i.val,List.mem_range.mpr i.isLt,?_⟩
    rw [hn i]
    exact congrArg Fin.val (rot.right_inv _)

theorem pairClause_count (xs : List Nat) (p q : Nat → Literal) (l : Literal) :
    ((xs.map fun i => [p i,q i]).flatten).count l =
      (xs.map p).count l+(xs.map q).count l := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.map_cons,List.flatten_cons,List.count_append,List.count_cons,List.count_nil,ih]
    omega

/-- Each occurrence label contributes exactly once in each polarity, whatever
the rotation order and whatever its sign in the old clause. -/
theorem ringClauses_occurrences {E : Nat} (rot : DartEquiv E E)
    (next : Nat → Nat) (signs : Nat → Bool)
    (hn : ∀ i : Fin E, next i.val = (rot.toFun i).val) (v : Nat) (s : Bool) :
    occurrences (ringClauses E next signs) v s = (List.range E).count v := by
  let pos : Nat → Literal := fun i => ⟨i,signs i⟩
  let neg : Nat → Literal := fun i => ⟨i,!(signs i)⟩
  have hp := (successor_range_perm rot next hn).map neg
  have he : ((List.range E).map fun i => neg (next i)).count ⟨v,s⟩ =
      ((List.range E).map neg).count ⟨v,s⟩ := by
    simpa only [List.map_map,Function.comp_def] using hp.count_eq ⟨v,s⟩
  rw [occurrences_eq_count,ringClauses,pairClause_count]
  change ((List.range E).map pos).count ⟨v,s⟩ +
    ((List.range E).map fun i => neg (next i)).count ⟨v,s⟩ = _
  rw [he,Nat.add_comm]
  have hc := opposite_counts ((List.range E).map pos) v s
  simpa [pos,neg,negate,List.map_map,Function.comp_def] using hc

theorem ringFormula_occurrences (f : CNF) (rot : DartEquiv f.flatten.length f.flatten.length)
    (next : Nat → Nat) (signs : Nat → Bool)
    (hn : ∀ i : Fin f.flatten.length, next i.val = (rot.toFun i).val) (v : Nat) :
    occurrences (ringFormula f next signs) v true ≤ 1 ∧
      occurrences (ringFormula f next signs) v false ≤ 2 := by
  have hcount : (List.range f.flatten.length).count v ≤ 1 :=
    List.nodup_iff_count.mp (List.nodup_range) v
  have hc : ((tagSource 0 f).flatten.map Prod.snd).count v = (List.range f.flatten.length).count v := by
    simp [tagSource_flatten]
  simp only [ringFormula,occurrences_append,copyFormula,sourceCopies_occurrences,
    ringClauses_occurrences rot next signs hn,hc]
  change 0 + (List.range f.flatten.length).count v ≤ 1 ∧
    (List.range f.flatten.length).count v + (List.range f.flatten.length).count v ≤ 2
  omega

theorem ringFormula_bounded {f : CNF}
    (hf : ∀ c ∈ f, c.length = 2 ∨ c.length = 3)
    (rot : DartEquiv f.flatten.length f.flatten.length) (next : Nat → Nat) (signs : Nat → Bool)
    (hn : ∀ i : Fin f.flatten.length, next i.val = (rot.toFun i).val) :
    BoundedOccurrence (ringFormula f next signs) := by
  refine ⟨?_,fun v => (ringFormula_occurrences f rot next signs hn v).1,
    fun v => (ringFormula_occurrences f rot next signs hn v).2⟩
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨ps,hps,rfl⟩ := List.mem_map.mp hc
    have hm : ps.map Prod.fst ∈ f := by
      rw [← tagSource_forget 0 f]
      exact List.mem_map.mpr ⟨ps,hps,rfl⟩
    simpa [sourceCopies] using hf _ hm
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hc
    exact Or.inl rfl

theorem ring_clause (f : CNF) (rot : DartEquiv f.flatten.length f.flatten.length)
    (next : Nat → Nat) (signs : Nat → Bool)
    (hn : ∀ i : Fin f.flatten.length, next i.val = (rot.toFun i).val)
    (hs : ∀ i : Fin f.flatten.length, signs i.val = (f.flatten[i.val]).positive)
    (i : Fin f.flatten.length) :
    [⟨i.val,signs i.val⟩,⟨next i.val,!(signs (next i.val))⟩] =
      sourceImplication (occurrence f i) (occurrence f (rot.toFun i)) := by
  rw [hn i,hs i,hs (rot.toFun i)]
  rfl

theorem ring_propagates (f : CNF) (rot : DartEquiv f.flatten.length f.flatten.length)
    (next : Nat → Nat) (signs : Nat → Bool)
    (hn : ∀ i : Fin f.flatten.length, next i.val = (rot.toFun i).val)
    (hs : ∀ i : Fin f.flatten.length, signs i.val = (f.flatten[i.val]).positive)
    {b : Assignment} (hb : evalCNF b (ringClauses f.flatten.length next signs) = true)
    {i j : Fin f.flatten.length} (hr : Reaches rot.toFun i j) :
    sourceValue b (occurrence f i) = true → sourceValue b (occurrence f j) = true := by
  obtain ⟨t,rfl⟩ := hr
  have hstep : ∀ i, sourceValue b (occurrence f i) = true →
      sourceValue b (occurrence f (rot.toFun i)) = true := by
    intro i
    apply (sourceImplication_eval b _ _).mp
    rw [← ring_clause f rot next signs hn hs i]
    exact List.all_eq_true.mp hb _ (List.mem_map.mpr ⟨i.val,List.mem_range.mpr i.isLt,rfl⟩)
  induction t generalizing i with
  | zero => exact id
  | succ t ih => exact fun hi => ih (hstep i hi)

theorem ring_constant (f : CNF) (rot : DartEquiv f.flatten.length f.flatten.length)
    (next : Nat → Nat) (signs : Nat → Bool)
    (hn : ∀ i : Fin f.flatten.length, next i.val = (rot.toFun i).val)
    (hs : ∀ i : Fin f.flatten.length, signs i.val = (f.flatten[i.val]).positive)
    (ho : ∀ i j : Fin f.flatten.length, Reaches rot.toFun i j ↔
      (f.flatten[i.val]).var = (f.flatten[j.val]).var)
    {b : Assignment} (hb : evalCNF b (ringClauses f.flatten.length next signs) = true)
    {p q : SourceOccurrence} (hp : p ∈ f.flatten.zipIdx) (hq : q ∈ f.flatten.zipIdx)
    (he : p.1.var = q.1.var) : sourceValue b p = sourceValue b q := by
  obtain ⟨i,rfl⟩ := occurrence_of_mem hp
  obtain ⟨j,rfl⟩ := occurrence_of_mem hq
  apply Bool.eq_iff_iff.mpr
  exact ⟨ring_propagates f rot next signs hn hs hb ((ho i j).mpr he),
    ring_propagates f rot next signs hn hs hb ((ho j i).mpr he.symm)⟩

/-- Reordering occurrence cycles to the actual incidence rotation preserves
SAT. Decoding is the existing `splitSource_satisfiable` proof. -/
theorem ringFormula_satisfiable (f : CNF) (rot : DartEquiv f.flatten.length f.flatten.length)
    (next : Nat → Nat) (signs : Nat → Bool)
    (hn : ∀ i : Fin f.flatten.length, next i.val = (rot.toFun i).val)
    (hs : ∀ i : Fin f.flatten.length, signs i.val = (f.flatten[i.val]).positive)
    (ho : ∀ i j : Fin f.flatten.length, Reaches rot.toFun i j ↔
      (f.flatten[i.val]).var = (f.flatten[j.val]).var) :
    Satisfiable (ringFormula f next signs) ↔ Satisfiable f := by
  constructor
  · rintro ⟨b,hb⟩
    rw [ringFormula,evalCNF_append,Bool.and_eq_true] at hb
    apply (splitSource_satisfiable f).mp
    refine ⟨b,?_⟩
    rw [splitSource,evalCNF_append,Bool.and_eq_true]
    refine ⟨hb.1,?_⟩
    apply List.all_eq_true.mpr
    intro c hc
    obtain ⟨ps,hps,hc⟩ := List.mem_flatMap.mp hc
    have hw : evalCNF b (sourceWheel ps) = true := by
      apply sourceWheel_of_constant
      intro p hp q hq
      obtain ⟨v,_,rfl⟩ := sourceGroups_mem hps
      obtain ⟨hpm,hpv⟩ := List.mem_filter.mp hp
      obtain ⟨hqm,hqv⟩ := List.mem_filter.mp hq
      exact ring_constant f rot next signs hn hs ho hb.2 hpm hqm
        ((beq_iff_eq.mp hpv).trans (beq_iff_eq.mp hqv).symm)
    exact List.all_eq_true.mp hw c hc
  · rintro ⟨a,ha⟩
    refine ⟨sourceLift f a,?_⟩
    rw [ringFormula,evalCNF_append,Bool.and_eq_true]
    constructor
    · have he := sourceCopies_eval a (sourceLift f a) (tagSource 0 f) (by
        intro p hp
        rw [tagSource_flatten] at hp
        rw [sourceLift_at a hp,Bool.not_not])
      rw [tagSource_forget] at he
      exact he.trans ha
    · apply List.all_eq_true.mpr
      intro c hc
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hc
      let i : Fin f.flatten.length := ⟨j,List.mem_range.mp hj⟩
      rw [ring_clause f rot next signs hn hs i]
      apply (sourceImplication_eval _ _ _).mpr
      rw [sourceLift_value a (occurrence_mem f i),sourceLift_value a (occurrence_mem f (rot.toFun i))]
      have hv := (ho i (rot.toFun i)).mp (Reaches.step rot.toFun i)
      change a (f.flatten[i.val]).var = true → a (f.flatten[(rot.toFun i).val]).var = true
      rw [hv]
      exact id

/-- Total lookup used by the concrete occurrence formula. Out-of-range values
are immaterial because ring clauses enumerate exactly the occurrence indices. -/
def sourceSigns (f : CNF) (i : Nat) : Bool :=
  ((f.flatten[i]?).getD ⟨0,false⟩).positive

@[simp] theorem sourceSigns_at (f : CNF) (i : Fin f.flatten.length) :
    sourceSigns f i.val = (f.flatten[i.val]).positive := by
  simp [sourceSigns,List.getElem?_eq_getElem i.isLt]

@[simp] theorem nextIndex_at {E : Nat} (B : Embedding.BipartiteRotation E) (i : Fin E) :
    nextIndex B i.val = (B.varRot.toFun i).val := by
  simp [nextIndex,i.isLt]

def embeddedRingFormula (f : CNF) (B : Embedding.BipartiteRotation f.flatten.length) : CNF :=
  ringFormula f (nextIndex B) (sourceSigns f)

theorem embeddedRingFormula_satisfiable (f : CNF) (B : Embedding.BipartiteRotation f.flatten.length)
    (ho : ∀ i j : Fin f.flatten.length, Reaches B.varRot.toFun i j ↔
      (f.flatten[i.val]).var = (f.flatten[j.val]).var) :
    Satisfiable (embeddedRingFormula f B) ↔ Satisfiable f :=
  ringFormula_satisfiable f B.varRot (nextIndex B) (sourceSigns f)
    (nextIndex_at B) (sourceSigns_at f) ho

theorem embeddedRingFormula_bounded {f : CNF}
    (hf : ∀ c ∈ f, c.length = 2 ∨ c.length = 3)
    (B : Embedding.BipartiteRotation f.flatten.length) :
    BoundedOccurrence (embeddedRingFormula f B) :=
  ringFormula_bounded hf B.varRot (nextIndex B) (sourceSigns f) (nextIndex_at B)

theorem embeddedRingFormula_planar (f : CNF) (B : Embedding.BipartiteRotation f.flatten.length)
    (clause : Fin f.flatten.length → Fin f.length)
    (hc : ∀ i : Fin f.flatten.length,
      ((incidenceGraph f)[i.val]'(by rw [incidenceGraph_length_flatten]; exact i.isLt)).2 =
        Sum.inr (clause i).val)
    (hp : PlanarGraph (Embedding.BipartiteRotation.expandedEdges B clause)) :
    PlanarGraph (incidenceGraph (embeddedRingFormula f B)) :=
  ringFormula_planar_of_expanded f B (sourceSigns f) clause hc hp

end STACS2027.PlanarSource.Formula
