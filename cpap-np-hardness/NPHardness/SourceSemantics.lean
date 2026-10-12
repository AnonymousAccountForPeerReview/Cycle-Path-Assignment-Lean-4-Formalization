module

public import NPHardness.SourceOccurrences

/-! Assignment reconstruction for the explicit occurrence-splitting map. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

def sourceLift (f : CNF) (a : Assignment) (i : Nat) : Bool :=
  match f.flatten[i]? with
  | none => false
  | some l => !(evalLiteral a l)

def sourceDecode (f : CNF) (b : Assignment) (v : Nat) : Bool :=
  match f.flatten.zipIdx.filter (fun p => p.1.var == v) with
  | [] => false
  | p :: _ => sourceValue b p

theorem sourceLift_at {f : CNF} (a : Assignment) {p : SourceOccurrence}
    (hp : p ∈ f.flatten.zipIdx) : sourceLift f a p.2 = !(evalLiteral a p.1) := by
  simp [sourceLift,List.mem_zipIdx_iff_getElem?.mp hp]

theorem sourceLift_value {f : CNF} (a : Assignment) {p : SourceOccurrence}
    (hp : p ∈ f.flatten.zipIdx) : sourceValue (sourceLift f a) p = a p.1.var := by
  unfold sourceValue
  rw [sourceLift_at a hp]
  cases h : p.1.positive <;> simp [evalLiteral,h]

theorem sourceCopies_eval (a b : Assignment) (pss : List (List SourceOccurrence))
    (h : ∀ p ∈ pss.flatten, (!(b p.2)) = evalLiteral a p.1) :
    evalCNF b (pss.map sourceCopies) = evalCNF a (pss.map (List.map Prod.fst)) := by
  induction pss with
  | nil => rfl
  | cons ps pss ih =>
    have he : evalClause b (sourceCopies ps) = evalClause a (ps.map Prod.fst) := by
      unfold sourceCopies evalClause
      simp only [List.any_map]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      constructor <;> rintro ⟨p,hp,hv⟩ <;> refine ⟨p,hp,?_⟩
      · exact (h p (List.mem_flatten.mpr ⟨ps,by simp,hp⟩)).symm.trans hv
      · exact (h p (List.mem_flatten.mpr ⟨ps,by simp,hp⟩)).trans hv
    simp only [List.map_cons,evalCNF_cons,he]
    rw [ih (fun p hp => h p (List.mem_append_right _ hp))]

theorem sourceDecode_value {f : CNF} {b : Assignment}
    (hw : evalCNF b ((sourceGroups f).flatMap sourceWheel) = true)
    {p : SourceOccurrence} (hp : p ∈ f.flatten.zipIdx) :
    sourceValue b p = sourceDecode f b p.1.var := by
  obtain ⟨hpm,hgm⟩ := sourceGroups_contains hp
  have hg : evalCNF b (sourceWheel (f.flatten.zipIdx.filter (fun q => q.1.var == p.1.var))) = true := by
    apply List.all_eq_true.mpr
    intro c hc
    exact List.all_eq_true.mp hw c (List.mem_flatMap.mpr ⟨_,hgm,hc⟩)
  unfold sourceDecode
  cases hs : f.flatten.zipIdx.filter (fun q => q.1.var == p.1.var) with
  | nil => rw [hs] at hpm; cases hpm
  | cons q qs =>
    rw [hs] at hg hpm
    exact sourceWheel_constant hg p hpm

theorem sourceDecode_literal {f : CNF} {b : Assignment}
    (hw : evalCNF b ((sourceGroups f).flatMap sourceWheel) = true)
    {p : SourceOccurrence} (hp : p ∈ f.flatten.zipIdx) :
    (!(b p.2)) = evalLiteral (sourceDecode f b) p.1 := by
  have h := sourceDecode_value hw hp
  unfold sourceValue at h
  unfold evalLiteral
  rw [← h]
  cases p.1.positive <;> simp

theorem splitSource_satisfiable (f : CNF) : Satisfiable (splitSource f) ↔ Satisfiable f := by
  constructor
  · rintro ⟨b,hb⟩
    rw [splitSource,evalCNF_append] at hb
    obtain ⟨hc,hw⟩ := Bool.and_eq_true_iff.mp hb
    refine ⟨sourceDecode f b,?_⟩
    have he := sourceCopies_eval (sourceDecode f b) b (tagSource 0 f) (by
      intro p hp
      rw [tagSource_flatten] at hp
      exact sourceDecode_literal hw hp)
    rw [tagSource_forget] at he
    exact he ▸ hc
  · rintro ⟨a,ha⟩
    refine ⟨sourceLift f a,?_⟩
    rw [splitSource,evalCNF_append,Bool.and_eq_true]
    constructor
    · have he := sourceCopies_eval a (sourceLift f a) (tagSource 0 f) (by
        intro p hp
        rw [tagSource_flatten] at hp
        rw [sourceLift_at a hp,Bool.not_not])
      rw [tagSource_forget] at he
      exact he.trans ha
    · apply List.all_eq_true.mpr
      intro c hc
      obtain ⟨ps,hps,hc⟩ := List.mem_flatMap.mp hc
      have hw : evalCNF (sourceLift f a) (sourceWheel ps) = true := by
        apply sourceWheel_of_constant
        intro p hp q hq
        obtain ⟨v,_,rfl⟩ := sourceGroups_mem hps
        obtain ⟨hp,hpv⟩ := List.mem_filter.mp hp
        obtain ⟨hq,hqv⟩ := List.mem_filter.mp hq
        rw [sourceLift_value a hp,sourceLift_value a hq,beq_iff_eq.mp hpv,beq_iff_eq.mp hqv]
      exact List.all_eq_true.mp hw c hc

end STACS2027
