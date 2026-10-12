module

public import NPHardness.BoundedSAT

/-! The implication wheel used to split occurrences of a source variable.
Each occurrence is complemented when necessary so its original clause uses
a negative literal. The wheel contributes one literal of each polarity per
occurrence. This module proves semantics without any hardness assumption. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

abbrev SourceOccurrence := Literal × Nat

def sourceValue (a : Assignment) (p : SourceOccurrence) : Bool :=
  if p.1.positive then !(a p.2) else a p.2

def sourceImplication (p q : SourceOccurrence) : Clause :=
  [⟨p.2,p.1.positive⟩, ⟨q.2,!q.1.positive⟩]

def sourceChain (last : SourceOccurrence) : List SourceOccurrence → CNF
  | [] => []
  | p :: ps => sourceImplication last p :: sourceChain p ps

def sourceWheel : List SourceOccurrence → CNF
  | [] => []
  | p :: ps => sourceChain p (ps ++ [p])

theorem sourceImplication_eval (a : Assignment) (p q : SourceOccurrence) :
    evalClause a (sourceImplication p q) = true ↔
      (sourceValue a p = true → sourceValue a q = true) := by
  simp only [sourceImplication,evalClause_cons,evalClause_nil,evalLiteral,sourceValue]
  cases p.1.positive <;> cases q.1.positive <;> cases a p.2 <;> cases a q.2 <;> decide

theorem sourceChain_propagates {a : Assignment} {p : SourceOccurrence} {ps : List SourceOccurrence}
    (h : evalCNF a (sourceChain p ps) = true) (hp : sourceValue a p = true) :
    ∀ q ∈ ps, sourceValue a q = true := by
  induction ps generalizing p with
  | nil => simp
  | cons q qs ih =>
    have hh : evalClause a (sourceImplication p q) = true ∧ evalCNF a (sourceChain q qs) = true := by
      simpa only [sourceChain,evalCNF_cons,Bool.and_eq_true] using h
    obtain ⟨hq,hqs⟩ := hh
    have hq' := (sourceImplication_eval a p q).mp hq hp
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hq'
    · exact ih hqs hq' r hr

theorem sourceChain_returns {a : Assignment} {p z : SourceOccurrence} {ps : List SourceOccurrence}
    (h : evalCNF a (sourceChain p (ps ++ [z])) = true) :
    ∀ q ∈ p :: ps, sourceValue a q = true → sourceValue a z = true := by
  induction ps generalizing p with
  | nil =>
    intro q hq
    have hqp : q = p := by simpa using hq
    subst q
    apply (sourceImplication_eval a p z).mp
    simpa [sourceChain] using h
  | cons q qs ih =>
    have hh : evalClause a (sourceImplication p q) = true ∧
        evalCNF a (sourceChain q (qs ++ [z])) = true := by
      simpa only [List.cons_append,sourceChain,evalCNF_cons,Bool.and_eq_true] using h
    obtain ⟨hp,ht⟩ := hh
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · intro hv
      exact ih ht q (by simp) ((sourceImplication_eval a _ q).mp hp hv)
    · exact ih ht r hr

theorem sourceWheel_constant {a : Assignment} {p : SourceOccurrence} {ps : List SourceOccurrence}
    (h : evalCNF a (sourceWheel (p :: ps)) = true) :
    ∀ q ∈ p :: ps, sourceValue a q = sourceValue a p := by
  intro q hq
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact sourceChain_returns h q hq
  · intro hp
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp
    · exact sourceChain_propagates h hp q (List.mem_append_left _ hq)

theorem sourceChain_of_constant {a : Assignment} {p : SourceOccurrence} {ps : List SourceOccurrence}
    (h : ∀ q ∈ ps, sourceValue a q = sourceValue a p) :
    evalCNF a (sourceChain p ps) = true := by
  induction ps generalizing p with
  | nil => rfl
  | cons q qs ih =>
    have hq := h q (by simp)
    simp only [sourceChain,evalCNF_cons,Bool.and_eq_true]
    constructor
    · exact (sourceImplication_eval a p q).mpr (fun hp => hq.trans hp)
    · exact ih (fun r hr => (h r (by simp [hr])).trans hq.symm)

theorem sourceWheel_of_constant {a : Assignment} {ps : List SourceOccurrence}
    (h : ∀ p ∈ ps, ∀ q ∈ ps, sourceValue a p = sourceValue a q) :
    evalCNF a (sourceWheel ps) = true := by
  cases ps with
  | nil => rfl
  | cons p ps =>
    apply sourceChain_of_constant
    intro q hq
    exact h q (by simpa [List.mem_append,List.mem_cons,or_comm] using hq) p (by simp)

theorem sourceChain_clause_length (p : SourceOccurrence) (ps : List SourceOccurrence) :
    ∀ c ∈ sourceChain p ps, c.length = 2 := by
  induction ps generalizing p with
  | nil => simp [sourceChain]
  | cons q qs ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · rfl
    · exact ih q c hc

theorem sourceWheel_clause_length (ps : List SourceOccurrence) :
    ∀ c ∈ sourceWheel ps, c.length = 2 := by
  cases ps with
  | nil => simp [sourceWheel]
  | cons p ps => exact sourceChain_clause_length p (ps ++ [p])

end STACS2027
