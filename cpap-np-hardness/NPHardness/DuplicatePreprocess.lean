module

public import NPHardness.GlobalCompleteness
public import NPHardness.Preprocess

/-! Semantics-preserving removal of repeated literals and tautologies. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

def distinctLiterals : Clause → Clause
  | [] => []
  | l :: ls => if l ∈ ls then distinctLiterals ls else l :: distinctLiterals ls

theorem distinctLiterals_sublist (c : Clause) : List.Sublist (distinctLiterals c) c := by
  induction c with
  | nil => exact List.Sublist.refl _
  | cons l ls ih =>
    unfold distinctLiterals
    split
    · exact ih.cons l
    · exact ih.cons_cons l

theorem distinctLiterals_mem (l : Literal) (c : Clause) : l ∈ distinctLiterals c ↔ l ∈ c := by
  induction c with
  | nil => simp [distinctLiterals]
  | cons r rs ih =>
    unfold distinctLiterals
    split
    · next hr =>
        rw [ih]
        constructor
        · exact List.mem_cons_of_mem _
        · intro h
          rcases List.mem_cons.mp h with rfl | h
          · exact hr
          · exact h
    · simp only [List.mem_cons,ih]

theorem distinctLiterals_nodup (c : Clause) : (distinctLiterals c).Nodup := by
  induction c with
  | nil => simp [distinctLiterals]
  | cons l ls ih =>
    unfold distinctLiterals
    split
    · exact ih
    · next h => exact List.nodup_cons.mpr ⟨fun hm => h ((distinctLiterals_mem l ls).mp hm),ih⟩

theorem distinctLiterals_eval (a : Assignment) (c : Clause) :
    evalClause a (distinctLiterals c) = evalClause a c := by
  apply Bool.eq_iff_iff.mpr
  simp only [evalClause,List.any_eq_true,distinctLiterals_mem]

def normalizeClauses (f : CNF) : CNF := removeTautologies (f.map distinctLiterals)

theorem normalizeClauses_eval (a : Assignment) (f : CNF) : evalCNF a (normalizeClauses f) = evalCNF a f := by
  rw [normalizeClauses,removeTautologies_eval]
  induction f with
  | nil => rfl
  | cons c f ih => simp only [List.map_cons,evalCNF_cons,distinctLiterals_eval,ih]

def FormulaDeletion (g f : CNF) : Prop :=
  List.Sublist g.flatten f.flatten ∧ g.length ≤ f.length ∧
    ∀ c ∈ g, ∃ d ∈ f, List.Sublist c d

theorem FormulaDeletion.refl (f : CNF) : FormulaDeletion f f :=
  ⟨List.Sublist.refl _,Nat.le_refl _,fun c hc => ⟨c,hc,List.Sublist.refl _⟩⟩

theorem FormulaDeletion.trans {f g h : CNF} (hfg : FormulaDeletion f g) (hgh : FormulaDeletion g h) :
    FormulaDeletion f h := by
  refine ⟨hfg.1.trans hgh.1,Nat.le_trans hfg.2.1 hgh.2.1,?_⟩
  intro c hc
  obtain ⟨d,hd,hcd⟩ := hfg.2.2 c hc
  obtain ⟨e,he,hde⟩ := hgh.2.2 d hd
  exact ⟨e,he,hcd.trans hde⟩

theorem FormulaDeletion.filter (f : CNF) (p : Clause → Bool) : FormulaDeletion (f.filter p) f := by
  induction f with
  | nil => exact FormulaDeletion.refl _
  | cons c f ih =>
    cases h : p c
    · simp only [List.filter_cons,h,reduceCtorEq,↓reduceIte]
      refine ⟨?_,by have := ih.2.1; simp only [List.length_cons]; omega,?_⟩
      · exact ih.1.trans (List.sublist_append_right c f.flatten)
      · intro d hd
        obtain ⟨e,he,hde⟩ := ih.2.2 d hd
        exact ⟨e,List.mem_cons_of_mem _ he,hde⟩
    · simp only [List.filter_cons,h,↓reduceIte]
      refine ⟨(List.Sublist.refl c).append ih.1,by have := ih.2.1; simp only [List.length_cons]; omega,?_⟩
      intro d hd
      rcases List.mem_cons.mp hd with hdc | hd
      · subst d
        exact ⟨c,by simp,List.Sublist.refl _⟩
      · obtain ⟨e,he,hde⟩ := ih.2.2 d hd
        exact ⟨e,List.mem_cons_of_mem _ he,hde⟩

theorem distinctLiterals_deletion (f : CNF) : FormulaDeletion (f.map distinctLiterals) f := by
  induction f with
  | nil => exact FormulaDeletion.refl _
  | cons c f ih =>
    refine ⟨(distinctLiterals_sublist c).append ih.1,by simp,?_⟩
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨c,by simp,distinctLiterals_sublist c⟩
    · obtain ⟨e,he,hde⟩ := ih.2.2 d hd
      exact ⟨e,List.mem_cons_of_mem _ he,hde⟩

theorem normalizeClauses_deletion (f : CNF) : FormulaDeletion (normalizeClauses f) f :=
  (FormulaDeletion.filter (f.map distinctLiterals) (fun c => !tautological c)).trans (distinctLiterals_deletion f)

theorem distinct_variables_of_nodup_nontaut {c : Clause} (hn : c.Nodup) (ht : tautological c = false) :
    (c.map Literal.var).Nodup := by
  rw [List.nodup_iff_pairwise_ne,List.pairwise_map]
  apply hn.imp_of_mem
  intro l r hl hr hne he
  have hp : l.positive ≠ r.positive := by
    intro h
    apply hne
    cases l; cases r
    cases he; cases h
    rfl
  have htaut : tautological c = true := by
    apply List.any_eq_true.mpr
    refine ⟨l,hl,List.any_eq_true.mpr ⟨r,hr,?_⟩⟩
    simp [he,hp]
  rw [ht] at htaut
  cases htaut

theorem normalizeClauses_distinct (f : CNF) : ClauseVariablesDistinct (normalizeClauses f) := by
  intro c hc
  obtain ⟨hm,ht⟩ := List.mem_filter.mp hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hm
  exact distinct_variables_of_nodup_nontaut (distinctLiterals_nodup d) (by simpa using ht)

theorem FormulaDeletion.occurrences_le {g f : CNF} (h : FormulaDeletion g f) (v : Nat) (p : Bool) :
    occurrences g v p ≤ occurrences f v p := by
  rw [occurrences_eq_count,occurrences_eq_count]
  exact h.1.count_le _

theorem FormulaDeletion.threeCNF {g f : CNF} (h : FormulaDeletion g f) (hf : IsThreeCNF f) : IsThreeCNF g := by
  intro c hc
  obtain ⟨d,hd,hsub⟩ := h.2.2 c hc
  exact Nat.le_trans hsub.length_le (hf d hd)

theorem FormulaDeletion.distinct {g f : CNF} (h : FormulaDeletion g f) (hf : ClauseVariablesDistinct f) :
    ClauseVariablesDistinct g := by
  intro c hc
  obtain ⟨d,hd,hsub⟩ := h.2.2 c hc
  exact (hsub.map Literal.var).nodup (hf d hd)

end STACS2027
