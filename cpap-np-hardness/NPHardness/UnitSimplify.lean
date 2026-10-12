module

public import NPHardness.DuplicatePreprocess

/-! Unit propagation with proved semantics and strict clause-count decrease. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

def assignLiteral (l : Literal) (a : Assignment) : Assignment :=
  fun v => if v = l.var then l.positive else a v

def setLiteral (l : Literal) : CNF → CNF
  | [] => []
  | c :: f => if l ∈ c then setLiteral l f
      else (c.filter fun r => r.var != l.var) :: setLiteral l f

theorem assignLiteral_self (l : Literal) (a : Assignment) : evalLiteral (assignLiteral l a) l = true := by
  cases l with
  | mk v p => cases p <;> simp [evalLiteral,assignLiteral]

theorem assignLiteral_away (l r : Literal) (a : Assignment) (h : r.var ≠ l.var) :
    evalLiteral (assignLiteral l a) r = evalLiteral a r := by
  simp [evalLiteral,assignLiteral,h]

theorem opposite_literal_false (a : Assignment) {l r : Literal}
    (hl : evalLiteral a l = true) (hv : r.var = l.var) (hne : r ≠ l) : evalLiteral a r = false := by
  cases l with
  | mk v p => cases r with
    | mk w q =>
      change w = v at hv
      subst w
      cases p <;> cases q <;> simp_all [evalLiteral]

theorem evalClause_filter_assigned (a : Assignment) {l : Literal} (hl : evalLiteral a l = true)
    (c : Clause) (hc : l ∉ c) : evalClause a (c.filter fun r => r.var != l.var) = evalClause a c := by
  induction c with
  | nil => rfl
  | cons r rs ih =>
    have hrl : r ≠ l := fun h => hc (by simp [h])
    have htail : l ∉ rs := fun h => hc (List.mem_cons_of_mem _ h)
    by_cases hvar : r.var = l.var
    · have hf := opposite_literal_false a hl hvar hrl
      simpa [hvar,hf] using ih htail
    · simpa [hvar] using congrArg (fun b => evalLiteral a r || b) (ih htail)

theorem setLiteral_eval (a : Assignment) {l : Literal} (hl : evalLiteral a l = true) (f : CNF) :
    evalCNF a (setLiteral l f) = evalCNF a f := by
  induction f with
  | nil => rfl
  | cons c f ih =>
    unfold setLiteral
    split
    · next hc =>
        have hcl : evalClause a c = true := List.any_eq_true.mpr ⟨l,hc,hl⟩
        simpa [hcl] using ih
    · next hc =>
        simp only [evalCNF_cons,evalClause_filter_assigned a hl c hc,ih]

theorem setLiteral_avoids (l : Literal) (f : CNF) :
    ∀ c ∈ setLiteral l f, ∀ r ∈ c, r.var ≠ l.var := by
  induction f with
  | nil => simp [setLiteral]
  | cons c f ih =>
    unfold setLiteral
    split
    · exact ih
    · intro d hd r hr
      rcases List.mem_cons.mp hd with hdc | hd
      · subst d
        exact bne_iff_ne.mp (List.mem_filter.mp hr).2
      · exact ih d hd r hr

theorem evalClause_congr_literals (a b : Assignment) (c : Clause)
    (h : ∀ l ∈ c, evalLiteral a l = evalLiteral b l) : evalClause a c = evalClause b c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    rw [evalClause_cons,evalClause_cons,h l (by simp),ih (fun r hr => h r (by simp [hr]))]

theorem evalCNF_congr_literals (a b : Assignment) (f : CNF)
    (h : ∀ c ∈ f, ∀ l ∈ c, evalLiteral a l = evalLiteral b l) : evalCNF a f = evalCNF b f := by
  induction f with
  | nil => rfl
  | cons c f ih =>
    rw [evalCNF_cons,evalCNF_cons,evalClause_congr_literals a b c (h c (by simp)),
      ih (fun d hd => h d (by simp [hd]))]

theorem setLiteral_satisfiable {f : CNF} {l : Literal} (hu : [l] ∈ f) :
    Satisfiable (setLiteral l f) ↔ Satisfiable f := by
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨assignLiteral l a,?_⟩
    rw [← setLiteral_eval (assignLiteral l a) (assignLiteral_self l a) f]
    rw [evalCNF_congr_literals (assignLiteral l a) a (setLiteral l f)
      (fun c hc r hr => assignLiteral_away l r a (setLiteral_avoids l f c hc r hr))]
    exact ha
  · rintro ⟨a,ha⟩
    have hl : evalLiteral a l = true := by
      have h := List.all_eq_true.mp ha [l] hu
      simpa using h
    exact ⟨a,by rw [setLiteral_eval a hl f]; exact ha⟩

theorem setLiteral_deletion (l : Literal) (f : CNF) : FormulaDeletion (setLiteral l f) f := by
  induction f with
  | nil => exact FormulaDeletion.refl _
  | cons c f ih =>
    unfold setLiteral
    split
    · refine ⟨ih.1.trans (List.sublist_append_right c f.flatten),by have := ih.2.1; simp; omega,?_⟩
      intro d hd
      obtain ⟨e,he,hde⟩ := ih.2.2 d hd
      exact ⟨e,List.mem_cons_of_mem _ he,hde⟩
    · refine ⟨List.filter_sublist.append ih.1,by have := ih.2.1; simp; omega,?_⟩
      intro d hd
      rcases List.mem_cons.mp hd with hdc | hd
      · subst d
        exact ⟨c,by simp,List.filter_sublist⟩
      · obtain ⟨e,he,hde⟩ := ih.2.2 d hd
        exact ⟨e,List.mem_cons_of_mem _ he,hde⟩

theorem setLiteral_length_lt {l : Literal} {f : CNF} (hu : [l] ∈ f) :
    (setLiteral l f).length < f.length := by
  induction f with
  | nil => simp at hu
  | cons c f ih =>
    unfold setLiteral
    split
    · have hle := (setLiteral_deletion l f).2.1
      simp only [List.length_cons]
      omega
    · next hc =>
        have htail : [l] ∈ f := by
          rcases List.mem_cons.mp hu with h | h
          · subst c
            exact False.elim (hc (by simp))
          · exact h
        have hlt := ih htail
        simp only [List.length_cons]
        omega

theorem empty_clause_unsatisfiable {f : CNF} (h : [] ∈ f) : ¬ Satisfiable f := by
  rintro ⟨a,ha⟩
  have hfalse := List.all_eq_true.mp ha [] h
  cases hfalse

end STACS2027
