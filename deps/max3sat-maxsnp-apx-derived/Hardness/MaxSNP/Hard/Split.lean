module

public import Hardness.MaxSNP.Hard.Defs
public import Hardness.MaxSNP.Max3SAT

/-!
# Splitting long clauses into 3-clauses, with exact counting

For the splitting `splitN` of a clause with fresh variables:

* the pieces have at most three literals (`length_le_three_of_mem_splitN`);
* under every assignment a false clause loses at least one piece (`satCount_splitN_le`);
* the fresh variables can be chosen such that a true clause loses no piece and a false clause
  exactly one (`exists_satCount_splitN`).

The same statements for a list of clauses with disjoint blocks of fresh variables
(`splitFrom`): `satCount_splitFrom_le`, `exists_satCount_splitFrom`.
-/

@[expose] public section

namespace Complexity

theorem splitN_of_short (m z : Nat) {ls : SAT.Clause} (h : ls.length ≤ 3) :
    splitN m z ls = [ls] := by
  cases m with
  | zero => rfl
  | succ m => simp [splitN, h]

theorem splitN_succ_cons (m z : Nat) (l₁ l₂ l₃ l₄ : SAT.Literal) (tl : SAT.Clause) :
    splitN (m + 1) z (l₁ :: l₂ :: l₃ :: l₄ :: tl) =
      [l₁, l₂, ⟨z, true⟩] :: splitN m (z + 1) (⟨z, false⟩ :: l₃ :: l₄ :: tl) := by
  simp [splitN]

/-- A clause is short or has four literals. -/
theorem clause_cases (ls : SAT.Clause) :
    ls.length ≤ 3 ∨ ∃ l₁ l₂ l₃ l₄ tl, ls = l₁ :: l₂ :: l₃ :: l₄ :: tl := by
  match ls with
  | [] | [_] | [_, _] | [_, _, _] => left; simp
  | l₁ :: l₂ :: l₃ :: l₄ :: tl => exact Or.inr ⟨l₁, l₂, l₃, l₄, tl, rfl⟩

theorem length_le_three_of_mem_splitN (m : Nat) :
    ∀ (z : Nat) (ls : SAT.Clause), ls.length ≤ m + 3 → ∀ cl ∈ splitN m z ls, cl.length ≤ 3 := by
  induction m with
  | zero =>
    intro z ls h cl hc
    simp only [splitN, List.mem_singleton] at hc
    subst hc
    simpa using h
  | succ m ih =>
    intro z ls h cl hc
    rcases clause_cases ls with hs | ⟨l₁, l₂, l₃, l₄, tl, rfl⟩
    · rw [splitN_of_short _ _ hs, List.mem_singleton] at hc
      subst hc
      exact hs
    · rw [splitN_succ_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp
      · refine ih _ _ ?_ cl hc
        simp only [List.length_cons] at h ⊢
        omega

theorem length_splitN_le (m : Nat) :
    ∀ (z : Nat) (ls : SAT.Clause), (splitN m z ls).length ≤ m + 1 := by
  induction m with
  | zero => intro z ls; simp [splitN]
  | succ m ih =>
    intro z ls
    rcases clause_cases ls with hs | ⟨l₁, l₂, l₃, l₄, tl, rfl⟩
    · rw [splitN_of_short _ _ hs]
      simp
    · rw [splitN_succ_cons, List.length_cons]
      have := ih (z + 1) (⟨z, false⟩ :: l₃ :: l₄ :: tl)
      omega

/-- The variables of the pieces are those of the clause and the fresh ones. -/
theorem var_lt_of_mem_splitN (m : Nat) :
    ∀ (z : Nat) (ls : SAT.Clause), (∀ l ∈ ls, l.var < z) →
      ∀ cl ∈ splitN m z ls, ∀ l ∈ cl, l.var < z + m := by
  induction m with
  | zero =>
    intro z ls h cl hc l hl
    simp only [splitN, List.mem_singleton] at hc
    subst hc
    exact h l hl
  | succ m ih =>
    intro z ls h cl hc l hl
    rcases clause_cases ls with hs | ⟨l₁, l₂, l₃, l₄, tl, rfl⟩
    · rw [splitN_of_short _ _ hs, List.mem_singleton] at hc
      subst hc
      have := h l hl
      omega
    · rw [splitN_succ_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl
        · have := h l (by simp)
          omega
        · have := h l (by simp)
          omega
        · show z < z + (m + 1)
          omega
      · have := ih (z + 1) (⟨z, false⟩ :: l₃ :: l₄ :: tl) (by
          intro l' hl'
          rcases List.mem_cons.mp hl' with rfl | hl'
          · exact Nat.lt_succ_self z
          · have := h l' (by simp only [List.mem_cons] at hl' ⊢; tauto)
            omega) cl hc l hl
        omega

theorem SAT.satCount_cons (y : SAT.Assignment) (cl : SAT.Clause) (f : SAT.CNF) :
    SAT.satCount y (cl :: f) = (if SAT.evalClause y cl then 1 else 0) + SAT.satCount y f := by
  simp only [SAT.satCount, List.countP_cons]
  omega

theorem SAT.satCount_append (y : SAT.Assignment) (f g : SAT.CNF) :
    SAT.satCount y (f ++ g) = SAT.satCount y f + SAT.satCount y g := by
  simp only [SAT.satCount, List.countP_append]

theorem split_arith (b₁ b₂ bz bt : Bool) (S L : Nat)
    (h : S + (if (!bz || bt) = true then 0 else 1) ≤ L) :
    (if (b₁ || (b₂ || bz)) = true then 1 else 0) + S +
      (if (b₁ || (b₂ || bt)) = true then 0 else 1) ≤ L + 1 := by
  cases b₁ <;> cases b₂ <;> cases bz <;> cases bt <;> simp at h ⊢ <;> omega

/-- Under every assignment, a false clause loses at least one piece. -/
theorem satCount_splitN_le (y : SAT.Assignment) (m : Nat) :
    ∀ (z : Nat) (ls : SAT.Clause),
      SAT.satCount y (splitN m z ls) + (if SAT.evalClause y ls then 0 else 1) ≤
        (splitN m z ls).length := by
  have short : ∀ ls : SAT.Clause,
      SAT.satCount y [ls] + (if SAT.evalClause y ls then 0 else 1) ≤ [ls].length := by
    intro ls
    rw [SAT.satCount_cons]
    cases SAT.evalClause y ls <;> simp [SAT.satCount]
  induction m with
  | zero => intro z ls; exact short ls
  | succ m ih =>
    intro z ls
    rcases clause_cases ls with hs | ⟨l₁, l₂, l₃, l₄, tl, rfl⟩
    · rw [splitN_of_short _ _ hs]
      exact short ls
    · rw [splitN_succ_cons, SAT.satCount_cons, List.length_cons]
      have h := ih (z + 1) (⟨z, false⟩ :: l₃ :: l₄ :: tl)
      simp only [SAT.evalClause_cons, SAT.evalClause_nil, SAT.evalLiteral_positive,
        SAT.evalLiteral_negative, Bool.or_false] at h ⊢
      exact split_arith _ _ _ _ _ _ h

theorem SAT.evalLiteral_congr {a b : SAT.Assignment} {l : SAT.Literal}
    (h : a l.var = b l.var) : SAT.evalLiteral a l = SAT.evalLiteral b l := by
  simp [SAT.evalLiteral, h]

/-- The fresh variables can be chosen such that a true clause loses no piece and a false
clause exactly one. -/
theorem exists_satCount_splitN (m : Nat) :
    ∀ (z : Nat) (ls : SAT.Clause) (y : SAT.Assignment), (∀ l ∈ ls, l.var < z) →
      ∃ y' : SAT.Assignment, (∀ v, v < z ∨ z + m ≤ v → y' v = y v) ∧
        SAT.satCount y' (splitN m z ls) + (if SAT.evalClause y ls then 0 else 1) =
          (splitN m z ls).length := by
  have short : ∀ (y : SAT.Assignment) (ls : SAT.Clause),
      SAT.satCount y [ls] + (if SAT.evalClause y ls then 0 else 1) = [ls].length := by
    intro y ls
    rw [SAT.satCount_cons]
    cases SAT.evalClause y ls <;> simp [SAT.satCount]
  induction m with
  | zero => intro z ls y _; exact ⟨y, fun _ _ => rfl, short y ls⟩
  | succ m ih =>
    intro z ls y hv
    rcases clause_cases ls with hs | ⟨l₁, l₂, l₃, l₄, tl, rfl⟩
    · rw [splitN_of_short _ _ hs]
      exact ⟨y, fun _ _ => rfl, short y ls⟩
    · have hv₁ : l₁.var < z := hv l₁ (by simp)
      have hv₂ : l₂.var < z := hv l₂ (by simp)
      have hvt : ∀ l ∈ l₃ :: l₄ :: tl, l.var < z := fun l hl =>
        hv l (by simp only [List.mem_cons] at hl ⊢; tauto)
      let y₀ : SAT.Assignment := fun v =>
        if v = z then !(SAT.evalLiteral y l₁ || SAT.evalLiteral y l₂) else y v
      have hy₀ : ∀ v, v ≠ z → y₀ v = y v := fun v hne => by simp [y₀, hne]
      have hy₀z : y₀ z = !(SAT.evalLiteral y l₁ || SAT.evalLiteral y l₂) := by simp [y₀]
      obtain ⟨y', hy', hcount⟩ := ih (z + 1) (⟨z, false⟩ :: l₃ :: l₄ :: tl) y₀ (by
        intro l hl
        rcases List.mem_cons.mp hl with rfl | hl
        · exact Nat.lt_succ_self z
        · have := hvt l hl
          omega)
      have hagree : ∀ v, v < z → y' v = y v := fun v hlt => by
        rw [hy' v (Or.inl (by omega)), hy₀ v (by omega)]
      refine ⟨y', fun v hvz => ?_, ?_⟩
      · rw [hy' v (by omega), hy₀ v (by omega)]
      · rw [splitN_succ_cons, SAT.satCount_cons, List.length_cons]
        have e₁ : SAT.evalLiteral y' l₁ = SAT.evalLiteral y l₁ :=
          SAT.evalLiteral_congr (hagree _ hv₁)
        have e₂ : SAT.evalLiteral y' l₂ = SAT.evalLiteral y l₂ :=
          SAT.evalLiteral_congr (hagree _ hv₂)
        have ez : y' z = !(SAT.evalLiteral y l₁ || SAT.evalLiteral y l₂) := by
          rw [hy' z (Or.inl (Nat.lt_succ_self z)), hy₀z]
        have et : SAT.evalClause y₀ (l₃ :: l₄ :: tl) = SAT.evalClause y (l₃ :: l₄ :: tl) :=
          SAT.evalClause_congr fun l hl => hy₀ _ (by have := hvt l hl; omega)
        have e₀ : SAT.evalClause y₀ (⟨z, false⟩ :: l₃ :: l₄ :: tl) =
            SAT.evalClause y (l₁ :: l₂ :: l₃ :: l₄ :: tl) := by
          rw [SAT.evalClause_cons, et, SAT.evalLiteral_negative, hy₀z]
          simp only [SAT.evalClause_cons, Bool.not_not, Bool.or_assoc]
        rw [e₀] at hcount
        have e₃ : SAT.evalClause y' [l₁, l₂, ⟨z, true⟩] = true := by
          simp only [SAT.evalClause_cons, SAT.evalClause_nil, SAT.evalLiteral_positive, e₁, e₂,
            ez]
          cases SAT.evalLiteral y l₁ <;> cases SAT.evalLiteral y l₂ <;> rfl
        rw [e₃]
        simp only [ite_true]
        omega

/-! ### Lists of clauses -/

theorem splitFrom_nil (m base s : Nat) : splitFrom m base s [] = [] := rfl

theorem splitFrom_cons (m base s : Nat) (ls : SAT.Clause) (Ls : List SAT.Clause) :
    splitFrom m base s (ls :: Ls) =
      splitN m (base + s * m) ls ++ splitFrom m base (s + 1) Ls := by
  simp [splitFrom, List.zipIdx_cons]

theorem length_splitFrom_le (m base : Nat) (Ls : List SAT.Clause) :
    ∀ s, (splitFrom m base s Ls).length ≤ Ls.length * (m + 1) := by
  induction Ls with
  | nil => intro s; simp [splitFrom_nil]
  | cons ls Ls ih =>
    intro s
    rw [splitFrom_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have h₁ := length_splitN_le m (base + s * m) ls
    have h₂ := ih (s + 1)
    omega

theorem isThreeCNF_splitFrom (m base : Nat) (Ls : List SAT.Clause)
    (h : ∀ ls ∈ Ls, ls.length ≤ m + 3) : ∀ s, SAT.IsThreeCNF (splitFrom m base s Ls) := by
  induction Ls with
  | nil => intro s cl hc; simp [splitFrom_nil] at hc
  | cons ls Ls ih =>
    intro s cl hc
    rw [splitFrom_cons, List.mem_append] at hc
    rcases hc with hc | hc
    · exact length_le_three_of_mem_splitN m _ ls (h ls (by simp)) cl hc
    · exact ih (fun ls' h' => h ls' (List.mem_cons_of_mem _ h')) (s + 1) cl hc

/-- Under every assignment, every false clause of the list loses at least one piece. -/
theorem satCount_splitFrom_le (y : SAT.Assignment) (m base : Nat) (Ls : List SAT.Clause) :
    ∀ s, SAT.satCount y (splitFrom m base s Ls) +
      Ls.countP (fun ls => !SAT.evalClause y ls) ≤ (splitFrom m base s Ls).length := by
  induction Ls with
  | nil => intro s; simp [splitFrom_nil, SAT.satCount]
  | cons ls Ls ih =>
    intro s
    rw [splitFrom_cons, SAT.satCount_append, List.length_append, List.countP_cons]
    have h₁ := satCount_splitN_le y m (base + s * m) ls
    have h₂ := ih (s + 1)
    cases h : SAT.evalClause y ls <;> simp [h] at h₁ ⊢ <;> omega

/-- The fresh variables can be chosen such that exactly one piece is lost for every false
clause of the list. -/
theorem exists_satCount_splitFrom (m base : Nat) (Ls : List SAT.Clause)
    (hv : ∀ ls ∈ Ls, ∀ l ∈ ls, l.var < base) :
    ∀ (s : Nat) (y : SAT.Assignment),
      ∃ y' : SAT.Assignment, (∀ v, v < base + s * m → y' v = y v) ∧
        SAT.satCount y' (splitFrom m base s Ls) +
          Ls.countP (fun ls => !SAT.evalClause y ls) = (splitFrom m base s Ls).length := by
  induction Ls with
  | nil => intro s y; exact ⟨y, fun _ _ => rfl, by simp [splitFrom_nil, SAT.satCount]⟩
  | cons ls Ls ih =>
    intro s y
    have hls : ∀ l ∈ ls, l.var < base + s * m := fun l hl => by
      have := hv ls (by simp) l hl
      omega
    obtain ⟨y₁, hy₁, hc₁⟩ := exists_satCount_splitN m (base + s * m) ls y hls
    obtain ⟨y', hy', hc'⟩ := ih (fun ls' h' => hv ls' (List.mem_cons_of_mem _ h')) (s + 1) y₁
    have hmul : base + (s + 1) * m = base + s * m + m := by rw [Nat.succ_mul]; omega
    refine ⟨y', fun v hlt => ?_, ?_⟩
    · rw [hy' v (by omega), hy₁ v (Or.inl hlt)]
    · rw [splitFrom_cons, SAT.satCount_append, List.length_append, List.countP_cons]
      have e₁ : SAT.satCount y' (splitN m (base + s * m) ls) =
          SAT.satCount y₁ (splitN m (base + s * m) ls) :=
        SAT.satCount_congr fun cl hc l hl => hy' _ (by
          have := var_lt_of_mem_splitN m _ ls hls cl hc l hl
          omega)
      have e₂ : Ls.countP (fun ls => !SAT.evalClause y₁ ls) =
          Ls.countP (fun ls => !SAT.evalClause y ls) :=
        List.countP_congr fun ls' h' => by
          rw [SAT.evalClause_congr (a := y₁) (b := y) fun l hl => hy₁ _ (Or.inl (by
            have := hv ls' (List.mem_cons_of_mem _ h') l hl
            omega))]
      rw [e₁]
      rw [e₂] at hc'
      cases h : SAT.evalClause y ls <;> simp [h] at hc₁ ⊢ <;> omega

end Complexity
