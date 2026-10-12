module

public import Runtimes.TwoSatScc
public import Complexity.SAT
import Mathlib.Tactic

/-!
# Linear-time 2-SAT (ANONYMIZED–ANONYMIZED–ANONYMIZED 1979): the abstract algorithm and its correctness

Formulas are those of the registered foundation (`Complexity.SAT`). A **2-CNF over the
variables `0, …, n - 1`** (`IsTwoCNF n f`) has clauses of exactly two literals (a clause
`[l, l]` is allowed and means `l`) whose variables are below `n`.

* **Literal codes and the implication graph.** The literal `l` is the node
  `code l = 2 · var + (if positive then 0 else 1)`; `neg u` is the complementary node
  (`neg (code l)` is the code of the negated literal). The codes of a formula, clause after
  clause, are `codes f` (the input of the machine); read in pairs `a, b` they give the arcs
  `neg a → b` and `neg b → a` (`arcsOfCodes`), and `outOf A u` lists the ends of the arcs of
  `A` leaving `u` (the out-neighbour lists searched by `Scc`).
* **Semantics** (`reach_val`): under an assignment satisfying `f`, truth propagates along the
  arcs, hence along paths.
* **The criterion** (`criterion`): for any labelling `comp` of the `2n` nodes that does not
  increase along arcs and in which equal labels imply reachability, `f` is unsatisfiable iff
  some variable has both of its literals with the same label, and otherwise the assignment
  `x ↦ (comp (2x) < comp (2x + 1))` satisfies `f` (`x` is true iff the component of `x`
  comes *after* that of `¬x` in the topological order "decreasing labels").
* **The algorithm** (`lab n cl`: the final labels of the path-based search `Scc.final` on the
  implication graph; `okB n cl`: no conflict; `asg n cl`: the assignment) and its
  **correctness** (`twoSat_correct`): `okB n (codes f) = true ↔ Satisfiable f`, and if so,
  `asg n (codes f)` satisfies `f`.
-/

@[expose] public section

namespace STACS2027.Runtimes.TwoSat

open Complexity.SAT Scc

/-! ### Literal codes -/

/-- The node of a literal: `2 · var` for `x var`, `2 · var + 1` for `¬ x var`. -/
def code (l : Literal) : ℕ := 2 * l.var + (if l.positive then 0 else 1)

/-- The complementary node. -/
def neg (u : ℕ) : ℕ := if u % 2 = 0 then u + 1 else u - 1

/-- The truth value of the literal with code `u` under `σ`. -/
def nodeVal (σ : Assignment) (u : ℕ) : Bool := if u % 2 = 0 then σ (u / 2) else !σ (u / 2)

theorem nodeVal_even (σ : Assignment) (x : ℕ) : nodeVal σ (2 * x) = σ x := by
  simp [nodeVal]

theorem nodeVal_odd (σ : Assignment) (x : ℕ) : nodeVal σ (2 * x + 1) = !σ x := by
  have h1 : (2 * x + 1) % 2 = 1 := by omega
  have h2 : (2 * x + 1) / 2 = x := by omega
  simp [nodeVal, h1, h2]

theorem nodeVal_code (σ : Assignment) (l : Literal) : nodeVal σ (code l) = evalLiteral σ l := by
  rcases l with ⟨v, p⟩
  cases p
  · have hc : code ⟨v, false⟩ = 2 * v + 1 := by simp [code]
    rw [hc, nodeVal_odd]; rfl
  · have hc : code ⟨v, true⟩ = 2 * v := by simp [code]
    rw [hc, nodeVal_even]; rfl

theorem nodeVal_neg (σ : Assignment) (u : ℕ) : nodeVal σ (neg u) = !nodeVal σ u := by
  unfold nodeVal neg
  by_cases h : u % 2 = 0
  · have h1 : (u + 1) % 2 = 1 := by omega
    have h2 : (u + 1) / 2 = u / 2 := by omega
    simp [h, h1, h2]
  · have h1 : (u - 1) % 2 = 0 := by omega
    have h2 : (u - 1) / 2 = u / 2 := by omega
    simp [h, h1, h2]

theorem neg_lt {n u : ℕ} (hu : u < 2 * n) : neg u < 2 * n := by
  unfold neg; split <;> omega

theorem neg_even (x : ℕ) : neg (2 * x) = 2 * x + 1 := by simp [neg]

theorem neg_odd (x : ℕ) : neg (2 * x + 1) = 2 * x := by
  have h : ¬ (2 * x + 1) % 2 = 0 := by omega
  simp only [neg, h, ↓reduceIte]; omega

theorem code_lt {n : ℕ} {l : Literal} (h : l.var < n) : code l < 2 * n := by
  unfold code; split <;> omega

/-! ### Formulas, codes and arcs -/

/-- A 2-CNF over the variables `0, …, n - 1`: every clause has exactly two literals, with
variables below `n`. -/
def IsTwoCNF (n : ℕ) (f : CNF) : Prop := ∀ c ∈ f, c.length = 2 ∧ ∀ l ∈ c, l.var < n

/-- The literal codes of a formula, clause after clause. -/
def codes (f : CNF) : List ℕ := f.flatMap fun c => c.map code

/-- The arcs of the implication graph of a list of codes read in pairs `a, b`:
`neg a → b` and `neg b → a`. -/
def arcsOfCodes : List ℕ → List (ℕ × ℕ)
  | a :: b :: rest => (neg a, b) :: (neg b, a) :: arcsOfCodes rest
  | _ => []

/-- The ends of the arcs of `A` leaving `u`, in the order of `A`. -/
def outOf (A : List (ℕ × ℕ)) (u : ℕ) : List ℕ := A.flatMap fun e => if e.1 = u then [e.2] else []

theorem mem_outOf {A : List (ℕ × ℕ)} {u w : ℕ} : w ∈ outOf A u ↔ (u, w) ∈ A := by
  simp only [outOf, List.mem_flatMap]
  constructor
  · rintro ⟨e, he, hw⟩
    split at hw
    · rename_i h; simp at hw; subst hw; subst h; exact he
    · simp at hw
  · intro h; exact ⟨(u, w), h, by simp⟩

/-- The out-neighbour lists of the implication graph. -/
def nbOf (cl : List ℕ) : ℕ → List ℕ := outOf (arcsOfCodes cl)

/-- All codes are nodes of the implication graph on `n` variables. -/
def CodesOk (n : ℕ) (cl : List ℕ) : Prop := ∀ a ∈ cl, a < 2 * n

theorem mem_arcsOfCodes {n : ℕ} : ∀ {cl : List ℕ}, CodesOk n cl → ∀ e ∈ arcsOfCodes cl,
    e.1 < 2 * n ∧ e.2 < 2 * n
  | a :: b :: rest, h, e, he => by
    have ha := h a (by simp)
    have hb := h b (by simp)
    simp only [arcsOfCodes, List.mem_cons] at he
    rcases he with rfl | rfl | he
    · exact ⟨neg_lt ha, hb⟩
    · exact ⟨neg_lt hb, ha⟩
    · exact mem_arcsOfCodes (fun x hx => h x (by simp [hx])) e he
  | [], _, _, he => by simp [arcsOfCodes] at he
  | [_], _, _, he => by simp [arcsOfCodes] at he

theorem closed_nbOf {n : ℕ} {cl : List ℕ} (h : CodesOk n cl) : Closed (2 * n) (nbOf cl) :=
  fun _ _ _ hw => (mem_arcsOfCodes h _ (mem_outOf.mp hw)).2

theorem codes_ok {n : ℕ} {f : CNF} (hf : IsTwoCNF n f) : CodesOk n (codes f) := by
  intro a ha
  simp only [codes, List.mem_flatMap, List.mem_map] at ha
  obtain ⟨c, hc, l, hl, rfl⟩ := ha
  exact code_lt ((hf c hc).2 l hl)

theorem length_codes {n : ℕ} {f : CNF} (hf : IsTwoCNF n f) : (codes f).length = 2 * f.length := by
  induction f with
  | nil => rfl
  | cons c f ih =>
    have := (hf c (by simp)).1
    simp only [codes, List.flatMap_cons, List.length_append, List.length_map, List.length_cons]
      at ih ⊢
    rw [ih (fun c' hc' => hf c' (by simp [hc'])), this]; ring

/-- The arcs of a clause `[a, b]`. -/
theorem arcs_cons_clause (a b : Literal) (f : CNF) :
    arcsOfCodes (codes ([a, b] :: f)) =
      (neg (code a), code b) :: (neg (code b), code a) :: arcsOfCodes (codes f) := by
  simp [codes, arcsOfCodes]

/-! ### Semantics of the implication graph -/

theorem clause_eq {n : ℕ} {f : CNF} (hf : IsTwoCNF n f) {c : Clause} (hc : c ∈ f) :
    ∃ a b, c = [a, b] := List.length_eq_two.mp (hf c hc).1

/-- The two arcs of a clause `[a, b]` of `f`. -/
theorem clause_arcs_mem {n : ℕ} {f : CNF} (hf : IsTwoCNF n f) {a b : Literal} (hab : [a, b] ∈ f) :
    (neg (code a), code b) ∈ arcsOfCodes (codes f) ∧ (neg (code b), code a) ∈ arcsOfCodes (codes f) := by
  induction f with
  | nil => simp at hab
  | cons c f ih =>
    obtain ⟨a', b', rfl⟩ := clause_eq hf (List.mem_cons_self)
    rw [arcs_cons_clause]
    rcases List.mem_cons.mp hab with h | h
    · simp only [List.cons.injEq, and_true] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    · have := ih (fun c' hc' => hf c' (List.mem_cons_of_mem _ hc')) h
      exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ this.1),
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ this.2)⟩

/-- Under an assignment satisfying `f`, every arc leads from a true literal to a true one. -/
theorem arc_val {n : ℕ} {f : CNF} (hf : IsTwoCNF n f) {σ : Assignment} (hσ : evalCNF σ f = true) :
    ∀ e ∈ arcsOfCodes (codes f), nodeVal σ e.1 = true → nodeVal σ e.2 = true := by
  induction f with
  | nil => simp [codes, arcsOfCodes]
  | cons c f ih =>
    obtain ⟨a, b, rfl⟩ := clause_eq hf (List.mem_cons_self)
    simp only [evalCNF_cons, Bool.and_eq_true, evalClause_cons, evalClause_nil,
      Bool.or_false, Bool.or_eq_true] at hσ
    rw [arcs_cons_clause]
    intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | rfl | he
    · simp only [nodeVal_neg, nodeVal_code, Bool.not_eq_eq_eq_not, Bool.not_true]
      intro h; rcases hσ.1 with h' | h'
      · rw [h] at h'; simp at h'
      · exact h'
    · simp only [nodeVal_neg, nodeVal_code, Bool.not_eq_eq_eq_not, Bool.not_true]
      intro h; rcases hσ.1 with h' | h'
      · exact h'
      · rw [h] at h'; simp at h'
    · exact ih (fun c' hc' => hf c' (by simp [hc'])) hσ.2 e he

/-- Truth propagates along paths of the implication graph. -/
theorem reach_val {n : ℕ} {f : CNF} (hf : IsTwoCNF n f) {σ : Assignment}
    (hσ : evalCNF σ f = true) {u w : ℕ} (h : Reach (nbOf (codes f)) u w) :
    nodeVal σ u = true → nodeVal σ w = true := by
  induction h with
  | refl => exact id
  | tail _ hbc ih =>
    intro hu
    exact arc_val hf hσ _ (mem_outOf.mp hbc) (ih hu)

/-! ### The criterion -/

/-- **The 2-SAT criterion** for a labelling `comp` of the nodes that does not increase along
arcs and in which equal labels imply reachability: some variable has both literals with the
same label iff `f` is unsatisfiable; otherwise `x ↦ comp (2x) < comp (2x + 1)` satisfies `f`. -/
theorem criterion {n : ℕ} {f : CNF} (hf : IsTwoCNF n f) (comp : ℕ → ℕ)
    (hM : ∀ u, u < 2 * n → ∀ w ∈ nbOf (codes f) u, comp w ≤ comp u)
    (hS : ∀ u w, u < 2 * n → comp u = comp w → Reach (nbOf (codes f)) u w) :
    ((∃ x < n, comp (2 * x) = comp (2 * x + 1)) ↔ ¬ Satisfiable f) ∧
    ((∀ x < n, comp (2 * x) ≠ comp (2 * x + 1)) →
      evalCNF (fun x => decide (comp (2 * x) < comp (2 * x + 1))) f = true) := by
  have hsat : (∀ x < n, comp (2 * x) ≠ comp (2 * x + 1)) →
      evalCNF (fun x => decide (comp (2 * x) < comp (2 * x + 1))) f = true := by
    intro hne
    set σ : Assignment := fun x => decide (comp (2 * x) < comp (2 * x + 1)) with hσ
    -- a literal is true iff its label is below that of its complement
    have hlit : ∀ l : Literal, l.var < n →
        (evalLiteral σ l = true ↔ comp (code l) < comp (neg (code l))) ∧
          comp (code l) ≠ comp (neg (code l)) := by
      rintro ⟨v, p⟩ hv
      have hv' := hne v hv
      cases p
      · have hc : code ⟨v, false⟩ = 2 * v + 1 := by simp [code]
        rw [hc, neg_odd]
        refine ⟨?_, fun h => hv' h.symm⟩
        simp only [evalLiteral, Bool.false_eq_true, ↓reduceIte, hσ, Bool.not_eq_eq_eq_not,
          Bool.not_true, decide_eq_false_iff_not]
        omega
      · have hc : code ⟨v, true⟩ = 2 * v := by simp [code]
        rw [hc, neg_even]
        refine ⟨?_, hv'⟩
        simp only [evalLiteral, ↓reduceIte, hσ, decide_eq_true_eq]
    have hmono : ∀ a b : Literal, [a, b] ∈ f → comp (code b) ≤ comp (neg (code a)) := by
      intro a b hab
      have ha := (hf _ hab).2 a (by simp)
      exact hM _ (neg_lt (code_lt ha)) _ (mem_outOf.mpr (clause_arcs_mem hf hab).1)
    have hmono' : ∀ a b : Literal, [a, b] ∈ f → comp (code a) ≤ comp (neg (code b)) := by
      intro a b hab
      have hb := (hf _ hab).2 b (by simp)
      exact hM _ (neg_lt (code_lt hb)) _ (mem_outOf.mpr (clause_arcs_mem hf hab).2)
    refine List.all_eq_true.mpr fun c hc => ?_
    obtain ⟨a, b, rfl⟩ := clause_eq hf hc
    have ha := hlit a ((hf _ hc).2 a (by simp))
    have hb := hlit b ((hf _ hc).2 b (by simp))
    have h1 := hmono a b hc
    have h2 := hmono' a b hc
    simp only [evalClause_cons, evalClause_nil, Bool.or_false, Bool.or_eq_true]
    by_contra hab
    simp only [not_or, Bool.not_eq_true] at hab
    have h3 : ¬ comp (code a) < comp (neg (code a)) := fun h => by
      have := ha.1.mpr h; rw [hab.1] at this; simp at this
    have h4 : ¬ comp (code b) < comp (neg (code b)) := fun h => by
      have := hb.1.mpr h; rw [hab.2] at this; simp at this
    have := ha.2; have := hb.2
    omega
  refine ⟨⟨fun ⟨x, hx, heq⟩ ⟨σ, hσ⟩ => ?_, fun hns => ?_⟩, hsat⟩
  · have h1 := reach_val hf hσ (hS (2 * x) (2 * x + 1) (by omega) heq)
    have h2 := reach_val hf hσ (hS (2 * x + 1) (2 * x) (by omega) heq.symm)
    rw [nodeVal_even, nodeVal_odd] at h1 h2
    cases h : σ x <;> simp_all
  · by_contra hne
    simp only [not_exists, not_and] at hne
    exact hns ⟨_, hsat hne⟩

/-! ### The algorithm -/

/-- The labels computed by the path-based search on the implication graph of the codes `cl`
over `n` variables. -/
def lab (n : ℕ) (cl : List ℕ) : ℕ → ℕ := (Scc.final (2 * n) (nbOf cl)).lab

/-- The algorithm's answer: no variable has both literals in one component. -/
def okB (n : ℕ) (cl : List ℕ) : Bool := decide (∀ x < n, lab n cl (2 * x) ≠ lab n cl (2 * x + 1))

/-- The algorithm's assignment: `x` is true iff the component of `x` comes after that of `¬x`
in the topological order of the components (labels decreasing along arcs). -/
def asg (n : ℕ) (cl : List ℕ) : Assignment := fun x => decide (lab n cl (2 * x) < lab n cl (2 * x + 1))

/-- **Correctness of the 2-SAT algorithm** (ANONYMIZED–ANONYMIZED–ANONYMIZED): on a 2-CNF `f` over the
variables `0, …, n - 1`, the algorithm answers `true` iff `f` is satisfiable, and then its
assignment satisfies `f`. -/
theorem twoSat_correct {n : ℕ} {f : CNF} (hf : IsTwoCNF n f) :
    (okB n (codes f) = true ↔ Satisfiable f) ∧
      (okB n (codes f) = true → evalCNF (asg n (codes f)) f = true) := by
  have hcl := closed_nbOf (codes_ok hf)
  obtain ⟨_, hM, hS⟩ := Scc.final_spec hcl
  have hc := criterion hf (lab n (codes f)) hM (fun u w hu h => hS u w hu h)
  refine ⟨?_, fun h => hc.2 (of_decide_eq_true h)⟩
  rw [okB, decide_eq_true_iff]
  constructor
  · intro h; by_contra hns; obtain ⟨x, hx, heq⟩ := hc.1.mpr hns; exact h x hx heq
  · intro hs x hx heq; exact hc.1.mp ⟨x, hx, heq⟩ hs

end STACS2027.Runtimes.TwoSat
