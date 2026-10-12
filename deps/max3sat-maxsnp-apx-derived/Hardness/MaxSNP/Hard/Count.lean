module

public import Hardness.MaxSNP.Hard.Split
public import Hardness.MaxSNP.Hard.Average

/-!
# MAX-3-SAT is MaxSNP-hard: counting

For the formula `F = snpToSat k φ (n, G)` with `I` clauses, the list `keptTuples k φ n G` of
`N'` kept tuples, and the value `value S` of the solution relations `S` (the number of tuples
satisfying `φ`):

* `isThreeCNF_snpToSat`: `F` is a 3-CNF formula;
* `satCount_snpToSat_le`: every assignment `y` of `F` satisfies at most
  `I - (N' - value (satToSnp y))` clauses;
* `exists_satCount_snpToSat`: for all `S` some assignment satisfies `I - (N' - value S)`
  clauses;
* `length_snpToSat_le`: `I ≤ N' * 2 ^ a * (a + 1)`;
* `exists_large_solution`: some `S` has `N' ≤ 2 ^ a * value S` (averaging),

where `a` is the number of occurrences of solution atoms in `φ`.
-/

@[expose] public section

namespace Complexity

/-! ### Evaluation with truth values for the atoms -/

/-- If `β` lists the truth values of the solution atoms of `A` at `x` under `S`, then
evaluating with `β` is evaluating with `S`. -/
theorem QF.evalB_eq_eval (A : List (Nat × List Nat)) (G S : Relations) (β : List Bool)
    (x : List Nat)
    (hβ : ∀ q ∈ A, β.getD (A.idxOf q) false = S.holds q.1 (q.2.map fun i => x.getD i 0)) :
    ∀ ψ : QF, (∀ q ∈ ψ.atoms, q ∈ A) → ψ.evalB A G β x = ψ.eval G S x := by
  intro ψ
  induction ψ with
  | input rel args => intro _; rfl
  | sol rel args => intro h; exact hβ (rel, args) (h _ (by simp [QF.atoms]))
  | eq i j => intro _; rfl
  | not ψ ih =>
    intro h
    simp only [QF.evalB, QF.eval]
    rw [ih h]
  | and ψ χ ih₁ ih₂ =>
    intro h
    simp only [QF.evalB, QF.eval]
    rw [ih₁ fun q hq => h q (by simp [QF.atoms, hq]),
      ih₂ fun q hq => h q (by simp [QF.atoms, hq])]
  | or ψ χ ih₁ ih₂ =>
    intro h
    simp only [QF.evalB, QF.eval]
    rw [ih₁ fun q hq => h q (by simp [QF.atoms, hq]),
      ih₂ fun q hq => h q (by simp [QF.atoms, hq])]

/-! ### Ground atoms and their variables -/

theorem groundAtom_mem {A : List (Nat × List Nat)} {k n : Nat} {t : List Nat}
    {q : Nat × List Nat} (ht : t ∈ tuples n k) (hq : q ∈ A) :
    groundAtom t q ∈ groundAtoms A k n :=
  List.mem_flatMap.mpr ⟨t, ht, List.mem_map.mpr ⟨q, hq, rfl⟩⟩

theorem length_tupleVars (A gl : List (Nat × List Nat)) (t : List Nat) :
    (tupleVars A gl t).length = A.length := by
  simp [tupleVars]

theorem tupleVars_lt {A : List (Nat × List Nat)} {k n : Nat} {t : List Nat}
    (ht : t ∈ tuples n k) :
    ∀ v ∈ tupleVars A (groundAtoms A k n) t, v < (groundAtoms A k n).length := by
  intro v hv
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
  exact List.idxOf_lt_length_of_mem (groundAtom_mem ht hq)

/-- Evaluating `φ` at a tuple with the values of its variables under an assignment that
agrees with the solution relations `S`. -/
theorem evalB_tupleVars {k n : Nat} (φ : QF) (G S : Relations) (y : Nat → Bool)
    {t : List Nat} (ht : t ∈ tuples n k)
    (hy : ∀ g ∈ groundAtoms φ.atoms k n,
      y ((groundAtoms φ.atoms k n).idxOf g) = S.holds g.1 g.2) :
    φ.evalB φ.atoms G ((tupleVars φ.atoms (groundAtoms φ.atoms k n) t).map y) t =
      φ.eval G S t := by
  refine QF.evalB_eq_eval _ G S _ t ?_ φ (fun q hq => hq)
  intro q hq
  have h := hy _ (groundAtom_mem ht hq)
  simp only [tupleVars, List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_idxOf hq, Option.map_some, Option.getD_some, Function.comp_apply]
  exact h

/-- The assignment of the variables given by solution relations. -/
def asgOf (gl : List (Nat × List Nat)) (S : Relations) : SAT.Assignment :=
  fun v => S.holds (gl.getD v (0, [])).1 (gl.getD v (0, [])).2

theorem asgOf_idxOf {gl : List (Nat × List Nat)} {S : Relations} {g : Nat × List Nat}
    (hg : g ∈ gl) : asgOf gl S (gl.idxOf g) = S.holds g.1 g.2 := by
  simp [asgOf, List.getD_eq_getElem?_getD, List.getElem?_idxOf hg]

theorem holds_relOfWord {gl : List (Nat × List Nat)} {R : Nat} {y : Word}
    {g : Nat × List Nat} (hg : g ∈ gl) (hR : g.1 < R) :
    (relOfWord gl R y).holds g.1 g.2 = y.getD (gl.idxOf g) false := by
  rw [Relations.holds_eq, Bool.eq_iff_iff, decide_eq_true_eq]
  have e : (relOfWord gl R y).getD g.1 [] =
      (gl.filter fun g' => g'.1 == g.1 && y.getD (gl.idxOf g') false).map Prod.snd := by
    simp [relOfWord, List.getD_eq_getElem?_getD, List.getElem?_range hR]
  rw [e, List.mem_map]
  constructor
  · rintro ⟨g', hg', h2⟩
    have hcond := (List.mem_filter.mp hg').2
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    have e' : g' = g := Prod.ext hcond.1 h2
    rw [← e']
    exact hcond.2
  · intro h
    refine ⟨g, List.mem_filter.mpr ⟨hg, ?_⟩, rfl⟩
    show (g.1 == g.1 && y.getD (gl.idxOf g) false) = true
    rw [h, beq_self_eq_true]
    rfl

theorem fst_lt_relBound {A : List (Nat × List Nat)} {q : Nat × List Nat} (hq : q ∈ A) :
    q.1 < relBound A := by
  unfold relBound
  induction A with
  | nil => simp at hq
  | cons q' A ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hq with rfl | hq
    · omega
    · have := ih hq
      omega

theorem fst_lt_relBound_of_mem_groundAtoms {A : List (Nat × List Nat)} {k n : Nat}
    {g : Nat × List Nat} (hg : g ∈ groundAtoms A k n) : g.1 < relBound A := by
  obtain ⟨t, -, hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
  exact (fst_lt_relBound hq : q.1 < relBound A)

/-- The assignment written by `w` agrees with the relations `satToSnp k φ (n, G) w`. -/
theorem holds_satToSnp (k : Nat) (φ : QF) (n : Nat) (G : Relations) (w : Word)
    {g : Nat × List Nat} (hg : g ∈ groundAtoms φ.atoms k n) :
    SAT.assignmentOf w ((groundAtoms φ.atoms k n).idxOf g) =
      (satToSnp k φ (n, G) w).holds g.1 g.2 :=
  (holds_relOfWord hg (fst_lt_relBound_of_mem_groundAtoms hg)).symm

/-! ### Kept tuples -/

theorem mem_keptTuples {k : Nat} {φ : QF} {n : Nat} {G : Relations} {t : List Nat} :
    t ∈ keptTuples k φ n G ↔
      t ∈ tuples n k ∧ keptTuple φ G (groundAtoms φ.atoms k n) t = true :=
  List.mem_filter

/-- A tuple satisfying `φ` for some solution relations is kept. -/
theorem keptTuple_of_eval {k n : Nat} (φ : QF) (G S : Relations) {t : List Nat}
    (ht : t ∈ tuples n k) (h : φ.eval G S t = true) :
    keptTuple φ G (groundAtoms φ.atoms k n) t = true := by
  unfold keptTuple
  rw [List.any_eq_true]
  refine ⟨(tupleVars φ.atoms (groundAtoms φ.atoms k n) t).map
    (asgOf (groundAtoms φ.atoms k n) S), mem_allWords.mpr ?_, ?_⟩
  · rw [List.length_map, length_tupleVars]
  · rw [normWord_map, evalB_tupleVars φ G S _ ht fun g hg => asgOf_idxOf hg]
    exact h

/-- The value of solution relations is attained on the kept tuples. -/
theorem countP_keptTuples_eval (k : Nat) (φ : QF) (n : Nat) (G S : Relations) :
    (keptTuples k φ n G).countP (fun t => φ.eval G S t) =
      (tuples n k).countP (fun t => φ.eval G S t) := by
  unfold keptTuples
  rw [List.countP_filter]
  refine List.countP_congr fun t ht => ?_
  constructor
  · intro h
    exact (Bool.and_eq_true _ _ ▸ h).1
  · intro h
    rw [Bool.and_eq_true]
    exact ⟨h, keptTuple_of_eval φ G S ht h⟩

/-! ### Long clauses -/

theorem evalClause_negClause (y : SAT.Assignment) (vs : List Nat) :
    ∀ β : List Bool, β.length = vs.length →
      (SAT.evalClause y (negClause vs β) = false ↔ β = vs.map y) := by
  induction vs with
  | nil =>
    intro β h
    have : β = [] := List.length_eq_zero_iff.mp h
    subst this
    simp [negClause]
  | cons v vs ih =>
    intro β h
    cases β with
    | nil => simp at h
    | cons b β =>
      have h' := ih β (by simpa using h)
      have e : negClause (v :: vs) (b :: β) = ⟨v, !b⟩ :: negClause vs β := rfl
      rw [e, SAT.evalClause_cons, Bool.or_eq_false_iff, h', List.map_cons, List.cons.injEq]
      have e₂ : SAT.evalLiteral y ⟨v, !b⟩ = false ↔ b = y v := by
        cases b <;> cases hy : y v <;> simp [SAT.evalLiteral, hy]
      rw [e₂]

theorem var_mem_of_mem_negClause {vs : List Nat} :
    ∀ {β : List Bool} {l : SAT.Literal}, l ∈ negClause vs β → l.var ∈ vs := by
  induction vs with
  | nil => intro β l h; simp [negClause] at h
  | cons v vs ih =>
    intro β l h
    cases β with
    | nil => simp [negClause] at h
    | cons b β =>
      have e : negClause (v :: vs) (b :: β) = ⟨v, !b⟩ :: negClause vs β := rfl
      rw [e, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (ih h)

theorem length_negClause_le (vs : List Nat) (β : List Bool) :
    (negClause vs β).length ≤ vs.length := by
  simp only [negClause, List.length_zipWith]
  omega

/-- Under an assignment, exactly the long clause of the actual truth values is false, and it
is present when `φ` is false. -/
theorem countP_emitted (φ : QF) (G : Relations) (gl : List (Nat × List Nat)) (t : List Nat)
    (y : SAT.Assignment) :
    (emitted φ G gl t).countP (fun cl => !SAT.evalClause y cl) =
      if φ.evalB φ.atoms G ((tupleVars φ.atoms gl t).map y) t then 0 else 1 := by
  have hlen : ((tupleVars φ.atoms gl t).map y).length = φ.atoms.length := by
    rw [List.length_map, length_tupleVars]
  unfold emitted
  rw [List.countP_map, List.countP_filter]
  have e : (allWords φ.atoms.length).countP (fun β =>
      ((fun cl => !SAT.evalClause y cl) ∘ negClause (tupleVars φ.atoms gl t)) β &&
        !φ.evalB φ.atoms G β t) =
      (allWords φ.atoms.length).countP (fun β =>
        decide (β = (tupleVars φ.atoms gl t).map y) &&
          !φ.evalB φ.atoms G ((tupleVars φ.atoms gl t).map y) t) := by
    refine List.countP_congr fun β hβ => ?_
    have hβl : β.length = (tupleVars φ.atoms gl t).length := by
      rw [mem_allWords.mp hβ, length_tupleVars]
    have h := evalClause_negClause y (tupleVars φ.atoms gl t) β hβl
    by_cases hb : β = (tupleVars φ.atoms gl t).map y
    · have h' := h.mpr hb
      simp only [Function.comp_apply, h', Bool.not_false, Bool.true_and]
      rw [← hb]
      simp
    · have h' : SAT.evalClause y (negClause (tupleVars φ.atoms gl t) β) = true := by
        cases hc : SAT.evalClause y (negClause (tupleVars φ.atoms gl t) β)
        · exact absurd (h.mp hc) hb
        · rfl
      simp [h', hb]
  rw [e]
  cases hv : φ.evalB φ.atoms G ((tupleVars φ.atoms gl t).map y) t
  · have h₁ : (allWords φ.atoms.length).countP
        (fun v => decide (v = (tupleVars φ.atoms gl t).map y)) ≤ 1 := by
      convert allWords_count_le_one φ.atoms.length ((tupleVars φ.atoms gl t).map y)
    have h₂ : 0 < (allWords φ.atoms.length).countP
        (fun v => decide (v = (tupleVars φ.atoms gl t).map y)) :=
      List.countP_pos_iff.mpr ⟨_, mem_allWords.mpr hlen, by simp⟩
    simp only [Bool.not_false, Bool.and_true, Bool.false_eq_true, ite_false]
    omega
  · simp

theorem countP_flatMap_emitted (φ : QF) (G : Relations) (gl : List (Nat × List Nat))
    (y : SAT.Assignment) (K : List (List Nat)) :
    (K.flatMap fun t => emitted φ G gl t).countP (fun cl => !SAT.evalClause y cl) +
      K.countP (fun t => φ.evalB φ.atoms G ((tupleVars φ.atoms gl t).map y) t) = K.length := by
  induction K with
  | nil => rfl
  | cons t K ih =>
    rw [List.flatMap_cons, List.countP_append, countP_emitted, List.countP_cons,
      List.length_cons]
    cases φ.evalB φ.atoms G ((tupleVars φ.atoms gl t).map y) t <;> simp <;> omega

theorem length_emitted_le (φ : QF) (G : Relations) (gl : List (Nat × List Nat))
    (t : List Nat) : (emitted φ G gl t).length ≤ 2 ^ φ.atoms.length := by
  unfold emitted
  rw [List.length_map, ← allWords_length]
  exact List.length_filter_le _ _

theorem length_flatMap_emitted_le (φ : QF) (G : Relations) (gl : List (Nat × List Nat))
    (K : List (List Nat)) :
    (K.flatMap fun t => emitted φ G gl t).length ≤ K.length * 2 ^ φ.atoms.length := by
  induction K with
  | nil => simp
  | cons t K ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have := length_emitted_le φ G gl t
    omega

theorem length_longClauses_le (k : Nat) (φ : QF) (n : Nat) (G : Relations) :
    (longClauses k φ n G).length ≤ (keptTuples k φ n G).length * 2 ^ φ.atoms.length :=
  length_flatMap_emitted_le φ G _ _

theorem mem_longClauses {k : Nat} {φ : QF} {n : Nat} {G : Relations} {ls : SAT.Clause}
    (h : ls ∈ longClauses k φ n G) :
    ∃ t ∈ tuples n k, ∃ β : List Bool,
      ls = negClause (tupleVars φ.atoms (groundAtoms φ.atoms k n) t) β := by
  obtain ⟨t, ht, h⟩ := List.mem_flatMap.mp h
  obtain ⟨β, -, rfl⟩ := List.mem_map.mp h
  exact ⟨t, (mem_keptTuples.mp ht).1, β, rfl⟩

theorem var_lt_of_mem_longClauses {k : Nat} {φ : QF} {n : Nat} {G : Relations} :
    ∀ ls ∈ longClauses k φ n G, ∀ l ∈ ls, l.var < (groundAtoms φ.atoms k n).length := by
  intro ls h l hl
  obtain ⟨t, ht, β, rfl⟩ := mem_longClauses h
  exact tupleVars_lt ht _ (var_mem_of_mem_negClause hl)

theorem length_le_of_mem_longClauses {k : Nat} {φ : QF} {n : Nat} {G : Relations} :
    ∀ ls ∈ longClauses k φ n G, ls.length ≤ φ.atoms.length := by
  intro ls h
  obtain ⟨t, ht, β, rfl⟩ := mem_longClauses h
  exact Nat.le_trans (length_negClause_le _ _) (Nat.le_of_eq (length_tupleVars _ _ _))

/-- The false long clauses and the kept tuples satisfying `φ`. -/
theorem countP_longClauses (k : Nat) (φ : QF) (n : Nat) (G : Relations) (y : SAT.Assignment) :
    (longClauses k φ n G).countP (fun cl => !SAT.evalClause y cl) +
      (keptTuples k φ n G).countP (fun t => φ.evalB φ.atoms G
        ((tupleVars φ.atoms (groundAtoms φ.atoms k n) t).map y) t) =
      (keptTuples k φ n G).length :=
  countP_flatMap_emitted φ G _ y _

/-- On kept tuples, evaluation with the values of an assignment agreeing with `S`. -/
theorem countP_keptTuples_evalB (k : Nat) (φ : QF) (n : Nat) (G S : Relations)
    (y : SAT.Assignment)
    (hy : ∀ g ∈ groundAtoms φ.atoms k n,
      y ((groundAtoms φ.atoms k n).idxOf g) = S.holds g.1 g.2) :
    (keptTuples k φ n G).countP (fun t => φ.evalB φ.atoms G
        ((tupleVars φ.atoms (groundAtoms φ.atoms k n) t).map y) t) =
      (tuples n k).countP (fun t => φ.eval G S t) := by
  rw [← countP_keptTuples_eval]
  refine List.countP_congr fun t ht => ?_
  rw [evalB_tupleVars φ G S y (mem_keptTuples.mp ht).1 hy]

/-! ### The formula -/

theorem snpToSat_mk (k : Nat) (φ : QF) (n : Nat) (G : Relations) :
    snpToSat k φ (n, G) = splitFrom φ.atoms.length (groundAtoms φ.atoms k n).length 0
      (longClauses k φ n G) := rfl

/-- The formula of a structure is a 3-CNF formula. -/
theorem isThreeCNF_snpToSat (k : Nat) (φ : QF) (p : Nat × Relations) :
    SAT.IsThreeCNF (snpToSat k φ p) :=
  isThreeCNF_splitFrom _ _ _ (fun ls h => by
    have := length_le_of_mem_longClauses ls h
    omega) 0

/-- The number of clauses is at most a constant times the number of kept tuples. -/
theorem length_snpToSat_le (k : Nat) (φ : QF) (n : Nat) (G : Relations) :
    (snpToSat k φ (n, G)).length ≤
      (keptTuples k φ n G).length * 2 ^ φ.atoms.length * (φ.atoms.length + 1) :=
  Nat.le_trans (length_splitFrom_le _ _ _ 0)
    (Nat.mul_le_mul_right _ (length_longClauses_le k φ n G))

/-- Every assignment loses at least one clause for each kept tuple at which its solution
relations falsify `φ`. -/
theorem satCount_snpToSat_le (k : Nat) (φ : QF) (n : Nat) (G : Relations) (w : Word) :
    SAT.satCount (SAT.assignmentOf w) (snpToSat k φ (n, G)) + (keptTuples k φ n G).length ≤
      (snpToSat k φ (n, G)).length +
        (tuples n k).countP (fun t => φ.eval G (satToSnp k φ (n, G) w) t) := by
  have h₁ := satCount_splitFrom_le (SAT.assignmentOf w) φ.atoms.length
    (groundAtoms φ.atoms k n).length (longClauses k φ n G) 0
  have h₂ := countP_longClauses k φ n G (SAT.assignmentOf w)
  rw [countP_keptTuples_evalB k φ n G (satToSnp k φ (n, G) w) (SAT.assignmentOf w)
    fun g hg => holds_satToSnp k φ n G w hg] at h₂
  rw [snpToSat_mk]
  omega

/-- For all solution relations some assignment loses exactly one clause for each kept tuple
at which they falsify `φ`. -/
theorem exists_satCount_snpToSat (k : Nat) (φ : QF) (n : Nat) (G S : Relations) :
    ∃ w : Word,
      SAT.satCount (SAT.assignmentOf w) (snpToSat k φ (n, G)) + (keptTuples k φ n G).length =
        (snpToSat k φ (n, G)).length + (tuples n k).countP (fun t => φ.eval G S t) := by
  obtain ⟨y', hy', h₁⟩ := exists_satCount_splitFrom φ.atoms.length
    (groundAtoms φ.atoms k n).length (longClauses k φ n G) var_lt_of_mem_longClauses 0
    (asgOf (groundAtoms φ.atoms k n) S)
  have h₂ := countP_longClauses k φ n G (asgOf (groundAtoms φ.atoms k n) S)
  rw [countP_keptTuples_evalB k φ n G S _ fun g hg => asgOf_idxOf hg] at h₂
  obtain ⟨w, hw⟩ := SAT.exists_word_assignment y' (snpToSat k φ (n, G))
  refine ⟨w, ?_⟩
  rw [SAT.satCount_congr hw]
  rw [snpToSat_mk]
  omega

/-- Averaging: some solution relations satisfy `φ` at the fraction `2 ^ (-a)` of the kept
tuples. -/
theorem exists_large_solution (k : Nat) (φ : QF) (n : Nat) (G : Relations) :
    ∃ S : Relations, (keptTuples k φ n G).length ≤
      2 ^ φ.atoms.length * (tuples n k).countP (fun t => φ.eval G S t) := by
  let gl := groundAtoms φ.atoms k n
  let val : List Nat → Word → Bool := fun t w =>
    φ.evalB φ.atoms G ((tupleVars φ.atoms gl t).map fun v => w.getD v false) t
  have h₁ : ∀ t ∈ keptTuples k φ n G,
      2 ^ gl.length ≤ (allWords gl.length).countP (val t) * 2 ^ φ.atoms.length := by
    intro t ht
    obtain ⟨ht, hk⟩ := mem_keptTuples.mp ht
    obtain ⟨β, hβ, hβv⟩ := List.any_eq_true.mp hk
    have hlen : β.length = (tupleVars φ.atoms gl t).length := by
      rw [mem_allWords.mp hβ, length_tupleVars]
    have h := count_extend gl.length (tupleVars φ.atoms gl t) β (tupleVars_lt ht) hlen
    rw [length_tupleVars] at h
    refine Nat.le_trans h (Nat.mul_le_mul_right _ (List.countP_mono_left fun w _ hw => ?_))
    rw [decide_eq_true_eq] at hw
    show φ.evalB φ.atoms G ((tupleVars φ.atoms gl t).map fun v => w.getD v false) t = true
    rw [hw]
    exact hβv
  have h₂ := mul_length_le_sum (keptTuples k φ n G)
    (fun t => (allWords gl.length).countP (val t) * 2 ^ φ.atoms.length) _ h₁
  rw [sum_map_mul_const, sum_map_countP_comm, ← sum_map_mul_const] at h₂
  obtain ⟨w, -, hw⟩ := exists_le_of_mul_length_le_sum (allWords gl.length)
    (fun w => (keptTuples k φ n G).countP (fun t => val t w) * 2 ^ φ.atoms.length)
    (keptTuples k φ n G).length (allWords_ne_nil _) (by
      rw [allWords_length, Nat.mul_comm]
      exact h₂)
  refine ⟨satToSnp k φ (n, G) w, ?_⟩
  have e := countP_keptTuples_evalB k φ n G (satToSnp k φ (n, G) w) (SAT.assignmentOf w)
    fun g hg => holds_satToSnp k φ n G w hg
  rw [Nat.mul_comm, ← e]
  exact hw

end Complexity
