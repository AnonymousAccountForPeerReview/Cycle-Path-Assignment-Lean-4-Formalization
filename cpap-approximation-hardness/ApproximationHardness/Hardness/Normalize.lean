module

public import ApproximationHardness.PolarizeLReduction
public import ComplexityExt.Approx.Defs
import Lean.Elab.Tactic.Omega

/-!
# From 3-OCCURRENCE MAX-3-SAT to the instances of Lemma 10

The problem `max3SAT3` of the MaxSNP-completeness formalization allows clauses with at most
three literals, repeated literals, empty clauses and unit clauses; the instances of Lemma 10
(`ThreeOccurrence`) have two or three distinct literals per clause. `normalize` removes the
repeated literals of each clause and the empty clauses, and replaces each unit clause `(l)`,
the `i`-th clause of the formula, by the three clauses

  `(l ∨ z) ∧ (¬z ∨ w) ∧ (¬z ∨ ¬w)`,  `z = n + 2i`, `w = n + 2i + 1`  (`n = variableBound f`).

The gadget satisfies at most `2 + [l]` of its clauses, and exactly that many when `z` is
false. With `u` the number of unit clauses (`unitCount`), `OPT(normalize f) = OPT(f) + 2u`
(`isMaxSat_normalize`), every assignment satisfies at most `2u` more clauses of `normalize f`
than of `f` (`satisfiedCount_normalize_le`), and `2u ≤ 4 OPT(f)`, because an assignment or its
complement satisfies at least half of the nonempty clauses (`two_mul_unitCount_le`).
-/

@[expose] public section

namespace STACS2027.Hardness

open Complexity

/-! ## Removing repeated literals -/

theorem eraseDups_sublist_nodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (n : Nat) (l : List α), l.length ≤ n → l.eraseDups.Sublist l ∧ l.eraseDups.Nodup
  | _, [], _ => by simp
  | 0, _ :: _, h => by simp at h
  | n + 1, a :: as, h => by
    rw [List.eraseDups_cons]
    have hlen : (as.filter fun b => !b == a).length ≤ n :=
      Nat.le_trans (List.length_filter_le _ _) (by simp at h; omega)
    obtain ⟨hs, hn⟩ := eraseDups_sublist_nodup n _ hlen
    refine ⟨(hs.trans (List.filter_sublist)).cons_cons a, List.nodup_cons.mpr ⟨fun ha => ?_, hn⟩⟩
    have := List.mem_filter.mp (List.mem_eraseDups.mp ha)
    simp at this

theorem eraseDups_sublist {α : Type} [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups.Sublist l :=
  (eraseDups_sublist_nodup l.length l (Nat.le_refl _)).1

theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup :=
  (eraseDups_sublist_nodup l.length l (Nat.le_refl _)).2

theorem eraseDups_eq_nil {α : Type} [BEq α] [LawfulBEq α] {l : List α} :
    l.eraseDups = [] ↔ l = [] := by
  constructor
  · intro h
    cases l with
    | nil => rfl
    | cons a as => rw [List.eraseDups_cons] at h; cases h
  · rintro rfl; rfl

theorem evalClause_eraseDups (a : SAT.Assignment) (c : SAT.Clause) :
    SAT.evalClause a c.eraseDups = SAT.evalClause a c := by
  unfold SAT.evalClause
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, List.any_eq_true]
  simp only [List.mem_eraseDups]

/-! ## The transformation -/

/-- The three clauses replacing the unit clause `(l)`, the `i`-th clause, with the fresh
variables `z = base + 2i` and `w = base + 2i + 1`. -/
def unitGadget (base i : Nat) (l : SAT.Literal) : SAT.CNF :=
  [[l, ⟨base + 2 * i, true⟩], [⟨base + 2 * i, false⟩, ⟨base + 2 * i + 1, true⟩],
    [⟨base + 2 * i, false⟩, ⟨base + 2 * i + 1, false⟩]]

/-- The clauses replacing the clause `p.1`, the `p.2`-th clause: none if it is empty, the gadget
if it has one literal (after removing repetitions), and the clause without repetitions
otherwise. -/
def normClause (base : Nat) (p : SAT.Clause × Nat) : SAT.CNF :=
  if p.1.eraseDups.length = 0 then []
  else if p.1.eraseDups.length = 1 then unitGadget base p.2 (p.1.eraseDups.headD ⟨0, true⟩)
  else [p.1.eraseDups]

/-- The transformation from the clause numbered `n` on, with fresh variables from `base` on. -/
def normFrom (base n : Nat) (f : SAT.CNF) : SAT.CNF := (f.zipIdx n).flatMap (normClause base)

/-- The transformation: `normClause` on every clause, with fresh variables above those of `f`. -/
def normalize (f : SAT.CNF) : SAT.CNF := normFrom (SAT.variableBound f) 0 f

/-- The clauses with exactly one literal once repetitions are removed. -/
def isUnit (c : SAT.Clause) : Bool := c.eraseDups.length == 1

/-- `u`, the number of unit clauses. -/
def unitCount (f : SAT.CNF) : Nat := f.countP isUnit

theorem normFrom_nil (base n : Nat) : normFrom base n [] = [] := rfl

theorem normFrom_cons (base n : Nat) (c : SAT.Clause) (f : SAT.CNF) :
    normFrom base n (c :: f) = normClause base (c, n) ++ normFrom base (n + 1) f := by
  simp [normFrom, List.zipIdx_cons]

/-! ## Clauses -/

theorem mem_normClause {base i : Nat} {c d : SAT.Clause} (hd : d ∈ normClause base (c, i)) :
    (d = c.eraseDups ∧ 2 ≤ c.eraseDups.length) ∨
      ∃ l ∈ c, d ∈ unitGadget base i l := by
  unfold normClause at hd
  dsimp only at hd
  split at hd
  · simp at hd
  · split at hd
    · next h0 h1 =>
      refine Or.inr ⟨c.eraseDups.headD ⟨0, true⟩, ?_, hd⟩
      cases h : c.eraseDups with
      | nil => simp [h] at h1
      | cons a t =>
        have : a ∈ c.eraseDups := by rw [h]; exact List.mem_cons_self
        simpa using List.mem_eraseDups.mp this
    · next h0 h1 =>
      simp only [List.mem_singleton] at hd
      exact Or.inl ⟨hd, by omega⟩

theorem mem_normFrom {base n : Nat} {f : SAT.CNF} {d : SAT.Clause} (hd : d ∈ normFrom base n f) :
    ∃ c ∈ f, ∃ i, (d = c.eraseDups ∧ 2 ≤ c.eraseDups.length) ∨
      ∃ l ∈ c, d ∈ unitGadget base i l := by
  induction f generalizing n with
  | nil => simp [normFrom_nil] at hd
  | cons c f ih =>
    rw [normFrom_cons, List.mem_append] at hd
    rcases hd with hd | hd
    · exact ⟨c, List.mem_cons_self, n, mem_normClause hd⟩
    · obtain ⟨c', hc', i, h⟩ := ih hd
      exact ⟨c', List.mem_cons_of_mem _ hc', i, h⟩

theorem length_eraseDups_le (c : SAT.Clause) : c.eraseDups.length ≤ c.length :=
  (eraseDups_sublist c).length_le

/-- Every clause of `normalize f` has two or three distinct literals, when the clauses of `f`
have at most three literals. -/
theorem normalize_clauses {f : SAT.CNF} (h3 : SAT.IsThreeCNF f) :
    ∀ d ∈ normalize f, (d.length = 2 ∨ d.length = 3) ∧ d.Nodup := by
  intro d hd
  obtain ⟨c, hc, i, h⟩ := mem_normFrom hd
  rcases h with ⟨rfl, h2⟩ | ⟨l, hl, hg⟩
  · have := length_eraseDups_le c
    have := h3 c hc
    exact ⟨by omega, eraseDups_nodup c⟩
  · have hv : l.var < SAT.variableBound f := SAT.literal_lt_variableBound hc hl
    simp only [unitGadget, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · refine ⟨by simp, ?_⟩
      simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
        List.nodup_nil, and_self, and_true]
      intro h
      have := congrArg SAT.Literal.var h
      simp at this
      omega
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, by simp⟩

/-! ## Occurrences -/

theorem filter_and_add {α : Type} (L : List α) (p q : α → Bool) :
    (L.filter fun l => p l && q l).length + (L.filter fun l => p l && !q l).length =
      L.countP p := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    simp only [List.filter_cons, List.countP_cons]
    cases p l <;> cases q l <;> simp <;> omega

theorem occurrences_true_add_false (L : List SAT.Literal) (v : Nat) :
    (L.filter fun l => l.var == v && l.positive == true).length +
      (L.filter fun l => l.var == v && l.positive == false).length =
      L.countP fun l => Nat.beq l.var v := by
  have h := filter_and_add L (fun l => Nat.beq l.var v) (fun l => l.positive)
  have e1 : (L.filter fun l => l.var == v && l.positive == true) =
      L.filter fun l => Nat.beq l.var v && l.positive := by
    apply List.filter_congr
    intro l _
    cases l.positive <;> by_cases hv : l.var = v <;> simp [hv] <;> rfl
  have e2 : (L.filter fun l => l.var == v && l.positive == false) =
      L.filter fun l => Nat.beq l.var v && !l.positive := by
    apply List.filter_congr
    intro l _
    cases l.positive <;> by_cases hv : l.var = v <;> simp [hv] <;> rfl
  rw [e1, e2]
  exact h

theorem occurrences_add (f : SAT.CNF) (v : Nat) :
    occurrences f v true + occurrences f v false = SAT.occurrences f v :=
  occurrences_true_add_false f.flatten v

/-- The literals of the original variables in `normFrom base n f` form a sublist of the
literals of `f`. -/
theorem normFrom_filter_sublist {base n : Nat} {f : SAT.CNF}
    (hf : ∀ c ∈ f, ∀ l ∈ c, l.var < base) :
    ((normFrom base n f).flatten.filter fun l => decide (l.var < base)).Sublist f.flatten := by
  induction f generalizing n with
  | nil => simp [normFrom_nil]
  | cons c f ih =>
    rw [normFrom_cons, List.flatten_append, List.filter_append, List.flatten_cons]
    refine List.Sublist.append ?_ (ih (fun c' hc' => hf c' (List.mem_cons_of_mem _ hc')))
    have hc : ∀ l ∈ c, l.var < base := hf c List.mem_cons_self
    unfold normClause
    split
    · simp
    · split
      · next h0 h1 =>
        cases h : c.eraseDups with
        | nil => simp [h] at h1
        | cons a t =>
          have ha : a ∈ c := List.mem_eraseDups.mp (by rw [h]; exact List.mem_cons_self)
          have hav := hc a ha
          have h1 : ¬ base + 2 * n < base := by omega
          have h2 : ¬ base + 2 * n + 1 < base := by omega
          simp only [List.headD_cons, unitGadget, List.flatten_cons, List.flatten_nil,
            List.cons_append, List.nil_append, List.append_nil, List.filter_cons, hav, h1, h2,
            decide_true, decide_false, ite_true, Bool.false_eq_true, ite_false, List.filter_nil]
          exact List.singleton_sublist.mpr ha
      · simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
        exact List.filter_sublist.trans (eraseDups_sublist c)

theorem occurrences_gadget {base i v : Nat} {l : SAT.Literal} (hl : l.var < base)
    (hv : base ≤ v) :
    SAT.occurrences (unitGadget base i l) v =
      (if v = base + 2 * i then 3 else 0) + (if v = base + 2 * i + 1 then 2 else 0) := by
  have hne : l.var ≠ v := by omega
  simp only [SAT.occurrences, unitGadget, List.flatten_cons, List.flatten_nil, List.cons_append,
    List.nil_append, List.append_nil, List.countP_cons, List.countP_nil]
  by_cases h1 : v = base + 2 * i <;> by_cases h2 : v = base + 2 * i + 1 <;>
    simp [hne, h1, h2] <;> omega

/-- The fresh variables: each occurs at most three times, and not at all below the fresh
variables of the clause numbered `n`. -/
theorem occurrences_normFrom_fresh {base n : Nat} {f : SAT.CNF}
    (hf : ∀ c ∈ f, ∀ l ∈ c, l.var < base) {v : Nat} (hv : base ≤ v) :
    SAT.occurrences (normFrom base n f) v ≤ 3 ∧
      (v < base + 2 * n → SAT.occurrences (normFrom base n f) v = 0) := by
  induction f generalizing n with
  | nil => simp [normFrom_nil, SAT.occurrences]
  | cons c f ih =>
    have hc : ∀ l ∈ c, l.var < base := hf c List.mem_cons_self
    obtain ⟨ih1, ih2⟩ := ih (n := n + 1) (fun c' hc' => hf c' (List.mem_cons_of_mem _ hc'))
    have hsplit : SAT.occurrences (normFrom base n (c :: f)) v =
        SAT.occurrences (normClause base (c, n)) v + SAT.occurrences (normFrom base (n + 1) f) v := by
      simp [SAT.occurrences, normFrom_cons, List.countP_append]
    have hfirst : SAT.occurrences (normClause base (c, n)) v =
        (if isUnit c then (if v = base + 2 * n then 3 else 0) +
          (if v = base + 2 * n + 1 then 2 else 0) else 0) := by
      unfold normClause isUnit
      dsimp only
      split
      · next h0 => simp [h0, SAT.occurrences]
      · split
        · next h0 h1 =>
          cases h : c.eraseDups with
          | nil => simp [h] at h1
          | cons a t =>
            have ha : a ∈ c := List.mem_eraseDups.mp (by rw [h]; exact List.mem_cons_self)
            have ht : t = [] := by rw [h] at h1; simpa using h1
            subst ht
            simp only [List.headD_cons]
            rw [occurrences_gadget (hc a ha) hv]
            simp
        · next h0 h1 =>
          rw [ite_eq_right (by simp [h1])]
          simp only [SAT.occurrences, List.flatten_cons, List.flatten_nil, List.append_nil]
          rw [List.countP_eq_zero]
          intro l hl
          have := hc l (List.mem_eraseDups.mp hl)
          intro hb
          simp only [Nat.beq_eq] at hb
          omega
    have hA : SAT.occurrences (normClause base (c, n)) v ≤ 3 := by
      rw [hfirst]
      cases isUnit c
      · simp
      · by_cases h1 : v = base + 2 * n <;> by_cases h2 : v = base + 2 * n + 1 <;> simp [h1, h2] <;>
          omega
    have hB : v ≠ base + 2 * n → v ≠ base + 2 * n + 1 →
        SAT.occurrences (normClause base (c, n)) v = 0 := by
      intro h1 h2
      rw [hfirst]
      cases isUnit c <;> simp [h1, h2]
    rw [hsplit]
    constructor
    · by_cases h1 : v = base + 2 * n
      · have := ih2 (by omega); omega
      · by_cases h2 : v = base + 2 * n + 1
        · have := ih2 (by omega); omega
        · have := hB h1 h2; omega
    · intro hlt
      have := hB (by omega) (by omega)
      have := ih2 (by omega)
      omega

/-- `normalize f` is an instance of Lemma 10. -/
theorem normalize_threeOccurrence {f : SAT.CNF} (h3 : SAT.IsThreeCNF f) (ho : SAT.IsThreeOcc f) :
    ThreeOccurrence (normalize f) := by
  refine ⟨fun d hd => (normalize_clauses h3 d hd).1, fun d hd => (normalize_clauses h3 d hd).2,
    fun v => ?_⟩
  rw [occurrences_add]
  have hf : ∀ c ∈ f, ∀ l ∈ c, l.var < SAT.variableBound f :=
    fun c hc l hl => SAT.literal_lt_variableBound hc hl
  by_cases hv : SAT.variableBound f ≤ v
  · exact (occurrences_normFrom_fresh hf hv).1
  · have hsub := (normFrom_filter_sublist (n := 0) hf).countP_le (p := fun l => Nat.beq l.var v)
    have heq : ((normFrom (SAT.variableBound f) 0 f).flatten.filter
        fun l => decide (l.var < SAT.variableBound f)).countP (fun l => Nat.beq l.var v) =
          SAT.occurrences (normalize f) v := by
      rw [List.countP_filter, normalize, SAT.occurrences]
      apply List.countP_congr
      intro l _
      by_cases h : l.var = v
      · subst h; simp; omega
      · simp [h]
    have := ho v
    unfold SAT.occurrences at this
    omega


/-! ## Satisfied clauses -/

theorem satisfiedCount_cons (a : SAT.Assignment) (c : SAT.Clause) (f : SAT.CNF) :
    satisfiedCount a (c :: f) = (if SAT.evalClause a c then 1 else 0) + satisfiedCount a f := by
  simp only [satisfiedCount, List.countP_cons]
  omega

theorem unitCount_cons (c : SAT.Clause) (f : SAT.CNF) :
    unitCount (c :: f) = (if isUnit c then 1 else 0) + unitCount f := by
  simp only [unitCount, List.countP_cons]
  omega

theorem satisfiedCount_gadget (b : SAT.Assignment) (base i : Nat) (l : SAT.Literal) :
    satisfiedCount b (unitGadget base i l) =
      (if SAT.evalLiteral b l || b (base + 2 * i) then 1 else 0) +
        (if !b (base + 2 * i) || b (base + 2 * i + 1) then 1 else 0) +
          (if !b (base + 2 * i) || !b (base + 2 * i + 1) then 1 else 0) := by
  have e1 : ∀ v, SAT.evalLiteral b ⟨v, true⟩ = b v := fun _ => rfl
  have e2 : ∀ v, SAT.evalLiteral b ⟨v, false⟩ = !b v := fun _ => rfl
  simp only [satisfiedCount, unitGadget, List.countP_cons, List.countP_nil, SAT.evalClause,
    List.any_cons, List.any_nil, Bool.or_false, e1, e2]
  generalize SAT.evalLiteral b l = e
  generalize b (base + 2 * i) = z
  generalize b (base + 2 * i + 1) = w
  cases e <;> cases z <;> cases w <;> rfl

/-- "The gadget satisfies at most `2 + [l]` of its clauses." -/
theorem satisfiedCount_gadget_le (b : SAT.Assignment) (base i : Nat) (l : SAT.Literal) :
    satisfiedCount b (unitGadget base i l) ≤ 2 + (if SAT.evalLiteral b l then 1 else 0) := by
  rw [satisfiedCount_gadget]
  generalize SAT.evalLiteral b l = e
  generalize b (base + 2 * i) = z
  generalize b (base + 2 * i + 1) = w
  cases e <;> cases z <;> cases w <;> decide

/-- "... and exactly that many when `z` is false." -/
theorem satisfiedCount_gadget_eq {b : SAT.Assignment} {base i : Nat} (l : SAT.Literal)
    (hz : b (base + 2 * i) = false) :
    satisfiedCount b (unitGadget base i l) = 2 + (if SAT.evalLiteral b l then 1 else 0) := by
  rw [satisfiedCount_gadget, hz]
  generalize SAT.evalLiteral b l = e
  generalize b (base + 2 * i + 1) = w
  cases e <;> cases w <;> decide

theorem eraseDups_eq_singleton {c : SAT.Clause} (h1 : c.eraseDups.length = 1) :
    ∃ l, c.eraseDups = [l] ∧ l ∈ c := by
  cases h : c.eraseDups with
  | nil => simp [h] at h1
  | cons a t =>
    have ht : t = [] := by rw [h] at h1; simpa using h1
    subst ht
    exact ⟨a, rfl, List.mem_eraseDups.mp (by rw [h]; exact List.mem_cons_self)⟩

theorem evalClause_of_eraseDups {b : SAT.Assignment} {c : SAT.Clause} {l : SAT.Literal}
    (h : c.eraseDups = [l]) : SAT.evalClause b c = SAT.evalLiteral b l := by
  rw [← evalClause_eraseDups, h]
  simp [SAT.evalClause]

theorem satisfiedCount_normClause_le (b : SAT.Assignment) (base : Nat) (c : SAT.Clause) (i : Nat) :
    satisfiedCount b (normClause base (c, i)) ≤
      (if SAT.evalClause b c then 1 else 0) + (if isUnit c then 2 else 0) := by
  unfold normClause isUnit
  dsimp only
  split
  · simp [satisfiedCount]
  · split
    · next h0 h1 =>
      obtain ⟨l, hl, -⟩ := eraseDups_eq_singleton h1
      rw [hl, evalClause_of_eraseDups hl]
      have := satisfiedCount_gadget_le b base i l
      simp only [List.headD_cons, List.length_singleton, beq_self_eq_true, ite_true]
      omega
    · next h0 h1 =>
      have hu : (c.eraseDups.length == 1) = false := by simp [h1]
      simp only [hu, Bool.false_eq_true, ite_false]
      simp [satisfiedCount, evalClause_eraseDups]

/-- The assignment `a` on the variables below `base`, and false on the fresh variables. -/
def freshFalse (base : Nat) (a : SAT.Assignment) : SAT.Assignment :=
  fun v => if v < base then a v else false

theorem evalClause_freshFalse {base : Nat} {a : SAT.Assignment} {c : SAT.Clause}
    (hc : ∀ l ∈ c, l.var < base) : SAT.evalClause (freshFalse base a) c = SAT.evalClause a c :=
  STACS2027.evalClause_congr fun l hl => by simp [freshFalse, hc l hl]

theorem satisfiedCount_normClause_eq (a : SAT.Assignment) {base : Nat} {c : SAT.Clause} (i : Nat)
    (hc : ∀ l ∈ c, l.var < base) :
    satisfiedCount (freshFalse base a) (normClause base (c, i)) =
      (if SAT.evalClause a c then 1 else 0) + (if isUnit c then 2 else 0) := by
  unfold normClause isUnit
  dsimp only
  split
  · next h0 =>
    have : c = [] := eraseDups_eq_nil.mp (List.eq_nil_of_length_eq_zero h0)
    subst this
    simp [satisfiedCount, SAT.evalClause]
  · split
    · next h0 h1 =>
      obtain ⟨l, hl, hlc⟩ := eraseDups_eq_singleton h1
      rw [hl, evalClause_of_eraseDups hl]
      have hz : freshFalse base a (base + 2 * i) = false := by
        unfold freshFalse; rw [ite_eq_right (by omega)]
      rw [List.headD_cons, satisfiedCount_gadget_eq l hz]
      have he : SAT.evalLiteral (freshFalse base a) l = SAT.evalLiteral a l := by
        simp [SAT.evalLiteral, freshFalse, hc l hlc]
      rw [he]
      simp
      omega
    · next h0 h1 =>
      have hu : (c.eraseDups.length == 1) = false := by simp [h1]
      simp only [hu, Bool.false_eq_true, ite_false]
      simp only [satisfiedCount, List.countP_cons, List.countP_nil, evalClause_eraseDups,
        evalClause_freshFalse hc]
      omega

theorem satisfiedCount_normFrom_le (b : SAT.Assignment) (base n : Nat) (f : SAT.CNF) :
    satisfiedCount b (normFrom base n f) ≤ satisfiedCount b f + 2 * unitCount f := by
  induction f generalizing n with
  | nil => simp [normFrom_nil, satisfiedCount, unitCount]
  | cons c f ih =>
    rw [normFrom_cons, satisfiedCount_append, satisfiedCount_cons, unitCount_cons]
    have h1 := satisfiedCount_normClause_le b base c n
    have h2 := ih (n + 1)
    split at h1 <;> split at h1 <;> simp only [ite_true, *] <;> omega

theorem satisfiedCount_normFrom_eq (a : SAT.Assignment) {base : Nat} (n : Nat) {f : SAT.CNF}
    (hf : ∀ c ∈ f, ∀ l ∈ c, l.var < base) :
    satisfiedCount (freshFalse base a) (normFrom base n f) = satisfiedCount a f + 2 * unitCount f := by
  induction f generalizing n with
  | nil => simp [normFrom_nil, satisfiedCount, unitCount]
  | cons c f ih =>
    rw [normFrom_cons, satisfiedCount_append, satisfiedCount_cons, unitCount_cons,
      satisfiedCount_normClause_eq a n (hf c List.mem_cons_self),
      ih (n + 1) (fun c' hc' => hf c' (List.mem_cons_of_mem _ hc'))]
    split <;> split <;> omega

/-- Every assignment satisfies at most `2u` more clauses of `normalize f` than of `f`. -/
theorem satisfiedCount_normalize_le (b : SAT.Assignment) (f : SAT.CNF) :
    satisfiedCount b (normalize f) ≤ satisfiedCount b f + 2 * unitCount f :=
  satisfiedCount_normFrom_le b _ 0 f

/-- `OPT(normalize f) = OPT(f) + 2u`. -/
theorem isMaxSat_normalize {f : SAT.CNF} {S : Nat} (hS : IsMaxSat f S) :
    IsMaxSat (normalize f) (S + 2 * unitCount f) := by
  obtain ⟨⟨a, ha⟩, hmax⟩ := hS
  refine ⟨⟨freshFalse (SAT.variableBound f) a, ?_⟩, fun b => ?_⟩
  · rw [normalize, satisfiedCount_normFrom_eq a 0
      (fun c hc l hl => SAT.literal_lt_variableBound hc hl), ha]
  · have := satisfiedCount_normalize_le b f
    have := hmax b
    omega

/-- An assignment or its complement satisfies every nonempty clause; in particular, `u` is at
most the number of clauses satisfied by `a` and by its complement. -/
theorem unitCount_le (a : SAT.Assignment) (f : SAT.CNF) :
    unitCount f ≤ satisfiedCount a f + satisfiedCount (fun v => !a v) f := by
  induction f with
  | nil => simp [unitCount, satisfiedCount]
  | cons c f ih =>
    rw [unitCount_cons, satisfiedCount_cons, satisfiedCount_cons]
    have : isUnit c = true → SAT.evalClause a c = true ∨ SAT.evalClause (fun v => !a v) c = true := by
      intro hu
      cases c with
      | nil => simp [isUnit] at hu
      | cons l t =>
        cases h : SAT.evalLiteral a l
        · right
          simp only [SAT.evalClause, List.any_cons]
          simp only [SAT.evalLiteral] at h ⊢
          split at h <;> simp_all
        · left
          simp [SAT.evalClause, h]
    split <;> split <;> split <;> simp_all <;> omega

/-- `2u ≤ 4 OPT(f)`. -/
theorem two_mul_unitCount_le {f : SAT.CNF} {S : Nat} (hS : IsMaxSat f S) :
    2 * unitCount f ≤ 4 * S := by
  have h := unitCount_le (fun _ => false) f
  have h1 := hS.2 (fun _ => false)
  have h2 := hS.2 (fun v => !(fun _ : Nat => false) v)
  simp only at h h2
  omega

end STACS2027.Hardness
