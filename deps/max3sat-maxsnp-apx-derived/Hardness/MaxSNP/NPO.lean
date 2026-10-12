module

public import Hardness.MaxSNP.Hard.Poly
public import Hardness.MaxSNP.Max3SAT
public import Hardness.APX.Parse
public import Hardness.APX.Binary
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The problems of the syntactic class MaxSNP₀ are in NPO

For all signatures `ga`, `sa`, every `k` and every formula `φ`, `maxSNP0 ga sa k φ` is in NPO
(`npo_maxSNP0`):

* solutions are polynomially bounded: a structure of signature `sa` over the universe
  `{0, …, n - 1}` is no larger than the structure in which every relation holds everywhere
  (`size_le_fullRel`), whose size is polynomial in `n` (`pt_fullRel`), and `n` is below the
  length of the instance;
* feasibility and value are computed by an explicit polynomial-time program (`snpFeas`): parse
  the universe size and the two families of relations (`parseRelations`, a lenient parser that
  inverts `encodeRelations`), check that re-encoding gives the input words back and that both
  structures have their signatures (`fitsB`), and count the satisfying tuples.

The parser is built from a generic parser for lists written by `SAT.writeList` (`parseList`),
whose results have size linear in the length of the word read (`parseList_bound`).
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity

open Complexity.PT Complexity.Reg

/-! ### Unary prefixes -/

theorem stripOnes_add_le (w : Word) (n : Nat) :
    (stripOnes w n).1.length + (stripOnes w n).2 ≤ n + w.length := by
  induction w generalizing n with
  | nil => simp [stripOnes]
  | cons b w ih =>
    cases b with
    | false =>
      simp only [stripOnes, List.length_cons]
      omega
    | true =>
      have h := ih (n + 1)
      simp only [stripOnes, List.length_cons]
      omega

/-- The leading block of ones and what follows its terminating zero fit in the word. -/
theorem length_leadingOnes_add_afterOnes (w : Word) :
    (leadingOnes w).length + (afterOnes w).length ≤ w.length := by
  have h := stripOnes_add_le w 0
  simp only [leadingOnes, afterOnes, List.length_replicate]
  omega

/-! ### A generic parser for lists -/

/-- Read one item with `st` and push it onto the list read so far. -/
def listStep {α : Type} (st : Word → α × Word) (s : List α × Word) : List α × Word :=
  ((st s.2).1 :: s.1, (st s.2).2)

/-- Read a list written by `SAT.writeList`: its length in unary, then that many items, each
read by `st`. Returns the list and the rest of the word. -/
def parseList {α : Type} (st : Word → α × Word) (w : Word) : List α × Word :=
  (((listStep st)^[(leadingOnes w).length] ([], afterOnes w)).1.reverse,
    ((listStep st)^[(leadingOnes w).length] ([], afterOnes w)).2)

/-- `parseList` inverts `SAT.writeList` when `st` inverts the code of the items. -/
theorem parseList_writeList {α : Type} (enc : α → Word) (st : Word → α × Word)
    (hst : ∀ a r, st (enc a ++ r) = (a, r)) (l : List α) (r : Word) :
    parseList st (SAT.writeList enc l ++ r) = (l, r) := by
  have h := iterate_writeValues enc (listStep st)
    (fun a acc r => by simp only [listStep, hst]) l [] r
  simp only [parseList, writeList_append, leadingOnes_ones, afterOnes_ones,
    List.length_replicate, h, List.append_nil, List.reverse_reverse]

section Bounds

variable {α : Type} [Code α]

/-- The items read by `st` are linearly bounded by the part of the word they consume. -/
def ReadBound (st : Word → α × Word) (K c : Nat) : Prop :=
  ∀ w, (st w).2.length ≤ w.length ∧ size (st w).1 + K * (st w).2.length ≤ K * w.length + c

theorem listStep_iterate_bound {st : Word → α × Word} {K c : Nat} (hb : ReadBound st K c)
    (i : Nat) (r : Word) :
    ((listStep st)^[i] ([], r)).2.length ≤ r.length ∧
      size ((listStep st)^[i] ([], r)).1 + K * ((listStep st)^[i] ([], r)).2.length ≤
        1 + i * (c + 1) + K * r.length := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨h3, h4⟩ := hb ((listStep st)^[i] ([], r)).2
    simp only [listStep, size_cons]
    refine ⟨Nat.le_trans h3 h1, ?_⟩
    rw [Nat.succ_mul]
    omega

/-- The lists read by `parseList st` are linearly bounded by the part of the word they
consume. -/
theorem parseList_bound {st : Word → α × Word} {K c : Nat} (hb : ReadBound st K c) :
    ReadBound (parseList st) (K + c + 1) 1 := by
  intro w
  obtain ⟨h1, h2⟩ := listStep_iterate_bound hb (leadingOnes w).length (afterOnes w)
  have h3 := length_leadingOnes_add_afterOnes w
  simp only [parseList, size_reverse]
  generalize ((listStep st)^[(leadingOnes w).length] ([], afterOnes w)) = s at h1 h2
  generalize (leadingOnes w).length = n at h2 h3
  generalize (afterOnes w).length = m at h1 h2 h3
  generalize s.2.length = q at h1 h2 ⊢
  refine ⟨by omega, ?_⟩
  have e1 : (K + c + 1) * q = K * q + (c + 1) * q := by ring
  have e2 : (c + 1) * q ≤ (c + 1) * m := Nat.mul_le_mul_left _ h1
  have e3 : (K + c + 1) * (n + m) = n * (c + 1) + K * m + (c + 1) * m + K * n := by ring
  have e4 : (K + c + 1) * (n + m) ≤ (K + c + 1) * w.length := Nat.mul_le_mul_left _ h3
  omega

/-- `parseList st` is polynomial-time when `st` is, and `st` reads linearly bounded items. -/
theorem pt_parseList {st : Word → α × Word} (hst : PT st) {K c : Nat}
    (hb : ReadBound st K c) : PT (parseList st) := by
  have hstep : PT (listStep st) := by
    unfold listStep
    fun_prop
  have h := PT.iterate_const (step := listStep st)
    (init := fun w : Word => (([] : List α), afterOnes w))
    (n := fun w : Word => (leadingOnes w).length) hstep (by fun_prop) (by fun_prop)
    (fun N => N * (c + 1) + K * N + 2 * N + 2)
    ((((PolynomialBound.identity.mul (PolynomialBound.constant (c + 1))).add
      ((PolynomialBound.constant K).mul PolynomialBound.identity)).add
        ((PolynomialBound.constant 2).mul PolynomialBound.identity)).add
          (PolynomialBound.constant 2)) ?_
  · exact (PT.pair (PT.reverse (PT.fst h)) (PT.snd h)).of_eq fun w => rfl
  · intro w i hi
    obtain ⟨h1, h2⟩ := listStep_iterate_bound hb i (afterOnes w)
    have h3 := length_leadingOnes_add_afterOnes w
    have hN : w.length ≤ size w := by
      rw [size_word]
      omega
    rw [size_prod, size_word]
    generalize (listStep st)^[i] ([], afterOnes w) = s at h1 h2
    have hi' : i ≤ size w := by omega
    have hm : (afterOnes w).length ≤ size w := by omega
    have e1 : i * (c + 1) ≤ size w * (c + 1) := Nat.mul_le_mul_right _ hi'
    have e2 : K * (afterOnes w).length ≤ K * size w := Nat.mul_le_mul_left _ hm
    omega

end Bounds

/-! ### Parsing relations -/

/-- Read a natural number written in unary. -/
def natItem (w : Word) : Nat × Word := ((leadingOnes w).length, afterOnes w)

theorem natItem_enc (n : Nat) (r : Word) : natItem (SAT.writeNat n ++ r) = (n, r) := by
  simp [natItem, writeNat_append]

theorem pt_natItem : PT natItem := by
  unfold natItem
  fun_prop

theorem natItem_bound : ReadBound natItem 1 1 := by
  intro w
  have h := length_leadingOnes_add_afterOnes w
  simp only [natItem, size_nat]
  omega

/-- Read a tuple of natural numbers. -/
def tupleItem : Word → List Nat × Word := parseList natItem

/-- Read a relation: a list of tuples. -/
def relItem : Word → List (List Nat) × Word := parseList tupleItem

/-- The lenient parser for families of relations. -/
def parseRelations (w : Word) : Relations := (parseList relItem w).1

theorem tupleItem_bound : ReadBound tupleItem 3 1 := parseList_bound natItem_bound

theorem relItem_bound : ReadBound relItem 5 1 := parseList_bound tupleItem_bound

theorem pt_tupleItem : PT tupleItem := pt_parseList pt_natItem natItem_bound

theorem pt_relItem : PT relItem := pt_parseList pt_tupleItem tupleItem_bound

theorem pt_parseRelations : PT parseRelations :=
  (PT.fst (pt_parseList pt_relItem relItem_bound)).of_eq fun _ => rfl

@[fun_prop] protected theorem PT.parseRelations {α : Type} [Code α] {w : α → Word}
    (hw : PT w) : PT (fun a => parseRelations (w a)) :=
  pt_parseRelations.comp hw

/-- The parser inverts `encodeRelations`. -/
@[simp] theorem parseRelations_encode (R : Relations) : parseRelations (encodeRelations R) = R := by
  have ht : ∀ (t : List Nat) (r : Word), tupleItem (SAT.writeList SAT.writeNat t ++ r) = (t, r) :=
    parseList_writeList SAT.writeNat natItem natItem_enc
  have hr : ∀ (l : List (List Nat)) (r : Word),
      relItem (SAT.writeList (SAT.writeList SAT.writeNat) l ++ r) = (l, r) :=
    parseList_writeList _ tupleItem ht
  have h := parseList_writeList _ relItem hr R []
  rw [List.append_nil] at h
  simp only [parseRelations, encodeRelations, h]

/-! ### Checking a signature -/

/-- The list has no repetitions (checked by counting). -/
def nodupB (l : List (List Nat)) : Bool := l.all fun t => l.count t == 1

/-- `R` is a structure of signature `ar` over the universe `{0, …, n - 1}` (a check). -/
def fitsB (R : Relations) (n : Nat) (ar : List Nat) : Bool :=
  R.length == ar.length && (R.zip ar).all fun p =>
    nodupB p.1 && p.1.all fun t => t.length == p.2 && t.all fun a => decide (a < n)

theorem nodupB_iff (l : List (List Nat)) : nodupB l = true ↔ l.Nodup := by
  rw [List.nodup_iff_count_eq_one]
  simp [nodupB]

theorem fitsB_iff (R : Relations) (n : Nat) (ar : List Nat) :
    fitsB R n ar = true ↔ R.Fits n ar := by
  simp only [fitsB, Relations.Fits, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, nodupB_iff,
    decide_eq_true_eq]

theorem pt_fitsB (ar : List Nat) : PT (fun p : Relations × Nat => fitsB p.1 p.2 ar) := by
  unfold fitsB nodupB
  fun_prop

@[fun_prop] protected theorem PT.fitsB {α : Type} [Code α] (ar : List Nat) {R : α → Relations}
    {n : α → Nat} (hR : PT R) (hn : PT n) : PT (fun a => fitsB (R a) (n a) ar) :=
  (pt_fitsB ar).comp (hR.pair hn)

/-! ### Evaluating a fixed formula -/

theorem pt_eval (ψ : QF) :
    PT (fun p : Relations × Relations × List Nat => ψ.eval p.1 p.2.1 p.2.2) := by
  induction ψ with
  | input rel args =>
    simp only [QF.eval, Relations.holds]
    fun_prop
  | sol rel args =>
    simp only [QF.eval, Relations.holds]
    fun_prop
  | eq i j =>
    simp only [QF.eval]
    fun_prop
  | not ψ ih =>
    simp only [QF.eval]
    fun_prop
  | and ψ χ ih₁ ih₂ =>
    simp only [QF.eval]
    fun_prop
  | or ψ χ ih₁ ih₂ =>
    simp only [QF.eval]
    fun_prop

@[fun_prop] protected theorem PT.eval {α : Type} [Code α] (ψ : QF) {G S : α → Relations}
    {x : α → List Nat} (hG : PT G) (hS : PT S) (hx : PT x) :
    PT (fun a => ψ.eval (G a) (S a) (x a)) :=
  (pt_eval ψ).comp (hG.pair (hS.pair hx))

/-! ### Feasibility and value -/

/-- The feasibility and value function of `maxSNP0 ga sa k φ`. -/
def snpFeas (ga sa : List Nat) (k : Nat) (φ : QF) (x y : Word) : Word :=
  if Code.enc ((leadingOnes x).length, parseRelations (afterOnes x)) = x ∧
      Code.enc (parseRelations y) = y ∧
      fitsB (parseRelations (afterOnes x)) (leadingOnes x).length ga = true ∧
      fitsB (parseRelations y) (leadingOnes x).length sa = true then
    true :: natBits ((tuples (leadingOnes x).length k).countP fun t =>
      φ.eval (parseRelations (afterOnes x)) (parseRelations y) t)
  else [false]

theorem snpFeas_iff (ga sa : List Nat) (k : Nat) (φ : QF) (x y : Word) (v : Nat) :
    (maxSNP0 ga sa k φ).Sol x y v ↔ snpFeas ga sa k φ x y = true :: natBits v := by
  constructor
  · rintro ⟨n, G, S, hG, hS, rfl, rfl, rfl⟩
    have h1 : (leadingOnes (SAT.writeNat n ++ encodeRelations G)).length = n := by
      simp [writeNat_append]
    have h2 : afterOnes (SAT.writeNat n ++ encodeRelations G) = encodeRelations G := by
      simp [writeNat_append]
    rw [snpFeas, h1, h2, parseRelations_encode, parseRelations_encode,
      ite_eq_left ⟨rfl, rfl, (fitsB_iff G n ga).mpr hG, (fitsB_iff S n sa).mpr hS⟩]
  · intro h
    rw [snpFeas] at h
    split at h
    · next hc =>
      obtain ⟨hx, hy, hG, hS⟩ := hc
      exact ⟨_, _, _, (fitsB_iff _ _ _).mp hG, (fitsB_iff _ _ _).mp hS, hx.symm, hy.symm,
        natBits_injective (List.cons.inj h).2.symm⟩
    · cases h

theorem pt_snpFeas (ga sa : List Nat) (k : Nat) (φ : QF) :
    PT (fun p : Word × Word => snpFeas ga sa k φ p.1 p.2) := by
  unfold snpFeas
  fun_prop

/-! ### Solutions are polynomially bounded -/

/-- The structure of signature `sa` over `{0, …, n - 1}` in which every relation holds
everywhere. -/
def fullRel : List Nat → Nat → Relations
  | [], _ => []
  | a :: sa, n => tuples n a :: fullRel sa n

theorem pt_fullRel (sa : List Nat) : PT (fullRel sa) := by
  induction sa with
  | nil =>
    simp only [fullRel]
    fun_prop
  | cons a sa ih =>
    simp only [fullRel]
    fun_prop

theorem size_le_of_subperm {β : Type} [Code β] {l₁ l₂ : List β} (h : l₁.Subperm l₂) :
    size l₁ ≤ size l₂ := by
  obtain ⟨l, hp, hs⟩ := h
  rw [size_list, size_list, ← hp.length_eq, ← (hp.map size).sum_eq]
  have h1 := hs.length_le
  have h2 := (hs.map size).sum_le_sum fun _ _ => Nat.zero_le _
  omega

/-- A structure of signature `sa` over `{0, …, n - 1}` is no larger than `fullRel sa n`. -/
theorem size_le_fullRel {sa : List Nat} {n : Nat} {S : Relations} (hS : S.Fits n sa) :
    size S ≤ size (fullRel sa n) := by
  induction sa generalizing S with
  | nil =>
    obtain ⟨hl, -⟩ := hS
    rw [List.length_eq_zero_iff.mp hl]
    rfl
  | cons a sa ih =>
    obtain ⟨hl, hz⟩ := hS
    cases S with
    | nil => simp at hl
    | cons r S =>
      have hr := hz (r, a) (by simp)
      have hS' : Relations.Fits S n sa :=
        ⟨by simpa using hl, fun p hp => hz p (List.mem_cons_of_mem _ hp)⟩
      have hsub : r.Subperm (tuples n a) :=
        List.subperm_of_subset hr.1 fun t ht => mem_tuples.mpr (hr.2 t ht)
      have h1 := size_le_of_subperm hsub
      have h2 := ih hS'
      simp only [fullRel, size_cons]
      omega

/-- **The problems of the syntactic class MaxSNP₀ are in NPO.** -/
theorem npo_maxSNP0 (ga sa : List Nat) (k : Nat) (φ : QF) : NPO (maxSNP0 ga sa k φ) := by
  obtain ⟨c, e, hce⟩ := (pt_fullRel sa).size_le
  refine ⟨⟨c, e, ?_⟩, fun z => snpFeas ga sa k φ (unpair z).1 (unpair z).2,
    PT.polyTime_pairWords_word (h := snpFeas ga sa k φ) (pt_snpFeas ga sa k φ),
    fun x y v => ?_⟩
  · rintro x y v ⟨n, G, S, -, hS, rfl, rfl, -⟩
    have h1 : (encodeRelations S).length = size S := rfl
    have h2 := hce n
    have h3 : size n ≤ (SAT.writeNat n ++ encodeRelations G).length := by
      simp [length_writeNat]
    rw [h1]
    exact Nat.le_trans (size_le_fullRel hS) (Nat.le_trans h2 (powerBound_mono c e h3))
  · simp only [unpair_pairWords]
    exact snpFeas_iff ga sa k φ x y v

end Complexity
