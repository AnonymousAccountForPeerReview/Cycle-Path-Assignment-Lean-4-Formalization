module

public import Hardness.APX.Defs
public import Hardness.APX.Binary
public import Hardness.APX.Blocks
public import ComplexityExt.Reg.Decide
public import PT.RawMore
import Mathlib.Tactic.Linarith

/-!
# The PTAS-reduction from an APX problem to MAX-3-SAT

Let `Q` be a problem of APX, with feasibility function `F` (`NPO`) and an approximation
algorithm `T` of ratio `a / b`. For the precision `k` and an instance `x`, let `t` be the value
of `T x` and consider the conditions on the value `v` of a solution of `x`

* `(k + 1 + i) * t ≤ (k + 1) * v` (maximization), resp.
* `(k + 1 + i) * v ≤ (k + 1) * t` (minimization),

for `i = 0, …, (k + 1) * a` (`accV`). The greatest `i` whose condition holds for the optimum
has the property that every solution satisfying the condition is within `1 + 1 / (k + 1)` of
the optimum (`threshold`).

"`w` is a solution of `x` whose value satisfies the `i`-th condition" is checked in
polynomial time (`chk`, on instances `thrInst`), so the hypothesis `WitnessGap` gives formulas
`φ_i`. The instance `redF k x` of MAX-3-SAT is the balanced disjoint union of the `φ_i`
(`blockUnion`); `redG k` decodes a candidate solution of `x` from the restriction of an
assignment to every block and returns the best feasible candidate, `T x` included.

Throughout this file MAX-3-SAT is the auxiliary problem `max3SATu` of `Hardness.Unbounded`, in
which every word is an assignment; the results are transferred to `max3SAT` (assignments no
longer than the instance) in `Hardness.Final.Max3SAT`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity

open Complexity.PT Complexity.Reg

/-! ### Optima and ratios, by cases on the goal -/

theorem OptProblem.IsOpt.cmp {P : OptProblem} {x y : Word} {opt v : Nat} (h : P.IsOpt x opt)
    (hs : P.Sol x y v) : if P.maximize then v ≤ opt else opt ≤ v := by
  have := h.2 y v hs
  cases hm : P.maximize <;> simpa [hm] using this

theorem OptProblem.withinRatio_iff (P : OptProblem) (a b opt v : Nat) :
    P.WithinRatio a b opt v ↔ if P.maximize then b * opt ≤ a * v else b * v ≤ a * opt := by
  unfold OptProblem.WithinRatio
  cases P.maximize <;> simp

/-! ### Thresholds -/

/-- The `i`-th threshold condition on the value `v`, relative to the value `t`. -/
def accV (mx : Bool) (k i t v : Nat) : Prop :=
  if mx then (k + 1 + i) * t ≤ (k + 1) * v else (k + 1 + i) * v ≤ (k + 1) * t

/-- The last index up to `I` of an initial run of a property. -/
theorem exists_last (p : Nat → Prop) (I : Nat) (h0 : p 0) :
    ∃ i, i ≤ I ∧ p i ∧ (i < I → ¬ p (i + 1)) := by
  induction I with
  | zero => exact ⟨0, Nat.le_refl _, h0, fun h => absurd h (Nat.lt_irrefl _)⟩
  | succ I ih =>
    obtain ⟨i, hi, hp, hlast⟩ := ih
    rcases Nat.lt_or_ge i I with hlt | hge
    · exact ⟨i, by omega, hp, fun _ => hlast hlt⟩
    · obtain rfl : i = I := by omega
      by_cases hI : p (i + 1)
      · exact ⟨i + 1, Nat.le_refl _, hI, fun h => absurd h (Nat.lt_irrefl _)⟩
      · exact ⟨i, by omega, hp, fun _ => hI⟩

theorem threshold_max {a b k t opt : Nat} (hb : 0 < b) (ht : t ≤ opt) (hr : b * opt ≤ a * t) :
    ∃ i, i ≤ (k + 1) * a ∧ (k + 1 + i) * t ≤ (k + 1) * opt ∧
      ∀ v, v ≤ opt → (k + 1 + i) * t ≤ (k + 1) * v → (k + 1) * opt ≤ (k + 2) * v := by
  obtain ⟨i, hi, hCi, hlast⟩ := exists_last (fun i => (k + 1 + i) * t ≤ (k + 1) * opt)
    ((k + 1) * a) (by simpa using Nat.mul_le_mul_left (k + 1) ht)
  refine ⟨i, hi, hCi, fun v hv hacc => ?_⟩
  rcases Nat.lt_or_ge i ((k + 1) * a) with hlt | hge
  · have h1 : (k + 1) * opt < (k + 1 + (i + 1)) * t := Nat.lt_of_not_le (hlast hlt)
    have htv : t ≤ v :=
      Nat.le_of_mul_le_mul_left
        (Nat.le_trans (Nat.mul_le_mul_right t (Nat.le_add_right (k + 1) i)) hacc) (Nat.succ_pos k)
    nlinarith
  · obtain rfl : i = (k + 1) * a := by omega
    have ht0 : t = 0 := by
      by_contra hne
      have htpos : 0 < t := Nat.pos_of_ne_zero hne
      have h2 : b * ((k + 1 + (k + 1) * a) * t) ≤ (k + 1) * (a * t) :=
        calc b * ((k + 1 + (k + 1) * a) * t) ≤ b * ((k + 1) * opt) := Nat.mul_le_mul_left b hCi
          _ = (k + 1) * (b * opt) := Nat.mul_left_comm _ _ _
          _ ≤ (k + 1) * (a * t) := Nat.mul_le_mul_left _ hr
      have h3 := Nat.le_mul_of_pos_left ((k + 1 + (k + 1) * a) * t) hb
      have h4 := Nat.mul_pos (Nat.succ_pos k) htpos
      nlinarith
    subst ht0
    have hopt0 : opt = 0 := by
      rcases Nat.eq_zero_or_pos opt with h | h
      · exact h
      · have := Nat.mul_pos hb h
        omega
    subst hopt0
    simp

theorem threshold_min {a b k t opt : Nat} (hb : 0 < b) (ht : opt ≤ t) (hr : b * t ≤ a * opt) :
    ∃ i, i ≤ (k + 1) * a ∧ (k + 1 + i) * opt ≤ (k + 1) * t ∧
      ∀ v, opt ≤ v → (k + 1 + i) * v ≤ (k + 1) * t → (k + 1) * v ≤ (k + 2) * opt := by
  obtain ⟨i, hi, hCi, hlast⟩ := exists_last (fun i => (k + 1 + i) * opt ≤ (k + 1) * t)
    ((k + 1) * a) (by simpa using Nat.mul_le_mul_left (k + 1) ht)
  refine ⟨i, hi, hCi, fun v hv hacc => ?_⟩
  rcases Nat.lt_or_ge i ((k + 1) * a) with hlt | hge
  · have h1 : (k + 1) * t < (k + 1 + (i + 1)) * opt := Nat.lt_of_not_le (hlast hlt)
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hv
    have h2 : (k + 1) * d ≤ (k + 1 + i) * d := Nat.mul_le_mul_right d (Nat.le_add_right (k + 1) i)
    nlinarith
  · obtain rfl : i = (k + 1) * a := by omega
    have hopt0 : opt = 0 := by
      by_contra hne
      have hpos : 0 < opt := Nat.pos_of_ne_zero hne
      have h2 : b * ((k + 1 + (k + 1) * a) * opt) ≤ (k + 1) * (a * opt) :=
        calc b * ((k + 1 + (k + 1) * a) * opt) ≤ b * ((k + 1) * t) := Nat.mul_le_mul_left b hCi
          _ = (k + 1) * (b * t) := Nat.mul_left_comm _ _ _
          _ ≤ (k + 1) * (a * opt) := Nat.mul_le_mul_left _ hr
      have h3 := Nat.le_mul_of_pos_left ((k + 1 + (k + 1) * a) * opt) hb
      have h4 := Nat.mul_pos (Nat.succ_pos k) hpos
      nlinarith
    subst hopt0
    have ht0 : t = 0 := by
      rcases Nat.eq_zero_or_pos t with h | h
      · exact h
      · have := Nat.mul_pos hb h
        omega
    subst ht0
    have hv0 : v = 0 := by
      rcases Nat.eq_zero_or_pos v with h | h
      · exact h
      · have := Nat.mul_pos (Nat.lt_of_lt_of_le (Nat.succ_pos k)
          (Nat.le_add_right (k + 1) ((k + 1) * a))) h
        omega
    subst hv0
    simp

/-- **Thresholds.** Let `t` be the value of a solution within the factor `a / b` of the
optimum `opt`. Some threshold condition with index `i ≤ (k + 1) * a` holds for `opt`, and every
value satisfying it is within the factor `1 + 1 / (k + 1)` of `opt`. -/
theorem threshold (mx : Bool) {a b k t opt : Nat} (hb : 0 < b)
    (ht : if mx then t ≤ opt else opt ≤ t)
    (hr : if mx then b * opt ≤ a * t else b * t ≤ a * opt) :
    ∃ i, i ≤ (k + 1) * a ∧ accV mx k i t opt ∧
      ∀ v, (if mx then v ≤ opt else opt ≤ v) → accV mx k i t v →
        if mx then (k + 1) * opt ≤ (k + 2) * v else (k + 1) * v ≤ (k + 2) * opt := by
  cases mx
  · simpa [accV] using threshold_min (k := k) hb (by simpa using ht) (by simpa using hr)
  · simpa [accV] using threshold_max (k := k) hb (by simpa using ht) (by simpa using hr)

/-! ### The verifier -/

/-- The check of the verifier on the instance `z = (x, m, θ)` and the certificate `w`: `w` is
a solution of `x` whose value `v` satisfies `θ ≤ m * v` (maximization) resp. `m * v ≤ θ`
(minimization), where `θ` is a binary numeral. -/
def chk (mx : Bool) (F : Word → Word) (z : Word × Nat × Word) (w : Word) : Bool :=
  solOut (F (pairWords z.1 w)) &&
    (if mx then leBits z.2.2 (mulSmall z.2.1 (F (pairWords z.1 w)).tail)
      else leBits (mulSmall z.2.1 (F (pairWords z.1 w)).tail) z.2.2)

theorem chk_iff {Sol : Word → Word → Nat → Prop} {F : Word → Word}
    (hF : ∀ x y v, Sol x y v ↔ F (pairWords x y) = true :: natBits v) (mx : Bool) (x : Word)
    (m : Nat) (θ w : Word) :
    chk mx F (x, m, θ) w = true ↔
      ∃ v, Sol x w v ∧ if mx then SAT.binaryValue θ ≤ m * v else m * v ≤ SAT.binaryValue θ := by
  simp only [chk, Bool.and_eq_true]
  constructor
  · rintro ⟨hs, hc⟩
    obtain ⟨v, hv⟩ := solOut_iff.mp hs
    refine ⟨v, (hF x w v).mpr hv, ?_⟩
    rw [hv] at hc
    cases mx <;> simpa [leBits_iff] using hc
  · rintro ⟨v, hs, hc⟩
    have hv := (hF x w v).mp hs
    rw [hv]
    refine ⟨solOut_iff.mpr ⟨v, rfl⟩, ?_⟩
    cases mx <;> simpa [leBits_iff] using hc

/-- The verifier instance of the `i`-th threshold, for the precision `k`, the instance `x` and
the binary numeral `tb` of the value of the approximate solution. -/
def thrInst (mx : Bool) (k : Nat) (x tb : Word) (i : Nat) : Word × Nat × Word :=
  if mx then (x, k + 1, mulSmall (k + 1 + i) tb) else (x, k + 1 + i, mulSmall (k + 1) tb)

theorem chk_thrInst {Sol : Word → Word → Nat → Prop} {F : Word → Word}
    (hF : ∀ x y v, Sol x y v ↔ F (pairWords x y) = true :: natBits v) (mx : Bool) (k : Nat)
    (x : Word) (t i : Nat) (w : Word) :
    chk mx F (thrInst mx k x (natBits t) i) w = true ↔ ∃ v, Sol x w v ∧ accV mx k i t v := by
  cases mx <;> simp [thrInst, chk_iff hF, accV]

theorem length_le_enc_thrInst (mx : Bool) (k : Nat) (x tb : Word) (i : Nat) :
    x.length ≤ (Code.enc (thrInst mx k x tb i)).length := by
  have h : ∀ z : Word × Nat × Word, z.1.length ≤ size z := by
    intro z
    rw [size_prod, size_word]
    omega
  have := h (thrInst mx k x tb i)
  cases mx <;> exact this

/-! ### The best feasible candidate -/

/-- A list has an element of greatest (`mx = true`) resp. least value. -/
theorem exists_best {α : Type} (f : α → Nat) (mx : Bool) :
    ∀ l : List α, l ≠ [] → ∃ c ∈ l, ∀ c' ∈ l, if mx then f c' ≤ f c else f c ≤ f c'
  | [], h => absurd rfl h
  | [a], _ => ⟨a, List.mem_cons_self, fun c' hc' => by
      obtain rfl : c' = a := by simpa using hc'
      cases mx <;> simp⟩
  | a :: b :: l, _ => by
    obtain ⟨c, hc, hmax⟩ := exists_best f mx (b :: l) (by simp)
    by_cases h : if mx then f a ≤ f c else f c ≤ f a
    · refine ⟨c, List.mem_cons_of_mem _ hc, fun c' hc' => ?_⟩
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact h
      · exact hmax c' hc'
    · refine ⟨a, List.mem_cons_self, fun c' hc' => ?_⟩
      rcases List.mem_cons.mp hc' with rfl | hc'
      · cases mx <;> simp
      · have := hmax c' hc'
        cases mx <;> simp at h this ⊢ <;> omega

/-- The first element of a list of pairs (solution, binary value) whose value is best. -/
def bestOf (mx : Bool) (cs : List (Word × Word)) : Option (Word × Word) :=
  cs.find? fun c => cs.all fun c' => if mx then leBits c'.2 c.2 else leBits c.2 c'.2

theorem bestOf_spec (mx : Bool) {cs : List (Word × Word)} (hne : cs ≠ []) :
    ∃ c ∈ cs, bestOf mx cs = some c ∧
      ∀ c' ∈ cs, if mx then SAT.binaryValue c'.2 ≤ SAT.binaryValue c.2
        else SAT.binaryValue c.2 ≤ SAT.binaryValue c'.2 := by
  obtain ⟨c₀, hc₀, h₀⟩ := exists_best (fun c : Word × Word => SAT.binaryValue c.2) mx cs hne
  have hp : (cs.all fun c' => if mx then leBits c'.2 c₀.2 else leBits c₀.2 c'.2) = true := by
    rw [List.all_eq_true]
    intro c' hc'
    have := h₀ c' hc'
    cases mx <;> simpa [leBits_iff] using this
  cases hfind : bestOf mx cs with
  | none =>
    rw [bestOf, List.find?_eq_none] at hfind
    exact absurd hp (hfind c₀ hc₀)
  | some c =>
    refine ⟨c, List.mem_of_find?_eq_some hfind, rfl, fun c' hc' => ?_⟩
    have h1 := List.find?_some hfind
    rw [List.all_eq_true] at h1
    have h2 := h1 c' hc'
    cases mx <;> simpa [leBits_iff] using h2

/-- The feasible words of a list, each with the binary numeral of its value. -/
def feasible (F : Word → Word) (x : Word) (ws : List Word) : List (Word × Word) :=
  ws.filterMap fun w =>
    if solOut (F (pairWords x w)) then some (w, (F (pairWords x w)).tail) else none

theorem mem_feasible {Sol : Word → Word → Nat → Prop} {F : Word → Word}
    (hF : ∀ x y v, Sol x y v ↔ F (pairWords x y) = true :: natBits v) {x : Word}
    {ws : List Word} {c : Word × Word} :
    c ∈ feasible F x ws ↔ ∃ w ∈ ws, ∃ v, Sol x w v ∧ c = (w, natBits v) := by
  simp only [feasible, List.mem_filterMap]
  constructor
  · rintro ⟨w, hw, hc⟩
    by_cases hs : solOut (F (pairWords x w)) = true
    · obtain ⟨v, hv⟩ := solOut_iff.mp hs
      rw [ite_eq_left hs, hv] at hc
      exact ⟨w, hw, v, (hF x w v).mpr hv, (Option.some.inj hc).symm⟩
    · rw [ite_eq_right hs] at hc
      cases hc
  · rintro ⟨w, hw, v, hs, rfl⟩
    refine ⟨w, hw, ?_⟩
    have hv := (hF x w v).mp hs
    rw [hv, ite_eq_left (solOut_iff.mpr ⟨v, rfl⟩)]
    rfl

/-- The best feasible word of a list (the empty word if none is feasible). -/
def pick (mx : Bool) (F : Word → Word) (x : Word) (ws : List Word) : Word :=
  ((bestOf mx (feasible F x ws)).getD ([], [])).1

theorem pick_spec {Sol : Word → Word → Nat → Prop} {F : Word → Word}
    (hF : ∀ x y v, Sol x y v ↔ F (pairWords x y) = true :: natBits v) (mx : Bool) {x : Word}
    {ws : List Word} {w₀ : Word} {v₀ : Nat} (hw₀ : w₀ ∈ ws) (hs₀ : Sol x w₀ v₀) :
    ∃ v, Sol x (pick mx F x ws) v ∧
      ∀ w ∈ ws, ∀ v', Sol x w v' → if mx then v' ≤ v else v ≤ v' := by
  have hne : feasible F x ws ≠ [] :=
    List.ne_nil_of_mem ((mem_feasible hF).mpr ⟨w₀, hw₀, v₀, hs₀, rfl⟩)
  obtain ⟨c, hc, hbest, hall⟩ := bestOf_spec mx hne
  obtain ⟨w, hw, v, hs, rfl⟩ := (mem_feasible hF).mp hc
  refine ⟨v, by rw [pick, hbest]; exact hs, fun w' hw' v' hs' => ?_⟩
  have := hall (w', natBits v') ((mem_feasible hF).mpr ⟨w', hw', v', hs', rfl⟩)
  simpa using this

/-! ### The reduction maps -/

section Maps

variable (mx : Bool) (F T : Word → Word) (a : Nat) (gφ : Word → SAT.CNF) (dec : Word → Word)

/-- The formulas of the threshold conditions `i = 0, …, (k + 1) * a`. -/
def formulas (k : Nat) (x : Word) : List SAT.CNF :=
  (List.range ((k + 1) * a + 1)).map fun i =>
    gφ (Code.enc (thrInst mx k x (F (pairWords x (T x))).tail i))

/-- The instance map of the reduction: the balanced disjoint union of the formulas of the
threshold conditions. -/
def redF (k : Nat) (x : Word) : Word :=
  SAT.encode (blockUnion (formulas mx F T a gφ k x))

/-- The candidate solutions decoded from the restrictions of the assignment `y` to the
blocks. -/
def candidates (k : Nat) (x y : Word) : List Word :=
  (List.range ((k + 1) * a + 1)).map fun i =>
    dec (pairWords (Code.enc (thrInst mx k x (F (pairWords x (T x))).tail i))
      (y.drop (i * maxVar (formulas mx F T a gφ k x))))

/-- The best feasible solution among the approximate solution `T x` and the candidates. -/
def solMap (k : Nat) (x y : Word) : Word :=
  pick mx F x (T x :: candidates mx F T a gφ dec k x y)

/-- The solution map of the reduction, on `pairWords x y`. -/
def redG (k : Nat) (z : Word) : Word :=
  solMap mx F T a gφ dec k (unpair z).1 (unpair z).2

end Maps

/-! ### Polynomial time -/

theorem pt_chk (mx : Bool) {F : Word → Word} (hF : PT F) :
    PT (fun p : (Word × Nat × Word) × Word => chk mx F p.1 p.2) := by
  unfold chk
  fun_prop

theorem pt_thrInst (mx : Bool) :
    PT (fun p : Nat × Word × Word × Nat => thrInst mx p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold thrInst
  fun_prop

theorem pt_formulas (mx : Bool) {F T : Word → Word} (a : Nat) {gφ : Word → SAT.CNF}
    (hF : PT F) (hT : PT T) (hg : PT gφ) :
    PT (fun p : Nat × Word => formulas mx F T a gφ p.1 p.2) := by
  have h := pt_thrInst mx
  unfold formulas
  fun_prop

theorem pt_redF (mx : Bool) {F T : Word → Word} (a : Nat) {gφ : Word → SAT.CNF}
    (hF : PT F) (hT : PT T) (hg : PT gφ) :
    PT (fun p : Nat × Word => redF mx F T a gφ p.1 p.2) := by
  have h := pt_formulas mx a hF hT hg
  unfold redF
  fun_prop

theorem pt_pick (mx : Bool) {F : Word → Word} (hF : PT F) :
    PT (fun p : Word × List Word => pick mx F p.1 p.2) := by
  unfold pick bestOf feasible
  fun_prop

theorem pt_solMap (mx : Bool) {F T : Word → Word} (a : Nat) {gφ : Word → SAT.CNF}
    {dec : Word → Word} (hF : PT F) (hT : PT T) (hg : PT gφ) (hdec : PT dec) :
    PT (fun p : Nat × Word × Word => solMap mx F T a gφ dec p.1 p.2.1 p.2.2) := by
  have h1 := pt_thrInst mx
  have h2 := pt_formulas mx a hF hT hg
  have h3 := pt_pick mx hF
  unfold solMap candidates
  fun_prop

theorem pt_redG (mx : Bool) {F T : Word → Word} (a : Nat) {gφ : Word → SAT.CNF}
    {dec : Word → Word} (hF : PT F) (hT : PT T) (hg : PT gφ) (hdec : PT dec) :
    PT (fun p : Nat × Word => redG mx F T a gφ dec p.1 p.2) := by
  have hu : PT (fun p : Nat × Word => (p.1, unpair p.2)) := PT.pair PT.fst' (PT.unpair PT.snd')
  have h := (pt_solMap mx a hF hT hg hdec).comp hu
  unfold redG
  exact h

/-! ### The reduction -/

/-- **Every problem of APX is PTAS-reducible to MAX-3-SAT**, by maps that are polynomial-time
jointly in the precision and the instance, given witness-recovering gap reductions. -/
theorem strongPTASReducible_max3SATu_of_witnessGap {num den : Nat} (hnum : 0 < num)
    (h : WitnessGap num den) {Q : OptProblem} (hQ : InAPX Q) :
    StrongPTASReducible Q max3SATu := by
  obtain ⟨⟨⟨c₀, e₀, hbound⟩, F, hFpt, hF⟩, a, b, hb, T, hTpt, hT⟩ := hQ
  have hF' : PT F := PT.of_polyTime hFpt
  have hT' : PT T := PT.of_polyTime hTpt
  obtain ⟨χ, hχ, hχ'⟩ :=
    PT.exists_polyTime_pairWords_raw_bool (f := chk Q.maximize F) (pt_chk Q.maximize hF')
  obtain ⟨M, hM, hacc⟩ := decider_of_polyTime hχ
  obtain ⟨gφ, dec, hg, hdec, hgd⟩ := h M c₀ e₀ hM
  have hg' : PT gφ := PT.of_polyTime_enc hg
  have hdec' : PT dec := PT.of_polyTime hdec
  have hacc' : ∀ (z : Word × Nat × Word) (w : Word),
      Accepts M (pairWords (Code.enc z) w) ↔ chk Q.maximize F z w = true := by
    intro z w
    rw [hacc, hχ']
    cases chk Q.maximize F z w <;> simp
  refine ⟨redF Q.maximize F T a gφ, redG Q.maximize F T a gφ dec,
    fun k => 2 * ((k + 1) * a + 1) * den, pt_redF _ a hF' hT' hg',
    pt_redG _ a hF' hT' hg' hdec', by fun_prop, ?_⟩
  intro k x opt hopt
  obtain ⟨t, hTsol, hTratio⟩ := hT x opt hopt
  have htb : (F (pairWords x (T x))).tail = natBits t := by
    rw [(hF x (T x) t).mp hTsol]
    rfl
  have hfs_len : (formulas Q.maximize F T a gφ k x).length = (k + 1) * a + 1 := by
    simp [formulas]
  have hfs_get : ∀ i, i ≤ (k + 1) * a → (formulas Q.maximize F T a gφ k x)[i]? =
      some (gφ (Code.enc (thrInst Q.maximize k x (natBits t) i))) := by
    intro i hi
    rw [formulas, List.getElem?_map, List.getElem?_range (Nat.lt_succ_of_le hi), htb]
    rfl
  have h3 : SAT.IsThreeCNF (blockUnion (formulas Q.maximize F T a gφ k x)) := by
    refine isThreeCNF_blockUnion fun f hf => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hf
    exact (hgd _).1
  obtain ⟨opt', hopt'⟩ := max3SATu_exists_opt h3
  refine ⟨opt', hopt', fun y v' hy => ?_⟩
  obtain ⟨-, rfl⟩ := max3SATu_sol_encode.mp hy
  -- the image is a solution at least as good as every feasible candidate
  obtain ⟨v, hv, hbest⟩ := pick_spec hF Q.maximize
    (ws := T x :: candidates Q.maximize F T a gφ dec k x y) List.mem_cons_self hTsol
  refine ⟨v, by simpa only [redG, solMap, unpair_pairWords] using hv, fun hr => ?_⟩
  have hr' := hr.1 rfl
  -- the threshold
  obtain ⟨i, hi, hacci, himp⟩ := threshold Q.maximize (k := k) hb (hopt.cmp hTsol)
    ((Q.withinRatio_iff a b opt t).mp hTratio)
  obtain ⟨wopt, hwopt⟩ := hopt.1
  have hsat : SAT.Satisfiable (gφ (Code.enc (thrInst Q.maximize k x (natBits t) i))) :=
    (hgd _).2.2.1 ⟨wopt,
      Nat.le_trans (hbound x wopt opt hwopt)
        (powerBound_mono c₀ e₀ (length_le_enc_thrInst _ _ _ _ _)),
      (hacc' _ _).mpr ((chk_thrInst hF _ _ _ _ _ _).mpr ⟨opt, hwopt, hacci⟩)⟩
  -- the restriction of `y` to the block of the threshold nearly satisfies its formula
  have hgap := blockUnion_gap (hfs_get i hi) (hgd _).2.1 hsat y hnum
    (by rw [hfs_len]; exact Nat.le_succ _)
    (fun y' => (hopt'.2 y' _ (max3SATu_sol_encode.mpr ⟨h3, rfl⟩)).1 rfl) hr'
  obtain ⟨vw, hvw, haccw⟩ :=
    (chk_thrInst hF _ _ _ _ _ _).mp ((hacc' _ _).mp ((hgd _).2.2.2 _ hgap).2)
  have hmem : dec (pairWords (Code.enc (thrInst Q.maximize k x (natBits t) i))
      (y.drop (i * maxVar (formulas Q.maximize F T a gφ k x)))) ∈
      T x :: candidates Q.maximize F T a gφ dec k x y :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le hi),
      by rw [htb]⟩)
  have hcmp := hbest _ hmem vw hvw
  have hratio := himp vw (hopt.cmp hvw) haccw
  rw [OptProblem.withinRatio_iff]
  cases hm : Q.maximize
  · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hcmp hratio ⊢
    exact Nat.le_trans (Nat.mul_le_mul_left _ hcmp) hratio
  · simp only [hm, ↓reduceIte] at hcmp hratio ⊢
    exact Nat.le_trans hratio (Nat.mul_le_mul_left _ hcmp)

/-- MAX-3-SAT is APX-hard in the strong form, given witness-recovering gap reductions. -/
theorem max3SATu_strongAPXHard_of_witnessGap {num den : Nat} (hnum : 0 < num)
    (h : WitnessGap num den) : StrongAPXHard max3SATu :=
  fun _ hQ => strongPTASReducible_max3SATu_of_witnessGap hnum h hQ

end Complexity
