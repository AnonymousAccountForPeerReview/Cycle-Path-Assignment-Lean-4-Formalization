module

public import BoundedCost.PrefixVariables

/-!
# Corollary 5: the zero-cost encoding is correct

`zeroCostFormula g k` is satisfiable iff `CPAP(G, k)` has an assignment of cost `0`, for
every `k ≥ 4`. A zero-cost assignment extends to a satisfying truth assignment by
setting `s_{e,x}` true exactly when one of the first `x + 1` cycles through `e` keeps
`e`; conversely the prefix clauses propagate a kept edge forward and forbid a second
cycle from keeping it, so Algorithm 3's recovery loop turns a satisfying truth assignment
into an assignment of cost `0` (`recoverAssignment_zeroCost`).
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

/-! ## Membership in the prefix clauses -/

theorem mem_prefixClauses (g : Graph) (k : Nat) (e : Edge) (cl : Clause) :
    cl ∈ prefixClauses g k e ↔
      (∃ x, x < (cyclesThrough g k e).length - 1 ∧
        cl = [⟨edgeVariable g k ((cyclesThrough g k e).getD x 0) e, true⟩, ⟨prefixVariable g k e x, true⟩]) ∨
      (∃ x, 0 < x ∧ x < (cyclesThrough g k e).length - 1 ∧
        cl = [⟨prefixVariable g k e (x - 1), false⟩, ⟨prefixVariable g k e x, true⟩]) ∨
      (∃ x, 0 < x ∧ x < (cyclesThrough g k e).length ∧
        cl = [⟨edgeVariable g k ((cyclesThrough g k e).getD x 0) e, true⟩, ⟨prefixVariable g k e (x - 1), false⟩]) := by
  simp only [prefixClauses, List.mem_append, List.mem_map, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ((⟨x, hx, rfl⟩ | ⟨x, hx, hcl⟩) | ⟨x, hx, hcl⟩)
    · exact Or.inl ⟨x, hx, rfl⟩
    · split at hcl
      · exact Or.inr (Or.inl ⟨x, by assumption, hx, (Option.some.inj hcl).symm⟩)
      · simp at hcl
    · split at hcl
      · exact Or.inr (Or.inr ⟨x, by assumption, hx, (Option.some.inj hcl).symm⟩)
      · simp at hcl
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx0, hx, rfl⟩ | ⟨x, hx0, hx, rfl⟩)
    · exact Or.inl (Or.inl ⟨x, hx, rfl⟩)
    · exact Or.inl (Or.inr ⟨x, hx, by simp [hx0]⟩)
    · exact Or.inr ⟨x, hx, by simp [hx0]⟩

theorem mem_zeroCostFormula (g : Graph) (k : Nat) (cl : Clause) :
    cl ∈ zeroCostFormula g k ↔
      cl ∈ pathConstraints g k ∨ ∃ e ∈ edgesOnCycles g k, cl ∈ prefixClauses g k e := by
  simp [zeroCostFormula, List.mem_append, List.mem_flatMap]

/-! ## The omission variables, by edge -/

theorem assignmentOf_edgeVariable (g : Graph) {k : Nat} (f : Nat → List Edge) {i : Nat}
    (hi : i < (cycles g k).length) {e : Edge} (he : e ∈ cycleEdges (kCycle g k i)) :
    assignmentOf g k f (edgeVariable g k i e) = !(f i).contains e := by
  unfold edgeVariable
  rw [assignmentOf_pathVariable g f i (edgePosition_lt hi he), cycleEdgeAt_edgePosition hi he]

theorem edgeVariable_lt (g : Graph) {k i : Nat} (hi : i < (cycles g k).length) {e : Edge}
    (he : e ∈ cycleEdges (kCycle g k i)) : edgeVariable g k i e < k * (cycles g k).length :=
  pathVariable_lt hi (edgePosition_lt hi he)

theorem evalClause_congr {σ σ' : Assignment} {cl : Clause} (h : ∀ l ∈ cl, σ l.var = σ' l.var) :
    evalClause σ cl = evalClause σ' cl := by
  induction cl with
  | nil => rfl
  | cons l cl ih =>
    simp only [evalClause, List.any_cons] at ih ⊢
    rw [ih (fun l' hl' => h l' (List.mem_cons_of_mem l hl'))]
    have := h l List.mem_cons_self
    simp [evalLiteral, this]

theorem evalClause_pos_neg (σ : Assignment) (x y : Nat) :
    evalClause σ [⟨x, true⟩, ⟨y, false⟩] = true ↔ σ x = true ∨ σ y = false := by
  simp [evalClause, evalLiteral]

theorem evalClause_neg_pos (σ : Assignment) (x y : Nat) :
    evalClause σ [⟨x, false⟩, ⟨y, true⟩] = true ↔ σ x = false ∨ σ y = true := by
  simp [evalClause, evalLiteral]

/-! ## The truth assignment of a zero-cost assignment -/

/-- All pairs `(e, x)` naming a prefix variable `s_{e,x+1}`. -/
def allPrefix (g : Graph) (k : Nat) : List (Edge × Nat) :=
  (edgesOnCycles g k).flatMap fun e =>
    (List.range ((cyclesThrough g k e).length - 1)).map fun x => (e, x)

theorem mem_allPrefix (g : Graph) (k : Nat) (q : Edge × Nat) :
    q ∈ allPrefix g k ↔ q.1 ∈ edgesOnCycles g k ∧ q.2 < (cyclesThrough g k q.1).length - 1 := by
  simp only [allPrefix, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨e, he, x, hx, rfl⟩; exact ⟨he, hx⟩
  · rintro ⟨he, hx⟩; exact ⟨q.1, he, q.2, hx, rfl⟩

/-- `s_{e,x+1}` is true when one of the first `x + 1` cycles through `e` keeps `e`. -/
def prefixValue (g : Graph) (k : Nat) (f : Nat → List Edge) (e : Edge) (x : Nat) : Bool :=
  (List.range (x + 1)).any fun m => (f ((cyclesThrough g k e).getD m 0)).contains e

/-- The truth assignment of the paths `f`: the omission variables on the path variables, and
the prefix values on the prefix variables. -/
noncomputable def zeroAssignment (g : Graph) (k : Nat) (f : Nat → List Edge) : Assignment :=
  fun v => if v < k * (cycles g k).length then assignmentOf g k f v
    else match (allPrefix g k).find? (fun q => prefixVariable g k q.1 q.2 == v) with
      | some q => prefixValue g k f q.1 q.2
      | none => false

theorem find?_key_injective {α : Type} (key : α → Nat) (l : List α)
    (hinj : ∀ a ∈ l, ∀ b ∈ l, key a = key b → a = b) {y : α} (hy : y ∈ l) (v : Nat) (hv : key y = v) :
    l.find? (fun q => key q == v) = some y := by
  subst hv
  induction l with
  | nil => simp at hy
  | cons a l ih =>
    by_cases hk : key a = key y
    · have : a = y := hinj a List.mem_cons_self y hy hk
      subst this
      simp
    · rw [List.find?_cons_of_neg (by simp [hk])]
      apply ih
      · intro p hp q hq; exact hinj p (List.mem_cons_of_mem a hp) q (List.mem_cons_of_mem a hq)
      · rcases List.mem_cons.mp hy with h | h
        · exact absurd (h ▸ rfl) hk
        · exact h

theorem zeroAssignment_pathVariable (g : Graph) {k : Nat} (f : Nat → List Edge) {i j : Nat}
    (hi : i < (cycles g k).length) (hj : j < k) :
    zeroAssignment g k f (pathVariable k i j) = assignmentOf g k f (pathVariable k i j) := by
  have h := pathVariable_lt hi hj
  simp only [zeroAssignment, h, ↓reduceIte]

theorem zeroAssignment_prefixVariable (g : Graph) {k : Nat} (f : Nat → List Edge) {e : Edge}
    (he : e ∈ edgesOnCycles g k) {x : Nat} (hx : x < (cyclesThrough g k e).length - 1) :
    zeroAssignment g k f (prefixVariable g k e x) = prefixValue g k f e x := by
  have hge := prefixOffset_ge g k e
  have hnot : ¬ prefixVariable g k e x < k * (cycles g k).length := by
    unfold prefixVariable; omega
  have hinj : ∀ a ∈ allPrefix g k, ∀ b ∈ allPrefix g k,
      (fun q : Edge × Nat => prefixVariable g k q.1 q.2) a = (fun q : Edge × Nat => prefixVariable g k q.1 q.2) b →
      a = b := by
    intro a ha b hb hab
    obtain ⟨ha1, ha2⟩ := (mem_allPrefix g k a).mp ha
    obtain ⟨hb1, hb2⟩ := (mem_allPrefix g k b).mp hb
    obtain ⟨h1, h2⟩ := prefixVariable_inj ha1 hb1 ha2 hb2 hab
    exact Prod.ext h1 h2
  have hmem : (e, x) ∈ allPrefix g k := (mem_allPrefix g k (e, x)).mpr ⟨he, hx⟩
  have hfind : (allPrefix g k).find? (fun q => prefixVariable g k q.1 q.2 == prefixVariable g k e x) =
      some (e, x) :=
    find?_key_injective (fun q : Edge × Nat => prefixVariable g k q.1 q.2) (allPrefix g k) hinj hmem
      (prefixVariable g k e x) rfl
  simp only [zeroAssignment, hnot, ↓reduceIte, hfind]

theorem prefixValue_succ (g : Graph) (k : Nat) (f : Nat → List Edge) (e : Edge) (x : Nat) :
    prefixValue g k f e (x + 1) =
      (prefixValue g k f e x || (f ((cyclesThrough g k e).getD (x + 1) 0)).contains e) := by
  unfold prefixValue
  rw [List.range_succ, List.any_append]
  simp

theorem prefixValue_iff (g : Graph) (k : Nat) (f : Nat → List Edge) (e : Edge) (x : Nat) :
    prefixValue g k f e x = true ↔ ∃ m, m ≤ x ∧ e ∈ f ((cyclesThrough g k e).getD m 0) := by
  unfold prefixValue
  simp only [List.any_eq_true, List.mem_range, List.contains_iff_mem]
  constructor
  · rintro ⟨m, hm, h⟩; exact ⟨m, by omega, h⟩
  · rintro ⟨m, hm, h⟩; exact ⟨m, by omega, h⟩

/-! ## From a zero-cost assignment to a satisfying truth assignment -/

theorem zeroCostFormula_satisfiable_of_assignment (g : Graph) (k : Nat) {f : Nat → List Edge}
    (hf : PathsOf g k f)
    (hzero : ∀ i i' e, i < (cycles g k).length → i' < (cycles g k).length → i ≠ i' →
      e ∈ cycleEdges (kCycle g k i) → e ∈ cycleEdges (kCycle g k i') → ¬ (e ∈ f i ∧ e ∈ f i')) :
    Satisfiable (zeroCostFormula g k) := by
  refine ⟨zeroAssignment g k f, ?_⟩
  rw [evalCNF_iff]
  intro cl hcl
  rcases (mem_zeroCostFormula g k cl).mp hcl with hcl | ⟨e, he, hcl⟩
  · -- path constraints: as under the omission variables
    obtain ⟨i, a, b, hi, hab, hb, _, rfl⟩ := (mem_pathConstraints g k cl).mp hcl
    rw [evalClause_congr (σ' := assignmentOf g k f)]
    · exact pathConstraints_satisfied g f (omittedIndex hf) (fun i hi => omittedIndex_spec hf hi) _ hcl
    · intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact zeroAssignment_pathVariable g f hi (by omega)
      · exact zeroAssignment_pathVariable g f hi hb
  · -- prefix clauses of `e`
    have hcs : ∀ x, x < (cyclesThrough g k e).length →
        zeroAssignment g k f (edgeVariable g k ((cyclesThrough g k e).getD x 0) e) =
          !(f ((cyclesThrough g k e).getD x 0)).contains e := by
      intro x hx
      have hi := cyclesThrough_getD_lt g k e hx
      have hei := cyclesThrough_getD_mem g k e hx
      unfold edgeVariable
      rw [zeroAssignment_pathVariable g f hi (edgePosition_lt hi hei),
        assignmentOf_pathVariable g f _ (edgePosition_lt hi hei), cycleEdgeAt_edgePosition hi hei]
    rcases (mem_prefixClauses g k e cl).mp hcl with ⟨x, hx, rfl⟩ | ⟨x, hx0, hx, rfl⟩ | ⟨x, hx0, hx, rfl⟩
    · rw [evalClause_two_pos, hcs x (by omega), zeroAssignment_prefixVariable g f he hx]
      cases hc : (f ((cyclesThrough g k e).getD x 0)).contains e
      · exact Or.inl rfl
      · right
        rw [prefixValue_iff]
        exact ⟨x, Nat.le_refl x, List.contains_iff_mem.mp hc⟩
    · rw [evalClause_neg_pos, zeroAssignment_prefixVariable g f he (by omega),
        zeroAssignment_prefixVariable g f he hx]
      cases hp : prefixValue g k f e (x - 1)
      · exact Or.inl rfl
      · right
        rw [prefixValue_iff] at hp ⊢
        obtain ⟨m, hm, hme⟩ := hp
        exact ⟨m, by omega, hme⟩
    · rw [evalClause_pos_neg, hcs x hx, zeroAssignment_prefixVariable g f he (by omega)]
      cases hp : prefixValue g k f e (x - 1)
      · exact Or.inr rfl
      · left
        rw [prefixValue_iff] at hp
        obtain ⟨m, hm, hme⟩ := hp
        have hmx : m < (cyclesThrough g k e).length := by omega
        have hne : (cyclesThrough g k e).getD m 0 ≠ (cyclesThrough g k e).getD x 0 := by
          intro h
          have := cyclesThrough_getD_inj g k e hmx hx h
          omega
        have := hzero _ _ e (cyclesThrough_getD_lt g k e hmx) (cyclesThrough_getD_lt g k e hx) hne
          (cyclesThrough_getD_mem g k e hmx) (cyclesThrough_getD_mem g k e hx)
        have hnot : e ∉ f ((cyclesThrough g k e).getD x 0) := fun h => this ⟨hme, h⟩
        rw [Bool.not_eq_true', contains_eq_false_iff]
        exact hnot

/-! ## From a satisfying truth assignment to a zero-cost assignment -/

theorem no_overlap_of_satisfied (g : Graph) {k : Nat} (σ : Assignment)
    (hσ : ∀ cl ∈ zeroCostFormula g k, evalClause σ cl = true) {f : Nat → List Edge}
    (hdec : ∀ i, i < (cycles g k).length → ∀ e ∈ cycleEdges (kCycle g k i),
      σ (edgeVariable g k i e) = true → e ∉ f i)
    {e : Edge} (he : e ∈ edgesOnCycles g k) {x y : Nat} (hxy : x < y)
    (hy : y < (cyclesThrough g k e).length)
    (hx' : e ∈ f ((cyclesThrough g k e).getD x 0)) (hy' : e ∈ f ((cyclesThrough g k e).getD y 0)) :
    False := by
  have hpre : ∀ cl ∈ prefixClauses g k e, evalClause σ cl = true :=
    fun cl hcl => hσ cl ((mem_zeroCostFormula g k cl).mpr (Or.inr ⟨e, he, hcl⟩))
  -- `b_x` is false, so `s_x` holds
  have hbx : σ (edgeVariable g k ((cyclesThrough g k e).getD x 0) e) = false := by
    have hxl : x < (cyclesThrough g k e).length := by omega
    cases h : σ (edgeVariable g k ((cyclesThrough g k e).getD x 0) e)
    · rfl
    · exact absurd hx' (hdec _ (cyclesThrough_getD_lt g k e hxl) e (cyclesThrough_getD_mem g k e hxl) h)
  have hsx : σ (prefixVariable g k e x) = true := by
    have := hpre _ ((mem_prefixClauses g k e _).mpr (Or.inl ⟨x, by omega, rfl⟩))
    rw [evalClause_two_pos, hbx] at this
    rcases this with h | h
    · cases h
    · exact h
  -- the prefix propagates to `s_{y-1}`
  have hchain : ∀ d, x + d < y → σ (prefixVariable g k e (x + d)) = true := by
    intro d
    induction d with
    | zero => intro _; simpa using hsx
    | succ d ih =>
      intro hd
      have hprev := ih (by omega)
      have := hpre _ ((mem_prefixClauses g k e _).mpr (Or.inr (Or.inl ⟨x + d + 1, by omega, by omega, rfl⟩)))
      rw [evalClause_neg_pos, Nat.add_sub_cancel, hprev] at this
      rw [show x + (d + 1) = x + d + 1 by omega]
      rcases this with h | h
      · cases h
      · exact h
  have hsy : σ (prefixVariable g k e (y - 1)) = true := by
    have := hchain (y - 1 - x) (by omega)
    rwa [show x + (y - 1 - x) = y - 1 by omega] at this
  -- so `b_y` holds, and `e` is omitted on the `y`-th cycle
  have := hpre _ ((mem_prefixClauses g k e _).mpr (Or.inr (Or.inr ⟨y, by omega, hy, rfl⟩)))
  rw [evalClause_pos_neg, hsy] at this
  rcases this with h | h
  · exact hdec _ (cyclesThrough_getD_lt g k e hy) e (cyclesThrough_getD_mem g k e hy) h hy'
  · cases h

/-- **Corollary 5, path recovery**: from a truth assignment satisfying the zero-cost formula
(and `k ≥ 4`), Algorithm 3's recovery loop gives a cycle-path assignment of cost `0`. -/
theorem recoverAssignment_zeroCost {k : Nat} (hk : 4 ≤ k) (g : Graph) (σ : Assignment)
    (hσ : evalCNF σ (zeroCostFormula g k) = true) :
    ValidChoices ((cycles g k).map selectedOptions) (recoverAssignment g k σ) ∧
      cost (recoverAssignment g k σ) = 0 := by
  rw [evalCNF_iff] at hσ
  have hpath : ∀ cl ∈ pathConstraints g k, evalClause σ cl = true :=
    fun cl hcl => hσ cl ((mem_zeroCostFormula g k cl).mpr (Or.inl hcl))
  have hf := recoveredPath_pathsOf g (by omega : 0 < k) σ
  have hdec := recoveredPath_omits hk g σ hpath
  refine ⟨validChoices_of_pathsOf hf, ?_⟩
  unfold recoverAssignment
  rw [cost_eq_countP_violated g k hf]
  apply List.countP_eq_zero.mpr
  intro u hu hviol
  obtain ⟨i, i', e, hlt, hi', he, he', rfl⟩ := (mem_candidateOverlaps g k u).mp hu
  have hi : i < (cycles g k).length := by omega
  simp only [violatedBy, List.contains_iff_mem, Bool.and_eq_true] at hviol
  have heL : e ∈ edgesOnCycles g k := (mem_edgesOnCycles g k e).mpr ⟨i, hi, he⟩
  have hi_cs : i ∈ cyclesThrough g k e := (mem_cyclesThrough g k e i).mpr ⟨hi, he⟩
  have hi'_cs : i' ∈ cyclesThrough g k e := (mem_cyclesThrough g k e i').mpr ⟨hi', he'⟩
  obtain ⟨x, hx, hxe⟩ := (mem_iff_getD (cyclesThrough g k e) 0 i).mp hi_cs
  obtain ⟨y, hy, hye⟩ := (mem_iff_getD (cyclesThrough g k e) 0 i').mp hi'_cs
  have hxy : x ≠ y := by
    intro h; subst h
    rw [hxe] at hye
    omega
  rcases Nat.lt_or_gt_of_ne hxy with h | h
  · exact no_overlap_of_satisfied g σ hσ hdec heL h hy (hxe ▸ hviol.1) (hye ▸ hviol.2)
  · exact no_overlap_of_satisfied g σ hσ hdec heL h hx (hye ▸ hviol.2) (hxe ▸ hviol.1)

/-- **Corollary 5**, the encoding: the zero-cost formula is satisfiable iff an assignment of
cost `0` exists. -/
theorem zeroCostFormula_satisfiable_iff {k : Nat} (hk : 4 ≤ k) (g : Graph) :
    Satisfiable (zeroCostFormula g k) ↔ HasAssignment g k 0 := by
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨hv, hc⟩ := recoverAssignment_zeroCost hk g σ hσ
    exact ⟨_, hv, Nat.le_of_eq hc⟩
  · rintro ⟨ps, hv, hc⟩
    obtain ⟨hf, hps⟩ := pathsOf_of_validChoices hv
    rw [hps, cost_eq_countP_violated g k hf] at hc
    have hzero := List.countP_eq_zero.mp (Nat.le_zero.mp hc)
    apply zeroCostFormula_satisfiable_of_assignment g k hf
    intro i i' e hi hi' hne he he' ⟨h1, h2⟩
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hu := (mem_candidateOverlaps g k (i, i', e)).mpr ⟨i, i', e, hlt, hi', he, he', rfl⟩
      apply hzero _ hu
      simp only [violatedBy, List.contains_iff_mem, Bool.and_eq_true]
      exact ⟨h1, h2⟩
    · have hu := (mem_candidateOverlaps g k (i', i, e)).mpr ⟨i', i, e, hgt, hi, he', he, rfl⟩
      apply hzero _ hu
      simp only [violatedBy, List.contains_iff_mem, Bool.and_eq_true]
      exact ⟨h2, h1⟩

end STACS2027
