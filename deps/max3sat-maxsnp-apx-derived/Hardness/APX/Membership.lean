module

public import Hardness.APX.Defs
public import Hardness.APX.Binary
public import Hardness.APX.Parse
public import Hardness.APX.Uniform
public import Hardness.MaxSNP.Main
public import Hardness.MaxSNP.Final
import Lean.Elab.Tactic.Omega

/-!
# MAX-3-SAT and the class APX

* `not_npo_max3SATu`: the auxiliary problem `max3SATu` (`Hardness.Unbounded`) is **not** in
  `NPO` as defined, because every word is an assignment of every formula, so solutions are not
  polynomially bounded. Consequently `InAPX max3SATu`, `APXComplete max3SATu` and
  `InMaxSNP max3SATu` are false.
* `max3SAT` (assignments no longer than the instance) does not have this defect: it has the
  same optima as `max3SATu` (`max3SAT_isOpt_iff`), the two problems are L-reducible to each
  other (`lReducible_max3SATu_max3SAT`, `lReducible_max3SAT_max3SATu`), and PTAS-reductions to
  `max3SATu` are PTAS-reductions to `max3SAT`.
* `npo_max3SAT`, hence `max3SAT_inMaxSNP` (with the L-reduction to the MaxSNP₀ problem of
  `φ₃`) and `MaxSNPHard.max3SATu_lReducible`: MAX-3-SAT L-reduces to every MaxSNP-hard
  problem.
* `max3Approx_spec` (the better of the all-true and the all-false assignment is a
  2-approximation), hence `max3SAT_inAPX`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity

open Complexity.PT Complexity.Reg

/-! ### Unbounded solutions -/

/-- `max3SATu` is not in `NPO`: its solutions are not polynomially bounded. -/
theorem not_npo_max3SATu : ¬ NPO max3SATu := by
  rintro ⟨⟨c, e, hb⟩, -⟩
  have := hb (SAT.encode []) (List.replicate (powerBound c e (SAT.encode []).length + 1) true) 0
    ⟨[], rfl, fun _ h => absurd h List.not_mem_nil, rfl⟩
  rw [List.length_replicate] at this
  omega

theorem not_inAPX_max3SATu : ¬ InAPX max3SATu := fun h => not_npo_max3SATu h.1

theorem not_apxComplete_max3SATu : ¬ APXComplete max3SATu := fun h => not_inAPX_max3SATu h.1

theorem not_inMaxSNP_max3SATu : ¬ InMaxSNP max3SATu := fun h => not_npo_max3SATu h.1

/-! ### `max3SATu` and `max3SAT` -/

theorem max3SATu_sol_of_sol {x y : Word} {v : Nat} (h : max3SAT.Sol x y v) :
    max3SATu.Sol x y v := by
  obtain ⟨f, hf, h3, -, hv⟩ := h
  exact ⟨f, hf, h3, hv⟩

theorem SAT.assignmentOf_take (y : Word) {n v : Nat} (hv : v < n) :
    SAT.assignmentOf (y.take n) v = SAT.assignmentOf y v := by
  simp [SAT.assignmentOf, List.getD_eq_getElem?_getD, hv]

/-- Truncating an assignment to the length of the instance does not change its value. -/
theorem max3SAT_sol_take {x y : Word} {v : Nat} (h : max3SATu.Sol x y v) :
    max3SAT.Sol x (y.take x.length) v := by
  obtain ⟨f, rfl, h3, rfl⟩ := h
  exact ⟨f, rfl, h3, List.length_take_le _ _, SAT.satCount_congr fun cl hc l hl =>
    (SAT.assignmentOf_take y (SAT.var_lt_encode_length hc hl)).symm⟩

/-- MAX-3-SAT and its version with unbounded assignments have the same optima. -/
theorem max3SAT_isOpt_iff {x : Word} {opt : Nat} :
    max3SAT.IsOpt x opt ↔ max3SATu.IsOpt x opt := by
  constructor
  · rintro ⟨⟨y, hy⟩, hall⟩
    exact ⟨⟨y, max3SATu_sol_of_sol hy⟩, fun y' v' h' => hall _ v' (max3SAT_sol_take h')⟩
  · rintro ⟨⟨y, hy⟩, hall⟩
    exact ⟨⟨_, max3SAT_sol_take hy⟩, fun y' v' h' => hall y' v' (max3SATu_sol_of_sol h')⟩

/-- MAX-3-SAT with unbounded assignments L-reduces to MAX-3-SAT (same instances; bounded
assignments are assignments). -/
theorem lReducible_max3SATu_max3SAT : LReducible max3SATu max3SAT := by
  refine ⟨fun x => x, fun z => (unpair z).2, 1, 1, polyTime_id, polyTime_pair_snd, ?_⟩
  intro x opt hopt
  refine ⟨opt, max3SAT_isOpt_iff.mpr hopt, by omega, fun y v' hy => ?_⟩
  exact ⟨v', by simpa only [unpair_pairWords] using max3SATu_sol_of_sol hy, by omega⟩

/-- MAX-3-SAT L-reduces to MAX-3-SAT with unbounded assignments (same instances; assignments
are truncated to the length of the instance). -/
theorem lReducible_max3SAT_max3SATu : LReducible max3SAT max3SATu := by
  have hg : PT (fun p : Word × Word => p.2.take p.1.length) := by fun_prop
  refine ⟨fun x => x, fun z => (unpair z).2.take (unpair z).1.length, 1, 1, polyTime_id,
    PT.polyTime_pairWords_word (h := fun x y : Word => y.take x.length) hg, ?_⟩
  intro x opt hopt
  refine ⟨opt, max3SAT_isOpt_iff.mp hopt, by omega, fun y v' hy => ?_⟩
  exact ⟨v', by simpa only [unpair_pairWords] using max3SAT_sol_take hy, by omega⟩

/-- A strong PTAS-reduction to `max3SATu` is one to `max3SAT`, with the same maps. -/
theorem StrongPTASReducible.to_max3SAT {Q : OptProblem} (h : StrongPTASReducible Q max3SATu) :
    StrongPTASReducible Q max3SAT := by
  obtain ⟨f, g, c, hf, hg, hc, h⟩ := h
  refine ⟨f, g, c, hf, hg, hc, fun k x opt hopt => ?_⟩
  obtain ⟨opt', hopt', hsol⟩ := h k x opt hopt
  exact ⟨opt', max3SAT_isOpt_iff.mpr hopt', fun y v' hy => hsol y v' (max3SATu_sol_of_sol hy)⟩

/-- A PTAS-reduction to `max3SATu` is one to `max3SAT`, with the same maps. -/
theorem PTASReducible.to_max3SAT {Q : OptProblem} (h : PTASReducible Q max3SATu) :
    PTASReducible Q max3SAT := by
  obtain ⟨f, g, c, hf, hg, hc, h⟩ := h
  refine ⟨f, g, c, hf, hg, hc, fun k x opt hopt => ?_⟩
  obtain ⟨opt', hopt', hsol⟩ := h k x opt hopt
  exact ⟨opt', max3SAT_isOpt_iff.mpr hopt', fun y v' hy => hsol y v' (max3SATu_sol_of_sol hy)⟩

theorem APXHard.to_max3SAT (h : APXHard max3SATu) : APXHard max3SAT :=
  fun Q hQ => (h Q hQ).to_max3SAT

theorem StrongAPXHard.to_max3SAT (h : StrongAPXHard max3SATu) : StrongAPXHard max3SAT :=
  fun Q hQ => (h Q hQ).to_max3SAT

/-! ### `max3SAT` is in NPO -/

/-- The feasibility and value function of `max3SAT`. -/
def max3Feas (x y : Word) : Word :=
  if SAT.encode (parseCNF x) = x ∧ (∀ cl ∈ parseCNF x, cl.length ≤ 3) ∧ y.length ≤ x.length then
    true :: natBits (SAT.satCount (SAT.assignmentOf y) (parseCNF x))
  else [false]

theorem max3Feas_iff (x y : Word) (v : Nat) :
    max3SAT.Sol x y v ↔ max3Feas x y = true :: natBits v := by
  constructor
  · rintro ⟨f, rfl, h3, hlen, rfl⟩
    rw [max3Feas, parseCNF_encode, ite_eq_left ⟨rfl, h3, hlen⟩]
  · intro h
    rw [max3Feas] at h
    split at h
    · next hc =>
      obtain ⟨hx, h3, hlen⟩ := hc
      exact ⟨parseCNF x, hx, h3, hlen, natBits_injective (List.cons.inj h).2.symm⟩
    · cases h

theorem pt_max3Feas : PT (fun p : Word × Word => max3Feas p.1 p.2) := by
  unfold max3Feas
  fun_prop

theorem npo_max3SAT : NPO max3SAT := by
  refine ⟨⟨1, 1, ?_⟩, fun z => max3Feas (unpair z).1 (unpair z).2,
    PT.polyTime_pairWords_word (h := max3Feas) pt_max3Feas, fun x y v => ?_⟩
  · rintro x y v ⟨f, -, -, hlen, -⟩
    rw [powerBound_eq, Nat.pow_one]
    omega
  · simp only [unpair_pairWords]
    exact max3Feas_iff x y v

/-- **MAX-3-SAT is in MaxSNP**: it is in NPO and L-reduces to the MaxSNP₀ problem of the
well-formed formula `φ₃` in four variables. -/
theorem max3SAT_inMaxSNP : InMaxSNP max3SAT :=
  ⟨npo_max3SAT, ga₃, sa₃, 4, φ₃, wellFormed_φ₃,
    lReducible_max3SAT_max3SATu.trans lReducible_max3SATu_maxSNP0_φ₃⟩

/-- MAX-3-SAT (also with unbounded assignments) L-reduces to every MaxSNP-hard problem. -/
theorem MaxSNPHard.max3SATu_lReducible {P : OptProblem} (hP : MaxSNPHard P) :
    LReducible max3SATu P :=
  lReducible_max3SATu_max3SAT.trans (hP max3SAT max3SAT_inMaxSNP)

/-! ### A 2-approximation -/

theorem countP_le_countP_add {α : Type} {p q r : α → Bool} {l : List α}
    (h : ∀ x ∈ l, p x = true → q x = true ∨ r x = true) :
    l.countP p ≤ l.countP q + l.countP r := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have h2 := h a List.mem_cons_self
    simp only [List.countP_cons]
    cases hp : p a <;> cases hq : q a <;> cases hr : r a <;> simp_all <;> omega

/-- Every satisfied clause is satisfied by the all-false or by the all-true assignment. -/
theorem SAT.satCount_le_false_add_true (a aF aT : SAT.Assignment) (f : SAT.CNF)
    (hF : ∀ cl ∈ f, ∀ l ∈ cl, aF l.var = false) (hT : ∀ cl ∈ f, ∀ l ∈ cl, aT l.var = true) :
    SAT.satCount a f ≤ SAT.satCount aF f + SAT.satCount aT f := by
  refine countP_le_countP_add fun cl hcl h => ?_
  obtain ⟨l, hl, -⟩ := List.any_eq_true.mp h
  cases hp : l.positive
  · exact Or.inl (List.any_eq_true.mpr ⟨l, hl, by simp [SAT.evalLiteral, hp, hF cl hcl l hl]⟩)
  · exact Or.inr (List.any_eq_true.mpr ⟨l, hl, by simp [SAT.evalLiteral, hp, hT cl hcl l hl]⟩)

/-- The better of the all-true and the all-false assignment. -/
def max3Approx (x : Word) : Word :=
  if SAT.satCount (SAT.assignmentOf []) (parseCNF x) ≤
      SAT.satCount (SAT.assignmentOf (List.replicate x.length true)) (parseCNF x) then
    List.replicate x.length true
  else []

theorem max3Approx_spec : max3SAT.ApproxAlgorithm 2 1 max3Approx := by
  refine ⟨PT.polyTime_word (by unfold max3Approx; fun_prop), fun x opt hopt => ?_⟩
  obtain ⟨⟨y, f, rfl, h3, hlen, rfl⟩, -⟩ := hopt
  have hT : ∀ cl ∈ f, ∀ l ∈ cl,
      SAT.assignmentOf (List.replicate (SAT.encode f).length true) l.var = true := by
    intro cl hc l hl
    simp [SAT.assignmentOf, List.getD_eq_getElem?_getD, SAT.var_lt_encode_length hc hl]
  have hFa : ∀ cl ∈ f, ∀ l ∈ cl, SAT.assignmentOf [] l.var = false := by
    intro cl _ l _
    simp [SAT.assignmentOf]
  have key := SAT.satCount_le_false_add_true (SAT.assignmentOf y) _ _ f hFa hT
  simp only [max3Approx, parseCNF_encode]
  split
  · refine ⟨_, ⟨f, rfl, h3, by simp, rfl⟩, fun _ => by omega, fun hmin => by cases hmin⟩
  · refine ⟨_, ⟨f, rfl, h3, by simp, rfl⟩, fun _ => by omega, fun hmin => by cases hmin⟩

/-- **MAX-3-SAT is in APX.** -/
theorem max3SAT_inAPX : InAPX max3SAT :=
  ⟨npo_max3SAT, 2, 1, by omega, max3Approx, max3Approx_spec⟩

end Complexity
