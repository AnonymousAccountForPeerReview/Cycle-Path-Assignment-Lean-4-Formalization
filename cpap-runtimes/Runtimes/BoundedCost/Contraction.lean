module

public import Runtimes.BoundedCost.CutGraph
import Mathlib.Tactic

/-!
# Required literals as contracted cut terminals

Variables required at their reference value are contracted to source zero;
variables required at the opposite value are contracted to sink one.  Arcs
entering the source or leaving the sink never cross a valid cut and are
discarded.  A maximum source-side minimum cut decodes to the least-deviation
assignment required by the annotated search.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

def sourceTerminal (τ : Assignment) (L : List Literal) (x : ℕ) : Bool :=
  L.any fun l => decide (l.var = x) && evalLiteral τ l

def sinkTerminal (τ : Assignment) (L : List Literal) (x : ℕ) : Bool :=
  L.any fun l => decide (l.var = x) && !(evalLiteral τ l)

theorem sourceTerminal_iff (τ : Assignment) (L : List Literal) (x : ℕ) :
    sourceTerminal τ L x = true ↔ ∃ l ∈ L, l.var = x ∧ evalLiteral τ l = true := by
  simp [sourceTerminal]

theorem sinkTerminal_iff (τ : Assignment) (L : List Literal) (x : ℕ) :
    sinkTerminal τ L x = true ↔ ∃ l ∈ L, l.var = x ∧ evalLiteral τ l = false := by
  simp [sinkTerminal]

def TerminalConsistent (τ : Assignment) (L : List Literal) : Prop :=
  ∀ x, sourceTerminal τ L x = true → sinkTerminal τ L x = false

theorem terminalConsistent_of_requires (τ : Assignment) {σ : Assignment} {L : List Literal}
    (hσ : Requires σ L) : TerminalConsistent τ L := by
  intro x hs
  obtain ⟨a, ha, hax, hta⟩ := (sourceTerminal_iff τ L x).mp hs
  have hra := (requires_iff_agreementRegion τ σ L).mp hσ a ha
  rw [hax, hta] at hra
  cases ht : sinkTerminal τ L x with
  | false => rfl
  | true =>
    obtain ⟨b, hb, hbx, htb⟩ := (sinkTerminal_iff τ L x).mp ht
    have hrb := (requires_iff_agreementRegion τ σ L).mp hσ b hb
    rw [hbx, htb, hra] at hrb
    cases hrb

/-- The contracted variable number: source zero, sink one, or the shifted variable. -/
def contractVariable (τ : Assignment) (L : List Literal) (x : ℕ) : ℕ :=
  if sourceTerminal τ L x then 0 else if sinkTerminal τ L x then 1 else x + 2

/-- Lift a contracted cut region to the original variables. -/
def liftContractRegion (τ : Assignment) (L : List Literal) (region : ℕ → Bool) : ℕ → Bool :=
  fun x => region (contractVariable τ L x)

/-- Extend an assignment's agreement region to the contracted nodes. -/
def projectContractRegion (τ σ : Assignment) : ℕ → Bool :=
  fun v => if v = 0 then true else if v = 1 then false else agreementRegion τ σ (v - 2)

theorem projectContractRegion_valid (τ σ : Assignment) :
    projectContractRegion τ σ 0 = true ∧ projectContractRegion τ σ 1 = false := by
  simp [projectContractRegion]

theorem lift_projectContractRegion (τ : Assignment) {σ : Assignment} {L : List Literal}
    (hσ : Requires σ L) :
    liftContractRegion τ L (projectContractRegion τ σ) = agreementRegion τ σ := by
  funext x
  by_cases hs : sourceTerminal τ L x = true
  · obtain ⟨l, hl, hlx, htl⟩ := (sourceTerminal_iff τ L x).mp hs
    have hr := (requires_iff_agreementRegion τ σ L).mp hσ l hl
    rw [hlx, htl] at hr
    simp [liftContractRegion, contractVariable, hs, projectContractRegion, hr]
  · have hs' : sourceTerminal τ L x = false := by simpa using hs
    by_cases ht : sinkTerminal τ L x = true
    · obtain ⟨l, hl, hlx, htl⟩ := (sinkTerminal_iff τ L x).mp ht
      have hr := (requires_iff_agreementRegion τ σ L).mp hσ l hl
      rw [hlx, htl] at hr
      simp [liftContractRegion, contractVariable, hs', ht, projectContractRegion, hr]
    · have ht' : sinkTerminal τ L x = false := by simpa using ht
      simp [liftContractRegion, contractVariable, hs', ht', projectContractRegion]

theorem requires_assignmentOfContractRegion {τ : Assignment} {L : List Literal}
    (hL : TerminalConsistent τ L) {region : ℕ → Bool}
    (hsource : region 0 = true) (hsink : region 1 = false) :
    Requires (assignmentOfRegion τ (liftContractRegion τ L region)) L := by
  rw [requires_iff_agreementRegion, agreementRegion_assignmentOfRegion]
  intro l hl
  cases ht : evalLiteral τ l with
  | true =>
    have hs := (sourceTerminal_iff τ L l.var).mpr ⟨l, hl, rfl, ht⟩
    simp [liftContractRegion, contractVariable, hs, hsource]
  | false =>
    have hsink' := (sinkTerminal_iff τ L l.var).mpr ⟨l, hl, rfl, ht⟩
    have hs : sourceTerminal τ L l.var = false := by
      cases hs : sourceTerminal τ L l.var with
      | false => rfl
      | true => have := hL l.var hs; rw [hsink'] at this; cases this
    simp [liftContractRegion, contractVariable, hs, hsink', hsink]

theorem terminalConsistent_iff_requires (τ : Assignment) (L : List Literal) :
    TerminalConsistent τ L ↔ ∃ σ, Requires σ L := by
  constructor
  · intro hL
    exact ⟨assignmentOfRegion τ (liftContractRegion τ L (fun v => decide (v ≠ 1))),
      requires_assignmentOfContractRegion hL (by decide) (by decide)⟩
  · rintro ⟨σ, hσ⟩
    exact terminalConsistent_of_requires τ hσ

/-- An arc that cannot cross a valid cut is removed. -/
def contractCutArc (τ : Assignment) (L : List Literal) (e : ℕ × ℕ) : Option (ℕ × ℕ) :=
  let u := contractVariable τ L e.1
  let v := contractVariable τ L e.2
  if v = 0 ∨ u = 1 then none else some (u, v)

def contractedCutArcs (τ : Assignment) (f : CNF) (L : List Literal) : List (ℕ × ℕ) :=
  (variableCutArcs τ f).filterMap (contractCutArc τ L)

theorem contractCutArc_cost {τ : Assignment} {L : List Literal} {region : ℕ → Bool}
    (hsource : region 0 = true) (hsink : region 1 = false) (e : ℕ × ℕ) :
    ((contractCutArc τ L e).toList.map (variableArcCut region)).sum =
      variableArcCut (liftContractRegion τ L region) e := by
  by_cases hv : contractVariable τ L e.2 = 0
  · simp [contractCutArc, hv, variableArcCut, liftContractRegion, hsource]
  · by_cases hu : contractVariable τ L e.1 = 1
    · simp [contractCutArc, hu, variableArcCut, liftContractRegion, hsink]
    · simp [contractCutArc, hu, hv, variableArcCut, liftContractRegion]

theorem contractedCutSize_eq_lift {τ : Assignment} {L : List Literal} {region : ℕ → Bool}
    (hsource : region 0 = true) (hsink : region 1 = false) (arcs : List (ℕ × ℕ)) :
    variableCutSize (arcs.filterMap (contractCutArc τ L)) region =
      variableCutSize arcs (liftContractRegion τ L region) := by
  induction arcs with
  | nil => simp [variableCutSize]
  | cons e arcs ih =>
    have he := contractCutArc_cost (τ := τ) (L := L) hsource hsink e
    cases hc : contractCutArc τ L e <;>
      simp [variableCutSize, hc] at he ih ⊢ <;> omega

/-- Exact cost preservation from contracted graph cuts to assignments. -/
theorem cutCost_assignmentOfContractRegion {τ : Assignment} {f : CNF} (hf : Clauses2 f)
    (hτ : evalCNF τ f = true) {L : List Literal} {region : ℕ → Bool}
    (hsource : region 0 = true) (hsink : region 1 = false) :
    cutCost τ (assignmentOfRegion τ (liftContractRegion τ L region)) f =
      variableCutSize (contractedCutArcs τ f L) region := by
  rw [cutCost_eq_variableCutSize hf hτ, agreementRegion_assignmentOfRegion]
  exact (contractedCutSize_eq_lift hsource hsink _).symm

/-- Exact cost preservation from assignments to contracted graph cuts. -/
theorem cutCost_projectContractRegion {τ σ : Assignment} {f : CNF} (hf : Clauses2 f)
    (hτ : evalCNF τ f = true) {L : List Literal} (hσ : Requires σ L) :
    cutCost τ σ f = variableCutSize (contractedCutArcs τ f L) (projectContractRegion τ σ) := by
  have hv := projectContractRegion_valid τ σ
  unfold contractedCutArcs
  rw [contractedCutSize_eq_lift hv.1 hv.2, lift_projectContractRegion τ hσ]
  exact cutCost_eq_variableCutSize hf hτ σ

theorem contractVariable_lt {n x : ℕ} (hx : x < n) (τ : Assignment) (L : List Literal) :
    contractVariable τ L x < n + 2 := by
  unfold contractVariable
  split <;> (try split) <;> omega

theorem contractedCutArcs_length_le (τ : Assignment) (f : CNF) (L : List Literal) :
    (contractedCutArcs τ f L).length ≤ f.length := by
  exact (List.length_filterMap_le _ _).trans (variableCutArcs_length_le τ f)

theorem contractedCutArcs_endpoints {n : ℕ} {f : CNF} (hf : TwoSat.IsTwoCNF n f)
    (τ : Assignment) (L : List Literal) :
    ∀ e ∈ contractedCutArcs τ f L, e.1 < n + 2 ∧ e.2 < n + 2 ∧ e.1 ≠ 1 ∧ e.2 ≠ 0 := by
  intro e he
  obtain ⟨arc, harc, he⟩ := List.mem_filterMap.mp he
  have hv := variableCutArcs_endpoints hf τ arc harc
  have hu := contractVariable_lt hv.1 τ L
  have hw := contractVariable_lt hv.2 τ L
  simp only [contractCutArc] at he
  split at he
  · simp at he
  · rename_i hn
    simp only [Option.some.injEq] at he
    subst e
    exact ⟨hu, hw, fun h => hn (Or.inr h), fun h => hn (Or.inl h)⟩

/-- A maximum source-side minimum cut, stated on the numbered arc list. -/
structure IsMaximumSourceCut (arcs : List (ℕ × ℕ)) (region : ℕ → Bool) : Prop where
  source : region 0 = true
  sink : region 1 = false
  optimal : ∀ other, other 0 = true → other 1 = false →
    variableCutSize arcs region ≤ variableCutSize arcs other
  maximum : ∀ other, other 0 = true → other 1 = false →
    variableCutSize arcs other = variableCutSize arcs region →
      ∀ v, other v = true → region v = true

/-- The maximal cut certificate gives exactly the least-cut oracle certificate
used by the executable search. -/
theorem leastCut_of_maximumSourceCut {τ : Assignment} {f : CNF} (hf : Clauses2 f)
    (hτ : evalCNF τ f = true) {L : List Literal} (hL : TerminalConsistent τ L)
    {region : ℕ → Bool} (hr : IsMaximumSourceCut (contractedCutArcs τ f L) region) :
    IsLeastCut τ f L (assignmentOfRegion τ (liftContractRegion τ L region)) := by
  refine ⟨requires_assignmentOfContractRegion hL hr.source hr.sink, ?_, ?_⟩
  · intro σ hσ
    rw [cutCost_assignmentOfContractRegion hf hτ hr.source hr.sink,
      cutCost_projectContractRegion hf hτ hσ]
    exact hr.optimal _ (projectContractRegion_valid τ σ).1 (projectContractRegion_valid τ σ).2
  · intro σ hσ he x hx
    have hv := projectContractRegion_valid τ σ
    have he' : variableCutSize (contractedCutArcs τ f L) (projectContractRegion τ σ) =
        variableCutSize (contractedCutArcs τ f L) region := by
      rwa [cutCost_projectContractRegion hf hτ hσ,
        cutCost_assignmentOfContractRegion hf hτ hr.source hr.sink] at he
    intro hxe
    have ha : agreementRegion τ σ x = true := by simp [agreementRegion, hxe]
    have hp := congrFun (lift_projectContractRegion τ hσ) x
    have hc : projectContractRegion τ σ (contractVariable τ L x) = true := by
      simpa [liftContractRegion, ha] using hp
    have hm := hr.maximum _ hv.1 hv.2 he' (contractVariable τ L x) hc
    have hsame : assignmentOfRegion τ (liftContractRegion τ L region) x = τ x := by
      simp [assignmentOfRegion, liftContractRegion, hm]
    exact hx hsame

end STACS2027.Runtimes.BoundedCost
