module

public import Runtimes.BoundedCost.ContractionData
public import Runtimes.BoundedCost.DenseState
public import Runtimes.BoundedCost.CutNetwork
public import Runtimes.Flow.PaddedEncoding
import Mathlib.Tactic

/-! Dense dual-literal tables and occurrence rows describe the exact contracted
cut graph, retaining separate indices for repeated clauses. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 Complexity.SAT

theorem mem_denseRequirements (n : ℕ) (forced : ℕ → Bool) (l : Literal) :
    l ∈ denseRequirements n forced ↔ l.var < n ∧ forced (TwoSat.code l) = true := by
  constructor
  · intro h
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h
    obtain ⟨hb, hf⟩ := List.mem_filter.mp hu
    refine ⟨?_, ?_⟩
    · have := List.mem_range.mp hb
      change u / 2 < n
      omega
    · simpa only [code_literalOfCode] using hf
  · rintro ⟨hl, hf⟩
    exact List.mem_map.mpr ⟨TwoSat.code l,
      List.mem_filter.mpr ⟨List.mem_range.mpr (TwoSat.code_lt hl), hf⟩,
      literalOfCode_code l⟩

theorem sourceTerminal_denseRequirements (τ : Assignment) (n : ℕ) (forced : ℕ → Bool)
    (x : ℕ) (hx : x < n) :
    sourceTerminal τ (denseRequirements n forced) x =
      ((forced (2 * x) && τ x) || (forced (2 * x + 1) && !(τ x))) := by
  apply Bool.eq_iff_iff.mpr
  rw [sourceTerminal_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨l, hl, he, ht⟩
    obtain ⟨_, hf⟩ := (mem_denseRequirements n forced l).mp hl
    rcases l with ⟨v, sign⟩
    dsimp at he
    subst v
    cases sign
    · apply Or.inr
      simpa [TwoSat.code, evalLiteral] using And.intro hf ht
    · apply Or.inl
      simpa [TwoSat.code, evalLiteral] using And.intro hf ht
  · rintro (⟨hf, ht⟩ | ⟨hf, ht⟩)
    · refine ⟨⟨x, true⟩, ?_, rfl, ?_⟩
      · exact (mem_denseRequirements n forced _).mpr ⟨hx, by simpa [TwoSat.code] using hf⟩
      · simpa [evalLiteral] using ht
    · refine ⟨⟨x, false⟩, ?_, rfl, ?_⟩
      · exact (mem_denseRequirements n forced _).mpr ⟨hx, by simpa [TwoSat.code] using hf⟩
      · simpa [evalLiteral] using ht

theorem sinkTerminal_denseRequirements (τ : Assignment) (n : ℕ) (forced : ℕ → Bool)
    (x : ℕ) (hx : x < n) :
    sinkTerminal τ (denseRequirements n forced) x =
      ((forced (2 * x) && !(τ x)) || (forced (2 * x + 1) && τ x)) := by
  apply Bool.eq_iff_iff.mpr
  rw [sinkTerminal_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨l, hl, he, ht⟩
    obtain ⟨_, hf⟩ := (mem_denseRequirements n forced l).mp hl
    rcases l with ⟨v, sign⟩
    dsimp at he
    subst v
    cases sign
    · apply Or.inr
      simpa [TwoSat.code, evalLiteral] using And.intro hf ht
    · apply Or.inl
      simpa [TwoSat.code, evalLiteral] using And.intro hf ht
  · rintro (⟨hf, ht⟩ | ⟨hf, ht⟩)
    · refine ⟨⟨x, true⟩, ?_, rfl, ?_⟩
      · exact (mem_denseRequirements n forced _).mpr ⟨hx, by simpa [TwoSat.code] using hf⟩
      · simpa [evalLiteral] using ht
    · refine ⟨⟨x, false⟩, ?_, rfl, ?_⟩
      · exact (mem_denseRequirements n forced _).mpr ⟨hx, by simpa [TwoSat.code] using hf⟩
      · simpa [evalLiteral] using ht

def terminalRowsOf (n : ℕ) (τ : Assignment) (forced : ℕ → Bool) : List TerminalRow :=
  List.ofFn fun x : Fin n => ⟨forced (2 * x.val), forced (2 * x.val + 1), τ x.val⟩

@[simp] theorem terminalRowsOf_length (n : ℕ) (τ : Assignment) (forced : ℕ → Bool) :
    (terminalRowsOf n τ forced).length = n := by simp [terminalRowsOf]

theorem terminalRowsOf_getD (n : ℕ) (τ : Assignment) (forced : ℕ → Bool)
    (x : ℕ) (hx : x < n) :
    (terminalRowsOf n τ forced).getD x default =
      ⟨forced (2 * x), forced (2 * x + 1), τ x⟩ := by
  simp [terminalRowsOf, List.getD_eq_getElem?_getD, hx]

theorem terminalLabel_contractVariable (τ : Assignment) (n : ℕ) (forced : ℕ → Bool)
    (x : ℕ) (hx : x < n) :
    terminalLabel x ⟨forced (2 * x), forced (2 * x + 1), τ x⟩ =
      contractVariable τ (denseRequirements n forced) x := by
  rw [contractVariable, sourceTerminal_denseRequirements τ n forced x hx,
    sinkTerminal_denseRequirements τ n forced x hx]
  cases hp : forced (2 * x) <;> cases hn : forced (2 * x + 1) <;> cases hr : τ x <;>
    simp [terminalLabel, hp, hn, hr]

theorem terminalLabelValue_code (τ : Assignment) (n : ℕ) (forced : ℕ → Bool)
    (l : Literal) (hl : l.var < n) :
    TerminalLabelValue (terminalRowsOf n τ forced) (TwoSat.code l) =
      contractVariable τ (denseRequirements n forced) l.var := by
  have hv : TwoSat.code l / 2 = l.var := by
    cases hp : l.positive <;> simp [TwoSat.code, hp] <;> omega
  simp only [TerminalLabelValue, hv, terminalRowsOf_getD n τ forced l.var hl]
  exact terminalLabel_contractVariable τ n forced l.var hl

theorem terminalConflictPrefix_dense (τ : Assignment) (n : ℕ) (forced : ℕ → Bool) :
    terminalConflictPrefix (terminalRowsOf n τ forced) n = true ↔
      ∃ x < n, forced (2 * x) = true ∧ forced (2 * x + 1) = true := by
  unfold terminalConflictPrefix
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨x, hx, hf⟩
    rw [terminalRowsOf_getD n τ forced x hx] at hf
    exact ⟨x, hx, by simpa [terminalConflict] using hf⟩
  · rintro ⟨x, hx, hp, hn⟩
    refine ⟨x, hx, ?_⟩
    rw [terminalRowsOf_getD n τ forced x hx]
    simp [terminalConflict, hp, hn]

theorem terminalConsistent_dense (τ : Assignment) (n : ℕ) (forced : ℕ → Bool) :
    TerminalConsistent τ (denseRequirements n forced) ↔
      ¬∃ x < n, forced (2 * x) = true ∧ forced (2 * x + 1) = true := by
  constructor
  · intro h
    rintro ⟨x, hx, hp, hn⟩
    have hs : sourceTerminal τ (denseRequirements n forced) x = true := by
      rw [sourceTerminal_denseRequirements τ n forced x hx]
      cases ht : τ x <;> simp [hp, hn, ht]
    have ht := h x hs
    rw [sinkTerminal_denseRequirements τ n forced x hx] at ht
    cases hr : τ x <;> simp_all
  · intro h x hs
    obtain ⟨l, hl, he, _⟩ := (sourceTerminal_iff τ _ x).mp hs
    have hx : x < n := he ▸ ((mem_denseRequirements n forced l).mp hl).1
    rw [sourceTerminal_denseRequirements τ n forced x hx] at hs
    rw [sinkTerminal_denseRequirements τ n forced x hx]
    have hn : ¬(forced (2 * x) = true ∧ forced (2 * x + 1) = true) :=
      fun hh => h ⟨x, hx, hh⟩
    cases hp : forced (2 * x) <;> cases hm : forced (2 * x + 1) <;>
      cases hr : τ x <;> simp_all

theorem terminalConflictPrefix_false_iff (τ : Assignment) (n : ℕ) (forced : ℕ → Bool) :
    terminalConflictPrefix (terminalRowsOf n τ forced) n = false ↔
      TerminalConsistent τ (denseRequirements n forced) := by
  rw [terminalConsistent_dense]
  have h := terminalConflictPrefix_dense τ n forced
  cases he : terminalConflictPrefix (terminalRowsOf n τ forced) n <;> simp_all

def contractionRowOf (τ : Assignment) : Bool × Clause → ContractionRow
  | (active, [a, b]) =>
      ⟨TwoSat.code a, TwoSat.code b, active, evalLiteral τ a, evalLiteral τ b⟩
  | _ => default

def contractionRowsOf (τ : Assignment) (rows : List (Bool × Clause)) : List ContractionRow :=
  rows.map (contractionRowOf τ)

theorem contractionRowOf_arc (τ : Assignment) (n : ℕ) (forced : ℕ → Bool)
    (active : Bool) (a b : Literal) (ha : a.var < n) (hb : b.var < n)
    (href : active = true → evalClause τ [a, b] = true) :
    (contractionRowArc (TerminalLabelValue (terminalRowsOf n τ forced))
      (contractionRowOf τ (active, [a, b]))).toList =
        if active then (clauseCutArcs τ [a, b]).filterMap
          (contractCutArc τ (denseRequirements n forced)) else [] := by
  simp only [contractionRowOf, contractionRowArc,
    terminalLabelValue_code τ n forced a ha, terminalLabelValue_code τ n forced b hb]
  cases hactive : active <;> cases hfirst : evalLiteral τ a <;>
    cases hsecond : evalLiteral τ b <;>
    simp_all [evalClause, clauseCutArcs, retainContractedArc, contractCutArc]
  all_goals split_ifs <;> simp_all [contractCutArc]

theorem map_getD_range {α : Type*} (rows : List α) (fallback : α) :
    (List.range rows.length).map (fun i => rows.getD i fallback) = rows := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < rows.length
  · simp [hi, List.getD_eq_getElem?_getD]
  · have hn : rows[i]? = none := List.getElem?_eq_none (by omega)
    simp [hi, hn]

theorem contractionArcsPrefix_all (labels : ℕ → ℕ) (rows : List ContractionRow) :
    contractionArcsPrefix labels rows rows.length = rows.filterMap (contractionRowArc labels) := by
  unfold contractionArcsPrefix
  have h := congrArg (List.filterMap (contractionRowArc labels)) (map_getD_range rows default)
  simpa only [List.filterMap_map, Function.comp_def] using h

theorem contractionRowsOf_arcs (τ : Assignment) (n : ℕ) (forced : ℕ → Bool)
    (rows : List (Bool × Clause))
    (hrows : ∀ row ∈ rows, row.2.length = 2 ∧ ∀ l ∈ row.2, l.var < n)
    (href : evalCNF τ (activeOccurrences rows) = true) :
    (contractionRowsOf τ rows).filterMap
      (contractionRowArc (TerminalLabelValue (terminalRowsOf n τ forced))) =
        contractedCutArcs τ (activeOccurrences rows) (denseRequirements n forced) := by
  induction rows with
  | nil => simp [contractionRowsOf, activeOccurrences, contractedCutArcs, variableCutArcs]
  | cons row rows ih =>
    rcases row with ⟨active, clause⟩
    obtain ⟨hclause, hbound⟩ := hrows (active, clause) (by simp)
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hclause
    have ht : ∀ row ∈ rows, row.2.length = 2 ∧ ∀ l ∈ row.2, l.var < n :=
      fun row hr => hrows row (by simp [hr])
    have hreference : active = true → evalClause τ [a, b] = true := by
      intro ha
      exact (evalCNF_iff τ _).mp href [a, b] (by simp [activeOccurrences, ha])
    have hrest : evalCNF τ (activeOccurrences rows) = true := by
      apply (evalCNF_iff τ _).mpr
      intro c hc
      apply (evalCNF_iff τ _).mp href c
      cases ha : active <;> simp [activeOccurrences, ha, hc]
    have hhead := contractionRowOf_arc τ n forced active a b
      (hbound a (by simp)) (hbound b (by simp)) hreference
    have hit := ih ht hrest
    have hs : ((contractionRowOf τ (active, [a, b])) :: contractionRowsOf τ rows).filterMap
        (contractionRowArc (TerminalLabelValue (terminalRowsOf n τ forced))) =
        (contractionRowArc (TerminalLabelValue (terminalRowsOf n τ forced))
          (contractionRowOf τ (active, [a, b]))).toList ++
          (contractionRowsOf τ rows).filterMap
            (contractionRowArc (TerminalLabelValue (terminalRowsOf n τ forced))) := by
      cases h : contractionRowArc (TerminalLabelValue (terminalRowsOf n τ forced))
          (contractionRowOf τ (active, [a, b])) <;> simp [h]
    change ((contractionRowOf τ (active, [a, b])) :: contractionRowsOf τ rows).filterMap
      (contractionRowArc (TerminalLabelValue (terminalRowsOf n τ forced))) = _
    rw [hs]
    rw [hhead]
    cases ha : active <;>
      simpa [ha, contractionRowsOf, activeOccurrences, contractedCutArcs, variableCutArcs,
        List.filterMap_append] using congrArg
          (fun tail => (if active then (clauseCutArcs τ [a, b]).filterMap
            (contractCutArc τ (denseRequirements n forced)) else []) ++ tail) hit

theorem contractionArcsPrefix_semantic (τ : Assignment) (n : ℕ) (forced : ℕ → Bool)
    (rows : List (Bool × Clause))
    (hrows : ∀ row ∈ rows, row.2.length = 2 ∧ ∀ l ∈ row.2, l.var < n)
    (href : evalCNF τ (activeOccurrences rows) = true) :
    contractionArcsPrefix (TerminalLabelValue (terminalRowsOf n τ forced))
      (contractionRowsOf τ rows) rows.length =
        contractedCutArcs τ (activeOccurrences rows) (denseRequirements n forced) := by
  have hlen : (contractionRowsOf τ rows).length = rows.length := by simp [contractionRowsOf]
  rw [← hlen, contractionArcsPrefix_all]
  exact contractionRowsOf_arcs τ n forced rows hrows href

theorem edgePairs_cutNetwork (nodes : ℕ) (arcs : List (ℕ × ℕ)) (hsize : 2 ≤ nodes)
    (hends : ∀ e ∈ arcs, e.1 < nodes ∧ e.2 < nodes) :
    Flow.edgePairs (cutNetwork nodes arcs hsize hends) = contractionArcCodes arcs := by
  unfold Flow.edgePairs contractionArcCodes
  have hm : (List.finRange arcs.length).map
      (fun i => ((cutNetwork nodes arcs hsize hends).tail i |>.val,
        (cutNetwork nodes arcs hsize hends).head i |>.val)) = arcs := by
    rw [← List.ofFn_eq_map]
    simpa [cutNetwork] using List.ofFn_getElem_eq_map arcs id
  rw [hm]

theorem contractionEdgeInput_cutNetwork (n : ℕ) (arcs : List (ℕ × ℕ))
    (hends : ∀ e ∈ arcs, e.1 < n + 2 ∧ e.2 < n + 2) :
    contractionEdgeInput n arcs = Flow.edgeInput
      (cutNetwork (n + 2) arcs (by omega) hends) n := by
  unfold contractionEdgeInput Flow.edgeInput
  rw [edgePairs_cutNetwork]
  rfl

theorem mem_activeOccurrences {α : Type*} {rows : List (Bool × α)} {c : α}
    (hc : c ∈ activeOccurrences rows) : ∃ active, (active, c) ∈ rows := by
  induction rows with
  | nil => simp [activeOccurrences] at hc
  | cons row rows ih =>
    rcases row with ⟨active, clause⟩
    cases ha : active
    · obtain ⟨b, hb⟩ := ih (by simpa [activeOccurrences, ha] using hc)
      exact ⟨b, by simp [hb]⟩
    · rcases List.mem_cons.mp (by simpa [activeOccurrences, ha] using hc) with rfl | hc
      · exact ⟨true, by simp [ha]⟩
      · obtain ⟨b, hb⟩ := ih hc
        exact ⟨b, by simp [hb]⟩

theorem activeOccurrences_twoCNF {n : ℕ} {rows : List (Bool × Clause)}
    (hrows : ∀ row ∈ rows, row.2.length = 2 ∧ ∀ l ∈ row.2, l.var < n) :
    TwoSat.IsTwoCNF n (activeOccurrences rows) := by
  intro c hc
  obtain ⟨active, hm⟩ := mem_activeOccurrences hc
  exact hrows (active, c) hm

/-- The buffer emitted by the two concrete scans is the exact separator input. -/
theorem contractionEdgeInput_semantic (τ : Assignment) (n : ℕ) (forced : ℕ → Bool)
    (rows : List (Bool × Clause))
    (hrows : ∀ row ∈ rows, row.2.length = 2 ∧ ∀ l ∈ row.2, l.var < n)
    (href : evalCNF τ (activeOccurrences rows) = true) :
    let f := activeOccurrences rows
    let hf : TwoSat.IsTwoCNF n f := activeOccurrences_twoCNF hrows
    contractionEdgeInput n (contractionArcsPrefix
      (TerminalLabelValue (terminalRowsOf n τ forced)) (contractionRowsOf τ rows) rows.length) =
        Flow.edgeInput (contractedCutNetwork f hf τ (denseRequirements n forced)) n := by
  dsimp only
  rw [contractionArcsPrefix_semantic τ n forced rows hrows href]
  exact contractionEdgeInput_cutNetwork n _ _

end STACS2027.Runtimes.BoundedCost
