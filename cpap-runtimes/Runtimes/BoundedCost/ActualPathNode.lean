module

public import Runtimes.BoundedCost.PathBasicFrame
public import Runtimes.BoundedCost.PathActionRepresentation
import Mathlib.Tactic

/-! A genuine flow-backed RAM search node represents the canonical semantic
annotated-path transition. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM Complexity.SAT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem searchRowsOf_literal_bounds {nodes : ℕ} (τ δ : Assignment) (rows : List (Bool × Clause))
    (hn : 0 < nodes)
    (hrows : ∀ row ∈ rows, row.2.length = 2 ∧ ∀ l ∈ row.2, l.var < nodes) :
    (summarizePrefix (searchRowsOf τ δ rows) rows.length).firstLiteral < 2 * nodes ∧
      (summarizePrefix (searchRowsOf τ δ rows) rows.length).secondLiteral < 2 * nodes := by
  apply summarizePrefix_literal_bounds (by omega) (count := rows.length)
  · intro i hi
    have hi' : i < rows.length := by simpa only [searchRowsOf_length] using hi
    rw [searchRowsOf_getD τ δ rows i hi', ← List.getElem_eq_getD (h := hi') default]
    obtain ⟨hl, hb⟩ := hrows rows[i] (List.getElem_mem hi')
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl
    have he : rows[i] = (rows[i].1, [a, b]) := Prod.ext rfl hab
    rw [he]
    exact ⟨TwoSat.code_lt (hb a (by rw [hab]; simp)),
      TwoSat.code_lt (hb b (by rw [hab]; simp))⟩
  · simp

theorem actualPathNode_spec {F : Stmt} {T : ℕ → ℕ}
    (hF : Flow.MinCostFlowSolver F T) (hAL : Flow.AlmostLinear T) :
    ∃ C : ℕ, ∀ {layout : CompilerLayout} {nodes S : ℕ} {original : CNF}
      {τ : Assignment} {digits oldOutput : List ℕ} {oldMemory : ℕ → ℕ}
      {state : SearchPathState} {i : ℕ},
      3 ≤ nodes → original.length ≤ nodes → layout.span = (C + 1) * (nodes + 1) ^ 2 →
      LeastCutGeometry S layout.span layout.formula layout.active layout.candidate layout.reference
        layout.forced layout.labels layout.edgeInput nodes original.length →
      (∀ j, j < digits.length → SearchNodeMemoryFrame layout.span layout.active layout.candidate
        layout.forced layout.labels layout.edgeInput nodes original.length (layout.innerDigits + j)) →
      state.live = true → i < digits.length →
      HTB S (searchNode F)
        (fun c => (ActualPathRep F layout nodes original τ digits oldOutput state c ∧
          SameOn (SearchNodeMemoryFrame layout.span layout.active layout.candidate layout.forced
            layout.labels layout.edgeInput nodes original.length) oldMemory c.mem) ∧
          c.reg (callerRegister nodeChoice) = digits.getD i 0 ∧
          c.reg (callerRegister pathIndex) = i ∧ c.reg (callerRegister pathDepth) = digits.length)
        (fun c => (ActualPathRep F layout nodes original τ digits oldOutput
            (annotatedPathStep (citedFlowLeastCutOperation hF hAL τ) τ state (digits.getD i 0)) c ∧
          SameOn (SearchNodeMemoryFrame layout.span layout.active layout.candidate layout.forced
            layout.labels layout.edgeInput nodes original.length) oldMemory c.mem) ∧
          c.reg (callerRegister pathIndex) = i ∧ c.reg (callerRegister pathDepth) = digits.length)
        ((800 + (wregs (Flow.hornSeparator F)).length) * (layout.span + 1)) := by
  obtain ⟨C, hnode⟩ := searchNode_spec hF hAL
  refine ⟨C, ?_⟩
  intro layout nodes S original τ digits oldOutput oldMemory state i hn hm hspan hgeo hdigits hlive hi
  cases state with
  | failed => simp [SearchPathState.live] at hlive
  | answered σ => simp [SearchPathState.live] at hlive
  | running formula required budget =>
    intro c hpre
    obtain ⟨⟨⟨hb, hs⟩, hsourceFrame⟩, hchoice, hindex, hdepth⟩ := hpre
    obtain ⟨rows, forced, hlen, horiginal, hrows, hformula, hmask, hforced, hrequired,
      href, hbudget, hl, hsuccess⟩ := hs
    subst formula
    have hfn : TwoSat.IsTwoCNF nodes original := by
      rw [← horiginal]
      intro clause hc
      obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hc
      exact hrows row hr
    have hfa : Clauses2 (activeOccurrences rows) := by
      intro clause hc
      exact (hrows (true, clause) (mem_activeOccurrences_true hc)).1
    have hgeo' : LeastCutGeometry S layout.span layout.formula layout.active layout.candidate layout.reference
        layout.forced layout.labels layout.edgeInput nodes rows.length := by simpa only [hlen] using hgeo
    have hcodeRows : Arr c.mem layout.formula (TwoSat.codes (rows.map Prod.snd)) := by
      rw [horiginal]; exact hb.2.1
    have hterminal := terminalRowsMem_of_tables hforced hb.2.2.1
    have hrowMemory := contractionRowsMem_of_tables hrows hcodeRows hmask hb.2.2.1
    have hcontrol : NodeControlGlobals budget (digits.getD i 0) 0 c :=
      ⟨hbudget, hchoice, hsuccess, hl⟩
    obtain ⟨c', time, he, hp, ht⟩ := hnode rows τ forced c hn (by omega) hspan hrows href hgeo'
      (by simpa only [hlen] using hb.1) hterminal hrowMemory hb.2.2.1 hcontrol hb.2.2.2.1 c rfl
    have hbasic : PathBasic F layout nodes original τ digits oldOutput c' :=
      pathBasic_of_searchNodeResult hlen (by rw [TwoSat.length_codes hfn]) hgeo hdigits hb hp
    have hindex' : c'.reg (callerRegister pathIndex) = i :=
      (hp.2.2.1 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hindex
    have hdepth' : c'.reg (callerRegister pathDepth) = digits.length :=
      (hp.2.2.1 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hdepth
    have hfinalFrame : SameOn (SearchNodeMemoryFrame layout.span layout.active layout.candidate
        layout.forced layout.labels layout.edgeInput nodes original.length) oldMemory c'.mem := by
      intro a ha
      exact (hp.2.2.2.1 a (by simpa only [hlen] using ha)).trans (hsourceFrame a ha)
    refine ⟨c', time, he, ⟨⟨⟨hbasic, ?_⟩, hfinalFrame⟩, hindex', hdepth'⟩, ht⟩
    rcases hp.2.2.2.2 with hbad | hgood
    · have hnone : citedFlowLeastCutOperation hF hAL τ (activeOccurrences rows) required = none := by
        apply ((citedFlowLeastCutOperation_correct hF hAL τ) _ _ hfa href).1.mpr
        rintro ⟨σ, hσ⟩
        exact hbad.1 ⟨σ, (hrequired σ).mpr hσ⟩
      simpa only [annotatedPathStep, hnone] using ⟨hbad.2.1, hbad.2.2.2⟩
    · obtain ⟨δ, memory, hleast, hframe, htruth, hupdated⟩ := hgood
      have hleast' := hleast.requirements_congr hrequired
      have hcut := citedFlowLeastCutOperation_eq_some hF hAL hfa href hleast'
      have hmask' := hmask.leastCutFrame hgeo' hframe
      have hforced' := hforced.leastCutFrame hgeo' hframe
      have hsep : layout.active + original.length ≤ layout.forced := by
        obtain ⟨_, hfa, hac, hcr, hrf, hfl, hlo, hos⟩ := hgeo
        omega
      have hstate := pathStateRep_of_nodeUpdated hlen horiginal hrows href hmask' hforced'
        hrequired hsep (searchRowsOf_literal_bounds τ δ rows (by omega) hrows) htruth hupdated
      rw [nodeActionState_annotatedPathStep _ τ δ rows required budget (digits.getD i 0)
        (fun row hr => (hrows row hr).1) hcut] at hstate
      exact hstate

end STACS2027.Runtimes.BoundedCost
