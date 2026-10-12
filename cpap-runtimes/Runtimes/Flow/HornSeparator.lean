module

public import Runtimes.Flow.HornRAM
public import Runtimes.Flow.Separator
import Mathlib.Tactic

/-! # The uniform maximum source-side cut program from the sole cited flow contract -/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027 STACS2027.RAM

/-- The two linear encoders and the verified Horn-query extractor are one RAM program. -/
def hornSeparator (F : Stmt) : Stmt := pipe3 paddedInputLength paddedEncode F hornRAM

/-- A returned vertex bit is the corresponding finite region-membership bit. -/
@[simp] theorem maximalRegionBits_get {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (flow : IndexedFlow arcs) (v : Fin nodes) :
    (maximalRegionBits net flow).getD v.val 0 = if maximalCutRegion net flow v then 1 else 0 := by
  simp [maximalRegionBits]

/-- Binary oracle output reifies exactly the original occurrence-flow projection. -/
theorem originalFlowBits_projection {arcs padding : ℕ} (bits : List ℕ)
    (hlen : bits.length = arcs + padding) (hbits : ∀ b ∈ bits, b ≤ 1) :
    originalFlowBits (maxFlowProjection bits : IndexedFlow arcs) = bits.take arcs := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi hi'
    have hia : i < arcs := by simpa using hi
    have hib : i < bits.length := by omega
    have hb := hbits bits[i] (List.getElem_mem hib)
    simp only [originalFlowBits, List.getElem_map, List.getElem_finRange, maxFlowProjection,
      List.getElem_take]
    by_cases hzero : bits[i] = 0
    · simp [List.getElem?_eq_getElem hib, hzero]
    · have hone : bits[i] = 1 := by omega
      simp [List.getElem?_eq_getElem hib, hone]

/-- The extractor's input is the exact output of the permitted oracle following the edge input. -/
theorem hornInput_projection {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs)
    (padding : ℕ) (bits : List ℕ) (hlen : bits.length = arcs + padding)
    (hbits : ∀ b ∈ bits, b ≤ 1) :
    hornInput net padding (maxFlowProjection bits) (bits.drop arcs) =
      edgeInput net padding ++ (1 :: bits) := by
  simp only [hornInput, originalFlowBits_projection bits hlen hbits, List.cons_append, List.take_append_drop]

private theorem hornResourceBounds (nodes arcs padding K C : ℕ)
    (hn : nodes ≤ padding + 2) (hm : arcs ≤ padding) :
    let q := (padding + 1) ^ 2
    1010 * (nodes + 1) * (nodes + arcs + 3) ≤ 15150 * q ∧
    3 * arcs + padding + 6 + nodes * (21 * (nodes + arcs + 3)) ≤ 321 * q ∧
    2 + 4 * ((2 * arcs + 5) + (3 * (arcs + padding) + 5) + (1 + arcs + padding) +
      (2 * arcs + 5) + (36 * K * q) + (321 * q)) ≤ (1358 + 144 * K) * q ∧
    5 + 12 * (2 * arcs + 5) +
      4 * (40 * (arcs + padding + 1) + C * q + 15150 * q) + 20 ≤
      (61005 + 4 * C) * q := by
  dsimp
  have hq : padding + 1 ≤ (padding + 1) ^ 2 := by nlinarith
  have hprod : (nodes + 1) * (nodes + arcs + 3) ≤ 15 * (padding + 1) ^ 2 := by
    calc
      _ ≤ (3 * (padding + 1)) * (5 * (padding + 1)) :=
        Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hprod' : nodes * (21 * (nodes + arcs + 3)) ≤ 315 * (padding + 1) ^ 2 := by
    calc
      _ ≤ (nodes + 1) * (21 * (nodes + arcs + 3)) := Nat.mul_le_mul_right _ (by omega)
      _ = 21 * ((nodes + 1) * (nodes + arcs + 3)) := by ring
      _ ≤ _ := by nlinarith
  refine ⟨by nlinarith, by nlinarith, ?_, ?_⟩
  · have hx : 2 * arcs + 5 ≤ 5 * (padding + 1) := by omega
    have hy : 3 * (arcs + padding) + 5 ≤ 6 * (padding + 1) := by omega
    have hz : 1 + arcs + padding ≤ 2 * (padding + 1) := by omega
    nlinarith
  · have hx : 2 * arcs + 5 ≤ 5 * (padding + 1) := by omega
    have hp : 40 * (arcs + padding + 1) ≤ 80 * (padding + 1) := by omega
    nlinarith

/-- Actual RAM execution returns the greatest minimum-cut source side with a uniform
quadratic time and memory bound. The only external algorithmic hypotheses are the cited
minimum-cost-flow solver and its almost-linear bound. -/
theorem hornSeparator_computes {F : Stmt} {T : ℕ → ℕ}
    (hF : MinCostFlowSolver F T) (hT : AlmostLinear T) :
    ∃ C : ℕ, ∀ {nodes arcs : ℕ} (net : IndexedNetwork nodes arcs) (padding : ℕ),
      nodes ≤ padding + 2 → arcs ≤ padding → 2 ≤ arcs + padding →
      (∀ i, net.head i ≠ net.source) → (∀ i, net.tail i ≠ net.sink) →
      ∃ (flow : IndexedFlow arcs) (d steps : ℕ),
        ComputesIn (hornSeparator F) (edgeInput net padding) (maximalRegionBits net flow)
          steps (C * (padding + 1) ^ 2) ∧ steps ≤ C * (padding + 1) ^ 2 ∧
        IsIndexedFlow net d flow ∧ IsMinimumCut net (maximalCutRegion net flow) ∧
        cutSize net (maximalCutRegion net flow) = d ∧
        ∀ other : Fin nodes → Bool, IsMinimumCut net other →
          ∀ v, other v = true → maximalCutRegion net flow v = true := by
  obtain ⟨Cflow, hflow⟩ := paddedMaxFlow_oracle_cut hF hT
  obtain ⟨K, hK⟩ := hT.polynomialBound
  have hSpaceC : 1358 + 144 * K ≤ 62000 + 4 * Cflow + 144 * K := by omega
  have hTimeC : 61005 + 4 * Cflow ≤ 62000 + 4 * Cflow + 144 * K := by omega
  refine ⟨62000 + 4 * Cflow + 144 * K, ?_⟩
  intro nodes arcs net padding hn hm hsize hhead htail
  obtain ⟨bits, tf, d, hf, htf, hlen, hbits, hfeasible, hcut, hvalue, hgreatest⟩ :=
    hflow net padding hm (by omega) hsize hhead htail
  obtain ⟨tp, hp, htp⟩ := paddedEncode_computes net padding
  have hdrop : (bits.drop arcs).length = padding := by simp [hlen]
  obtain ⟨tr, hr, htr⟩ := hornRAM_computes net padding (maxFlowProjection bits)
    (bits.drop arcs) hdrop
  rw [hornInput_projection net padding bits hlen hbits] at hr
  obtain ⟨steps, hprogram, ht⟩ := pipe3_spec
    (paddedInputLength_spec net padding (S := 2) (by omega)) hp hf hr
  have hspaceF : T (netInput (numberedNodeNumber net) nodes padding
      (paddedMaxFlowNetwork net padding)).length ≤ 36 * K * (padding + 1) ^ 2 := by
    have hb := hK (netInput (numberedNodeNumber net) nodes padding
      (paddedMaxFlowNetwork net padding)).length
    simp only [length_netInput, paddedMaxFlowNetwork_length] at hb
    simp only [length_netInput, paddedMaxFlowNetwork_length]
    calc
      _ ≤ K * (3 * (arcs + padding) + 5 + 1) ^ 2 := hb
      _ ≤ K * (6 * (padding + 1)) ^ 2 := by
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_left
        omega
      _ = 36 * K * (padding + 1) ^ 2 := by ring
  obtain ⟨hRtime, hRspace, hspace, htime⟩ := hornResourceBounds nodes arcs padding K Cflow hn hm
  simp only [length_netInput, paddedMaxFlowNetwork_length] at hspaceF
  have hs : 2 + 4 * ((edgeInput net padding).length +
      (netInput (numberedNodeNumber net) nodes padding (paddedMaxFlowNetwork net padding)).length +
      (1 :: bits).length + (2 * arcs + 5) +
      T (netInput (numberedNodeNumber net) nodes padding (paddedMaxFlowNetwork net padding)).length +
      (3 * arcs + padding + 6 + nodes * (21 * (nodes + arcs + 3)))) ≤
      (62000 + 4 * Cflow + 144 * K) * (padding + 1) ^ 2 := by
    simp only [edgeInput_length, length_netInput, paddedMaxFlowNetwork_length,
      List.length_cons, hlen]
    calc
      _ ≤ 2 + 4 * ((2 * arcs + 5) + (3 * (arcs + padding) + 5) + (1 + arcs + padding) +
          (2 * arcs + 5) + (36 * K * (padding + 1) ^ 2) + (321 * (padding + 1) ^ 2)) := by
        nlinarith only [hspaceF, hRspace]
      _ ≤ (1358 + 144 * K) * (padding + 1) ^ 2 := hspace
      _ ≤ _ := Nat.mul_le_mul_right _ hSpaceC
  have hsteps : steps ≤ (62000 + 4 * Cflow + 144 * K) * (padding + 1) ^ 2 := by
    simp only [edgeInput_length] at ht
    have htr' := htr.trans hRtime
    calc
      steps ≤ 5 + 12 * (2 * arcs + 5) + 4 * (tp + tf + tr) + 20 := ht
      _ ≤ 5 + 12 * (2 * arcs + 5) +
          4 * (40 * (arcs + padding + 1) + Cflow * (padding + 1) ^ 2 +
            15150 * (padding + 1) ^ 2) + 20 := by
        nlinarith only [htp, htf, htr']
      _ ≤ (61005 + 4 * Cflow) * (padding + 1) ^ 2 := htime
      _ ≤ _ := Nat.mul_le_mul_right _ hTimeC
  exact ⟨maxFlowProjection bits, d, steps, hprogram.mono hs, hsteps,
    hfeasible, hcut, hvalue, hgreatest⟩

end STACS2027.Runtimes.Flow
