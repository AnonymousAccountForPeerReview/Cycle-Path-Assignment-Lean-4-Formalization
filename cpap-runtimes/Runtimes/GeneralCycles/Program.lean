module

public import Runtimes.GeneralCycles.Counter
public import Runtimes.GeneralCycles.Bounds
import Mathlib.Tactic

/-! Composition of the read-only tuple enumerator. Artifact date: 2026-10-12. -/

@[expose] public section

namespace STACS2027.Runtimes.GeneralCycles

open STACS2027 STACS2027.RAM

abbrev inputEdgeCount : ℕ := 11

def checkerScratch (d : ℕ) : List ℕ := rT :: (List.range' 20 20 ++ [d])

/-- A checked validity block leaves every bank, both input counts, memory and
output unchanged. Its cost is bounded independently of the labels. -/
def ValiditySpec (block : Stmt) (indices values k d B : ℕ) : Prop :=
  ∀ (g : Graph) (is : List ℕ) (c₀ : Config) (S : ℕ),
    is.length = k → 2 * g.length + 1 ≤ S →
    c₀.reg inputEdgeCount = g.length → c₀.mem = (initial (graphInput g)).mem →
    Placed indices values (initial (graphInput g)).mem is c₀ →
    HTB S block (fun c => c = c₀)
      (fun c => c.reg d = bit (decide (Valid g k is)) ∧
        Agree (checkerScratch d) c₀ c) (B * (2 * g.length + 1))

def outputInvariant (g : Graph) (cs : List Cycle) (c : Config) : Prop :=
  c.reg inputEdgeCount = g.length ∧ c.out = cs.flatten

def rejectionInvariant (g : Graph) (k : ℕ) (outer : List ℕ) (cs : List Cycle)
    (b : Bool) (c : Config) : Prop :=
  outputInvariant g cs c ∧
    Placed outerIndices (outerValues k) (initial (graphInput g)).mem outer c ∧
      c.reg acceptanceFlag = bit b

def counterBody (innerValidity : Stmt) (k : ℕ) : Stmt :=
  .seq innerValidity (clearCounter k)

def representativeBody (outerValidity innerValidity : Stmt) (k : ℕ) : Stmt :=
  .seq outerValidity (.seq
    (scanTuples (innerIndices k) (innerValues k) 0 k (counterBody innerValidity k))
    (.ifz acceptanceFlag .skip (emitValues (outerValues k) k)))

def initCounts : Stmt :=
  .seq (.const choiceAddr 0) (.seq (.load inputEdgeCount choiceAddr)
    (.add endpointCount inputEdgeCount inputEdgeCount))

def enumerateProgram (outerValidity innerValidity : Stmt) (k : ℕ) : Stmt :=
  .seq initCounts (scanTuples outerIndices (outerValues k) 0 k
    (representativeBody outerValidity innerValidity k))

theorem placed_indep_of {indices values : ℕ} {memory : ℕ → ℕ} {is : List ℕ}
    {W : List ℕ}
    (h : ∀ j, j < is.length → indices + j ∉ W ∧ values + j ∉ W) :
    Indep W (Placed indices values memory is) := by
  intro c c' ha hp j hj
  exact ⟨(ha.reg _ (h j hj).1).trans (hp j hj).1,
    (ha.reg _ (h j hj).2).trans (hp j hj).2⟩

theorem outputInvariant_indep (g : Graph) (cs : List Cycle) {W : List ℕ}
    (h : inputEdgeCount ∉ W) : Indep W (outputInvariant g cs) := by
  intro c c' ha ⟨hm, ho⟩
  exact ⟨(ha.reg _ h).trans hm, ha.out.trans ho⟩

theorem outputInvariant_outer_indep (g : Graph) (k : ℕ) (cs : List Cycle) :
    Indep (controlRegs outerIndices (outerValues k) k) (outputInvariant g cs) := by
  apply outputInvariant_indep
  simp [controlRegs, outerIndices, outerValues, inputEdgeCount, rT, choiceAddr,
    List.mem_range']
  omega

theorem rejectionInvariant_inner_indep (g : Graph) (k : ℕ) (outer : List ℕ)
    (cs : List Cycle) (b : Bool) (hl : outer.length = k) :
    Indep (controlRegs (innerIndices k) (innerValues k) k)
      (rejectionInvariant g k outer cs b) := by
  intro c c' ha ⟨hout, hplaced, hb⟩
  refine ⟨?_, ?_, ?_⟩
  · apply outputInvariant_indep _ _ ?_ _ _ ha hout
    simp [controlRegs, innerIndices, innerValues, inputEdgeCount, rT, choiceAddr,
      List.mem_range']
    repeat' constructor
    all_goals omega
  · apply placed_indep_of ?_ _ _ ha hplaced
    intro j hj
    simp [controlRegs, outerIndices, outerValues, innerIndices, innerValues,
      rT, choiceAddr, List.mem_range']
    repeat' constructor
    all_goals omega
  · have hf : acceptanceFlag ∉ controlRegs (innerIndices k) (innerValues k) k := by
      simp [controlRegs, innerIndices, innerValues, rT, choiceAddr, acceptanceFlag,
        List.mem_range']
      constructor <;> intro x hx <;> omega
    exact (ha.reg _ hf).trans hb

theorem checker_placed_indep {indices values d : ℕ} {g : Graph} {is : List ℕ}
    (hi : 100 ≤ indices) (hv : 100 ≤ values) (hd : d ≤ 41) :
    Indep (checkerScratch d) (Placed indices values (initial (graphInput g)).mem is) := by
  apply placed_indep_of
  intro j hj
  simp [checkerScratch, rT, List.mem_range']
  repeat' constructor
  all_goals omega

theorem checker_output_indep (g : Graph) (cs : List Cycle) (d : ℕ) (hd : 40 ≤ d) :
    Indep (checkerScratch d) (outputInvariant g cs) := by
  apply outputInvariant_indep
  simp [checkerScratch, inputEdgeCount, rT, List.mem_range']
  repeat' constructor
  all_goals omega


theorem clear_placed_indep {indices values : ℕ} {g : Graph} {is : List ℕ}
    (hi : 100 ≤ indices) (hv : 100 ≤ values) :
    Indep [rT, acceptanceFlag] (Placed indices values (initial (graphInput g)).mem is) := by
  apply placed_indep_of
  intro j hj
  simp [rT, acceptanceFlag]
  omega

 theorem counterBody_spec {innerValidity : Stmt} {k B S : ℕ}
    (hvalid : ValiditySpec innerValidity (innerIndices k) (innerValues k) k innerValidFlag B)
    (g : Graph) (outer inner : List ℕ) (cs : List Cycle) (b : Bool)
    (ho : outer.length = k) (hi : inner.length = k) (hS : 2 * g.length + 1 ≤ S) :
    HTB S (counterBody innerValidity k)
      (fun c => rejectionInvariant g k outer cs b c ∧
        c.reg endpointCount = (endpoints g).length ∧ c.mem = (initial (graphInput g)).mem ∧
          Placed (innerIndices k) (innerValues k) (initial (graphInput g)).mem inner c)
      (fun c => rejectionInvariant g k outer cs (rejectStep g k outer b inner) c ∧
        c.reg endpointCount = (endpoints g).length ∧ c.mem = (initial (graphInput g)).mem ∧
          Placed (innerIndices k) (innerValues k) (initial (graphInput g)).mem inner c)
      ((B + size (clearCounter k)) * (2 * g.length + 1)) := by
  let R := fun c => outputInvariant g cs c ∧
    Placed outerIndices (outerValues k) (initial (graphInput g)).mem outer c ∧
    c.reg endpointCount = (endpoints g).length ∧ c.mem = (initial (graphInput g)).mem ∧
      Placed (innerIndices k) (innerValues k) (initial (graphInput g)).mem inner c
  have hRc : Indep (checkerScratch innerValidFlag) R := by
    intro c c' ha ⟨hout, hp, hn, hm, ht⟩
    refine ⟨checker_output_indep g cs _ (by decide) _ _ ha hout,
      checker_placed_indep (by decide) (by simp [outerValues]) (by decide) _ _ ha hp,
      (ha.reg _ (by decide)).trans hn, ha.mem.trans hm,
      checker_placed_indep (by simp [innerIndices]) (by simp [innerValues])
        (by decide) _ _ ha ht⟩
  have hRclear : Indep [rT, acceptanceFlag] R := by
    intro c c' ha ⟨hout, hp, hn, hm, ht⟩
    refine ⟨outputInvariant_indep _ _ (by decide) _ _ ha hout,
      clear_placed_indep (by decide) (by simp [outerValues]) _ _ ha hp,
      (ha.reg _ (by decide)).trans hn, ha.mem.trans hm,
      clear_placed_indep (by simp [innerIndices]) (by simp [innerValues])
        _ _ ha ht⟩
  have hstart : HTB S innerValidity
      (fun c => R c ∧ c.reg acceptanceFlag = bit b)
      (fun c => R c ∧ c.reg acceptanceFlag = bit b ∧
        c.reg innerValidFlag = bit (decide (Valid g k inner))) (B * (2 * g.length + 1)) := by
    apply HTB.of_forall
    intro c₀ ⟨hR, hb⟩
    have h := hvalid g inner c₀ S hi hS hR.1.1 hR.2.2.2.1 hR.2.2.2.2
    exact h.mono (fun _ hc => hc) (fun c ⟨hv, ha⟩ =>
      ⟨hRc _ _ ha hR, (ha.reg _ (by decide)).trans hb, hv⟩) le_rfl
  have hclear : HTB S (clearCounter k)
      (fun c => R c ∧ c.reg acceptanceFlag = bit b ∧
        c.reg innerValidFlag = bit (decide (Valid g k inner)))
      (fun c => R c ∧ c.reg acceptanceFlag = bit (rejectStep g k outer b inner))
      (size (clearCounter k)) := by
    refine HTB.run_le (clearCounter_loopFree k) le_rfl ?_
    intro c ⟨hR, hb, hv⟩
    exact ⟨AddrOK.of_memFree (clearCounter_memFree k),
      hRclear _ _ (clearCounter_agree k c) hR,
      clearCounter_value g k outer inner b c ho hi hR.2.1 hR.2.2.2.2 hv hb⟩
  refine (hstart.seq hclear).mono ?_ ?_ ?_
  · rintro c ⟨⟨hout, hp, hb⟩, hn, hm, ht⟩
    exact ⟨⟨hout, hp, hn, hm, ht⟩, hb⟩
  · rintro c ⟨⟨hout, hp, hn, hm, ht⟩, hb⟩
    exact ⟨⟨hout, hp, hb⟩, hn, hm, ht⟩
  · nlinarith

end STACS2027.Runtimes.GeneralCycles
