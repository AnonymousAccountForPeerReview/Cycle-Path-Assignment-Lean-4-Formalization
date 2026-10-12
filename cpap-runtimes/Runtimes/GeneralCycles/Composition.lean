module

public import Runtimes.GeneralCycles.Program
import Mathlib.Tactic

/-! End-to-end composition of the bounded enumeration loops.
Artifact date: 2026-10-12. -/

@[expose] public section

namespace STACS2027.Runtimes.GeneralCycles

open STACS2027 STACS2027.RAM

def callbackCost (k B : ℕ) (g : Graph) : ℕ :=
  (B + size (clearCounter k)) * (2 * g.length + 1)

theorem rejectionScan_spec {innerValidity : Stmt} {k B S : ℕ}
    (hvalid : ValiditySpec innerValidity (innerIndices k) (innerValues k) k innerValidFlag B)
    (g : Graph) (outer : List ℕ) (cs : List Cycle) (ho : outer.length = k)
    (hS : 2 * g.length + 1 ≤ S) :
    HTB S (scanTuples (innerIndices k) (innerValues k) 0 k (counterBody innerValidity k))
      (fun c => rejectionInvariant g k outer cs (decide (Valid g k outer)) c ∧
        c.reg endpointCount = (endpoints g).length ∧ c.mem = (initial (graphInput g)).mem)
      (fun c => rejectionInvariant g k outer cs (decide (Accepted g k outer)) c ∧
        c.reg endpointCount = (endpoints g).length ∧ c.mem = (initial (graphInput g)).mem)
      (tupleTime (endpoints g).length (callbackCost k B g) k) := by
  have hs : (endpoints g).length + 1 ≤ S := by rw [length_endpoints]; exact hS
  have h := scanTuples_spec (rejectionInvariant g k outer cs) (rejectStep g k outer)
    (by simp [innerIndices]; omega) (by simp [innerIndices, innerValues]; omega) hs
    (fun b => rejectionInvariant_inner_indep g k outer cs b ho)
    (fun full hfull _ b => counterBody_spec hvalid g outer full cs b ho hfull hS)
    k 0 [] (decide (Valid g k outer)) rfl (by omega) (by simp)
  refine h.mono ?_ ?_ le_rfl
  · rintro c ⟨hp, hn, hm⟩
    exact ⟨hp, hn, hm, placed_nil _ _ _ _⟩
  · rintro c ⟨hp, hn, hm, _⟩
    rw [rejection_result] at hp
    exact ⟨hp, hn, hm⟩

 theorem emitAccepted_spec {g : Graph} {k S : ℕ} {outer : List ℕ} {cs : List Cycle}
    (ho : outer.length = k) :
    HTB S (.ifz acceptanceFlag .skip (emitValues (outerValues k) k))
      (fun c => rejectionInvariant g k outer cs (decide (Accepted g k outer)) c ∧
        c.reg endpointCount = (endpoints g).length ∧ c.mem = (initial (graphInput g)).mem)
      (fun c => outputInvariant g (outputStep g k cs outer) c ∧
        c.reg endpointCount = (endpoints g).length ∧ c.mem = (initial (graphInput g)).mem ∧
          Placed outerIndices (outerValues k) (initial (graphInput g)).mem outer c)
      (k + 3) := by
  refine HTB.run_le (by simp [LoopFree]) (by simp [size]; omega) ?_
  intro c ⟨⟨hout, hp, hb⟩, hn, hm⟩
  refine ⟨by simp, ?_⟩
  by_cases ha : Accepted g k outer
  · have hflag : c.reg acceptanceFlag = 1 := by simpa [bit, ha] using hb
    have hrun : run (.ifz acceptanceFlag .skip (emitValues (outerValues k) k)) c =
        run (emitValues (outerValues k) k) c := by simp [run, hflag]
    rw [hrun]
    have hfr := run_frame (emitValues_loopFree (outerValues k) k) c
    have hregs : ∀ r, (run (emitValues (outerValues k) k) c).reg r = c.reg r :=
      fun r => hfr.reg r (by simp)
    refine ⟨⟨(hregs _).trans hout.1, ?_⟩, (hregs _).trans hn,
      (hfr.mem (by simp)).trans hm, ?_⟩
    · rw [emitValues_out, Placed.emission_labels ho hp, hout.2]
      simp [outputStep, ha, List.flatten_append]
    · intro j hj
      exact ⟨(hregs _).trans (hp j hj).1, (hregs _).trans (hp j hj).2⟩
  · have hflag : c.reg acceptanceFlag = 0 := by simpa [bit, ha] using hb
    simp only [run, hflag, ↓reduceIte]
    simpa [outputStep, ha] using And.intro hout (And.intro hn (And.intro hm hp))

end STACS2027.Runtimes.GeneralCycles
