module

public import Runtimes.GeneralCycles.Composition
import Mathlib.Tactic

/-! Assembly of a uniform program from checked validity blocks.
Artifact date: 2026-10-12. -/

@[expose] public section

namespace STACS2027.Runtimes.GeneralCycles

open STACS2027 STACS2027.RAM

theorem representativeBody_spec {outerValidity innerValidity : Stmt} {k B S : ℕ}
    (houterValid : ValiditySpec outerValidity outerIndices (outerValues k) k acceptanceFlag B)
    (hinnerValid : ValiditySpec innerValidity (innerIndices k) (innerValues k) k innerValidFlag B)
    (g : Graph) (outer : List ℕ) (cs : List Cycle) (ho : outer.length = k)
    (hS : 2 * g.length + 1 ≤ S) :
    HTB S (representativeBody outerValidity innerValidity k)
      (fun c => outputInvariant g cs c ∧ c.reg endpointCount = (endpoints g).length ∧
        c.mem = (initial (graphInput g)).mem ∧
          Placed outerIndices (outerValues k) (initial (graphInput g)).mem outer c)
      (fun c => outputInvariant g (outputStep g k cs outer) c ∧
        c.reg endpointCount = (endpoints g).length ∧ c.mem = (initial (graphInput g)).mem ∧
          Placed outerIndices (outerValues k) (initial (graphInput g)).mem outer c)
      (callbackCost k B g + tupleTime (endpoints g).length (callbackCost k B g) k + k + 3) := by
  let R := fun c => outputInvariant g cs c ∧
    c.reg endpointCount = (endpoints g).length ∧ c.mem = (initial (graphInput g)).mem ∧
      Placed outerIndices (outerValues k) (initial (graphInput g)).mem outer c
  have hR : Indep (checkerScratch acceptanceFlag) R := by
    intro c c' ha ⟨hout, hn, hm, hp⟩
    exact ⟨checker_output_indep g cs _ (by decide) _ _ ha hout,
      (ha.reg _ (by decide)).trans hn, ha.mem.trans hm,
      checker_placed_indep (by decide) (by simp [outerValues]) (by decide) _ _ ha hp⟩
  have hstart : HTB S outerValidity R
      (fun c => rejectionInvariant g k outer cs (decide (Valid g k outer)) c ∧
        c.reg endpointCount = (endpoints g).length ∧ c.mem = (initial (graphInput g)).mem)
      (callbackCost k B g) := by
    apply HTB.of_forall
    intro c₀ ⟨hout, hn, hm, hp⟩
    have h := houterValid g outer c₀ S ho hS hout.1 hm hp
    refine h.mono (fun _ hc => hc) ?_ ?_
    · intro c ⟨hv, ha⟩
      obtain ⟨hout', hn', hm', hp'⟩ := hR _ _ ha ⟨hout, hn, hm, hp⟩
      exact ⟨⟨hout', hp', hv⟩, hn', hm'⟩
    · dsimp [callbackCost]
      exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have hscan := rejectionScan_spec hinnerValid g outer cs ho hS
  have hemit := emitAccepted_spec (g := g) (S := S) (cs := cs) ho
  refine (hstart.seq (hscan.seq hemit)).weaken ?_
  omega

 theorem outerScan_spec {outerValidity innerValidity : Stmt} {k B S : ℕ}
    (houterValid : ValiditySpec outerValidity outerIndices (outerValues k) k acceptanceFlag B)
    (hinnerValid : ValiditySpec innerValidity (innerIndices k) (innerValues k) k innerValidFlag B)
    (g : Graph) (hS : 2 * g.length + 1 ≤ S) :
    HTB S (scanTuples outerIndices (outerValues k) 0 k
      (representativeBody outerValidity innerValidity k))
      (fun c => outputInvariant g [] c ∧ c.reg endpointCount = (endpoints g).length ∧
        c.mem = (initial (graphInput g)).mem)
      (fun c => outputInvariant g (outputCycles g k) c ∧
        c.reg endpointCount = (endpoints g).length ∧ c.mem = (initial (graphInput g)).mem)
      (tupleTime (endpoints g).length
        (callbackCost k B g + tupleTime (endpoints g).length (callbackCost k B g) k + k + 3) k) := by
  have hs : (endpoints g).length + 1 ≤ S := by rw [length_endpoints]; exact hS
  have h := scanTuples_spec (outputInvariant g) (outputStep g k)
    (by decide) (by simp [outerValues, outerIndices]) hs
    (fun cs => outputInvariant_outer_indep g k cs)
    (fun full hfull _ cs => representativeBody_spec houterValid hinnerValid g full cs hfull hS)
    k 0 [] [] rfl (by omega) (by simp)
  refine h.mono ?_ ?_ le_rfl
  · rintro c ⟨hp, hn, hm⟩
    exact ⟨hp, hn, hm, placed_nil _ _ _ _⟩
  · rintro c ⟨hp, hn, hm, _⟩
    rw [output_result] at hp
    exact ⟨hp, hn, hm⟩

 theorem initCounts_spec (g : Graph) (S : ℕ) (hS : 1 ≤ S) :
    HTB S initCounts (fun c => c = initial (graphInput g))
      (fun c => outputInvariant g [] c ∧ c.reg endpointCount = (endpoints g).length ∧
        c.mem = (initial (graphInput g)).mem) 3 := by
  refine HTB.run_le (by simp [initCounts, LoopFree]) (by simp [initCounts, size]) ?_
  intro c hc
  subst c
  simp [initCounts, AddrOK, run, initial, graphInput, outputInvariant,
    inputEdgeCount, endpointCount, choiceAddr, length_endpoints]
  constructor <;> omega

 theorem enumerateProgram_computes {outerValidity innerValidity : Stmt} {k B : ℕ}
    (houterValid : ValiditySpec outerValidity outerIndices (outerValues k) k acceptanceFlag B)
    (hinnerValid : ValiditySpec innerValidity (innerIndices k) (innerValues k) k innerValidFlag B)
    (g : Graph) :
    ∃ t, t ≤ tupleTime (2 * g.length)
      (callbackCost k B g + tupleTime (2 * g.length) (callbackCost k B g) k + k + 3) k + 3 ∧
      ComputesIn (enumerateProgram outerValidity innerValidity k) (graphInput g)
        (outputCycles g k).flatten t (2 * g.length + 1) := by
  have hinit := initCounts_spec g (2 * g.length + 1) (by omega)
  have hscan := outerScan_spec houterValid hinnerValid g (S := 2 * g.length + 1) le_rfl
  have h := (hinit.seq hscan).mono (fun _ hc => hc) (fun _ hc => hc.1.2) le_rfl
  have hc := h.computesIn
  simpa [enumerateProgram, length_endpoints, Nat.add_comm] using hc

end STACS2027.Runtimes.GeneralCycles
