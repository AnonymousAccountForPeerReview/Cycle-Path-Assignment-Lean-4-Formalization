module

public import Runtimes.TwoSatSearch
import Mathlib.Tactic

/-!
# Linear-time 2-SAT on the RAM: the search loop

`stepScc = sccInit; whileC sccCond sccBody` runs the path-based search to its end
(`stepScc_spec`). The loop invariant says that the machine represents `Scc.run N nb k init`
for some `k`, with the test register holding `(N - nxt) + |stk|` (zero iff halted). The time
is amortized with the potential `64 · mu` (`HTB.whileCPot`): a round costs at most `62` steps
plus `10` per vertex popped from `S`, and lowers the measure `mu` by more than one plus that
number (`Scc.mu_step`). As `mu (init) = 5 N + M` (`N = 2n` nodes, `M = 2m` arcs), the loop
takes at most `64 (10 n + 2 m) + 3` steps, and it ends in the representation of
`Scc.final N nb`.
-/

@[expose] public section

namespace STACS2027.Runtimes.TwoSat

open STACS2027.RAM Scc

variable {S : ℕ}

section loop

variable {n m : ℕ} {cl : List ℕ} {c₀ : Config}

/-- The machine's view of the parts of the state that the measure reads. -/
def absOf (n m : ℕ) (c₀ c : Config) : State :=
  ⟨fun v => c.mem (bLAB n m (c₀.reg rFREE) + v), fun v => c.mem (bPTR n m (c₀.reg rFREE) + v),
    List.replicate (c.reg tSP) 0, List.replicate (c.reg tSSP) 0, List.replicate (c.reg tBP) 0,
    c.reg tNXT, 0⟩

/-- The measure of the search, read off the machine. -/
def muC (n m : ℕ) (cl : List ℕ) (c₀ c : Config) : ℕ := mu (2 * n) (nbOf cl) (absOf n m c₀ c)

theorem muC_eq {s : State} {c : Config} (hR : SrchRep n m cl c₀ s c) :
    muC n m cl c₀ c = mu (2 * n) (nbOf cl) s :=
  mu_congr (fun v hv => hR.mem.tlab.get hv) (fun v hv => hR.mem.tptr.get hv)
    (by simp [absOf, hR.sp]) (by simp [absOf, hR.ssp]) (by simp [absOf, hR.bp])
    (by simp [absOf, hR.nxt])

/-- The invariant of the loop. -/
def LoopInv (n m : ℕ) (cl : List ℕ) (c₀ c : Config) : Prop :=
  ∃ k, SrchRep n m cl c₀ (Scc.run (2 * n) (nbOf cl) k init) c ∧
    c.reg rT = (2 * n - (Scc.run (2 * n) (nbOf cl) k init).nxt) +
      (Scc.run (2 * n) (nbOf cl) k init).stk.length

/-- The loop test. -/
theorem sccCond_run {s : State} {c : Config} (hR : SrchRep n m cl c₀ s c) :
    SrchRep n m cl c₀ s (run sccCond c) ∧ (run sccCond c).reg rT = (2 * n - s.nxt) + s.stk.length := by
  refine ⟨(SrchRep.indep n m cl c₀ s).mono (W' := [rT]) (by decide) _ _
    (agree_run (by decide) rfl rfl (by decide) c) hR, ?_⟩
  simp +decide [sccCond, hR.nxt, hR.sp, hR.glob.rn2]

theorem sccInit_spec :
    HTB S sccInit (fun c => Glob n m c₀ c ∧ CsrMem n m cl c₀ c.mem ∧
        ZeroFrom c.mem (bLAB n m (c₀.reg rFREE)))
      (SrchRep n m cl c₀ init) 6 := HTB.of_HT rfl <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨hG, hC, hZ⟩ => ?_
  have hL := layout_eqs n m (c₀.reg rFREE)
  refine ⟨(Glob.regIndep n m c₀).run_of_sub (by decide) (by decide) hG, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp +decide [sccInit, run_addc, init]
  · simp +decide [sccInit, run_addc, init]
  · simp +decide [sccInit, run_addc, init]
  · simp +decide [sccInit, run_addc, init]
  · simp +decide [sccInit, run_addc, init, hG.rn2]
  · have hm : (run sccInit c).mem = c.mem := run_mem_of_stores (by decide) rfl c
    rw [hm]
    exact ⟨hC, hZ.tab le_rfl _, hZ.tab (by omega) _, by simp [init], by simp [init],
      by simp [init], hZ.mono (by omega)⟩

/-- One round of the loop, with the potential. -/
theorem sccRound_spec (hSp : endL n m (c₀.reg rFREE) ≤ S) (hcl : cl.length = 2 * m)
    (hok : CodesOk n cl) (v : ℕ) :
    HTBt S (.seq sccBody sccCond)
      (fun c => LoopInv n m cl c₀ c ∧ c.reg rT ≠ 0 ∧ 64 * muC n m cl c₀ c = v)
      (fun c' t => LoopInv n m cl c₀ c' ∧ 64 * muC n m cl c₀ c' + t + 1 ≤ v) := by
  intro c ⟨⟨k, hR, hT⟩, hne, hμ⟩
  set s := Scc.run (2 * n) (nbOf cl) k init with hs
  have hcl' := closed_nbOf hok
  have hI : Scc.Inv (2 * n) (nbOf cl) s := inv_run hcl' k inv_init
  have hh : ¬ Halted (2 * n) s := fun h => hne (by rw [hT, h.1, List.length_nil]; have := h.2; omega)
  have hb := sccBody_spec (c₀ := c₀) hSp hcl hok s hI hh
  have hc : HTB S sccCond (SrchRep n m cl c₀ (step (2 * n) (nbOf cl) s))
      (fun c => LoopInv n m cl c₀ c ∧ muC n m cl c₀ c = mu (2 * n) (nbOf cl) (step (2 * n) (nbOf cl) s)) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hR' => by
      obtain ⟨h1, h2⟩ := sccCond_run hR'
      refine ⟨⟨k + 1, ?_, ?_⟩, muC_eq h1⟩ <;> rw [run_succ]
      · exact h1
      · exact h2
  obtain ⟨c', t, he, ⟨hL, hμ'⟩, ht⟩ := (hb.seq hc) c hR
  refine ⟨c', t, he, hL, ?_⟩
  have hm := mu_step hcl' hI hh
  rw [muC_eq hR] at hμ
  rw [hμ']
  omega

/-- **The search loop**: from the initial representation, the loop ends in the representation
of the final state of the search within `64 (10 n + 2 m) + 3` steps. -/
theorem sccLoop_spec (hSp : endL n m (c₀.reg rFREE) ≤ S) (hcl : cl.length = 2 * m)
    (hok : CodesOk n cl) :
    HTB S (whileC sccCond sccBody) (SrchRep n m cl c₀ init)
      (SrchRep n m cl c₀ (Scc.final (2 * n) (nbOf cl))) (2 + (64 * (10 * n + 2 * m) + 1)) := by
  have hcl' := closed_nbOf hok
  have hmu : mu (2 * n) (nbOf cl) init = 10 * n + 2 * m := by
    rw [mu_init]
    have hA := length_arcsOfCodes m cl hcl
    have := ps_total (A := arcsOfCodes cl) (N := 2 * n) (fun e he => (mem_arcsOfCodes hok e he).1)
    unfold ps at this
    simp only [nbOf]
    omega
  have hinit : HTB S sccCond (SrchRep n m cl c₀ init)
      (fun c => LoopInv n m cl c₀ c ∧ 64 * muC n m cl c₀ c ≤ 64 * (10 * n + 2 * m)) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hR => by
      obtain ⟨h1, h2⟩ := sccCond_run hR
      refine ⟨⟨0, h1, h2⟩, ?_⟩
      rw [muC_eq h1, hmu]
  refine (HTB.whileCPot (fun c => 64 * muC n m cl c₀ c) hinit (sccRound_spec hSp hcl hok)).post
    fun c ⟨⟨k, hR, hT⟩, h0⟩ => ?_
  have hH : Halted (2 * n) (Scc.run (2 * n) (nbOf cl) k init) := by
    rw [h0] at hT
    exact ⟨List.length_eq_zero_iff.mp (by omega), by omega⟩
  rwa [run_eq_final hcl' hH] at hR

/-- **Step 5: the search.** -/
theorem stepScc_spec (hSp : endL n m (c₀.reg rFREE) ≤ S) (hcl : cl.length = 2 * m)
    (hok : CodesOk n cl) :
    HTB S stepScc (fun c => Glob n m c₀ c ∧ CsrMem n m cl c₀ c.mem ∧
        ZeroFrom c.mem (bLAB n m (c₀.reg rFREE)))
      (SrchRep n m cl c₀ (Scc.final (2 * n) (nbOf cl))) (6 + (2 + (64 * (10 * n + 2 * m) + 1))) :=
  sccInit_spec.seq (sccLoop_spec hSp hcl hok)

end loop

end STACS2027.Runtimes.TwoSat
