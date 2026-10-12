module

public import Runtimes.Greedy.Cycle
import Mathlib.Tactic

/-!
# Lemma 15 (manuscript the paper): the running time of Algorithm 1, in linear space

Lemma 15 of the paper (`lem:greedy_time`): *if the `t` simple `k`-cycles of `G` can be
enumerated in time `Υ_k`, Algorithm 1 runs in `O(kt + Υ_k)` time.* As for Corollary 5, the
enumeration is charged separately: the machine `greedyProg` receives Corollary 5's input
`ZeroCost.zeroCostInput g k` (the graph, `k`, `t` and the vertices of the cycles of `cycles g k`,
cycle after cycle). Reading the graph costs `m + 1 ≤ Υ_k + 1`, so `C · (kt + m + 1)` is the
manuscript's `O(kt + Υ_k)`.

**The machine** (`Runtimes/Greedy/Prog.lean`): Corollary 5's front end (phases 1–4, no `N × N`
table) numbers the at most `kt` distinct cycle edges (`EID[q] = eidOf g k q` for every occurrence
`q`), a load table `LD` over these identifiers starts at zero (fresh memory), and for each cycle
`C_i` in order (`O(k)` steps, `cycBody_spec`): the total load of its `k` edges, the load-sum of
each option `j` as the total minus the loads at the two omitted positions (`O(1)` each), the
first option of minimum load-sum (`pos g k i`, written), and the increments of the loads of the
`k − 2` edges of the chosen path.

**Output**: one position `pos_i < k` per cycle, and the paths `selected C_i pos_i` are exactly
Algorithm 1's assignment `greedy ((cycles g k).map selectedOptions)` of Section 7, which breaks
ties by the first minimizer (`zipWith_pos`). With Section 7's Theorem 14 (`greedy_cost_integer_bound`,
duplicate-free `g`): it is a cycle-path assignment with `2 ALG ≤ 12 c(qs) + 5 (k − 2) t` for every
assignment `qs` (`greedy_guarantee_ram`).

**Time and space**: at most `CG · (kt + m + 1)` steps, accessing only the addresses below
`CG · (labelBound g + kt + m + 1)` (`grSpace_le`: the input, Corollary 5's label dictionary of
`labelBound g` cells — space only —, its arrays of `O(kt)` cells, and the load table).
No hypothesis on `k`: for `k < 3` there are no cycles, and the machine writes nothing.
-/

@[expose] public section

namespace STACS2027.Runtimes.Greedy

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost

variable {S : ℕ}

/-! ### Phases 5 and 6 -/

/-- **Phase 5**: the load table, zero. -/
theorem stepLoad_spec (g : Graph) (k : ℕ) :
    HTB S stepLoad (EdgesPost g k) (fun c => GR g k c ∧ GM g k (ldF g k 0) c.mem ∧ c.out = []) 3 :=
  HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hP => by
    have hag : Agree [rT, xLD, rFREE] c (run stepLoad c) :=
      agree_run (by decide) rfl rfl (by decide) c
    refine ⟨⟨(show Indep [rT, xLD, rFREE] (GA g k) by indep [gA_iff]) c _ hag hP.ga,
      by rw [hag.reg gEID (by decide), hP.reid], ?_⟩, ⟨by rw [hag.mem]; exact hP.meid, ?_⟩,
      by rw [hag.out, hP.rout]⟩
    · simp +decide [stepLoad, run_alloc (show ZeroCost.gNE ≠ rT by decide)
        (show xLD ≠ ZeroCost.gNE by decide), hP.rfree]
    · rw [hag.mem]
      exact (hP.mzero.tab (le_refl _) _).congr_fun fun e _ => by simp [ldF, acc_zero, load]

/-- The state before cycle `i`: the loads of the paths chosen for the first `i` cycles, and their
options written. -/
def LoopInv (g : Graph) (k i : ℕ) (c : Config) : Prop :=
  CS g k i (ldF g k i) ((List.range i).map (pos g k)) c

/-- **Phase 6: Algorithm 1**, `O(k)` steps per cycle. -/
theorem stepGreedy_spec (g : Graph) (k : ℕ) (hS : grSpace g k ≤ S) :
    HTB S stepGreedy (fun c => GR g k c ∧ GM g k (ldF g k 0) c.mem ∧ c.out = [])
      (fun c => c.out = (List.range (cycles g k).length).map (pos g k))
      ((cycles g k).length * (k * 50 + 34) + 4) := by
  have h0 : HTB S (.const xB 0) (fun c => GR g k c ∧ GM g k (ldF g k 0) c.mem ∧ c.out = [])
      (fun c => LoopInv g k 0 c ∧ c.reg gT = (cycles g k).length) 1 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hG, hM, ho⟩ =>
      ⟨⟨(show RegIndep [xB] (GR g k) by indep [gR_iff, gA_iff]).setReg (by decide) _ hG,
        by simp, hM, by simp [ho]⟩, by simp +decide [hG.ga.rt]⟩
  have hl := HTB.forUpC (i := xI) (n := gT) (N := (cycles g k).length) (body := cycBody)
    (LoopInv g k) (k * 50 + 30) (by decide) (by decide) (by decide)
    (fun i => by indep [LoopInv, CS, gR_iff, gA_iff])
    (fun i hi => ((cycBody_spec hS hi).frameReg
      (F := fun c => c.reg xI = i ∧ c.reg gT = (cycles g k).length) (by indep)).mono
      (fun _ h => h) (fun _ h => h) le_rfl)
  exact (h0.seq hl).mono (fun _ h => h) (fun c ⟨⟨_, _, _, ho⟩, _, _⟩ => ho) (le_of_eq (by ring))

/-! ### The whole machine -/

/-- The constant of the time and space bounds. -/
def CG : ℕ := 400

/-- **The memory is linear** in `labelBound g + kt + m + 1`. -/
theorem grSpace_le (g : Graph) (k : ℕ) :
    grSpace g k ≤ CG * (labelBound g + k * (cycles g k).length + g.length + 1) := by
  have hL := layout_eqs g k
  have hN := nV_le (g := g) (k := k)
  have hE := nE_le g k
  have hM := maxV_lt_labelBound (g := g) (k := k)
  unfold grSpace CG; omega

/-- **The machine of Lemma 15**, as a Hoare triple: started on `zeroCostInput g k`, it writes the
options chosen by Algorithm 1 within `CG · (kt + m + 1)` steps, accessing only the addresses
below any `S ≥ grSpace g k`. -/
theorem greedyProg_spec (g : Graph) (k : ℕ) (hS : grSpace g k ≤ S) :
    HTB S greedyProg (fun c => c = initial (zeroCostInput g k))
      (fun c => c.out = (List.range (cycles g k).length).map (pos g k))
      (CG * (k * (cycles g k).length + g.length + 1)) := by
  have hL := layout_eqs g k
  have hO : bOFF g k ≤ S := by unfold grSpace at hS; omega
  have h := (stepInit_spec g k (by omega)).seq ((stepMax_spec g k (by omega)).seq
    ((stepDict_spec g k (by omega)).seq ((stepEdges_spec g k hO).seq
    ((stepLoad_spec g k).seq (stepGreedy_spec g k hS)))))
  refine h.weaken ?_
  have hN := nV_le (g := g) (k := k)
  have htk := t_le_kt (g := g) (k := k)
  set t := (cycles g k).length
  have e1 : t * (k * 36 + 8) = 36 * (k * t) + 8 * t := by ring
  have e2 : t * (k * 50 + 34) = 50 * (k * t) + 34 * t := by ring
  simp only [CG, PairIds.CI, PairIds.CL, PairIds.CR]
  omega

/-- **Lemma 15**: Algorithm 1's assignment (`greedy`), one position `pos_i < k` per cycle, within
`C (kt + m + 1)` steps (`O(kt + Υ_k)`) and `C (labelBound g + kt + m + 1)` addresses. -/
theorem greedy_ram :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ (g : Graph) (k : ℕ),
      ∃ (out : List ℕ) (T : ℕ),
        RAM.ComputesIn prog (ZeroCost.zeroCostInput g k) out T
          (C * (labelBound g + k * (cycles g k).length + g.length + 1)) ∧
        T ≤ C * (k * (cycles g k).length + g.length + 1) ∧
        out.length = (cycles g k).length ∧ (∀ p ∈ out, p < k) ∧
        List.zipWith selected (cycles g k) out = greedy ((cycles g k).map selectedOptions) :=
  ⟨greedyProg, CG, fun g k => by
    obtain ⟨T, hT, hc⟩ := HTB.computesIn (greedyProg_spec g k le_rfl)
    refine ⟨_, T, hc.mono (grSpace_le g k), hT, by simp, ?_, zipWith_pos⟩
    simp only [List.mem_map, List.mem_range]
    rintro p ⟨i, hi, rfl⟩
    exact pos_lt hi⟩

/-- **Lemma 15 with Theorem 14's guarantee** (duplicate-free `g`): the output is a cycle-path
assignment of cost `ALG` with `2 ALG ≤ 12 c(qs) + 5 (k − 2) t` for every assignment `qs`. -/
theorem greedy_guarantee_ram :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ (g : Graph) (k : ℕ), g.Nodup →
      ∃ (out : List ℕ) (T : ℕ),
        RAM.ComputesIn prog (ZeroCost.zeroCostInput g k) out T
          (C * (labelBound g + k * (cycles g k).length + g.length + 1)) ∧
        T ≤ C * (k * (cycles g k).length + g.length + 1) ∧
        out.length = (cycles g k).length ∧ (∀ p ∈ out, p < k) ∧
        ValidChoices ((cycles g k).map selectedOptions) (List.zipWith selected (cycles g k) out) ∧
        ∀ qs, ValidChoices ((cycles g k).map selectedOptions) qs →
          2 * cost (List.zipWith selected (cycles g k) out) ≤
            12 * cost qs + 5 * ((k - 2) * (cycles g k).length) := by
  obtain ⟨prog, C, h⟩ := greedy_ram
  refine ⟨prog, C, fun g k hg => ?_⟩
  obtain ⟨out, T, hc, hT, hl, hp, hz⟩ := h g k
  have hrun := (greedy_is_assignment g k).1
  refine ⟨out, T, hc, hT, hl, hp, ?_, fun qs hq => ?_⟩
  · rw [hz]; exact (greedy_is_assignment g k).2 _ hrun
  · rw [hz]; exact greedy_cost_integer_bound hg hrun hq

end STACS2027.Runtimes.Greedy
