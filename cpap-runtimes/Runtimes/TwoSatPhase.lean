module

public import Runtimes.TwoSatLoop
import Mathlib.Tactic

/-!
# Linear-time 2-SAT on the RAM: the phase and its specification

`twoSat` runs the allocation, the complement table, the arcs, the CSR lists, the path-based
search (`TwoSatProg.lean`, `TwoSatCsr.lean`, `TwoSatSearch.lean`, `TwoSatLoop.lean`) and the
answer pass `stepOut`: for each variable `x < n`, `tOK := 0` if `LAB[2x] = LAB[2x + 1]`, and
`AS[x] := 1` if `LAB[2x] < LAB[2x + 1]`, else `0`.

**Specification** (`twoSat_spec`). From `TwoSatIn n m cl` (`n` in `tN = 200`, `m` in
`tM = 201`, the `2m` codes `cl` at `tCL = 202`, free memory from `rFREE = F`), with
`|cl| = 2m` and all codes `< 2n`, the phase halts within `CT · (n + m + 1)` steps
(`CT = 700`), accessing only the addresses below any `S ≥ endL n m F` (`endL_le`:
`≤ F + 19 (n + m + 1)`), in a configuration satisfying `TwoSatOut n m cl c₀`:
* `tOK = 203` holds `1` if `okB n cl` (no conflict), else `0`;
* the array at `tAS = 204` holds the bits `asgBits n cl` of the assignment `asg n cl`;
* the array lies in fresh memory (`c₀.rFREE ≤ tAS`, `tAS + n ≤ rFREE = endL n m F`), the memory
  below the
  initial `rFREE` is unchanged, all memory from `rFREE` on is zero, `tN`, `tM`, `tCL` keep
  their values, the output is unchanged, and every register outside `{rT, rFREE}` and the block
  `200–249` keeps its value (`twoSat_wregs`).

**Correctness** (`twoSatOut_correct`): for `cl = codes f` of a 2-CNF `f` over `n` variables,
`tOK = 1` iff `f` is satisfiable, and then the bits at `tAS` form a satisfying assignment.
-/

@[expose] public section

namespace STACS2027.Runtimes.TwoSat

open STACS2027.RAM Scc Complexity.SAT

variable {S : ℕ}

/-! ### The answer pass -/

/-- The loads of an answer step: `sX := LAB[2i]`, `sY := LAB[2i + 1]`. -/
def outRead : Stmt := .seq (.add sP sI sI) (.seq (addc sQ sP 1) (.seq (ld sX tLAB sP) (ld sY tLAB sQ)))

/-- The flag update of an answer step: `tOK := 0` on a conflict. -/
def outOk : Stmt := ifEq sX sY (.const tOK 0) .skip

/-- The bit of an answer step: `sW := [LAB[2i] < LAB[2i + 1]]`. -/
def outBit : Stmt := ifLt sX sY (.const sW 1) (.const sW 0)

/-- One variable `i` of the answer pass. -/
def outBody : Stmt := .seq outRead (.seq outOk (.seq outBit (st tAS sI sW)))

/-- Step 6: the answer. -/
def stepOut : Stmt := .seq (.const tOK 1) (forUp sI tN outBody)

/-- **The 2-SAT phase.** -/
def twoSat : Stmt :=
  .seq allocT (.seq stepNeg (.seq stepArc (.seq stepCsr (.seq stepScc stepOut))))

/-- The bits of the algorithm's assignment. -/
def asgBits (n : ℕ) (cl : List ℕ) : List ℕ := (List.range n).map fun x => if asg n cl x then 1 else 0

section out

variable {n m : ℕ} {cl : List ℕ} {c₀ : Config}

/-- The memory during the answer pass, after `j` variables. -/
structure OutMem (n m : ℕ) (cl : List ℕ) (c₀ : Config) (j : ℕ) (mm : ℕ → ℕ) : Prop where
  same : SameOn (· < c₀.reg rFREE) c₀.mem mm
  tlab : Tab mm (bLAB n m (c₀.reg rFREE)) (2 * n) (lab n cl)
  tas : Tab mm (bAS n m (c₀.reg rFREE)) j fun x => if asg n cl x then 1 else 0
  zero : ZeroFrom mm (endL n m (c₀.reg rFREE))

/-- The value of `tOK` after `j` variables. -/
def okv (n : ℕ) (cl : List ℕ) (j : ℕ) : ℕ :=
  if ∀ x < j, lab n cl (2 * x) ≠ lab n cl (2 * x + 1) then 1 else 0

theorem okv_succ (j : ℕ) : okv n cl (j + 1) =
    if lab n cl (2 * j) = lab n cl (2 * j + 1) then 0 else okv n cl j := by
  unfold okv
  by_cases he : lab n cl (2 * j) = lab n cl (2 * j + 1)
  · simp only [he, ↓reduceIte, ite_eq_right_iff, one_ne_zero, imp_false]
    exact fun h => h j (by omega) he
  · simp only [he, ↓reduceIte]
    congr 1
    apply propext
    constructor
    · intro h x hx; exact h x (by omega)
    · intro h x hx
      rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
      · exact h x hx
      · exact he

/-- The invariant of the answer pass after `j` variables. -/
def OutInv (n m : ℕ) (cl : List ℕ) (c₀ : Config) (j : ℕ) (c : Config) : Prop :=
  Glob n m c₀ c ∧ c.reg tOK = okv n cl j ∧ OutMem n m cl c₀ j c.mem

theorem outBody_spec (hSp : endL n m (c₀.reg rFREE) ≤ S) (j : ℕ) (hj : j < n) :
    HTB S outBody (fun c => OutInv n m cl c₀ j c ∧ c.reg sI = j ∧ c.reg tN = n)
      (fun c => OutInv n m cl c₀ (j + 1) c ∧ c.reg sI = j ∧ c.reg tN = n) 20 := by
  have hP1 : HTB S outRead (fun c => OutInv n m cl c₀ j c ∧ c.reg sI = j ∧ c.reg tN = n)
      (fun c => (OutInv n m cl c₀ j c ∧ c.reg sI = j ∧ c.reg tN = n) ∧ c.reg sX = lab n cl (2 * j) ∧
        c.reg sY = lab n cl (2 * j + 1)) 7 :=
    HTB.run_le (by decide) (by decide) fun c ⟨⟨hG, hok, hM⟩, hi, hn⟩ => by
      have h1 := hM.tlab.get (i := 2 * j) (by omega)
      have h2 := hM.tlab.get (i := 2 * j + 1) (by omega)
      have e1 : j + j = 2 * j := by ring
      refine ⟨by have := fits hSp; addr_ok [outRead, hG.rlab, hi, e1],
        Indep.run (s := outRead) (P := fun c => OutInv n m cl c₀ j c ∧ c.reg sI = j ∧
        c.reg tN = n) (by indep [OutInv, glob_iff]) (by decide) rfl rfl ⟨⟨hG, hok, hM⟩, hi, hn⟩,
        ?_, ?_⟩
      · simp +decide [outRead, run_addc, hG.rlab, hi, e1, h1]
      · simp +decide [outRead, run_addc, hG.rlab, hi, e1, h2]
  have hP2 : HTB S outOk
      (fun c => (OutInv n m cl c₀ j c ∧ c.reg sI = j ∧ c.reg tN = n) ∧ c.reg sX = lab n cl (2 * j) ∧
        c.reg sY = lab n cl (2 * j + 1))
      (fun c => (Glob n m c₀ c ∧ c.reg tOK = okv n cl (j + 1) ∧ OutMem n m cl c₀ j c.mem ∧
        c.reg sI = j ∧ c.reg tN = n) ∧ c.reg sX = lab n cl (2 * j) ∧ c.reg sY = lab n cl (2 * j + 1)) 7 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨⟨hG, hok, hM⟩, hi, hn⟩, hX, hY⟩ => by
      rw [okv_succ]
      simp only [outOk, run_ifEq (show sX ≠ rT by decide) (show sY ≠ rT by decide), hX, hY]
      by_cases he : lab n cl (2 * j) = lab n cl (2 * j + 1)
      · simp only [he, ↓reduceIte, run_const]
        refine ⟨⟨(Glob.regIndep n m c₀).setReg (by decide) _ ((Glob.regIndep n m c₀).setReg
          (by decide) _ hG), by simp +decide, hM, by simp +decide [hi], by simp +decide [hn]⟩,
          by simp +decide [hX, he], by simp +decide [hY]⟩
      · simp only [he, ↓reduceIte, run_skip]
        refine ⟨⟨(Glob.regIndep n m c₀).setReg (by decide) _ hG, by simp +decide [hok], hM,
          by simp +decide [hi], by simp +decide [hn]⟩, by simp +decide [hX], by simp +decide [hY]⟩
  have hP3 : HTB S outBit
      (fun c => (Glob n m c₀ c ∧ c.reg tOK = okv n cl (j + 1) ∧ OutMem n m cl c₀ j c.mem ∧
        c.reg sI = j ∧ c.reg tN = n) ∧ c.reg sX = lab n cl (2 * j) ∧ c.reg sY = lab n cl (2 * j + 1))
      (fun c => (Glob n m c₀ c ∧ c.reg tOK = okv n cl (j + 1) ∧ OutMem n m cl c₀ j c.mem ∧
        c.reg sI = j ∧ c.reg tN = n) ∧ c.reg sW = if asg n cl j then 1 else 0) 4 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨hG, hok, hM, hi, hn⟩, hX, hY⟩ => by
      have hasg : asg n cl j = decide (lab n cl (2 * j) < lab n cl (2 * j + 1)) := rfl
      simp only [outBit, run_ifLt, hX, hY, hasg]
      by_cases hl : lab n cl (2 * j) < lab n cl (2 * j + 1)
      · simp only [hl, ↓reduceIte, run_const, decide_true]
        exact ⟨⟨(Glob.regIndep n m c₀).setReg (by decide) _ ((Glob.regIndep n m c₀).setReg
          (by decide) _ hG), by simp +decide [hok], hM, by simp +decide [hi], by simp +decide [hn]⟩,
          by simp +decide⟩
      · simp only [hl, ↓reduceIte, run_const, decide_false]
        exact ⟨⟨(Glob.regIndep n m c₀).setReg (by decide) _ ((Glob.regIndep n m c₀).setReg
          (by decide) _ hG), by simp +decide [hok], hM, by simp +decide [hi], by simp +decide [hn]⟩,
          by simp +decide⟩
  have hP4 : HTB S (st tAS sI sW)
      (fun c => (Glob n m c₀ c ∧ c.reg tOK = okv n cl (j + 1) ∧ OutMem n m cl c₀ j c.mem ∧
        c.reg sI = j ∧ c.reg tN = n) ∧ c.reg sW = if asg n cl j then 1 else 0)
      (fun c => OutInv n m cl c₀ (j + 1) c ∧ c.reg sI = j ∧ c.reg tN = n) 2 :=
    HTB.run_le (by decide) (by decide) fun c ⟨⟨hG, hok, hM, hi, hn⟩, hW⟩ => by
      refine ⟨by have := fits hSp; addr_ok [hG.ras, hi], ?_⟩
      have hL := layout_eqs n m (c₀.reg rFREE)
      rw [run_st (by decide)]
      refine ⟨⟨(Glob.regIndep n m c₀).setReg (by decide) _ ((Glob.regIndep n m c₀).setMem _ _ hG),
        by simp +decide [hok], ?_⟩, by simp +decide [hi], by simp +decide [hn]⟩
      simp only [setReg_mem, setMem_mem_upd, hG.ras, hi, hW]
      exact ⟨hM.same.upd_of_ge (by omega) _, hM.tlab.upd_of_disjoint (by omega),
        (hM.tas.upd_of_disjoint (by omega)).snoc (by simp), hM.zero.upd (by omega)⟩
  exact (hP1.seq (hP2.seq (hP3.seq hP4))).weaken (by omega)

/-- **Step 6: the answer.** -/
theorem stepOut_spec (hSp : endL n m (c₀.reg rFREE) ≤ S) :
    HTB S stepOut (fun c => SrchRep n m cl c₀ (Scc.final (2 * n) (nbOf cl)) c)
      (fun c => OutInv n m cl c₀ n c ∧ c.reg sI = n ∧ c.reg tN = n) (1 + (n * 24 + 3)) := by
  have h0 : HTB S (.const tOK 1) (fun c => SrchRep n m cl c₀ (Scc.final (2 * n) (nbOf cl)) c)
      (fun c => OutInv n m cl c₀ 0 c ∧ c.reg tN = n) 1 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hR => by
      have hL := layout_eqs n m (c₀.reg rFREE)
      have hG := hR.glob
      simp only [run_const]
      refine ⟨⟨(Glob.regIndep n m c₀).setReg (by decide) _ hG, by simp +decide [okv], ?_⟩,
        by simp +decide [hG.rn]⟩
      simp only [setReg_mem]
      exact ⟨hR.mem.csr.same, hR.mem.tlab, by simp, hR.mem.zero.mono (by omega)⟩
  exact h0.seq (HTB.forUpC (i := sI) (n := tN) (N := n) (body := outBody) (OutInv n m cl c₀) 20
    (by decide) (by decide) (by decide) (fun j => by indep [OutInv, glob_iff])
    (fun j hj => outBody_spec hSp j hj))

end out

/-! ### The phase -/

/-- The state after the 2-SAT phase started in `c₀`. -/
structure TwoSatOut (n m : ℕ) (cl : List ℕ) (c₀ c : Config) : Prop where
  ok : c.reg tOK = if okB n cl then 1 else 0
  asg : Arr c.mem (c.reg tAS) (asgBits n cl)
  rn : c.reg tN = n
  rm : c.reg tM = m
  rcl : c.reg tCL = c₀.reg tCL
  fresh : c₀.reg rFREE ≤ c.reg tAS ∧ c.reg tAS + n ≤ c.reg rFREE
  rfree : c.reg rFREE = endL n m (c₀.reg rFREE)
  free : ZeroFrom c.mem (c.reg rFREE)
  same : SameOn (· < c₀.reg rFREE) c₀.mem c.mem
  out : c.out = c₀.out
  frame : ∀ r, r ≠ rT → r ≠ rFREE → (r < 200 ∨ 250 ≤ r) → c.reg r = c₀.reg r

/-- The constant of the running time of the 2-SAT phase. -/
def CT : ℕ := 700

/-- The registers `rT`, `rFREE` and the block `200–249`. -/
def InBlock (r : ℕ) : Prop := r = rT ∨ r = rFREE ∨ (200 ≤ r ∧ r < 250)

instance : DecidablePred InBlock := fun r => by unfold InBlock; infer_instance

theorem inBlock_seq {a b : Stmt} (ha : ∀ r ∈ wregs a, InBlock r) (hb : ∀ r ∈ wregs b, InBlock r) :
    ∀ r ∈ wregs (.seq a b), InBlock r := by
  intro r hr; rw [wregs_seq, List.mem_append] at hr; exact hr.elim (ha r) (hb r)

/-- The registers written by `twoSat`: the macro temporary `rT`, `rFREE`, and the block
`200–249`. -/
theorem twoSat_wregs : ∀ r ∈ wregs twoSat, r = rT ∨ r = rFREE ∨ (200 ≤ r ∧ r < 250) :=
  inBlock_seq (a := allocT) (by decide) (inBlock_seq (a := stepNeg) (by decide)
    (inBlock_seq (a := stepArc) (by decide) (inBlock_seq (a := stepCsr) (by decide)
      (inBlock_seq (a := stepScc) (b := stepOut) (by decide) (by decide)))))

/-- `twoSat` does not write output. -/
theorem twoSat_writes : writes twoSat = false := by decide

/-- The phase without the frame facts. -/
theorem twoSat_core (n m : ℕ) (cl : List ℕ) (c₀ : Config) (hB : TwoSatIn n m cl c₀)
    (hcl : cl.length = 2 * m) (hok : CodesOk n cl) (hSp : endL n m (c₀.reg rFREE) ≤ S) :
    HTB S twoSat (fun c => c = c₀) (fun c => OutInv n m cl c₀ n c)
      (46 + ((n * 12 + 3) + ((m * 25 + 3) +
        ((2 * m * 12 + 3 + (1 + (2 * n * 11 + 3) + (2 * m * 20 + 3))) +
        ((6 + (2 + (64 * (10 * n + 2 * m) + 1))) + (1 + (n * 24 + 3))))))) := by
  have h2 := (stepNeg_spec n m c₀ hSp).post (Q' := fun c => ArcInv n m cl c₀ 0 c ∧ c.reg tM = m)
    fun c ⟨⟨hG, hM⟩, _, _⟩ => by
      have hL := layout_eqs n m (c₀.reg rFREE)
      exact ⟨⟨hG, hM.same, hM.tneg, by simp, by simp, hM.zero.mono (by omega)⟩, hG.rm⟩
  have h3 := (stepArc_spec n m cl c₀ hB hcl hok hSp).post (Q' := fun c => ArcInv n m cl c₀ m c ∧
    c.reg tM = m) fun c ⟨h, _, hm⟩ => ⟨h, hm⟩
  have h6 := (stepOut_spec (n := n) (m := m) (cl := cl) (c₀ := c₀) hSp).post
    (Q' := fun c => OutInv n m cl c₀ n c) fun c h => h.1
  exact (allocT_spec n m cl c₀ hB).seq (h2.seq (h3.seq ((stepCsr_spec hcl hok hSp).seq
    ((stepScc_spec hSp hcl hok).seq h6))))

/-- **The 2-SAT phase** (ANONYMIZED–ANONYMIZED–ANONYMIZED, with the path-based strongly connected
components): from `TwoSatIn n m cl` with `|cl| = 2m` codes below `2n`, the program `twoSat`
halts within `CT · (n + m + 1)` steps, accessing only the addresses below any
`S ≥ endL n m F` (`F` the initial `rFREE`; `endL_le`: `≤ F + 19 (n + m + 1)`), in a
configuration satisfying `TwoSatOut n m cl c₀`: the flag `okB n cl` in `tOK` and the
assignment `asgBits n cl` in fresh memory at `tAS`, `rFREE = endL n m F`, with the memory below
the initial `rFREE`, the output, and every register outside `rT`, `rFREE` and the block
`200–249` unchanged. -/
theorem twoSat_spec (n m : ℕ) (cl : List ℕ) (c₀ : Config) (hcl : cl.length = 2 * m)
    (hok : CodesOk n cl) (hSp : endL n m (c₀.reg rFREE) ≤ S) :
    HTB S twoSat (fun c => TwoSatIn n m cl c ∧ c = c₀) (TwoSatOut n m cl c₀) (CT * (n + m + 1)) := by
  intro c ⟨hB, hc⟩
  subst hc
  obtain ⟨c', t, he, ⟨⟨hG, hokv, hM⟩, hfr⟩, ht⟩ :=
    (twoSat_core n m cl c hB hcl hok hSp).withFrame c c ⟨rfl, rfl⟩
  have hL := layout_eqs n m (c.reg rFREE)
  refine ⟨c', t, he, ⟨?_, ?_, hG.rn, hG.rm, hG.rcl, ?_, hG.rfree, ?_, hM.same,
    hfr.out twoSat_writes, ?_⟩, ?_⟩
  · rw [hokv]; simp [okv, okB]
  · rw [hG.ras]; exact hM.tas.toArr
  · rw [hG.ras, hG.rfree]; omega
  · rw [hG.rfree]; exact hM.zero
  · intro r h1 h2 h3
    refine hfr.reg r fun hr => ?_
    rcases twoSat_wregs r hr with h | h | h
    · exact h1 h
    · exact h2 h
    · omega
  · simp only [CT]
    omega

/-! ### Correctness -/

/-- The value of a 2-CNF over `n` variables depends only on the variables below `n`. -/
theorem evalCNF_congr {n : ℕ} {f : CNF} (hf : IsTwoCNF n f) {σ σ' : Assignment}
    (h : ∀ x < n, σ x = σ' x) : evalCNF σ f = evalCNF σ' f := by
  induction f with
  | nil => rfl
  | cons c f ih =>
    simp only [evalCNF_cons]
    obtain ⟨a, b, rfl⟩ := clause_eq hf List.mem_cons_self
    have ha := (hf _ List.mem_cons_self).2 a (by simp)
    have hb := (hf _ List.mem_cons_self).2 b (by simp)
    rw [ih (fun c' hc' => hf c' (List.mem_cons_of_mem _ hc'))]
    simp only [evalClause_cons, evalClause_nil, evalLiteral, h a.var ha, h b.var hb]

/-- **Correctness of the phase's answer**: for the codes of a 2-CNF `f` over `n` variables,
the flag is `1` iff `f` is satisfiable, and then the bits stored at `tAS` (read as
`x ↦ (mem[tAS + x] = 1)`) satisfy `f`. -/
theorem twoSatOut_correct {n m : ℕ} {f : CNF} (hf : IsTwoCNF n f) {c₀ c : Config}
    (h : TwoSatOut n m (codes f) c₀ c) :
    (c.reg tOK = 1 ↔ Satisfiable f) ∧
      (c.reg tOK = 1 → evalCNF (fun x => decide (c.mem (c.reg tAS + x) = 1)) f = true) := by
  have hc := twoSat_correct hf
  have hok : c.reg tOK = 1 ↔ okB n (codes f) = true := by
    rw [h.ok]; cases okB n (codes f) <;> simp
  refine ⟨hok.trans hc.1, fun h1 => ?_⟩
  rw [evalCNF_congr hf (σ' := asg n (codes f)) fun x hx => ?_]
  · exact hc.2 (hok.mp h1)
  · have := h.asg.get (i := x) (by simp [asgBits, hx])
    simp only [asgBits, List.getElem_map, List.getElem_range] at this
    rw [this]
    cases asg n (codes f) x <;> simp

end STACS2027.Runtimes.TwoSat
