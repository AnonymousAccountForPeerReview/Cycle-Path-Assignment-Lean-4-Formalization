module

public import Runtimes.BoundedCost.DenseState
public import Runtimes.BoundedCost.CallerRegisters
import Mathlib.Tactic

/-! The bounded RAM traversal of one ternary annotated-search path. A stopped
path performs no further node calls. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM

abbrev pathDigitsBase : ℕ := 344
abbrev pathDepth : ℕ := 345
abbrev pathIndex : ℕ := 346

def pathControlStep (node : Stmt) : Stmt :=
  .ifz nodeLive .skip (.seq (ld nodeChoice pathDigitsBase pathIndex) node)

def pathControl (node : Stmt) : Stmt := forUp pathIndex pathDepth (pathControlStep node)

def livePathStep {α : Type*} (live : α → Bool) (step : α → ℕ → α)
    (state : α) (choice : ℕ) : α := if live state then step state choice else state

def pathPrefix {α : Type*} (live : α → Bool) (step : α → ℕ → α)
    (digits : List ℕ) (count : ℕ) (state : α) : α :=
  (List.range count).foldl
    (fun state i => livePathStep live step state (digits.getD i 0)) state

theorem pathPrefix_succ {α : Type*} (live : α → Bool) (step : α → ℕ → α)
    (digits : List ℕ) (count : ℕ) (state : α) :
    pathPrefix live step digits (count + 1) state =
      livePathStep live step (pathPrefix live step digits count state) (digits.getD count 0) := by
  simp [pathPrefix, List.range_succ, List.foldl_append]

theorem pathControl_spec {α : Type*} {S base B : ℕ} {node : Stmt}
    (digits : List ℕ)
    (live : α → Bool) (step : α → ℕ → α) (Rep : α → Config → Prop)
    (hindep : ∀ state, Indep [pathIndex, rT, nodeChoice] (Rep state))
    (hrep : ∀ state c, Rep state c →
      c.reg nodeLive = (if live state then 1 else 0) ∧
      c.reg pathDigitsBase = base ∧ c.reg pathDepth = digits.length ∧ Arr c.mem base digits)
    (hS : base + digits.length ≤ S)
    (hnode : ∀ i, i < digits.length → ∀ state,
      HTB S node
        (fun c => Rep state c ∧ c.reg nodeChoice = digits.getD i 0 ∧
          c.reg pathIndex = i ∧ c.reg pathDepth = digits.length)
        (fun c => Rep (step state (digits.getD i 0)) c ∧
          c.reg pathIndex = i ∧ c.reg pathDepth = digits.length) B)
    (state : α) :
    HTB S (pathControl node)
      (fun c => Rep state c ∧ c.reg pathDepth = digits.length)
      (fun c => Rep (pathPrefix live step digits digits.length state) c ∧
        c.reg pathIndex = digits.length ∧ c.reg pathDepth = digits.length)
      (digits.length * (B + 7) + 3) := by
  let Inv := fun i c => Rep (pathPrefix live step digits i state) c
  have hl := HTB.forUpC (S := S) (i := pathIndex) (n := pathDepth)
    (N := digits.length) (body := pathControlStep node) Inv (B + 3)
    (by decide) (by decide) (by decide)
    (fun i => (hindep _).mono (by simp)) (fun i hi => ?_)
  · simpa [pathControl, Inv, pathPrefix] using hl
  · intro c ⟨hr, hindex, hdepth⟩
    let current := pathPrefix live step digits i state
    have hc : Rep current c := hr
    obtain ⟨hlive, hbase, _, htable⟩ := hrep current c hc
    cases hv : live current with
    | false =>
      have hzero : c.reg nodeLive = 0 := by simpa [hv] using hlive
      refine ⟨c, 2, ExecB.ifzTrue hzero (ExecB.skip c), ?_, by omega⟩
      refine ⟨?_, hindex, hdepth⟩
      simpa [Inv, pathPrefix_succ, livePathStep, current, hv] using hc
    | true =>
      have hnonzero : c.reg nodeLive ≠ 0 := by simp_all
      have haddr : c.reg pathDigitsBase + c.reg pathIndex < S := by
        rw [hbase, hindex]; omega
      let loaded := c.setReg nodeChoice (digits.getD i 0)
      have hvalue : c.mem (c.reg pathDigitsBase + c.reg pathIndex) = digits.getD i 0 := by
        rw [hbase, hindex]
        exact htable.getD hi
      have heq : run (ld nodeChoice pathDigitsBase pathIndex) c = loaded := by
        simp [loaded, hvalue]
      have hload : ExecB S (ld nodeChoice pathDigitsBase pathIndex) c 2 loaded := by
        have he := execB_run (S := S) (ld nodeChoice pathDigitsBase pathIndex)
          (by simp) c ((addrOK_ld _ _ _).mpr haddr)
        simpa [heq, ld, RAM.cost, loaded, hvalue] using he
      have hr' : Rep current loaded :=
        (hindep current).setReg (by simp) _ hc
      have hb := hnode i hi current
      obtain ⟨c', time, he, hpost, htime⟩ := hb loaded ⟨hr', by simp [loaded],
        by simpa [loaded] using hindex, by simpa [loaded] using hdepth⟩
      refine ⟨c', 2 + time + 1, ExecB.ifzFalse hnonzero (ExecB.seq hload he), ?_, by omega⟩
      refine ⟨?_, hpost.2⟩
      simpa [Inv, pathPrefix_succ, livePathStep, current, hv] using hpost.1

def renamedPathControlStep (φ : ℕ → ℕ) (node : Stmt) : Stmt :=
  .ifz (φ nodeLive) .skip (.seq (ld (φ nodeChoice) (φ pathDigitsBase) (φ pathIndex)) node)

def renamedPathControl (φ : ℕ → ℕ) (node : Stmt) : Stmt :=
  forUp (φ pathIndex) (φ pathDepth) (renamedPathControlStep φ node)

theorem renamedPathControl_spec {α : Type*} {S base B : ℕ} {node : Stmt}
    (φ : ℕ → ℕ) (hφ : Function.Injective φ)
    (hindex : φ pathIndex ≠ rT) (hdepth : φ pathDepth ≠ rT)
    (digits : List ℕ) (live : α → Bool) (step : α → ℕ → α) (Rep : α → Config → Prop)
    (hindep : ∀ state, Indep [φ pathIndex, rT, φ nodeChoice] (Rep state))
    (hrep : ∀ state c, Rep state c →
      c.reg (φ nodeLive) = (if live state then 1 else 0) ∧
      c.reg (φ pathDigitsBase) = base ∧ c.reg (φ pathDepth) = digits.length ∧ Arr c.mem base digits)
    (hS : base + digits.length ≤ S)
    (hnode : ∀ i, i < digits.length → ∀ state,
      HTB S node
        (fun c => Rep state c ∧ c.reg (φ nodeChoice) = digits.getD i 0 ∧
          c.reg (φ pathIndex) = i ∧ c.reg (φ pathDepth) = digits.length)
        (fun c => Rep (step state (digits.getD i 0)) c ∧
          c.reg (φ pathIndex) = i ∧ c.reg (φ pathDepth) = digits.length) B)
    (state : α) :
    HTB S (renamedPathControl φ node)
      (fun c => Rep state c ∧ c.reg (φ pathDepth) = digits.length)
      (fun c => Rep (pathPrefix live step digits digits.length state) c ∧
        c.reg (φ pathIndex) = digits.length ∧ c.reg (φ pathDepth) = digits.length)
      (digits.length * (B + 7) + 3) := by
  let Inv := fun i c => Rep (pathPrefix live step digits i state) c
  have hl := HTB.forUpC (S := S) (i := φ pathIndex) (n := φ pathDepth)
    (N := digits.length) (body := renamedPathControlStep φ node) Inv (B + 3)
    hindex hdepth (fun he => (by decide : pathDepth ≠ pathIndex) (hφ he))
    (fun i => (hindep _).mono (by simp)) (fun i hi => ?_)
  · simpa [renamedPathControl, Inv, pathPrefix] using hl
  · intro c ⟨hr, hindex, hdepth⟩
    let current := pathPrefix live step digits i state
    have hc : Rep current c := hr
    obtain ⟨hlive, hbase, _, htable⟩ := hrep current c hc
    cases hv : live current with
    | false =>
      have hzero : c.reg (φ nodeLive) = 0 := by simpa [hv] using hlive
      refine ⟨c, 2, ExecB.ifzTrue hzero (ExecB.skip c), ?_, by omega⟩
      refine ⟨?_, hindex, hdepth⟩
      simpa [Inv, pathPrefix_succ, livePathStep, current, hv] using hc
    | true =>
      have hnonzero : c.reg (φ nodeLive) ≠ 0 := by simp_all
      have haddr : c.reg (φ pathDigitsBase) + c.reg (φ pathIndex) < S := by
        rw [hbase, hindex]; omega
      let loaded := c.setReg (φ nodeChoice) (digits.getD i 0)
      have hvalue : c.mem (c.reg (φ pathDigitsBase) + c.reg (φ pathIndex)) = digits.getD i 0 := by
        rw [hbase, hindex]
        exact htable.getD hi
      have heq : run (ld (φ nodeChoice) (φ pathDigitsBase) (φ pathIndex)) c = loaded := by
        simp [loaded, hvalue]
      have hload : ExecB S (ld (φ nodeChoice) (φ pathDigitsBase) (φ pathIndex)) c 2 loaded := by
        have he := execB_run (S := S) (ld (φ nodeChoice) (φ pathDigitsBase) (φ pathIndex))
          (by simp) c ((addrOK_ld _ _ _).mpr haddr)
        simpa [heq, ld, RAM.cost, loaded, hvalue] using he
      have hr' : Rep current loaded := (hindep current).setReg (by simp) _ hc
      have hb := hnode i hi current
      obtain ⟨c', time, he, hpost, htime⟩ := hb loaded ⟨hr', by simp [loaded],
        by simpa [loaded, hφ.eq_iff] using hindex,
        by simpa [loaded, hφ.eq_iff] using hdepth⟩
      refine ⟨c', 2 + time + 1, ExecB.ifzFalse hnonzero (ExecB.seq hload he), ?_, by omega⟩
      refine ⟨?_, hpost.2⟩
      simpa [Inv, pathPrefix_succ, livePathStep, current, hv] using hpost.1

end STACS2027.Runtimes.BoundedCost
