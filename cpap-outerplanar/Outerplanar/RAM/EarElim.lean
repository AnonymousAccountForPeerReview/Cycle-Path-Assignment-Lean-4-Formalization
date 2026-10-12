module

public import Outerplanar.RAM.EarPeelR
import Mathlib.Tactic

/-!
# The ear-elimination machine: one round of the elimination loop

* `outChk_Z`: the adjacency test of the orientation stored by the peeling: `rZ = 1` iff `w` is
  an out-neighbour of `u` or `u` one of `w` (`OutAdj`, in the frozen memory `m₀`);
* `elimBlk_run`: once `u`, `w` are in `rU`, `rW`, the block `elimBlk` kills `v`, logs
  `(v, u, w)` and either lowers the degrees of `u`, `w` or adds the virtual edge: the machine
  then holds `Ear.elim s v u w`, provided the test answers the query `s.mat u w` (`hq`);
* `round_spec`: one round of the loop (`mbody`, then the test `mcond`) from a running state `s`
  ends in `Ear.step s` within `roundCost s` steps: `21 |adj v| + 127` for an elimination of the
  popped vertex `v`, `19` otherwise. The query is answered by the orientation: with the ghost
  invariants `Ear.Inv` and `Ear.Static` of `s`, `Ear.query_static` says that `s.mat u w` is the
  adjacency in `L`, which the orientation records (`OutOK`).

The triples are `HTB S` triples, for any bound `S ≥ bEND F N |L|` of the layout.
-/

@[expose] public section

namespace STACS2027.RAM.EarR

open STACS2027 STACS2027.Ear

variable {N : ℕ} {L : List Edge} {F : ℕ} {m₀ : ℕ → ℕ} {S : ℕ}

/-! ### The orientation -/

/-- `w` is an out-neighbour of `u` or `u` one of `w`, in the out-neighbour tables of the memory
`m`. -/
def OutAdj (N F : ℕ) (m : ℕ → ℕ) (u w : ℕ) : Prop :=
  m (bO1 F N + u) = w ∨ m (bO2 F N + u) = w ∨ m (bO1 F N + w) = u ∨ m (bO2 F N + w) = u

/-- The orientation stored in `m` answers the adjacency of `L` between different vertices. -/
def OutOK (N : ℕ) (L : List Edge) (F : ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ a b, a < N → b < N → a ≠ b → (Adj L a b ↔ OutAdj N F m a b)

/-! ### Equations of `killLog` and `outChk` -/

theorem killLog_mem (c : Config) :
    (run killLog c).mem = upd (upd (upd (upd c.mem (c.reg rDEAD + c.reg rV) (c.reg rONE))
      (c.reg rLGV + c.reg rLC) (c.reg rV)) (c.reg rLGU + c.reg rLC) (c.reg rU))
      (c.reg rLGW + c.reg rLC) (c.reg rW) := by
  simp +decide only [killLog, run_seq', run_st (show rONE ≠ rT by decide),
    run_st (show rV ≠ rT by decide), run_st (show rU ≠ rT by decide),
    run_st (show rW ≠ rT by decide), run_dec (show rCNT ≠ rT by decide),
    run_inc (show rLC ≠ rT by decide), setReg_reg, setReg_mem, setMem_mem_upd, setMem_reg,
    ↓reduceIte]

theorem killLog_cnt (c : Config) : (run killLog c).reg rCNT = c.reg rCNT - 1 := by
  simp +decide only [killLog, run_seq', run_st (show rONE ≠ rT by decide),
    run_st (show rV ≠ rT by decide), run_st (show rU ≠ rT by decide),
    run_st (show rW ≠ rT by decide), run_dec (show rCNT ≠ rT by decide),
    run_inc (show rLC ≠ rT by decide), setReg_reg, setMem_reg, ↓reduceIte]

theorem killLog_lc (c : Config) : (run killLog c).reg rLC = c.reg rLC + 1 := by
  simp +decide only [killLog, run_seq', run_st (show rONE ≠ rT by decide),
    run_st (show rV ≠ rT by decide), run_st (show rU ≠ rT by decide),
    run_st (show rW ≠ rT by decide), run_dec (show rCNT ≠ rT by decide),
    run_inc (show rLC ≠ rT by decide), setReg_reg, setMem_reg, ↓reduceIte]

theorem killLog_reg {r : ℕ} (hr : r ∉ wregs killLog) (c : Config) : (run killLog c).reg r = c.reg r :=
  run_reg_of_not_mem (by decide) hr c

/-- **The adjacency test** of the orientation. -/
theorem outChk_Z (c : Config) :
    (run outChk c).reg rZ = if c.mem (c.reg rO1 + c.reg rU) = c.reg rW ∨
      c.mem (c.reg rO2 + c.reg rU) = c.reg rW ∨ c.mem (c.reg rO1 + c.reg rW) = c.reg rU ∨
      c.mem (c.reg rO2 + c.reg rW) = c.reg rU then 1 else 0 := by
  simp +decide only [outChk, eqChk, run_seq', run_ld, run_const, run_skip,
    run_ifEq (show rA ≠ rT by decide) (show rW ≠ rT by decide),
    run_ifEq (show rA ≠ rT by decide) (show rU ≠ rT by decide), setReg_reg, setReg_mem,
    config_ite_reg, config_ite_mem, ↓reduceIte]
  split_ifs <;> simp_all

theorem outChk_mem (c : Config) : (run outChk c).mem = c.mem :=
  run_mem_of_stores (by decide) (by decide) c

theorem outChk_reg {r : ℕ} (hr : r ≠ rZ ∧ r ≠ rA ∧ r ≠ rT) (c : Config) :
    (run outChk c).reg r = c.reg r := by
  have h : ∀ r ∈ wregs outChk, r = rZ ∨ r = rA ∨ r = rT := by decide
  exact run_reg_of_not_mem (by decide) (fun h' => by
    rcases h r h' with e | e | e
    · exact hr.1 e
    · exact hr.2.1 e
    · exact hr.2.2 e) c

/-! ### The elimination block -/

/-- **The elimination of `v`** with the neighbours `u`, `w` (in `rV`, `rU`, `rW`), when the
orientation answers the query `s0.mat u w` (`hq`). -/
theorem elimBlk_run {s0 : State} {v u w : ℕ} {c : Config} (hR : LRep N L F m₀ s0 c)
    (hV : c.reg rV = v) (hU : c.reg rU = u) (hW : c.reg rW = w) (hv : v < N) (hu : u < N)
    (hw : w < N) (hlog : s0.log.length + 1 ≤ N) (hstk : s0.stack.length + 2 ≤ 4 * N + 1)
    (hcnt : 1 ≤ s0.cnt) (hq : OutAdj N F m₀ u w ↔ s0.mat u w = true)
    (hS : bEND F N L.length ≤ S) :
    AddrOK S elimBlk c ∧ LRep N L F m₀ (elim s0 v u w) (run elimBlk c) := by
  have hg := hR.glob
  have hnpb := hR.npb
  have hnpS := hR.mem.npS
  have hlc := hR.lc
  -- kill and log
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, c₁ = run killLog c := ⟨_, rfl⟩
  have hg₁ : Glob N L.length F c₁ := by
    rw [hc₁]; exact (Glob.regIndep _ _ _).run_of_sub (by decide) (by decide) hg
  have hr₁ : ∀ r, r ∉ wregs killLog → c₁.reg r = c.reg r := fun r hr => by
    rw [hc₁]; exact killLog_reg hr c
  have hEM₁ : EMem N L.length F m₀
      { s0 with dead := Function.update s0.dead v true, cnt := s0.cnt - 1,
                log := (v, u, w) :: s0.log } (fun _ => 0) [] (c.reg rNP) c₁.mem := by
    have h := (hR.mem.kill hv).log v u w hlog
    rw [hc₁, killLog_mem, hg.dead, hg.lgv, hg.lgu, hg.lgw, hg.one, hV, hU, hW, hR.lc]
    exact h.congr rfl rfl rfl rfl rfl
  -- the test
  obtain ⟨c₂, hc₂⟩ : ∃ c₂, c₂ = run outChk c₁ := ⟨_, rfl⟩
  have hr₂ : ∀ r, r ∉ wregs killLog → r ≠ rZ ∧ r ≠ rA ∧ r ≠ rT → c₂.reg r = c.reg r :=
    fun r h1 h2 => by rw [hc₂, outChk_reg h2, hr₁ r h1]
  have hm₂ : c₂.mem = c₁.mem := by rw [hc₂, outChk_mem]
  have hg₂ : Glob N L.length F c₂ := by
    rw [hc₂]; exact (Glob.regIndep _ _ _).run_of_sub (by decide) (by decide) hg₁
  have hU₂ : c₂.reg rU = u := (hr₂ rU (by decide) (by decide)).trans hU
  have hW₂ : c₂.reg rW = w := (hr₂ rW (by decide) (by decide)).trans hW
  have hnp₂ : c₂.reg rNP = c.reg rNP := hr₂ rNP (by decide) (by decide)
  have hsp₂ : c₂.reg rSP = s0.stack.length := (hr₂ rSP (by decide) (by decide)).trans hR.sp
  have hcnt₂ : c₂.reg rCNT = s0.cnt - 1 := by
    rw [hc₂, outChk_reg (by decide), hc₁, killLog_cnt, hR.cnt]
  have hlc₂ : c₂.reg rLC = s0.log.length + 1 := by
    rw [hc₂, outChk_reg (by decide), hc₁, killLog_lc, hR.lc]
  have hlow : ∀ a, a < bHD F N → c₁.mem a = m₀ a := fun a ha => hEM₁.same a ha
  have hZ₂ : c₂.reg rZ = 0 ↔ s0.mat u w = false := by
    rw [hc₂, outChk_Z, hr₁ rO1 (by decide), hr₁ rO2 (by decide), hr₁ rU (by decide),
      hr₁ rW (by decide), hg.o1, hg.o2, hU, hW, hlow _ (by lomega), hlow _ (by lomega),
      hlow _ (by lomega), hlow _ (by lomega)]
    have := hq
    unfold OutAdj at this
    split_ifs with h
    · simp only [false_iff, Bool.not_eq_false]; exact this.mp h
    · simp only [true_iff]
      cases hm : s0.mat u w
      · rfl
      · exact absurd (this.mpr hm) h
  have hA₁ : AddrOK S killLog c := by
    ear_addr [killLog, hg.dead, hg.lgv, hg.lgu, hg.lgw, hV, hU, hW, hlc]
  have hA₂ : AddrOK S outChk c₁ := by
    ear_addr [outChk, eqChk, hg₁.o1, hg₁.o2, hr₁ rU (by decide), hr₁ rW (by decide), hU, hW]
  have hrun : run elimBlk c = if c₂.reg rZ = 0 then run addVirt c₂ else run decBoth c₂ := by
    rw [hc₂, hc₁]; rfl
  have hsplit : AddrOK S (.ifz rZ addVirt decBoth) c₂ → AddrOK S elimBlk c := fun h =>
    hA₁.seq (by rw [← hc₁]; exact hA₂.seq (by rw [← hc₂]; exact h))
  cases hmat : s0.mat u w
  · -- the virtual edge
    have hz : c₂.reg rZ = 0 := hZ₂.mpr hmat
    rw [hrun]
    simp only [hz, ↓reduceIte]
    rw [← hnp₂] at hEM₁
    rw [← hm₂] at hEM₁
    obtain ⟨c₅, hc₅⟩ : ∃ c₅, c₅ = run (prepend rU rW) c₂ := ⟨_, rfl⟩
    have hm₅ := prepend_emem (x := rU) (y := rW) (by decide) (by decide) hg₂ hEM₁
      (by rw [hU₂]; omega) (by rw [hnp₂]; exact hR.np1) (by rw [hnp₂]; lomega)
    rw [← hc₅, hU₂, hW₂] at hm₅
    have hg₅ : Glob N L.length F c₅ := by
      rw [hc₅]; exact (Glob.regIndep _ _ _).run_of_sub (by decide) (by decide) hg₂
    have hr₅ : ∀ r, r ≠ rZ → r ≠ rT → r ≠ rNP → c₅.reg r = c₂.reg r := fun r h1 h2 h3 => by
      rw [hc₅, prepend_reg _ _ ⟨h1, h2, h3⟩]
    have hnp₅ : c₅.reg rNP = c.reg rNP + 1 := by
      rw [hc₅, prepend_np (by decide), hnp₂]
    obtain ⟨c₆, hc₆⟩ : ∃ c₆, c₆ = run (prepend rW rU) c₅ := ⟨_, rfl⟩
    have hm₆ := prepend_emem (x := rW) (y := rU) (by decide) (by decide) hg₅ hm₅
      (by rw [hr₅ rW (by decide) (by decide) (by decide), hW₂]; omega)
      (by rw [hnp₅]; omega) (by rw [hnp₅]; lomega)
    rw [← hc₆, hr₅ rU (by decide) (by decide) (by decide), hr₅ rW (by decide) (by decide)
      (by decide), hU₂, hW₂] at hm₆
    have hr₆ : ∀ r, r ≠ rZ → r ≠ rT → r ≠ rNP → c₆.reg r = c₂.reg r := fun r h1 h2 h3 => by
      rw [hc₆, prepend_reg _ _ ⟨h1, h2, h3⟩, hr₅ r h1 h2 h3]
    have hnp₆ : c₆.reg rNP = c.reg rNP + 2 := by
      rw [hc₆, prepend_np (by decide), hnp₅]
    have hrun' : run addVirt c₂ = c₆ := by rw [hc₆, hc₅]; rfl
    have hAV : AddrOK S addVirt c₂ := by
      refine (prepend_addrOK (by decide) (by decide) hg₂ (by rw [hU₂]; omega)
        (by rw [hnp₂]; lomega) hS).seq ?_
      rw [← hc₅]
      exact prepend_addrOK (by decide) (by decide) hg₅
        (by rw [hr₅ rW (by decide) (by decide) (by decide), hW₂]; omega) (by rw [hnp₅]; lomega) hS
    refine ⟨hsplit (AddrOK.ifz (fun _ => hAV) (fun h => absurd hz h)), ?_⟩
    have he : elim s0 v u w =
        { adj := Function.update (Function.update s0.adj u (w :: s0.adj u)) w
            (u :: Function.update s0.adj u (w :: s0.adj u) w),
          mat := update2 (update2 s0.mat u w true) w u true, deg := s0.deg,
          dead := Function.update s0.dead v true, stack := s0.stack, log := (v, u, w) :: s0.log,
          cnt := s0.cnt - 1 } := by
      simp only [elim, hmat, Bool.false_eq_true, ↓reduceIte]
    rw [hrun', he]
    have hg₆ : Glob N L.length F c₆ := by
      rw [hc₆]; exact (Glob.regIndep _ _ _).run_of_sub (by decide) (by decide) hg₅
    refine ⟨hg₆, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hr₆ rSP (by decide) (by decide) (by decide), hsp₂]
    · rw [hr₆ rCNT (by decide) (by decide) (by decide), hcnt₂]
    · rw [hr₆ rLC (by decide) (by decide) (by decide), hlc₂, List.length_cons]
    · rw [hnp₆]; omega
    · rw [hnp₆]
      show c.reg rNP + 2 + 2 * (s0.cnt - 1) ≤ poolSz N L.length
      omega
    · exact hm₆.congr rfl rfl rfl rfl rfl
  · -- lowering the degrees
    have hz : c₂.reg rZ ≠ 0 := fun h => by
      have := hZ₂.mp h
      rw [hmat] at this
      exact Bool.noConfusion this
    rw [hrun]
    simp only [hz, ↓reduceIte]
    rw [← hnp₂] at hEM₁
    rw [← hm₂] at hEM₁
    obtain ⟨hm₃, hsp₃, hr₃⟩ := decDegP_emem (x := rU) (by decide) hg₂ hEM₁ (by rw [hU₂]; omega)
      hsp₂ (by simp; omega)
    rw [hU₂] at hm₃ hsp₃
    obtain ⟨c₃, hc₃⟩ : ∃ c₃, c₃ = run (decDegP rU) c₂ := ⟨_, rfl⟩
    rw [← hc₃] at hm₃ hsp₃ hr₃
    have hg₃ : Glob N L.length F c₃ := by
      rw [hc₃]; exact (Glob.regIndep _ _ _).run_of_sub (by decide) (by decide) hg₂
    rw [← hr₃ rNP (by decide) (by decide) (by decide)] at hm₃
    have hstk₃ : (decDeg
        { s0 with dead := Function.update s0.dead v true, cnt := s0.cnt - 1,
                  log := (v, u, w) :: s0.log } u).stack.length + 1 ≤ 4 * N + 1 := by
      rw [decDeg_stack]; split_ifs <;> simp <;> omega
    obtain ⟨hm₄, hsp₄, hr₄⟩ := decDegP_emem (x := rW) (by decide) hg₃ hm₃
      (by rw [hr₃ rW (by decide) (by decide) (by decide), hW₂]; omega) hsp₃ hstk₃
    rw [hr₃ rW (by decide) (by decide) (by decide), hW₂] at hm₄ hsp₄
    have hrun' : run decBoth c₂ = run (decDegP rW) c₃ := by rw [hc₃]; rfl
    have hAD : AddrOK S decBoth c₂ := by
      refine (decDegP_addrOK (by decide) hg₂ (by rw [hU₂]; omega) (by rw [hsp₂]; omega) hS).seq ?_
      rw [← hc₃]
      exact decDegP_addrOK (by decide) hg₃ (by rw [hr₃ rW (by decide) (by decide) (by decide), hW₂]; omega)
        (by rw [hsp₃]; omega) hS
    refine ⟨hsplit (AddrOK.ifz (fun h => absurd h hz) (fun _ => hAD)), ?_⟩
    have he : elim s0 v u w = decDeg (decDeg
        { s0 with dead := Function.update s0.dead v true, cnt := s0.cnt - 1,
                  log := (v, u, w) :: s0.log } u) w := by
      simp only [elim, hmat, ↓reduceIte]
    rw [hrun', he]
    have hr₄' : ∀ r, r ≠ rD → r ≠ rT → r ≠ rSP → (run (decDegP rW) c₃).reg r = c₂.reg r :=
      fun r h1 h2 h3 => (hr₄ r h1 h2 h3).trans (hr₃ r h1 h2 h3)
    refine ⟨(Glob.regIndep _ _ _).run_of_sub (by decide) (by decide) hg₃, hsp₄, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hr₄' rCNT (by decide) (by decide) (by decide), hcnt₂, decDeg_cnt, decDeg_cnt]
    · rw [hr₄' rLC (by decide) (by decide) (by decide), hlc₂, decDeg_log, decDeg_log,
        List.length_cons]
    · rw [hr₄' rNP (by decide) (by decide) (by decide), hnp₂]; exact hR.np1
    · rw [hr₄' rNP (by decide) (by decide) (by decide), hnp₂, decDeg_cnt, decDeg_cnt]
      simp only; omega
    · rw [hr₄' rNP (by decide) (by decide) (by decide), hnp₂]
      rw [hr₃ rNP (by decide) (by decide) (by decide), hnp₂] at hm₄
      exact hm₄

/-! ### One round -/

/-- The cost of one round of the elimination loop from `s`. -/
def roundCost (s : State) : ℕ :=
  match s.stack with
  | [] => 0
  | v :: _ => if s.dead v = false ∧ s.deg v = 2 then 21 * (s.adj v).length + 127 else 19

theorem roundCost_cons {s : State} {v : ℕ} {rest : List ℕ} (hs : s.stack = v :: rest) :
    roundCost s = if s.dead v = false ∧ s.deg v = 2 then 21 * (s.adj v).length + 127 else 19 := by
  unfold roundCost; rw [hs]

/-- **One round** of the elimination loop (body and test) from a running state `s` with the ghost
invariants (`Ear.Inv`, `Ear.Static`), the orientation answering the adjacency of `L` (`hO`). -/
theorem round_spec (hN : 3 ≤ N) {ham0 : List ℕ} {s : State} {H : List ℕ} (hG : Good N s)
    (hRun : Running s) (hI : Inv N ham0 s H) (hSt : Static L s H) (hO : OutOK N L F m₀)
    (hS : bEND F N L.length ≤ S) :
    HTB S (.seq mbody mcond) (LRep N L F m₀ s)
      (fun c => LRep N L F m₀ (step s) c ∧ (c.reg rT = 0 ↔ ¬ Running (step s))) (roundCost s) := by
  obtain ⟨hne, hc3⟩ := hRun
  obtain ⟨v, rest, hs⟩ := List.exists_cons_of_ne_nil hne
  have hv : v < N := hG.stack_lt v (by simp [hs])
  have hpop : HTB S pop (LRep N L F m₀ s) (fun c => LRep N L F m₀ { s with stack := rest } c ∧
      c.reg rV = v ∧ (c.reg rA = 0 ↔ s.dead v = false)) 6 :=
    HTB.run_le (by decide) (by decide) fun c hR => by
      have hstk := hR.mem.stk
      rw [hs, List.reverse_cons] at hstk
      have hrv : c.mem (bSTK F N + (s.stack.length - 1)) = v := by
        have := hstk.get (i := rest.length) (by simp)
        rw [hs, List.length_cons, Nat.add_sub_cancel, this, List.getElem_append_right (by simp)]
        simp
      exact ⟨pop_addrOK hR hne hrv hv hS, pop_run hs hR hv⟩
  have hcond : HTB S mcond (LRep N L F m₀ (step s))
      (fun c => LRep N L F m₀ (step s) c ∧ (c.reg rT = 0 ↔ ¬ Running (step s))) 5 :=
    HTB.of_HT rfl (HT.run_le (by decide) (by decide) fun c hR => mcond_run hR)
  have hld : HTB S (ld rD rDEG rV) (fun c => (LRep N L F m₀ { s with stack := rest } c ∧
      c.reg rV = v ∧ (c.reg rA = 0 ↔ s.dead v = false)) ∧ c.reg rA = 0)
      (fun c => LRep N L F m₀ { s with stack := rest } c ∧ c.reg rV = v ∧ c.reg rD = s.deg v) 2 :=
    HTB.run_le (by decide) (by decide) fun c ⟨⟨hR, hV, _⟩, _⟩ => by
      refine ⟨by ear_addr [hR.glob.deg, hV], ?_⟩
      rw [run_ld]
      refine ⟨(LRep.indep _ _ _ _ _).setReg (by decide) _ hR, by simp +decide [hV], ?_⟩
      simp only [setReg_reg, ↓reduceIte, hR.glob.deg, hV]
      exact hR.mem.deg.get hv
  have hP' : Indep [rT] (fun c => LRep N L F m₀ { s with stack := rest } c ∧ c.reg rV = v ∧
      c.reg rD = s.deg v) :=
    ((LRep.indep _ _ _ _ _).mono (by decide)).and
      ((Indep.reg (r := rV) (by decide) (· = v)).and (Indep.reg (r := rD) (by decide) (· = s.deg v)))
  rw [roundCost_cons hs]
  by_cases h : s.dead v = false ∧ s.deg v = 2
  · simp only [h, and_self, ↓reduceIte]
    have hu := nbOf_lt hG.adj_lt (by omega) v 0
    have hw := nbOf_lt hG.adj_lt (by omega) v 1
    have hstep : step s = elim { s with stack := rest } v ((nbOf s v).getD 0 0) ((nbOf s v).getD 1 0) :=
      step_elim hs h
    have hlen := hG.log_len
    have hpot := hG.pot_le
    unfold pot at hpot
    rw [hs, List.length_cons] at hpot
    obtain ⟨hne', hqs⟩ := query_static (L := L) hI hSt hc3 hs h
    have hq : OutAdj N F m₀ ((nbOf s v).getD 0 0) ((nbOf s v).getD 1 0) ↔
        ({ s with stack := rest } : State).mat ((nbOf s v).getD 0 0) ((nbOf s v).getD 1 0) = true :=
      ((hO _ _ hu hw hne').symm.trans hqs.symm)
    have helim : HTB S elimBlk (fun c => (LRep N L F m₀ { s with stack := rest } c ∧
        c.reg rV = v) ∧ c.reg rU = (nbOf s v).getD 0 0 ∧ c.reg rW = (nbOf s v).getD 1 0)
        (LRep N L F m₀ (step s)) 102 :=
      HTB.run_le (by decide) (by decide) fun c ⟨⟨hR, hV⟩, hU, hW⟩ => by
        rw [hstep]
        exact elimBlk_run hR hV hU hW hv hu hw (by simp; omega) (by simp; omega) (by simp; omega)
          hq hS
    have hscan := scan_spec (N := N) (L := L) (F := F) (m₀ := m₀) (s := { s with stack := rest })
      hv (hG.adj_lt v) hS
    have hif := HTB.ifEq (S := S) (a := rD) (b := rTWO) (s := .seq scan elimBlk) (u := .skip)
      (Q := LRep N L F m₀ (step s)) (B := 21 * (s.adj v).length + 7 + 102) (by decide) (by decide) hP'
      ((hscan.pre fun c ⟨⟨hR, hV, _⟩, _⟩ => ⟨hR, hV⟩).seq helim)
      (HTB.of_false fun c ⟨⟨hR, _, hD⟩, hne⟩ => hne (by rw [hD, hR.glob.two, h.2]))
    have hck : HTB S checkDeg _ _ _ := hld.seq hif
    have hbody := hpop.seq (HTB.ifz (u := Stmt.skip) hck
      (HTB.of_false fun c ⟨⟨_, _, hA⟩, hA0⟩ => hA0 (hA.mpr h.1)))
    exact (hbody.seq hcond).weaken (by omega)
  · simp only [h, ↓reduceIte]
    have hstep : step s = { s with stack := rest } := step_skip hs h
    by_cases hd : s.dead v = false
    · have hd2 : s.deg v ≠ 2 := fun h2 => h ⟨hd, h2⟩
      have hif := HTB.ifEq (S := S) (a := rD) (b := rTWO) (s := .seq scan elimBlk) (u := .skip)
        (Q := LRep N L F m₀ (step s)) (B := 1) (by decide) (by decide) hP'
        (HTB.of_false fun c ⟨⟨hR, _, hD⟩, heq⟩ => hd2 (by rw [← hD, heq, hR.glob.two]))
        (HTB.skip.mono (fun c ⟨⟨hR, _, _⟩, _⟩ => by rw [hstep]; exact hR) (fun _ h => h) le_rfl)
      have hck : HTB S checkDeg _ _ _ := hld.seq hif
      have hbody := hpop.seq (HTB.ifz (u := Stmt.skip) hck
        (HTB.of_false fun c ⟨⟨_, _, hA⟩, hA0⟩ => hA0 (hA.mpr hd)))
      exact (hbody.seq hcond).weaken (by omega)
    · have hsk : HTB S Stmt.skip (fun c => (LRep N L F m₀ { s with stack := rest } c ∧
          c.reg rV = v ∧ (c.reg rA = 0 ↔ s.dead v = false)) ∧ c.reg rA ≠ 0)
          (LRep N L F m₀ (step s)) 7 :=
        (HTB.skip.mono (fun c ⟨⟨hR, _, _⟩, _⟩ => by rw [hstep]; exact hR) (fun _ h => h) (by omega))
      have hbody := hpop.seq (HTB.ifz (s := checkDeg) (b := 7)
        (HTB.of_false fun c ⟨⟨_, _, hA⟩, hA0⟩ => hd (hA.mp hA0)) hsk)
      exact (hbody.seq hcond).weaken (by omega)

end STACS2027.RAM.EarR
