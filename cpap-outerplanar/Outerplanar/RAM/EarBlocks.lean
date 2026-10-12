module

public import Outerplanar.RAM.EarProg
import Mathlib.Tactic

/-!
# The ear-elimination machine: the small blocks

The effect of the blocks shared by the initialization and the elimination loop, first as
equations for `run` (memory, registers), then on the memory representation `EMem`, and their
addresses (`AddrOK`, below any bound `S ≥ bEND F N M`):

* `prepend x y`: `y` prepended to the list of `x` (`prepend_mem`, `prepend_np`, `prepend_reg`,
  `prepend_emem`, `prepend_addrOK`);
* `incDeg x`: `deg[x] += 1` (`incDeg_mem`, `incDeg_reg`, `incDeg_emem`, `incDeg_addrOK`);
* `push x` (`push_mem`, `push_sp`, `push_reg`, `push_emem`, `push_addrOK`);
* `decDegP x`: `Ear.decDeg` (`decDegP_emem`, `decDegP_addrOK`).

Also the representation `LRep` of a state of the elimination loop.
-/

@[expose] public section

namespace STACS2027.RAM.EarR

open STACS2027 STACS2027.Ear

/-! ### Equations -/

theorem prepend_mem {x y : ℕ} (hx : x ≠ rZ ∧ x ≠ rT) (hy : y ≠ rZ ∧ y ≠ rT) (c : Config) :
    (run (prepend x y) c).mem = upd (upd (upd c.mem (c.reg rVAL + c.reg rNP) (c.reg y))
      (c.reg rNXT + c.reg rNP) (c.mem (c.reg rHD + c.reg x))) (c.reg rHD + c.reg x) (c.reg rNP) := by
  simp +decide only [prepend, run_seq', run_ld, run_st (show rZ ≠ rT by decide), run_st hy.2,
    run_st (show rNP ≠ rT by decide), run_inc (show rNP ≠ rT by decide), setReg_reg, setReg_mem,
    setMem_mem_upd, setMem_reg, hx.1, hx.2, hy.1, ↓reduceIte]

theorem prepend_np {x y : ℕ} (hy : y ≠ rT) (c : Config) :
    (run (prepend x y) c).reg rNP = c.reg rNP + 1 := by
  simp +decide only [prepend, run_seq', run_ld, run_st (show rZ ≠ rT by decide), run_st hy,
    run_st (show rNP ≠ rT by decide), run_inc (show rNP ≠ rT by decide), setReg_reg, setMem_reg,
    ↓reduceIte]

theorem prepend_reg (x y : ℕ) {r : ℕ} (hr : r ≠ rZ ∧ r ≠ rT ∧ r ≠ rNP) (c : Config) :
    (run (prepend x y) c).reg r = c.reg r :=
  run_reg_of_not_mem (by simp [prepend, LoopFree]) (by simp [prepend, wregs, hr.1, hr.2.1, hr.2.2]) c

theorem incDeg_mem {x : ℕ} (hx : x ≠ rZ ∧ x ≠ rT) (c : Config) :
    (run (incDeg x) c).mem = upd c.mem (c.reg rDEG + c.reg x) (c.mem (c.reg rDEG + c.reg x) + 1) := by
  simp +decide only [incDeg, run_seq', run_ld, run_inc (show rZ ≠ rT by decide),
    run_st (show rZ ≠ rT by decide), setReg_reg, setReg_mem, setMem_mem_upd, hx.1, hx.2, ↓reduceIte]

theorem incDeg_reg (x : ℕ) {r : ℕ} (hr : r ≠ rZ ∧ r ≠ rT) (c : Config) :
    (run (incDeg x) c).reg r = c.reg r :=
  run_reg_of_not_mem (by simp [incDeg, LoopFree]) (by simp [incDeg, wregs, hr.1, hr.2]) c

theorem push_mem {x : ℕ} (hx : x ≠ rT) (c : Config) :
    (run (push x) c).mem = upd c.mem (c.reg rSTK + c.reg rSP) (c.reg x) := by
  simp +decide only [push, run_seq', run_st hx, run_inc (show rSP ≠ rT by decide), setReg_mem,
    setMem_mem_upd]

theorem push_sp {x : ℕ} (hx : x ≠ rT) (c : Config) : (run (push x) c).reg rSP = c.reg rSP + 1 := by
  simp +decide only [push, run_seq', run_st hx, run_inc (show rSP ≠ rT by decide), setReg_reg,
    setMem_reg, ↓reduceIte]

theorem push_reg (x : ℕ) {r : ℕ} (hr : r ≠ rT ∧ r ≠ rSP) (c : Config) :
    (run (push x) c).reg r = c.reg r :=
  run_reg_of_not_mem (by simp [push, LoopFree]) (by simp [push, hr.1, hr.2]) c

/-! ### Addresses -/

section Addr

variable {N M F S : ℕ} {c : Config}

theorem prepend_addrOK {x y : ℕ} (hx : x ≠ rZ ∧ x ≠ rT) (hy : y ≠ rT) (hg : Glob N M F c)
    (hxv : c.reg x < N) (hn : c.reg rNP < poolSz N M) (hS : bEND F N M ≤ S) :
    AddrOK S (prepend x y) c := by
  ear_addr [prepend, hg.hd, hg.val, hg.nxt, hx.1, hx.2, run_st hy]

theorem incDeg_addrOK {x : ℕ} (hx : x ≠ rZ ∧ x ≠ rT) (hg : Glob N M F c) (hxv : c.reg x < N)
    (hS : bEND F N M ≤ S) : AddrOK S (incDeg x) c := by
  ear_addr [incDeg, hg.deg, hx.1, hx.2]

theorem push_addrOK (x : ℕ) (hg : Glob N M F c) (hsp : c.reg rSP < 4 * N + 1)
    (hS : bEND F N M ≤ S) : AddrOK S (push x) c := by
  ear_addr [push, hg.stk]

theorem decDegP_addrOK {x : ℕ} (hx : x ≠ rD ∧ x ≠ rT ∧ x ≠ rSP) (hg : Glob N M F c)
    (hxv : c.reg x < N) (hsp : c.reg rSP < 4 * N + 1) (hS : bEND F N M ≤ S) :
    AddrOK S (decDegP x) c := by
  ear_addr [decDegP, push, hg.deg, hg.stk, hx.1, hx.2.1, hx.2.2]

end Addr

/-! ### On the memory representation -/

section Rep

variable {N M F : ℕ} {m₀ : ℕ → ℕ} {s : State} {succ : ℕ → ℕ} {ham : List ℕ} {np : ℕ} {c : Config}

theorem prepend_emem {x y : ℕ} (hx : x ≠ rZ ∧ x ≠ rT) (hy : y ≠ rZ ∧ y ≠ rT)
    (hg : Glob N M F c) (hm : EMem N M F m₀ s succ ham (c.reg rNP) c.mem) (hxv : c.reg x < N)
    (hn : 0 < c.reg rNP) (hnS : c.reg rNP + 1 ≤ poolSz N M) :
    EMem N M F m₀ { s with adj := Function.update s.adj (c.reg x) (c.reg y :: s.adj (c.reg x)) }
      succ ham ((run (prepend x y) c).reg rNP) (run (prepend x y) c).mem := by
  rw [prepend_mem hx hy, prepend_np hy.2, hg.val, hg.nxt, hg.hd]
  exact hm.prepend _ hxv hn hnS

theorem incDeg_emem {x : ℕ} (hx : x ≠ rZ ∧ x ≠ rT) (hg : Glob N M F c)
    (hm : EMem N M F m₀ s succ ham np c.mem) (hxv : c.reg x < N) :
    EMem N M F m₀ { s with deg := Function.update s.deg (c.reg x) (s.deg (c.reg x) + 1) } succ ham np
      (run (incDeg x) c).mem := by
  rw [incDeg_mem hx, hg.deg, hm.deg.get hxv]
  exact hm.setDeg _ hxv

theorem push_emem {x : ℕ} (hx : x ≠ rT) (hg : Glob N M F c)
    (hm : EMem N M F m₀ s succ ham np c.mem) (hsp : c.reg rSP = s.stack.length)
    (hS : s.stack.length + 1 ≤ 4 * N + 1) :
    EMem N M F m₀ { s with stack := c.reg x :: s.stack } succ ham np (run (push x) c).mem := by
  rw [push_mem hx, hg.stk, hsp]
  exact hm.push _ hS

/-- **Lowering a degree** (`Ear.decDeg`). -/
theorem decDegP_emem {x : ℕ} (hx : x ≠ rD ∧ x ≠ rT ∧ x ≠ rSP ∧ x ≠ rTWO) (hg : Glob N M F c)
    (hm : EMem N M F m₀ s succ ham np c.mem) (hxv : c.reg x < N) (hsp : c.reg rSP = s.stack.length)
    (hS : s.stack.length + 1 ≤ 4 * N + 1) :
    EMem N M F m₀ (decDeg s (c.reg x)) succ ham np (run (decDegP x) c).mem ∧
      (run (decDegP x) c).reg rSP = (decDeg s (c.reg x)).stack.length ∧
      ∀ r, r ≠ rD → r ≠ rT → r ≠ rSP → (run (decDegP x) c).reg r = c.reg r := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  set c₁ := run (.seq (ld rD rDEG x) (.seq (dec rD) (st rDEG x rD))) c with hc₁
  have hrun : run (decDegP x) c = run (ifEq rD rTWO (push x) .skip) c₁ := rfl
  have hm₁ : c₁.mem = upd c.mem (bDEG F N + c.reg x) (s.deg (c.reg x) - 1) := by
    simp +decide only [hc₁, run_seq', run_ld, run_dec (show rD ≠ rT by decide),
      run_st (show rD ≠ rT by decide), setReg_reg, setReg_mem, setMem_mem_upd, hx1, hx2,
      ↓reduceIte, hg.deg, hm.deg.get hxv]
  have hd₁ : c₁.reg rD = s.deg (c.reg x) - 1 := by
    simp +decide only [hc₁, run_seq', run_ld, run_dec (show rD ≠ rT by decide),
      run_st (show rD ≠ rT by decide), setReg_reg, setMem_reg, ↓reduceIte, hg.deg, hm.deg.get hxv]
  have hr₁ : ∀ r, r ≠ rD → r ≠ rT → c₁.reg r = c.reg r := fun r h1 h2 =>
    run_reg_of_not_mem (by simp [LoopFree]) (by simp [h1, h2]) c
  have hEM₁ := hm.setDeg (s.deg (c.reg x) - 1) hxv
  rw [← hm₁] at hEM₁
  have hx₁ : c₁.reg x = c.reg x := hr₁ x hx1 hx2
  have hsp₁ : c₁.reg rSP = s.stack.length := (hr₁ rSP (by decide) (by decide)).trans hsp
  have htwo : c₁.reg rTWO = 2 := (hr₁ rTWO (by decide) (by decide)).trans hg.two
  have hg₁ : Glob N M F c₁ := (Glob.regIndep N M F).run_of_sub (by simp [LoopFree]) (by simp [WV]) hg
  rw [hrun, run_ifEq (by decide) (by decide), hd₁, htwo]
  simp only [decDeg_stack]
  unfold decDeg pushIf2
  simp only [Function.update_self]
  by_cases h2 : s.deg (c.reg x) - 1 = 2
  · simp only [h2, ↓reduceIte]
    have hg₂ := (Glob.regIndep N M F).setReg (d := rT) (by decide) 0 hg₁
    have hEM := push_emem (x := x) (c := c₁.setReg rT 0) hx2 hg₂ hEM₁
      (by simp +decide [hsp₁]) (by simpa using hS)
    simp only [setReg_reg, hx2, ↓reduceIte, hx₁, h2] at hEM
    refine ⟨hEM, ?_, fun r h1 h2 h3 => ?_⟩
    · rw [push_sp hx2]; simp +decide [hsp₁]
    · rw [push_reg x ⟨h2, h3⟩]; simp [h2, hr₁ r h1 h2]
  · simp only [h2, ↓reduceIte, run_skip]
    refine ⟨hEM₁, ?_, fun r h1 h2 _ => ?_⟩
    · simp +decide [hsp₁]
    · simp [h2, hr₁ r h1 h2]

end Rep

/-! ### The state of the elimination loop -/

/-- The machine holds the abstract state `s` of the elimination loop. -/
@[mk_iff] structure LRep (N : ℕ) (L : List Edge) (F : ℕ) (m₀ : ℕ → ℕ) (s : State) (c : Config) :
    Prop where
  glob : Glob N L.length F c
  sp : c.reg rSP = s.stack.length
  cnt : c.reg rCNT = s.cnt
  lc : c.reg rLC = s.log.length
  np1 : 1 ≤ c.reg rNP
  npb : c.reg rNP + 2 * s.cnt ≤ poolSz N L.length
  mem : EMem N L.length F m₀ s (fun _ => 0) [] (c.reg rNP) c.mem

theorem LRep.indep (N : ℕ) (L : List Edge) (F : ℕ) (m₀ : ℕ → ℕ) (s : State) :
    Indep [rT, rI, rA, rB, rV, rU, rW, rX, rK, rP, rQ, rZ, rD, rY, rC, rPSP] (LRep N L F m₀ s) := by
  indep [lRep_iff, glob_iff]

end STACS2027.RAM.EarR
