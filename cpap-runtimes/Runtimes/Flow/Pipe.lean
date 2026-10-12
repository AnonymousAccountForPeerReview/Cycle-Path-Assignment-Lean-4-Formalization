module

public import Runtimes.Flow.Reloc
import Mathlib.Tactic

/-!
# Three RAM programs as one

`pipe3 lenP P Q R` runs `P` on the input `x`, then `Q` on the output `y` of `P`, then `R` on
`x ++ z`, `z` the output of `Q`, as **one** RAM program (`pipe3_spec`), within
`tL + 12|x| + 4 (t_P + t_Q + t_R) + 20` steps, accessing only the addresses below
`S_L + 4 (|x| + |y| + |z| + S_P + S_Q + S_R)` when the stages access only the addresses below
`S_L` (`lenP`), `S_P`, `S_Q`, `S_R` (`pipe3_spec_time`: the same without the space bounds):

1. `lenP` computes the length `|x|` of the input into `xL` (a program depending on the input
   format; it uses registers of class `3` only and does not store);
2. `spread` copies the input into the classes `0` (the memory of `P`) and `2` (the beginning of
   the input of `R`) and clears the classes `1` and `3` of the input region: cell `4a` and cell
   `4a + 2` receive `x_a` (`sp x`), going down from `a = |x| - 1` so that no input cell is
   overwritten before it is read;
3. `P` relocated into class `0`, its output buffered in class `1` from cell `1` on — which is
   exactly the input of `Q` in class `1`;
4. `Q` relocated into class `1`, its output buffered in class `2` after the copy of `x`;
5. `R` relocated into class `2`, its output written.

The relocations are simulated by `sim_step` (`Runtimes/Flow/Reloc.lean`): stage `j` with space
`S_j` accesses the addresses `4a + j < 4 S_j`; the buffered outputs occupy the cells `4i + 1`
(`i < |y|`) and `4 (|x| + i) + 2` (`i < |z|`), and `spread` the cells below `4|x|`. `pipe3` is a whole
program, not a phase of a larger machine: its stages use the registers of their residue
classes, so the register-block convention of the phases does not apply to it (the composition's
own registers are those of class `3`: `xT xP xFour xJ j` and `xI xV xA xZ xOne xL`).
-/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027.RAM

/-! ### Registers (class `3`) -/

/-- The spreading counter. -/
abbrev xI : ℕ := 603
/-- A value. -/
abbrev xV : ℕ := 607
/-- An address. -/
abbrev xA : ℕ := 611
/-- Holds `0` (never written). -/
abbrev xZ : ℕ := 615
/-- Holds `1`. -/
abbrev xOne : ℕ := 619
/-- The length of the input. -/
abbrev xL : ℕ := 623

/-! ### Spreading the input -/

/-- The spread input: `x_a` at `4a` and `4a + 2`, zero elsewhere. -/
def sp (x : List ℕ) (a : ℕ) : ℕ := if a % 4 = 0 ∨ a % 4 = 2 then x.getD (a / 4) 0 else 0

/-- One step: `i := i - 1`; cells `4i, 4i+1, 4i+2, 4i+3 := x_i, 0, x_i, 0`. -/
def spreadBody : Stmt :=
  .seq (.sub xI xI xOne) (.seq (.load xV xI) (.seq (.add xA xI xI) (.seq (.add xA xA xA)
    (.seq (.store xA xV) (.seq (.add xA xA xOne) (.seq (.store xA xZ) (.seq (.add xA xA xOne)
    (.seq (.store xA xV) (.seq (.add xA xA xOne) (.store xA xZ))))))))))

/-- Spreading the input of length `xL`. -/
def spread : Stmt := .seq (.add xI xL xZ) (.loop xI spreadBody)

/-- The invariant of the spreading loop. -/
def SpInv (x : List ℕ) (R : ℕ → ℕ) (O : List ℕ) (c : Config) : Prop :=
  c.reg xI ≤ x.length ∧ (∀ a, c.mem a = if a < 4 * c.reg xI then x.getD a 0 else sp x a) ∧
    c.out = O ∧ ∀ r, r ≠ xI → r ≠ xV → r ≠ xA → c.reg r = R r

theorem spreadBody_spec {S : ℕ} (x : List ℕ) (R : ℕ → ℕ) (O : List ℕ) (hZ : R xZ = 0)
    (hOne : R xOne = 1) (hS : 4 * x.length ≤ S) (v : ℕ) :
    HTB S spreadBody (fun c => SpInv x R O c ∧ c.reg xI ≠ 0 ∧ c.reg xI = v)
      (fun c => SpInv x R O c ∧ c.reg xI < v) 11 :=
    HTB.of_HT_addrOK (by decide) (fun c ⟨⟨hle, _, _, hr⟩, h0, hv⟩ => by
      have hOne' : c.reg xOne = 1 := by rw [hr xOne (by decide) (by decide) (by decide), hOne]
      addr_ok [spreadBody, hv, hOne']) <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨hle, hm, ho, hr⟩, h0, hv⟩ => ?_
  have hZ' : c.reg xZ = 0 := by rw [hr xZ (by decide) (by decide) (by decide), hZ]
  have hOne' : c.reg xOne = 1 := by rw [hr xOne (by decide) (by decide) (by decide), hOne]
  have hval : c.mem (v - 1) = x.getD (v - 1) 0 := by rw [hm]; simp [hv]; omega
  set u := x.getD (v - 1) 0 with hu
  have e : v - 1 + (v - 1) + (v - 1 + (v - 1)) = 4 * (v - 1) := by omega
  have hrm : (run spreadBody c).mem = upd (upd (upd (upd c.mem (4 * (v - 1)) u)
      (4 * (v - 1) + 1) 0) (4 * (v - 1) + 1 + 1) u) (4 * (v - 1) + 1 + 1 + 1) 0 := by
    simp +decide only [spreadBody, run_seq', run_sub, run_load, run_add, run_store,
      setReg_reg, setReg_mem, setMem_reg, setMem_mem_upd, ↓reduceIte, hv, hZ', hOne', hval, e]
  have hxI : (run spreadBody c).reg xI = v - 1 := by
    simp +decide only [spreadBody, run_seq', run_sub, run_load, run_add, run_store,
      setReg_reg, setMem_reg, ↓reduceIte, hv, hOne']
  refine ⟨⟨by rw [hxI]; omega, fun a => ?_, by rw [run_out_of_writes (by decide) rfl]; exact ho,
    fun r h1 h2 h3 => ?_⟩, by rw [hxI]; omega⟩
  · rw [hrm, hxI]
    simp only [upd_apply]
    by_cases ha : a < 4 * (v - 1)
    · have : a < 4 * v := by omega
      simp only [show a ≠ 4 * (v - 1) + 1 + 1 + 1 by omega, show a ≠ 4 * (v - 1) + 1 + 1 by omega,
        show a ≠ 4 * (v - 1) + 1 by omega, show a ≠ 4 * (v - 1) by omega, ↓reduceIte, ha, hm a, hv,
        this]
    · by_cases ha' : 4 * v ≤ a
      · have : ¬ a < 4 * v := by omega
        simp only [show a ≠ 4 * (v - 1) + 1 + 1 + 1 by omega, show a ≠ 4 * (v - 1) + 1 + 1 by omega,
          show a ≠ 4 * (v - 1) + 1 by omega, show a ≠ 4 * (v - 1) by omega, ↓reduceIte, ha, hm a, hv,
          this]
      · simp only [ha, ↓reduceIte, sp]
        have hq : a / 4 = v - 1 := by omega
        rw [hq]
        obtain ⟨r, hr4, rfl⟩ : ∃ r, r < 4 ∧ a = 4 * (v - 1) + r := ⟨a - 4 * (v - 1), by omega, by omega⟩
        rw [← hu]
        split_ifs <;> omega
  · rw [run_reg_of_not_mem (by decide) (by simp [spreadBody, wregs, h1, h2, h3]) c]
    exact hr r h1 h2 h3

/-- **Spreading the input** `x` (of length `xL`): afterwards the memory is `sp x`. -/
theorem spread_spec {S : ℕ} (x : List ℕ) (R : ℕ → ℕ) (O : List ℕ) (hZ : R xZ = 0)
    (hOne : R xOne = 1) (hL : R xL = x.length) (hS : 4 * x.length ≤ S) :
    HTB S spread (fun c => c.mem = (initial x).mem ∧ c.out = O ∧ c.reg = R)
      (fun c => c.mem = sp x ∧ c.out = O ∧ ∀ r, r ≠ xI → r ≠ xV → r ≠ xA → c.reg r = R r)
      (12 * x.length + 2) := by
  have h0 : HTB S (.add xI xL xZ) (fun c => c.mem = (initial x).mem ∧ c.out = O ∧ c.reg = R)
      (fun c => SpInv x R O c ∧ c.reg xI ≤ x.length) 1 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨hm, ho, hr⟩ => ?_
    have hxl : c.reg xL + c.reg xZ = x.length := by rw [hr, hL, hZ]; rfl
    refine ⟨⟨?_, fun a => ?_, ?_, fun r h1 _ _ => ?_⟩, ?_⟩
    all_goals simp only [run_add, setReg_reg, setReg_mem, setReg_out, ↓reduceIte, hxl, le_refl]
    · rw [hm, initial_mem]
      split_ifs with ha
      · rfl
      · have : x.length ≤ a / 4 := by omega
        simp only [sp]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        split_ifs <;> simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none this]
    · exact ho
    · simp only [h1, ↓reduceIte]; rw [hr]
  have hl := HTB.loopT (a := xI) (body := spreadBody) (Inv := SpInv x R O) (fun c => c.reg xI)
    (fun v => spreadBody_spec x R O hZ hOne hS v) x.length
  refine (h0.seq hl).mono (fun _ h => h) (fun c ⟨⟨_, hm, ho, hr⟩, h0⟩ => ⟨?_, ho, hr⟩) (by omega)
  funext a
  rw [hm a, h0]
  simp

/-! ### The composition -/

theorem ne_of_mod {r x : ℕ} (h : r % 4 ≠ 3) (hx : x % 4 = 3) : r ≠ x := fun e => h (e ▸ hx)

/-- The constants of the relocated stages; the first buffer pointer. -/
def setConsts : Stmt := .seq (.const xFour 4) (.seq (.const (xJ 1) 1) (.seq (.const (xJ 2) 2)
  (.const xP 1)))

/-- The second buffer pointer: `4 |x| + 2`. -/
def ptr2 : Stmt := .seq (.add xA xL xL) (.seq (.add xA xA xA) (.seq (.const xV 2) (.add xP xA xV)))

/-- **Three programs as one**: `R (x ++ Q (P x))`. -/
def pipe3 (lenP P Q R : Stmt) : Stmt :=
  .seq lenP (.seq (.const xOne 1) (.seq spread (.seq setConsts (.seq (tr 0 true P)
    (.seq ptr2 (.seq (tr 1 true Q) (tr 2 false R)))))))

/-- What `lenP` must establish: the length of the input in `xL`, the memory and the output
untouched, and zero in the registers of the stages, in `xJ 0` and in `xZ`. -/
def LenPost (x : List ℕ) (c : Config) : Prop :=
  c.reg xL = x.length ∧ c.mem = (initial x).mem ∧ c.out = [] ∧
    ∀ r, (r % 4 ≠ 3 ∨ r = xJ 0 ∨ r = xZ) → c.reg r = 0

theorem exec_loopFree {s : Stmt} (hs : LoopFree s) (c : Config) {n : ℕ} (hn : RAM.cost s c = n) :
    Exec s c n (run s c) := hn ▸ exec_run s hs c

theorem getD_append_left' {l l' : List ℕ} {a : ℕ} (h : a < l.length) :
    (l ++ l').getD a 0 = l.getD a 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right'' {l l' : List ℕ} {a : ℕ} (h : l.length ≤ a) :
    (l ++ l').getD a 0 = l'.getD (a - l.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- **The composition theorem**: if `P` computes `y` from `x` in `t₁` steps and the addresses
below `S₁`, `Q` computes `z` from `y` in `t₂` steps and the addresses below `S₂`, `R` computes
`w` from `x ++ z` in `t₃` steps and the addresses below `S₃`, and `lenP` computes `|x|` in `tL`
steps and the addresses below `SL`, then `pipe3 lenP P Q R` computes `w` from `x` within
`tL + 12|x| + 4 (t₁ + t₂ + t₃) + 20` steps, accessing only the addresses below
`SL + 4 (|x| + |y| + |z| + S₁ + S₂ + S₃)`. -/
theorem pipe3_spec {lenP P Q R : Stmt} {x y z w : List ℕ} {tL t₁ t₂ t₃ SL S₁ S₂ S₃ : ℕ}
    (hL : HTB SL lenP (· = initial x) (LenPost x) tL)
    (h1 : ComputesIn P x y t₁ S₁) (h2 : ComputesIn Q y z t₂ S₂)
    (h3 : ComputesIn R (x ++ z) w t₃ S₃) :
    ∃ t, ComputesIn (pipe3 lenP P Q R) x w t
        (SL + 4 * (x.length + y.length + z.length + S₁ + S₂ + S₃)) ∧
      t ≤ tL + 12 * x.length + 4 * (t₁ + t₂ + t₃) + 20 := by
  set S' := SL + 4 * (x.length + y.length + z.length + S₁ + S₂ + S₃) with hS'
  -- phase 1: the length
  obtain ⟨c₁, s₁, e₁, ⟨hL₁, hm₁, ho₁, hz₁⟩, hs₁⟩ := hL _ rfl
  -- phase 2: `xOne`
  set c₂ := c₁.setReg xOne 1 with hc₂
  have e₂ : ExecB S' (.const xOne 1) c₁ 1 c₂ := ExecB.const _ _ _
  -- phase 3: spreading
  obtain ⟨c₃, s₃, e₃, ⟨hm₃, ho₃, hr₃⟩, hs₃⟩ := spread_spec (S := S') x c₂.reg [] (by
      simp [hc₂, hz₁ xZ (Or.inr (Or.inr rfl))]) (by simp [hc₂]) (by simp [hc₂, hL₁]) (by omega) c₂
    ⟨by simp [hc₂, hm₁], by simp [hc₂, ho₁], rfl⟩
  -- phase 4: the constants
  set c₄ := run setConsts c₃ with hc₄
  have e₄ : ExecB S' setConsts c₃ 4 c₄ :=
    Exec.toExecB_of_memFree rfl (exec_loopFree (by decide) c₃ (by simp [setConsts, RAM.cost]))
  have hm₄ : c₄.mem = sp x := by rw [hc₄, run_mem_of_stores (by decide) rfl, hm₃]
  have ho₄ : c₄.out = [] := by rw [hc₄, run_out_of_writes (by decide) rfl, ho₃]
  have hr₄ : ∀ r, r % 4 ≠ 3 → c₄.reg r = 0 := by
    intro r hr
    have e1 : r ≠ xFour := by show r ≠ 11; omega
    have e2 : r ≠ xJ 1 := by show r ≠ 4 * (3 + 1) + 3; omega
    have e3 : r ≠ xJ 2 := by show r ≠ 4 * (3 + 2) + 3; omega
    have e4 : r ≠ xP := by show r ≠ 7; omega
    have e5 : r ≠ xOne := by show r ≠ 619; omega
    simp only [hc₄, setConsts, run_seq', run_const, setReg_reg, e1, e2, e3, e4, ↓reduceIte]
    rw [hr₃ r (by show r ≠ 603; omega) (by show r ≠ 607; omega) (by show r ≠ 611; omega)]
    simp only [hc₂, setReg_reg, e5, ↓reduceIte]
    exact hz₁ r (Or.inl hr)
  have hK₄ : c₄.reg xFour = 4 ∧ c₄.reg (xJ 0) = 0 ∧ c₄.reg (xJ 1) = 1 ∧ c₄.reg (xJ 2) = 2 ∧
      c₄.reg xP = 1 ∧ c₄.reg xL = x.length := by
    have hJ0 : c₃.reg (xJ 0) = 0 := by
      rw [hr₃ _ (by decide) (by decide) (by decide)]
      simp only [hc₂, setReg_reg, show xJ 0 ≠ xOne by decide, ↓reduceIte]
      exact hz₁ _ (Or.inr (Or.inl rfl))
    have hL₃ : c₃.reg xL = x.length := by
      rw [hr₃ _ (by decide) (by decide) (by decide)]; simp [hc₂, hL₁]
    simp +decide [hc₄, setConsts, hJ0, hL₃]
  -- stage 0: `P`
  obtain ⟨cP, eP, hP⟩ := h1
  obtain ⟨C₅, s₅, e₅, hS₅, hO₅, hs₅, hp₅, hr₅, hm₅⟩ := sim_step (j := 0) (k := 1) (B := 0)
    (b := true) (O₀ := []) (S' := S') (by norm_num) (by norm_num) (by simp) (by omega) eP c₄
    ⟨fun r => by rw [hr₄ _ (by unfold rl; omega)]; rfl, fun a => by
      rw [hm₄]; simp [sp, initial_mem], hK₄.2.1, hK₄.1⟩
    ⟨by rw [hK₄.2.2.2.2.1]; rfl, fun i hi => absurd hi (by simp), ho₄⟩
    (fun _ => by rw [hP]; omega)
  rw [hP] at hO₅
  obtain ⟨hp5, hb5, ho5⟩ := hO₅
  -- the second pointer
  set C₆ := run ptr2 C₅ with hC₆
  have e₆ : ExecB S' ptr2 C₅ 4 C₆ :=
    Exec.toExecB_of_memFree rfl (exec_loopFree (by decide) C₅ (by simp [ptr2, RAM.cost]))
  have hL₅ : C₅.reg xL = x.length := by
    rw [hr₅ xL (by decide) (by decide) (by decide)]; exact hK₄.2.2.2.2.2
  have hm₆ : C₆.mem = C₅.mem := by rw [hC₆, run_mem_of_stores (by decide) rfl]
  have ho₆ : C₆.out = [] := by rw [hC₆, run_out_of_writes (by decide) rfl, ho5]
  have hp₆ : C₆.reg xP = 4 * (x.length + 0) + 2 := by
    simp +decide only [hC₆, ptr2, run_seq', run_add, run_const, setReg_reg, ↓reduceIte, hL₅]
    omega
  have hr₆ : ∀ r, r ≠ xA → r ≠ xV → r ≠ xP → C₆.reg r = C₅.reg r := by
    intro r h1 h2 h3
    exact run_reg_of_not_mem (by decide) (by simp [ptr2, wregs, h1, h2, h3]) C₅
  -- registers of the later stages are still zero
  have hreg₆ : ∀ r, r % 4 = 1 ∨ r % 4 = 2 → C₆.reg r = 0 := by
    intro r hr
    have h3 : r % 4 ≠ 3 := by omega
    rw [hr₆ r (ne_of_mod h3 (by decide)) (ne_of_mod h3 (by decide)) (ne_of_mod h3 (by decide)),
      hr₅ r (by omega) (ne_of_mod h3 (by decide)) (ne_of_mod h3 (by decide)), hr₄ r h3]
  have hJ₆ : ∀ j, j = 1 ∨ j = 2 → C₆.reg (xJ j) = j := by
    intro j hj
    rcases hj with rfl | rfl
    · rw [hr₆ _ (by decide) (by decide) (by decide), hr₅ _ (by decide) (by decide) (by decide)]
      exact hK₄.2.2.1
    · rw [hr₆ _ (by decide) (by decide) (by decide), hr₅ _ (by decide) (by decide) (by decide)]
      exact hK₄.2.2.2.1
  have hF₆ : C₆.reg xFour = 4 := by
    rw [hr₆ _ (by decide) (by decide) (by decide), hr₅ _ (by decide) (by decide) (by decide)]
    exact hK₄.1
  -- stage 1: `Q`
  have hmem₆ : ∀ a, C₆.mem (4 * a + 1) = (initial y).mem a := by
    -- the input of `Q`: the buffered output of `P`
    intro a
    rw [hm₆, initial_mem]
    by_cases ha : a < y.length
    · rw [show 4 * a + 1 = 4 * (0 + a) + 1 by ring, hb5 a ha]
    · rw [hm₅ _ (by omega) (Or.inr (Or.inr (by rw [hp5]; omega))), hm₄]
      have hc : ¬ ((4 * a + 1) % 4 = 0 ∨ (4 * a + 1) % 4 = 2) := by omega
      simp only [sp, hc, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
  obtain ⟨cQ, eQ, hQ⟩ := h2
  obtain ⟨C₇, s₇, e₇, _, hO₇, hs₇, hp₇, hr₇, hm₇⟩ := sim_step (j := 1) (k := 2) (B := x.length)
    (b := true) (O₀ := []) (S' := S') (by norm_num) (by norm_num) (by simp) (by omega) eQ C₆
    ⟨fun r => by rw [hreg₆ _ (by unfold rl; omega)]; rfl, hmem₆, hJ₆ 1 (Or.inl rfl), hF₆⟩
    ⟨by rw [hp₆]; rfl, fun i hi => absurd hi (by simp), ho₆⟩
    (fun _ => by rw [hQ]; omega)
  rw [hQ] at hO₇
  obtain ⟨hp7, hb7, ho7⟩ := hO₇
  -- stage 2: `R`
  have hreg₇ : ∀ r, C₇.reg (rl 2 r) = (initial (x ++ z)).reg r := by
    intro r
    rw [hr₇ _ (by unfold rl; omega) (rl_ne (by norm_num) r (by decide))
      (rl_ne (by norm_num) r (by decide)), hreg₆ _ (by unfold rl; omega)]; rfl
  have hmem₇ : ∀ a, C₇.mem (4 * a + 2) = (initial (x ++ z)).mem a := by
    -- the input of `R`: `x`, then the buffered output of `Q`
    intro a
    rw [initial_mem]
    by_cases ha : a < x.length
    · rw [hm₇ _ (by omega) (Or.inr (Or.inl (by rw [hp₆]; omega))), hm₆,
        hm₅ _ (by omega) (Or.inl (by omega)), hm₄, getD_append_left' ha]
      have hc : (4 * a + 2) % 4 = 0 ∨ (4 * a + 2) % 4 = 2 := by omega
      simp only [sp, hc, ↓reduceIte]
      congr 1; omega
    · by_cases ha' : a < x.length + z.length
      · rw [getD_append_right'' (by omega), show 4 * a + 2 = 4 * (x.length + (a - x.length)) + 2 by
          omega, hb7 _ (by omega)]
      · rw [hm₇ _ (by omega) (Or.inr (Or.inr (by rw [hp7]; omega))), hm₆,
          hm₅ _ (by omega) (Or.inl (by omega)), hm₄, getD_append_right'' (by omega)]
        have hc : (4 * a + 2) % 4 = 0 ∨ (4 * a + 2) % 4 = 2 := by omega
        simp only [sp, hc, ↓reduceIte]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
          List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  have hJ₇ : C₇.reg (xJ 2) = 2 := by
    rw [hr₇ _ (by decide) (by decide) (by decide)]
    exact hJ₆ 2 (Or.inr rfl)
  have hF₇ : C₇.reg xFour = 4 := by rw [hr₇ _ (by decide) (by decide) (by decide)]; exact hF₆
  obtain ⟨cR, eR, hR⟩ := h3
  obtain ⟨C₈, s₈, e₈, _, hO₈, hs₈, -, -, -⟩ := sim_step (j := 2) (k := 2) (B := 0)
    (b := false) (O₀ := []) (S' := S') (by norm_num) (by norm_num) (by simp) (by omega) eR C₇
    ⟨hreg₇, hmem₇, hJ₇, hF₇⟩ (show C₇.out = [] ++ (initial (x ++ z)).out by simp [ho7])
    (fun h => absurd h (by simp))
  -- the output
  have hout : C₈.out = w := by
    have : C₈.out = [] ++ cR.out := hO₈
    rw [this, hR]; rfl
  refine ⟨s₁ + (1 + (s₃ + (4 + (s₅ + (4 + (s₇ + s₈)))))), ⟨C₈, ?_, hout⟩, ?_⟩
  · exact ExecB.seq (e₁.mono (by omega)) (ExecB.seq e₂ (ExecB.seq e₃ (ExecB.seq e₄ (ExecB.seq e₅
      (ExecB.seq e₆ (ExecB.seq e₇ e₈))))))
  · omega

/-- **The composition theorem, time only** (from `pipe3_spec`: every run is bounded by some
address bound, `Exec.exists_execB`). -/
theorem pipe3_spec_time {lenP P Q R : Stmt} {x y z w : List ℕ} {tL t₁ t₂ t₃ : ℕ}
    (hL : HT lenP (· = initial x) (LenPost x) tL)
    (h1 : Computes P x y t₁) (h2 : Computes Q y z t₂) (h3 : Computes R (x ++ z) w t₃) :
    ∃ t, Computes (pipe3 lenP P Q R) x w t ∧
      t ≤ tL + 12 * x.length + 4 * (t₁ + t₂ + t₃) + 20 := by
  obtain ⟨c₁, s₁, e₁, hp₁, hs₁⟩ := hL _ rfl
  obtain ⟨SL, eB⟩ := Exec.exists_execB e₁
  have hLB : HTB SL lenP (· = initial x) (LenPost x) tL := fun c hc => by
    subst hc; exact ⟨c₁, s₁, eB, hp₁, hs₁⟩
  obtain ⟨S₁, h1'⟩ := Computes.exists_computesIn h1
  obtain ⟨S₂, h2'⟩ := Computes.exists_computesIn h2
  obtain ⟨S₃, h3'⟩ := Computes.exists_computesIn h3
  obtain ⟨t, hc, ht⟩ := pipe3_spec hLB h1' h2' h3'
  exact ⟨t, hc.computes, ht⟩

end STACS2027.Runtimes.Flow
