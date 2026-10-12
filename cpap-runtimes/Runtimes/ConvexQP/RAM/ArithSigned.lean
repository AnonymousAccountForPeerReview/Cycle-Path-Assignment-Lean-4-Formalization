module

public import Runtimes.ConvexQP.RAM.ArithCore
public import Runtimes.ConvexQP.Numeric
import Mathlib.Tactic

/-!
# Big-number arithmetic on the add/subtract RAM: signed integers

A **signed integer** `z` occupies a register pair `(r, r + 1)` (or two memory cells
`a, a + 1`): the sign bit `sgnBit z` (`1` iff `z < 0`) and the magnitude `|z|`; zero is
canonical (sign `0`). `SReg c r z` / `SMem m a z` say so.

The cores of this file work on fixed registers of the library's block:
* `saddCore` (`sZ := sX + sY`), `sflip r` (`r := −r` in place), `sleCore`
  (`sB := [sX ≤ sY]`), all loop-free (`O(1)`);
* `smulCore` (`mZ := mX · mY`, through `gCore`, `O(size |mY| + 1)` steps);
* `sdivCore` (`mZ := mX / mY`, `mRm := mX % mY` with Lean's `Int.ediv`/`Int.emod`, `mY ≠ 0`,
  `O(size |mX| + 1 − size |mY|)` steps);
* `roundCore` (`mZ := roundDiv rU rV = ⌊(2u + v)/(2v)⌋` for `v = reg rV ≥ 1`, `O(size |u| + 1)`
  steps).

**Space**: `saddCore_specB`, `sflip_specB`, `sleCore_specB` (memory-free), `smulCore_specB`
(scratch `2 · size |v|` cells from `rFREE`), `sdivCore_specB` (`2 · entB |v| |u|`),
`roundCore_specB` (`2 · (size |u| + 2)`) are the bounded forms (`HTB S`, hypothesis
`hS : ∀ c, P c → c.reg rFREE + K ≤ S`).

The arithmetic facts behind them: `ediv_eq_natAbs` (`Int.ediv`/`Int.emod` through natural
division of the magnitudes) and `size_round_le` (the bit length of `2u + v` against `2v`).
-/

@[expose] public section

namespace STACS2027.Runtimes.Arith

open STACS2027.RAM

/-! ### Signed values -/

/-- The sign bit of an integer: `1` if negative, `0` otherwise. -/
def sgnBit (z : ℤ) : ℕ := if z < 0 then 1 else 0

/-- The register pair `(r, r + 1)` holds the integer `z`: sign bit and magnitude. -/
def SReg (c : Config) (r : ℕ) (z : ℤ) : Prop := c.reg r = sgnBit z ∧ c.reg (r + 1) = z.natAbs

/-- The memory cells `a, a + 1` hold the integer `z`: sign bit and magnitude. -/
def SMem (m : ℕ → ℕ) (a : ℕ) (z : ℤ) : Prop := m a = sgnBit z ∧ m (a + 1) = z.natAbs

theorem indep_sreg {W : List ℕ} {r : ℕ} (h0 : r ∉ W) (h1 : r + 1 ∉ W) (z : ℤ) :
    Indep W (fun c => SReg c r z) :=
  (Indep.reg h0 (· = sgnBit z)).and (Indep.reg h1 (· = z.natAbs))

theorem regIndep_sreg {W : List ℕ} {r : ℕ} (h0 : r ∉ W) (h1 : r + 1 ∉ W) (z : ℤ) :
    RegIndep W (fun c => SReg c r z) :=
  (RegIndep.reg h0 (· = sgnBit z)).and (RegIndep.reg h1 (· = z.natAbs))

/-- The value of a register pair holding `z`. -/
theorem SReg.eq {c : Config} {r : ℕ} {z : ℤ} (h : SReg c r z) :
    z = if c.reg r = 0 then (c.reg (r + 1) : ℤ) else -(c.reg (r + 1) : ℤ) := by
  obtain ⟨h0, h1⟩ := h
  rw [h0, h1]; unfold sgnBit
  by_cases hz : z < 0 <;> simp only [hz, ↓reduceIte] <;> omega

/-- `SReg` from the two register values, by cases on the sign. -/
theorem sreg_of {c : Config} {r : ℕ} {z : ℤ} (h0 : c.reg r = sgnBit z)
    (h1 : c.reg (r + 1) = z.natAbs) :
    SReg c r z := ⟨h0, h1⟩

theorem sgnBit_le_one (z : ℤ) : sgnBit z ≤ 1 := by unfold sgnBit; split_ifs <;> omega

theorem sgnBit_mul (u v : ℤ) : sgnBit (u * v) =
    if u.natAbs * v.natAbs = 0 then 0 else if sgnBit u = sgnBit v then 0 else 1 := by
  unfold sgnBit
  rcases lt_trichotomy u 0 with hu | rfl | hu <;> rcases lt_trichotomy v 0 with hv | rfl | hv
  · have : 0 < u * v := mul_pos_of_neg_of_neg hu hv
    simp [hu, hv, show ¬ u * v < 0 by omega, show u ≠ 0 by omega, show v ≠ 0 by omega]
  · simp
  · have : u * v < 0 := mul_neg_of_neg_of_pos hu hv
    simp [hu, this, show u ≠ 0 by omega, show v ≠ 0 by omega, show ¬ v < 0 by omega]
  · simp
  · simp
  · simp
  · have : u * v < 0 := mul_neg_of_pos_of_neg hu hv
    simp [hv, this, show u ≠ 0 by omega, show v ≠ 0 by omega, show ¬ u < 0 by omega]
  · simp
  · have : 0 < u * v := mul_pos hu hv
    simp [show ¬ u * v < 0 by omega, show u ≠ 0 by omega, show v ≠ 0 by omega,
      show ¬ u < 0 by omega, show ¬ v < 0 by omega]

/-! ### Registers -/

/-- `saddCore`/`sleCore` input `x` (pair `412, 413`). -/
abbrev sX : ℕ := 412
/-- `saddCore`/`sleCore` input `y` (pair `414, 415`). -/
abbrev sY : ℕ := 414
/-- `saddCore` output (pair `416, 417`). -/
abbrev sZ : ℕ := 416
/-- `sleCore` output: `1` if `x ≤ y`, else `0`. -/
abbrev sB : ℕ := 418
/-- `smulCore`/`sdivCore` input `x` (pair `420, 421`). -/
abbrev mX : ℕ := 420
/-- `smulCore`/`sdivCore` input `y` (pair `422, 423`). -/
abbrev mY : ℕ := 422
/-- `smulCore`/`sdivCore`/`roundCore` output (pair `424, 425`). -/
abbrev mZ : ℕ := 424
/-- `sdivCore` output: the remainder `x % y` (a natural). -/
abbrev mRm : ℕ := 426
/-- `sdivCore` scratch: the magnitude of the quotient. -/
abbrev mQ : ℕ := 427
/-- `roundCore` input `u` (pair `428, 429`). -/
abbrev rU : ℕ := 428
/-- `roundCore` input `v ≥ 1` (a natural). -/
abbrev rV : ℕ := 430

/-! ### Addition, negation, comparison -/

/-- `sZ := sX + sY`. -/
def saddCore : Stmt :=
  .seq (ifEq sX sY
          (.seq (mov sZ sX) (.add (sZ + 1) (sX + 1) (sY + 1)))
          (ifLe (sY + 1) (sX + 1)
             (.seq (mov sZ sX) (.sub (sZ + 1) (sX + 1) (sY + 1)))
             (.seq (mov sZ sY) (.sub (sZ + 1) (sY + 1) (sX + 1)))))
       (.ifz (sZ + 1) (.const sZ 0) .skip)

theorem wregs_saddCore_sub : ∀ r ∈ wregs saddCore, r ∈ [rT, sZ, sZ + 1] := by decide

/-- **Signed addition** (`26` steps). -/
theorem saddCore_spec {P : Config → Prop} (hP : Indep [rT, sZ, sZ + 1] P) (u v : ℤ) :
    HT saddCore (fun c => P c ∧ SReg c sX u ∧ SReg c sY v) (fun c => P c ∧ SReg c sZ (u + v))
      26 := by
  refine HT.run_le (by decide) (by decide) fun c ⟨hc, ⟨hxs, hxm⟩, ⟨hys, hym⟩⟩ => ?_
  refine ⟨(hP.mono wregs_saddCore_sub).run (by decide) rfl rfl hc, ?_, ?_⟩ <;>
  simp +decide only [saddCore, run_seq', run_ifEq, run_ifLe, run_mov, run_add, run_sub,
    run_ifz', run_const, run_skip, setReg_reg, config_ite_reg, ↓reduceIte, hxs, hys, hxm, hym] <;>
  simp only [sgnBit] <;> split_ifs <;> first | contradiction | omega

/-- **Signed addition** within any bound (memory-free). -/
theorem saddCore_specB {S : ℕ} {P : Config → Prop} (hP : Indep [rT, sZ, sZ + 1] P) (u v : ℤ) :
    HTB S saddCore (fun c => P c ∧ SReg c sX u ∧ SReg c sY v)
      (fun c => P c ∧ SReg c sZ (u + v)) 26 :=
  HTB.of_HT rfl (saddCore_spec hP u v)

/-- `r := −r` in place (pair `(r, r + 1)`): flip the sign bit of a nonzero value. -/
def sflip (r : ℕ) : Stmt := .ifz (r + 1) .skip (.seq (.const rT 1) (.sub r rT r))

theorem run_sflip {r : ℕ} (hr : r ≠ rT) {c : Config} {z : ℤ} (h : SReg c r z) :
    run (sflip r) c = if z = 0 then c else (c.setReg rT 1).setReg r (1 - sgnBit z) := by
  obtain ⟨h0, h1⟩ := h
  have : r ≠ r + 1 := by omega
  by_cases hz : z = 0
  · simp [sflip, h1, hz]
  · have : z.natAbs ≠ 0 := by omega
    simp [sflip, h1, hz, this, hr, h0]

/-- **Negation in place** (`4` steps). -/
theorem sflip_spec {P : Config → Prop} {r : ℕ} (hr : r ≠ rT) (hr1 : r + 1 ≠ rT)
    (hP : Indep [rT, r] P) (z : ℤ) :
    HT (sflip r) (fun c => P c ∧ SReg c r z) (fun c => P c ∧ SReg c r (-z)) 4 := by
  refine HT.run_le (by simp [sflip, LoopFree]) (by simp [sflip, size]) fun c ⟨hc, h⟩ => ?_
  rw [run_sflip hr h]
  obtain ⟨h0, h1⟩ := h
  have hne : r + 1 ≠ r := by omega
  by_cases hz : z = 0
  · subst hz; simp only [↓reduceIte]; exact ⟨hc, by simpa using h0, by simpa using h1⟩
  · simp only [hz, ↓reduceIte]
    refine ⟨hP.setReg (by simp) _ (hP.setReg (by simp) _ hc), ?_, ?_⟩
    · simp only [setReg_reg, ↓reduceIte]; unfold sgnBit; split_ifs <;> omega
    · simp only [setReg_reg, hne, ↓reduceIte, hr1, h1, Int.natAbs_neg]

/-- **Negation in place** within any bound (memory-free). -/
theorem sflip_specB {S : ℕ} {P : Config → Prop} {r : ℕ} (hr : r ≠ rT) (hr1 : r + 1 ≠ rT)
    (hP : Indep [rT, r] P) (z : ℤ) :
    HTB S (sflip r) (fun c => P c ∧ SReg c r z) (fun c => P c ∧ SReg c r (-z)) 4 :=
  HTB.of_HT rfl (sflip_spec hr hr1 hP z)

/-- `sB := 1` if `sX ≤ sY`, else `0`. -/
def sleCore : Stmt :=
  .ifz sX
    (.ifz sY (ifLe (sX + 1) (sY + 1) (.const sB 1) (.const sB 0)) (.const sB 0))
    (.ifz sY (.const sB 1) (ifLe (sY + 1) (sX + 1) (.const sB 1) (.const sB 0)))

/-- **Comparison** (`13` steps). -/
theorem sleCore_spec {P : Config → Prop} (hP : Indep [rT, sB] P) (u v : ℤ) :
    HT sleCore (fun c => P c ∧ SReg c sX u ∧ SReg c sY v)
      (fun c => P c ∧ c.reg sB = if u ≤ v then 1 else 0) 13 := by
  refine HT.run_le (by decide) (by decide) fun c ⟨hc, ⟨hxs, hxm⟩, ⟨hys, hym⟩⟩ => ?_
  refine ⟨(hP.mono (by decide)).run (by decide) rfl rfl hc, ?_⟩
  simp +decide only [sleCore, run_ifz', run_ifLe, run_const, setReg_reg, config_ite_reg,
    ↓reduceIte, hxs, hys, hxm, hym]
  simp only [sgnBit]
  split_ifs <;> first | contradiction | omega

/-- **Comparison** within any bound (memory-free). -/
theorem sleCore_specB {S : ℕ} {P : Config → Prop} (hP : Indep [rT, sB] P) (u v : ℤ) :
    HTB S sleCore (fun c => P c ∧ SReg c sX u ∧ SReg c sY v)
      (fun c => P c ∧ c.reg sB = if u ≤ v then 1 else 0) 13 :=
  HTB.of_HT rfl (sleCore_spec hP u v)

/-! ### Multiplication -/

/-- `mZ := mX · mY`. -/
def smulCore : Stmt :=
  .seq (.seq (.const gA0 1) (.seq (mov gB0 (mX + 1)) (mov gL (mY + 1))))
    (.seq gCore (.seq (mov (mZ + 1) gAcc) (.seq (ifEq mX mY (.const mZ 0) (.const mZ 1))
      (.ifz (mZ + 1) (.const mZ 0) .skip))))

/-- The registers written by `smulCore`. -/
def smW : List ℕ := mZ :: (mZ + 1) :: gW

/-- Cost of `smulCore` with multiplier `v`. -/
def smulCost (v : ℤ) : ℕ := gCost (Nat.size v.natAbs) + 20

/-- **Signed multiplication** in `31 · size |v| + 35` steps, within the bound `S` when the scratch
table of `gCore` (`2 · size |v|` cells from `rFREE`) fits below `S` (`hS`). -/
theorem smulCore_specB {S : ℕ} {P : Config → Prop} (hP : Indep smW P)
    (hZ : ∀ c, P c → ZeroFrom c.mem (c.reg rFREE)) (u v : ℤ)
    (hS : ∀ c, P c → c.reg rFREE + 2 * Nat.size v.natAbs ≤ S) :
    HTB S smulCore (fun c => P c ∧ SReg c mX u ∧ SReg c mY v) (fun c => P c ∧ SReg c mZ (u * v))
      (smulCost v) := by
  have hP' : Indep gW (fun c => P c ∧ SReg c mX u ∧ SReg c mY v) :=
    (hP.mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)).and
      ((indep_sreg (by decide) (by decide) u).and (indep_sreg (by decide) (by decide) v))
  have h1 : HTB S (.seq (.const gA0 1) (.seq (mov gB0 (mX + 1)) (mov gL (mY + 1))))
      (fun c => P c ∧ SReg c mX u ∧ SReg c mY v)
      (fun c => (P c ∧ SReg c mX u ∧ SReg c mY v) ∧ (c.reg gA0 = 1 ∧ c.reg gB0 = u.natAbs ∧
        c.reg gL = v.natAbs ∧ 1 ≤ 1)) 5 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => by
      refine ⟨(hP'.mono (by decide)).run (by decide) rfl rfl hc, ?_⟩
      obtain ⟨_, ⟨_, hxm⟩, ⟨_, hym⟩⟩ := hc
      refine ⟨?_, ?_, ?_, le_rfl⟩ <;>
      simp +decide only [run_seq', run_const, run_mov, setReg_reg, ↓reduceIte, hxm, hym]
  have h3 : HTB S (.seq (mov (mZ + 1) gAcc) (.seq (ifEq mX mY (.const mZ 0) (.const mZ 1))
      (.ifz (mZ + 1) (.const mZ 0) .skip)))
      (fun c => (P c ∧ SReg c mX u ∧ SReg c mY v) ∧ (c.reg gAcc = u.natAbs * (v.natAbs / 1) ∧
        c.reg gR = v.natAbs % 1))
      (fun c => P c ∧ SReg c mZ (u * v)) 15 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨hc, ⟨hxs, _⟩, ⟨hys, _⟩⟩,
        hacc, _⟩ => by
      refine ⟨(hP.mono (by decide)).run (by decide) rfl rfl hc, ?_, ?_⟩ <;>
      simp +decide only [run_seq', run_mov, run_ifEq, run_ifz', run_const, run_skip, setReg_reg,
        config_ite_reg, ↓reduceIte, hxs, hys, hacc, Nat.div_one, Int.natAbs_mul, ite_self]
      rw [sgnBit_mul]
  have hent : entB 1 v.natAbs = Nat.size v.natAbs := by simp [entB, Nat.size_one]
  refine (h1.seq ((gCore_frameB hP' (fun c h => hZ c h.1) 1 u.natAbs v.natAbs
    (fun c h => by rw [hent]; exact hS c h.1)).seq h3)).weaken ?_
  simp only [entB, Nat.size_one, Nat.add_sub_cancel, smulCost]
  omega

/-! ### Division (`Int.ediv`, `Int.emod`) -/

/-- The magnitude of `u / b` (`Int.ediv`, `b > 0`): `⌊|u|/b⌋`, plus one for a negative `u`
with a nonzero remainder. -/
def qMag (u : ℤ) (b : ℕ) : ℕ :=
  if 0 ≤ u ∨ u.natAbs % b = 0 then u.natAbs / b else u.natAbs / b + 1

/-- `u % b` (`Int.emod`, `b > 0`) as a natural. -/
def rNat (u : ℤ) (b : ℕ) : ℕ :=
  if 0 ≤ u ∨ u.natAbs % b = 0 then u.natAbs % b else b - u.natAbs % b

theorem ediv_pos_aux (u : ℤ) (b : ℕ) (hb : 0 < b) :
    u / (b : ℤ) = (if 0 ≤ u then (qMag u b : ℤ) else -(qMag u b : ℤ)) ∧
      u % (b : ℤ) = (rNat u b : ℤ) := by
  have h1 := Nat.mod_add_div u.natAbs b
  have h2 := Nat.mod_lt u.natAbs hb
  have hbI : (0 : ℤ) < b := by exact_mod_cast hb
  simp only [qMag, rNat]
  rw [Int.ediv_emod_unique hbI]
  set a := u.natAbs
  set q := a / b
  set r := a % b
  have h1' : (r : ℤ) + b * q = a := by exact_mod_cast h1
  have h2' : (r : ℤ) < b := by exact_mod_cast h2
  by_cases hu : 0 ≤ u
  · have ha : (a : ℤ) = u := by omega
    simp only [hu, true_or, ↓reduceIte]
    refine ⟨by linarith, by positivity, h2'⟩
  · have ha : (a : ℤ) = -u := by omega
    by_cases hr : r = 0
    · simp only [hu, hr, or_true, ↓reduceIte]
      rw [hr] at h1'
      push_cast at h1' ⊢
      exact ⟨by linarith, trivial, hbI⟩
    · simp only [hu, hr, or_false, ↓reduceIte]
      have h3 : r ≤ b := h2.le
      have h4 : (0:ℤ) < r := by exact_mod_cast Nat.pos_of_ne_zero hr
      push_cast [h3]
      refine ⟨by linarith, by linarith, by linarith⟩

/-- **`Int.ediv` and `Int.emod` through natural division of the magnitudes.** -/
theorem ediv_eq_natAbs (u v : ℤ) (hv : v ≠ 0) :
    u / v = (if (u < 0 ↔ v < 0) then (qMag u v.natAbs : ℤ) else -(qMag u v.natAbs : ℤ)) ∧
      u % v = (rNat u v.natAbs : ℤ) := by
  obtain ⟨b, hb, rfl | rfl⟩ : ∃ b : ℕ, 0 < b ∧ (v = b ∨ v = -b) :=
    ⟨v.natAbs, Int.natAbs_pos.mpr hv, by omega⟩
  · obtain ⟨h1, h2⟩ := ediv_pos_aux u b hb
    simp only [Int.natAbs_natCast, h1, h2, and_true]
    by_cases hu : u < 0
    · simp [hu, show ¬ (0 ≤ u) by omega]
    · simp [hu, show (0 ≤ u) by omega]
  · obtain ⟨h1, h2⟩ := ediv_pos_aux u b hb
    simp only [Int.natAbs_neg, Int.natAbs_natCast, Int.ediv_neg, Int.emod_neg, h1, h2, and_true]
    have hb' : b ≠ 0 := by omega
    by_cases hu : u < 0
    · simp [hu, hb', show ¬ (0 ≤ u) by omega]
    · simp [hu, hb', show (0 ≤ u) by omega]

/-- `sdivCore`, part 1: `gCore` with `a₀ = |mY|`, `b₀ = 1`, `L = |mX|`. -/
def sdivPre : Stmt := .seq (.const gB0 1) (.seq (mov gA0 (mY + 1)) (mov gL (mX + 1)))

/-- `sdivCore`, part 3: from `⌊|x|/|y|⌋` and `|x| % |y|` to `Int.ediv`, `Int.emod`. -/
def sdivFix : Stmt :=
  .seq (mov mQ gAcc) (.seq (mov mRm gR) (.seq
    (.ifz mX .skip (.ifz mRm .skip (.seq (inc mQ) (.sub mRm (mY + 1) mRm))))
    (.seq (ifEq mX mY (.const mZ 0) (.const mZ 1)) (.seq (mov (mZ + 1) mQ)
      (.ifz (mZ + 1) (.const mZ 0) .skip)))))

/-- `mZ := mX / mY`, `mRm := mX % mY` (`Int.ediv`, `Int.emod`; `mY ≠ 0`). -/
def sdivCore : Stmt := .seq sdivPre (.seq gCore sdivFix)

/-- The registers written by `sdivCore`. -/
def sdW : List ℕ := mZ :: (mZ + 1) :: mRm :: mQ :: gW

/-- Cost of `sdivCore` for `u / v`. -/
def sdivCost (u v : ℤ) : ℕ := gCost (entB v.natAbs u.natAbs) + 28

theorem sdivFix_run {c : Config} {u v : ℤ} (hv : v ≠ 0) (hxs : c.reg mX = sgnBit u)
    (hys : c.reg mY = sgnBit v) (hym : c.reg (mY + 1) = v.natAbs)
    (hacc : c.reg gAcc = 1 * (u.natAbs / v.natAbs)) (hr : c.reg gR = u.natAbs % v.natAbs) :
    SReg (run sdivFix c) mZ (u / v) ∧ ((run sdivFix c).reg mRm : ℤ) = u % v := by
  obtain ⟨e1, e2⟩ := ediv_eq_natAbs u v hv
  have hb : 0 < v.natAbs := Int.natAbs_pos.mpr hv
  have hr0 : u.natAbs % v.natAbs < v.natAbs := Nat.mod_lt _ hb
  rw [e1, e2]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;>
  simp +decide only [sdivFix, run_seq', run_mov, run_ifEq, run_ifz', run_const, run_skip,
    run_inc, run_sub, setReg_reg, config_ite_reg, ↓reduceIte, hxs, hys, hym, hacc, hr,
    Nat.one_mul] <;>
  simp only [sgnBit, qMag, rNat] <;>
  split_ifs <;> first | contradiction | omega

/-- **Signed division** (`Int.ediv`/`Int.emod`, `v ≠ 0`) in
`31 · (size |u| + 1 − size |v|) + 43` steps, within the bound `S` when the scratch table of
`gCore` (`2 · entB |v| |u| = 2 · (size |u| + 1 − size |v|)` cells from `rFREE`) fits below `S`. -/
theorem sdivCore_specB {S : ℕ} {P : Config → Prop} (hP : Indep sdW P)
    (hZ : ∀ c, P c → ZeroFrom c.mem (c.reg rFREE)) (u v : ℤ) (hv : v ≠ 0)
    (hS : ∀ c, P c → c.reg rFREE + 2 * entB v.natAbs u.natAbs ≤ S) :
    HTB S sdivCore (fun c => P c ∧ SReg c mX u ∧ SReg c mY v)
      (fun c => P c ∧ SReg c mZ (u / v) ∧ (c.reg mRm : ℤ) = u % v) (sdivCost u v) := by
  have hP' : Indep gW (fun c => P c ∧ SReg c mX u ∧ SReg c mY v) :=
    (hP.mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))).and
      ((indep_sreg (by decide) (by decide) u).and (indep_sreg (by decide) (by decide) v))
  have h1 : HTB S sdivPre (fun c => P c ∧ SReg c mX u ∧ SReg c mY v)
      (fun c => (P c ∧ SReg c mX u ∧ SReg c mY v) ∧ (c.reg gA0 = v.natAbs ∧ c.reg gB0 = 1 ∧
        c.reg gL = u.natAbs ∧ 1 ≤ v.natAbs)) 5 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => by
      refine ⟨(hP'.mono (by decide)).run (by decide) rfl rfl hc, ?_⟩
      obtain ⟨_, ⟨_, hxm⟩, ⟨_, hym⟩⟩ := hc
      refine ⟨?_, ?_, ?_, Int.natAbs_pos.mpr hv⟩ <;>
      simp +decide only [sdivPre, run_seq', run_const, run_mov, setReg_reg, ↓reduceIte, hxm, hym]
  have h3 : HTB S sdivFix (fun c => (P c ∧ SReg c mX u ∧ SReg c mY v) ∧
        (c.reg gAcc = 1 * (u.natAbs / v.natAbs) ∧ c.reg gR = u.natAbs % v.natAbs))
      (fun c => P c ∧ SReg c mZ (u / v) ∧ (c.reg mRm : ℤ) = u % v) 23 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨hc, ⟨hxs, _⟩, ⟨hys, hym⟩⟩, hacc,
        hr⟩ =>
      ⟨(hP.mono (by decide)).run (by decide) rfl rfl hc, sdivFix_run hv hxs hys hym hacc hr⟩
  refine (h1.seq ((gCore_frameB hP' (fun c h => hZ c h.1) v.natAbs 1 u.natAbs
    (fun c h => hS c h.1)).seq h3)).weaken ?_
  simp only [sdivCost]
  omega

/-! ### Rounded division -/

/-- The bit length of `2u + v` against that of `2v` (`v ≥ 1`): the division of `roundCore`
has at most `size |u| + 2` table entries. -/
theorem size_round_le (u : ℤ) {v : ℕ} (hv : 1 ≤ v) :
    entB (2 * v) (2 * u + v).natAbs ≤ Nat.size u.natAbs + 2 := by
  unfold entB
  have h1 := Nat.lt_size_self u.natAbs
  have h2 := Nat.lt_size_self v
  have h3 : (2 * u + v).natAbs ≤ 2 * u.natAbs + v := by omega
  obtain ⟨M, hM1, hM2, hM⟩ : ∃ M, Nat.size u.natAbs + 1 ≤ M ∧ Nat.size v ≤ M ∧
      (M = Nat.size u.natAbs + 1 ∨ M = Nat.size v) :=
    ⟨max (Nat.size u.natAbs + 1) (Nat.size v), le_max_left _ _, le_max_right _ _, by omega⟩
  have h4 : 2 ^ (Nat.size u.natAbs + 1) ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) hM1
  have h5 : 2 ^ (Nat.size v) ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) hM2
  have h6 : (2 * u + v).natAbs < 2 ^ (M + 1) := by
    rw [pow_succ] at h4 ⊢; omega
  have h7 : Nat.size (2 * u + v).natAbs ≤ M + 1 := Nat.size_le.mpr h6
  have h8 : 2 ^ (Nat.size v) ≤ 2 * v := by
    have := pow_size_pred_le hv
    have hs := Nat.size_pos.mpr hv
    calc 2 ^ Nat.size v = 2 * 2 ^ (Nat.size v - 1) := by rw [← pow_succ']; congr 1; omega
      _ ≤ 2 * v := by omega
  have h9 : Nat.size v < Nat.size (2 * v) := Nat.lt_size.mpr h8
  omega

/-- `roundCore`, part 1: `mX := 2u + v`, `mY := 2v`. -/
def roundPre : Stmt :=
  .seq (.add (mX + 1) (rU + 1) (rU + 1))
  (.seq (.ifz rU (.seq (.const mX 0) (.add (mX + 1) (mX + 1) rV))
           (ifLe (mX + 1) rV (.seq (.const mX 0) (.sub (mX + 1) rV (mX + 1)))
                             (.seq (.const mX 1) (.sub (mX + 1) (mX + 1) rV))))
  (.seq (.const mY 0) (.add (mY + 1) rV rV)))

/-- `mZ := roundDiv rU rV = ⌊(2u + v)/(2v)⌋` (`rV ≥ 1`). -/
def roundCore : Stmt := .seq roundPre sdivCore

/-- The registers written by `roundCore`. -/
def rdW : List ℕ := mX :: (mX + 1) :: mY :: (mY + 1) :: sdW

/-- Cost of `roundCore` for `roundDiv u v`. -/
def roundCost (u : ℤ) : ℕ := gCost (Nat.size u.natAbs + 2) + 40

theorem roundPre_run {c : Config} {u : ℤ} {v : ℕ} (hv : 1 ≤ v) (hu : SReg c rU u)
    (hrv : c.reg rV = v) :
    SReg (run roundPre c) mX (2 * u + v) ∧ SReg (run roundPre c) mY (2 * (v : ℤ)) := by
  obtain ⟨hus, hum⟩ := hu
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
  simp +decide only [roundPre, run_seq', run_add, run_ifz', run_const, run_ifLe, run_sub,
    setReg_reg, config_ite_reg, ↓reduceIte, hus, hum, hrv] <;>
  simp only [sgnBit] <;> split_ifs <;> first | contradiction | omega

/-- **Rounded division** `roundDiv u v = ⌊(2u + v)/(2v)⌋` (`v ≥ 1`) in
`31 · size |u| + 117` steps, within the bound `S` when `2 · (size |u| + 2)` cells from `rFREE`
(the scratch table of the division) fit below `S`. -/
theorem roundCore_specB {S : ℕ} {P : Config → Prop} (hP : Indep rdW P)
    (hZ : ∀ c, P c → ZeroFrom c.mem (c.reg rFREE)) (u : ℤ) (v : ℕ) (hv : 1 ≤ v)
    (hS : ∀ c, P c → c.reg rFREE + 2 * (Nat.size u.natAbs + 2) ≤ S) :
    HTB S roundCore (fun c => P c ∧ SReg c rU u ∧ c.reg rV = v)
      (fun c => P c ∧ SReg c mZ (ConvexQP.roundDiv u v)) (roundCost u) := by
  have h1 : HTB S roundPre (fun c => P c ∧ SReg c rU u ∧ c.reg rV = v)
      (fun c => P c ∧ SReg c mX (2 * u + v) ∧ SReg c mY (2 * (v : ℤ))) 12 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hc, hu, hrv⟩ =>
      ⟨(hP.mono (by decide)).run (by decide) rfl rfl hc, roundPre_run hv hu hrv⟩
  have hsz := size_round_le u hv
  have e : (2 * (v : ℤ)).natAbs = 2 * v := by omega
  have h2 := sdivCore_specB (S := S) (P := P) (hP.mono fun r hr => by
      simp only [rdW, List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr hr)))) hZ
    (2 * u + v) (2 * (v : ℤ)) (by omega) (fun c h => by rw [e]; have := hS c h; omega)
  refine (h1.seq h2).mono (fun _ h => h) (fun c ⟨hc, hz, _⟩ => ⟨hc, hz⟩) ?_
  simp only [sdivCost, roundCost, gCost, e] at hsz ⊢
  omega

end STACS2027.Runtimes.Arith
