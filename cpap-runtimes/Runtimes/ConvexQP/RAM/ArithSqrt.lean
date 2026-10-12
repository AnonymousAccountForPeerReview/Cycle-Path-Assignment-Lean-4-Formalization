module

public import Runtimes.ConvexQP.RAM.ArithCore
import Mathlib.Tactic

/-!
# Big-number arithmetic on the add/subtract RAM: the integer square root

`isqrtCore` (registers `431–435`, calling `pow2Core` and `gCore`) computes
`reg qR := Nat.sqrt (reg qN)` bit by bit from the top: with `h = size N` (found by doubling),
`R := 0`, and for `j = h − 1, …, 0`: `T := R + 2^j` (`pow2Core`), `T² ` (`gCore` as a
multiplication), and `R := T` if `T² ≤ N`. Invariant: `R² ≤ N < (R + 2^j)²`; at `j = 0` this
characterises `R = ⌊√N⌋` (`Nat.eq_sqrt`). Each round costs `O(h)` steps (the power of two and the
product of `(h+1)`-bit numbers), so the whole costs `O((size N + 1)²)` steps
(`isqrtCost_le : isqrtCost N ≤ 40 · (size N + 1)²`). The memory is unchanged (the scratch table
of `gCore` is zeroed again). Bounded form: `isqrtCore_specB` (scratch `2 · (size N + 1)` cells
from `rFREE` below `S`).
-/

@[expose] public section

namespace STACS2027.Runtimes.Arith

open STACS2027.RAM

/-! ### Registers and program -/

/-- `isqrtCore` input `N`. -/
abbrev qN : ℕ := 431
/-- `isqrtCore` output `⌊√N⌋` (the running root `R`). -/
abbrev qR : ℕ := 432
/-- `isqrtCore`: the bit index. -/
abbrev qJ : ℕ := 433
/-- `isqrtCore`: the candidate `T = R + 2^j`. -/
abbrev qT : ℕ := 434
/-- `isqrtCore`: the doubling power. -/
abbrev qH : ℕ := 435

/-- The registers written by `isqrtCore`. -/
def sqW : List ℕ := qR :: qJ :: qT :: qH :: gW

/-- Doubling test: `rT ≠ 0` iff `2^j ≤ N`. -/
def qCond : Stmt := .seq (addc rT qN 1) (.sub rT rT qH)
/-- Doubling step. -/
def qBody : Stmt := .seq (.add qH qH qH) (inc qJ)

/-- One bit: `j := j − 1`, `T := R + 2^j`, `R := T` if `T² ≤ N`. -/
def qStep : Stmt :=
  .seq (.seq (dec qJ) (mov pE qJ)) (.seq pow2Core
    (.seq (.seq (.add qT qR pR) (.seq (.const gA0 1) (.seq (mov gB0 qT) (mov gL qT))))
      (.seq gCore (ifLe gAcc qN (mov qR qT) .skip))))

/-- `qR := ⌊√(reg qN)⌋`. -/
def isqrtCore : Stmt :=
  .seq (.seq (.const qH 1) (.const qJ 0)) (.seq (whileC qCond qBody) (.seq (.const qR 0)
    (.loop qJ qStep)))

/-- The cost of one bit for `h = size N`. -/
def qStepCost (h : ℕ) : ℕ := 4 * h + gCost (h + 1) + 17

/-- The cost of `isqrtCore` for `h = size N`. -/
def isqrtCost (N : ℕ) : ℕ :=
  Nat.size N * (qStepCost (Nat.size N) + 1) + 7 * Nat.size N + 8

theorem isqrtCost_le (N : ℕ) : isqrtCost N ≤ 40 * (Nat.size N + 1) ^ 2 := by
  unfold isqrtCost qStepCost gCost
  nlinarith

/-! ### One bit -/

/-- The frame of a bit step: everything but the scratch registers. -/
def QF (P : Config → Prop) (N R j : ℕ) (c : Config) : Prop :=
  P c ∧ c.reg qN = N ∧ c.reg qR = R ∧ c.reg qJ = j

theorem qStep_specB {S : ℕ} {P : Config → Prop} (hP : Indep sqW P)
    (hZ : ∀ c, P c → ZeroFrom c.mem (c.reg rFREE)) (N R j : ℕ) (hR : R * R ≤ N)
    (hj : j < Nat.size N) (hS : ∀ c, P c → c.reg rFREE + 2 * (Nat.size N + 1) ≤ S) :
    HTB S qStep (QF P N R (j + 1))
      (QF P N (if (R + 2 ^ j) * (R + 2 ^ j) ≤ N then R + 2 ^ j else R) j)
      (qStepCost (Nat.size N)) := by
  have hF : ∀ j', Indep gW (QF P N R j') := fun j' =>
    (hP.mono fun r hr => by simp only [sqW, List.mem_cons] at hr ⊢; tauto).and
      ((Indep.reg (show qN ∉ gW by decide) (· = N)).and ((Indep.reg (show qR ∉ gW by decide)
        (· = R)).and (Indep.reg (show qJ ∉ gW by decide) (· = j'))))
  have hA : HTB S (.seq (dec qJ) (mov pE qJ)) (QF P N R (j + 1))
      (fun c => QF P N R j c ∧ c.reg pE = j) 4 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hc, hN, hR', hJ⟩ => by
      refine ⟨⟨(hP.mono (by decide)).run (by decide) rfl rfl hc, ?_, ?_, ?_⟩, ?_⟩ <;>
      simp +decide only [run_seq', run_dec, run_mov, setReg_reg, ↓reduceIte, hN, hR', hJ,
        Nat.add_sub_cancel]
  have hB := pow2Core_specB (S := S) (P := QF P N R j) ((hF j).mono (by decide)) j
  have hC : HTB S (.seq (.add qT qR pR) (.seq (.const gA0 1) (.seq (mov gB0 qT) (mov gL qT))))
      (fun c => QF P N R j c ∧ c.reg pR = 2 ^ j)
      (fun c => (QF P N R j c ∧ c.reg qT = R + 2 ^ j) ∧ (c.reg gA0 = 1 ∧
        c.reg gB0 = R + 2 ^ j ∧ c.reg gL = R + 2 ^ j ∧ 1 ≤ 1)) 6 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨hc, hN, hR', hJ⟩, hp⟩ => by
      refine ⟨⟨⟨(hP.mono (by decide)).run (by decide) rfl rfl hc, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_,
        le_rfl⟩ <;>
      simp +decide only [run_seq', run_add, run_const, run_mov, setReg_reg, ↓reduceIte, hN, hR',
        hJ, hp]
  -- the size of the candidate
  have hNs := Nat.lt_size_self N
  have hRle : R ≤ N := le_trans (Nat.le_mul_self R) hR
  have hpj : 2 ^ j ≤ 2 ^ (Nat.size N) := Nat.pow_le_pow_right (by norm_num) hj.le
  have hTs : Nat.size (R + 2 ^ j) ≤ Nat.size N + 1 :=
    Nat.size_le.mpr (by rw [pow_succ]; omega)
  have hD := gCore_frameB (S := S) (P := fun c => QF P N R j c ∧ c.reg qT = R + 2 ^ j)
    ((hF j).and (Indep.reg (show qT ∉ gW by decide) (· = R + 2 ^ j))) (fun c h => hZ c h.1.1) 1
    (R + 2 ^ j) (R + 2 ^ j) (fun c h => by
      have := hS c h.1.1
      simp only [entB, Nat.size_one, Nat.add_sub_cancel]
      omega)
  have hE : HTB S (ifLe gAcc qN (mov qR qT) .skip)
      (fun c => (QF P N R j c ∧ c.reg qT = R + 2 ^ j) ∧
        (c.reg gAcc = (R + 2 ^ j) * ((R + 2 ^ j) / 1) ∧ c.reg gR = (R + 2 ^ j) % 1))
      (QF P N (if (R + 2 ^ j) * (R + 2 ^ j) ≤ N then R + 2 ^ j else R) j) 5 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨⟨hc, hN, hR', hJ⟩, hT⟩, hacc, _⟩ =>
        by
      rw [Nat.div_one] at hacc
      refine ⟨(hP.mono (by decide)).run (by decide) rfl rfl hc, ?_, ?_, ?_⟩ <;>
      simp +decide only [run_ifLe, run_mov, run_skip, setReg_reg, config_ite_reg, ↓reduceIte,
        hN, hR', hJ, hT, hacc, ite_self]
  refine (hA.seq (hB.seq (hC.seq (hD.seq hE)))).weaken ?_
  simp only [entB, Nat.size_one, Nat.add_sub_cancel, qStepCost, gCost]
  omega

/-! ### The whole -/

/-- The state after a doubling test. -/
def QD (P : Config → Prop) (N : ℕ) (c : Config) : Prop :=
  P c ∧ c.reg qN = N ∧ c.reg qH = 2 ^ c.reg qJ ∧ c.reg rT = N + 1 - 2 ^ c.reg qJ ∧
    c.reg qJ ≤ Nat.size N

/-- The state before a bit step. -/
def QI (P : Config → Prop) (N : ℕ) (c : Config) : Prop :=
  P c ∧ c.reg qN = N ∧ c.reg qR * c.reg qR ≤ N ∧
    N < (c.reg qR + 2 ^ c.reg qJ) * (c.reg qR + 2 ^ c.reg qJ) ∧ c.reg qJ ≤ Nat.size N

/-- **Integer square root** `qR := Nat.sqrt N` in `isqrtCost N ≤ 40 (size N + 1)²` steps, within
the bound `S` when the scratch table of the squarings (`2 · (size N + 1)` cells from `rFREE`)
fits below `S`. -/
theorem isqrtCore_specB {S : ℕ} {P : Config → Prop} (hP : Indep sqW P)
    (hZ : ∀ c, P c → ZeroFrom c.mem (c.reg rFREE)) (N : ℕ)
    (hS : ∀ c, P c → c.reg rFREE + 2 * (Nat.size N + 1) ≤ S) :
    HTB S isqrtCore (fun c => P c ∧ c.reg qN = N) (fun c => P c ∧ c.reg qR = Nat.sqrt N)
      (isqrtCost N) := by
  have h0 : HTB S (.seq (.const qH 1) (.const qJ 0)) (fun c => P c ∧ c.reg qN = N)
      (fun c => P c ∧ c.reg qN = N ∧ c.reg qH = 1 ∧ c.reg qJ = 0) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hc, hN⟩ => by
      refine ⟨(hP.mono (by decide)).run (by decide) rfl rfl hc, ?_, ?_, ?_⟩ <;>
      simp +decide only [run_seq', run_const, setReg_reg, ↓reduceIte, hN]
  have hc0 : HTB S qCond (fun c => P c ∧ c.reg qN = N ∧ c.reg qH = 1 ∧ c.reg qJ = 0)
      (fun c => QD P N c ∧ Nat.size N - c.reg qJ ≤ Nat.size N) 3 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hc, hN, hH, hJ⟩ => by
      refine ⟨⟨(hP.mono (by decide)).run (by decide) rfl rfl hc, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      simp +decide only [qCond, run_seq', run_addc, run_sub, setReg_reg, ↓reduceIte, hN, hH, hJ,
        pow_zero] <;> omega
  have hstep : ∀ v, HTB S (.seq qBody qCond)
      (fun c => QD P N c ∧ c.reg rT ≠ 0 ∧ Nat.size N - c.reg qJ = v)
      (fun c => QD P N c ∧ Nat.size N - c.reg qJ < v) 6 := fun v =>
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨hc, hN, hH, ht, hJ⟩, hne, hv⟩ => by
      have hle : 2 ^ c.reg qJ ≤ N := by omega
      have hlt : c.reg qJ < Nat.size N := Nat.lt_size.mpr hle
      refine ⟨⟨(hP.mono (by decide)).run (by decide) rfl rfl hc, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      simp +decide only [qBody, qCond, run_seq', run_add, run_inc, run_addc, run_sub, setReg_reg,
        ↓reduceIte, hN, hH, pow_succ] <;> omega
  have hw := HTB.whileC (cond := qCond) (body := qBody) (fun c => Nat.size N - c.reg qJ) hc0 hstep
  have hm : HTB S (.const qR 0) (fun c => QD P N c ∧ c.reg rT = 0)
      (fun c => QI P N c ∧ c.reg qJ ≤ Nat.size N) 1 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨hc, hN, _, ht, hJ⟩, h0⟩ => by
      have hlt : N < 2 ^ c.reg qJ := by omega
      have : 2 ^ c.reg qJ ≤ 2 ^ c.reg qJ * 2 ^ c.reg qJ :=
        Nat.le_mul_of_pos_right _ Nat.one_le_two_pow
      refine ⟨⟨(hP.mono (by decide)).run (by decide) rfl rfl hc, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      simp +decide only [run_const, setReg_reg, ↓reduceIte, hN, Nat.zero_add, Nat.zero_mul,
        Nat.zero_le] <;> omega
  have hl := HTB.loopT (a := qJ) (body := qStep) (Inv := QI P N) (fun c => c.reg qJ)
    (T := qStepCost (Nat.size N)) (fun v c ⟨⟨hc, hN, hR, hRN, hJ⟩, hne, hv⟩ => by
      obtain ⟨j, hj⟩ : ∃ j, c.reg qJ = j + 1 := ⟨c.reg qJ - 1, by omega⟩
      obtain ⟨c', t, he, ⟨hc', hN', hR', hJ'⟩, ht⟩ :=
        qStep_specB hP hZ N (c.reg qR) j hR (by omega) hS c ⟨hc, hN, rfl, hj⟩
      refine ⟨c', t, he, ⟨⟨hc', hN', ?_, ?_, by omega⟩, by omega⟩, ht⟩
      · rw [hR']; split_ifs with h
        · exact h
        · exact hR
      · rw [hR', hJ']
        rw [hj, pow_succ] at hRN
        split_ifs with h
        · have e : c.reg qR + 2 ^ j + 2 ^ j = c.reg qR + 2 ^ j * 2 := by ring
          rw [e]; exact hRN
        · exact Nat.lt_of_not_le h) (Nat.size N)
  refine (h0.seq (hw.seq (hm.seq hl))).mono (fun _ h => h) (fun c ⟨⟨hc, _, hR, hRN, _⟩, h0⟩ => ?_)
    (by unfold isqrtCost; ring_nf; omega)
  refine ⟨hc, ?_⟩
  rw [h0, pow_zero] at hRN
  exact (Nat.eq_sqrt.mpr ⟨hR, hRN⟩)

end STACS2027.Runtimes.Arith
