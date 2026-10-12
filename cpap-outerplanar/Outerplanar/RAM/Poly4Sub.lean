module

public import Outerplanar.RAM.Poly4Spec
import Mathlib.Tactic

/-!
# Phase P4 of the polygon solver: the sub-programs

Registers of phase P4 (all at or above `gPx`) and its sub-programs, with specifications that
do not mention the polygon:

* `divmod`: `rDX, rDQ := rDX % k, rDX / k` by repeated subtraction (`divmod_spec`,
  `7 x + 5` steps);
* `decode`: the `L` lowest base-`k` digits of `rDX` written at `rDB` (`decode_spec`: the
  memory becomes `wr m b (cfg k L x)`);
* `lookup`: the digit `lkp l ds ts te vv i` of the pool index `rI` — its digit in the decoded
  configuration `ds` (at `rAD`) if it is in the list `l` (at `gBIDX + rBO`, duplicate-free),
  else the value stored at `rVAL + i` if `ts ≤ i < te`, else `0` (`lookup_spec`);
* `child`: for the child of the slot `rQ` of the face at `rFO`, its index `jw` through the
  slot id `FSID[rFO + rQ]`, its boundary list `lw` (through `gBOFF`, `gBIDX`), the number
  `enc k (lw.map dig)` of the digits found by `lookup`, stored at `rA + jw` (`child_spec`).

`divmod` is memory-free (an `HT` triple); the others are bounded triples (`HTB S`), with the
addresses they access below `S` as hypotheses (`LkBnd S E` for `lookup`).
-/

@[expose] public section

namespace STACS2027.RAM.P4

open STACS2027.Poly

/-! ### Registers -/

/-- `k`. -/
abbrev rK : ℕ := 84
/-- Base of the configurations `A` passed to the segments. -/
abbrev rA : ℕ := 86
/-- Base of the values `valOf` of the pool cycles. -/
abbrev rVAL : ℕ := 87
/-- Counter of the backtracking loop. -/
abbrev rJ : ℕ := 88
/-- The index of the current segment in `segOrder`. -/
abbrev rM : ℕ := 89
/-- `α`. -/
abbrev rAL : ℕ := 90
/-- `β`. -/
abbrev rBE : ℕ := 91
/-- Offset of the boundary list of the current segment. -/
abbrev rBO : ℕ := 92
/-- Number of its boundary cycles. -/
abbrev rNB : ℕ := 93
/-- Start of its top cycles. -/
abbrev rTS : ℕ := 94
/-- End of its top cycles. -/
abbrev rTE : ℕ := 95
/-- Base of the digits of `α`. -/
abbrev rAD : ℕ := 96
/-- Offset of its face. -/
abbrev rFO : ℕ := 97
/-- Number of its slots. -/
abbrev rNSL : ℕ := 98
/-- Slot counter. -/
abbrev rQ : ℕ := 99
/-- First end of the slot. -/
abbrev rX : ℕ := 100
/-- Second end of the slot. -/
abbrev rY : ℕ := 101
/-- Index of the child. -/
abbrev rJW : ℕ := 102
/-- Offset of the boundary list of the child. -/
abbrev rBW : ℕ := 103
/-- Number of boundary cycles of the child. -/
abbrev rNW : ℕ := 104
/-- The accumulated configuration of the child. -/
abbrev rACC : ℕ := 105
/-- The power of `k`. -/
abbrev rPW : ℕ := 106
/-- Digit counter. -/
abbrev rQ2 : ℕ := 107
/-- The pool index looked up. -/
abbrev rI : ℕ := 108
/-- The digit found. -/
abbrev rD : ℕ := 109
/-- Found flag. -/
abbrev rF : ℕ := 110
/-- Scan counter. -/
abbrev rP : ℕ := 111
/-- Scan temporary. -/
abbrev rZ : ℕ := 112
/-- Product. -/
abbrev rTMP : ℕ := 113
/-- Multiplication counter. -/
abbrev rMC : ℕ := 114
/-- Temporary. -/
abbrev rTN : ℕ := 115
/-- Decoding: the number. -/
abbrev rDX : ℕ := 116
/-- Decoding: the number of digits. -/
abbrev rDL : ℕ := 117
/-- Decoding: the base of the digits. -/
abbrev rDB : ℕ := 118
/-- Decoding: digit counter. -/
abbrev rDT : ℕ := 119
/-- Decoding: quotient. -/
abbrev rDQ : ℕ := 120

/-! ### Division by repeated subtraction -/

/-- The test `rDX ≥ k`: `rT := rDX + 1 - k`. -/
def dmCond : Stmt := .seq (.const rT 1) (.seq (.add rT rDX rT) (.sub rT rT rK))
/-- One subtraction. -/
def dmBody : Stmt := .seq (.sub rDX rDX rK) (inc rDQ)
/-- `rDX, rDQ := rDX % k, rDX / k`. -/
def divmod : Stmt := .seq (.const rDQ 0) (whileC dmCond dmBody)

/-- The invariant of the division. -/
def DmInv (k x : ℕ) (c : Config) : Prop :=
  c.reg rK = k ∧ c.reg rDX + k * c.reg rDQ = x ∧ c.reg rT = c.reg rDX + 1 - k

/-- **Division** by repeated subtraction. -/
theorem divmod_spec {k x : ℕ} (hk : 0 < k) :
    HT divmod (fun c => c.reg rDX = x ∧ c.reg rK = k)
      (fun c => c.reg rDX = x % k ∧ c.reg rDQ = x / k) (7 * x + 5) := by
  have hc : HT (.const rDQ 0) (fun c => c.reg rDX = x ∧ c.reg rK = k)
      (fun c => c.reg rDX = x ∧ c.reg rK = k ∧ c.reg rDQ = 0) 1 :=
    HT.run_le (by decide) (by decide) fun c ⟨h1, h2⟩ => by simp +decide [h1, h2]
  have hinit : HT dmCond (fun c => c.reg rDX = x ∧ c.reg rK = k ∧ c.reg rDQ = 0)
      (fun c => DmInv k x c ∧ c.reg rDX ≤ x) 3 :=
    HT.run_le (by decide) (by decide) fun c ⟨h1, h2, h3⟩ => by
      simp +decide [dmCond, DmInv, h1, h2, h3]
  have hstep : ∀ v, HT (.seq dmBody dmCond) (fun c => DmInv k x c ∧ c.reg rT ≠ 0 ∧ c.reg rDX = v)
      (fun c => DmInv k x c ∧ c.reg rDX < v) 6 := fun v =>
    HT.run_le (by decide) (by decide) fun c ⟨⟨h1, h2, h3⟩, h4, h5⟩ => by
      simp +decide only [dmBody, dmCond, DmInv, run_seq', run_sub, run_inc (show rDQ ≠ rT by decide),
        run_const, run_add, setReg_reg, ↓reduceIte, h1, true_and]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [Nat.mul_add, Nat.mul_one]; omega
      · trivial
      · omega
  refine (hc.seq (HT.whileC (fun c => c.reg rDX) hinit hstep)).mono (fun _ h => h) ?_ (by omega)
  rintro c ⟨⟨h1, h2, h3⟩, h4⟩
  have hlt : c.reg rDX < k := by omega
  rw [← h2]
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · rw [Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt hlt, Nat.zero_add]

/-! ### Decoding a configuration -/

/-- One digit: `DIG[rDT] := rDX % k; rDX := rDX / k`. -/
def decBody : Stmt := .seq divmod (.seq (st rDB rDT rDX) (mov rDX rDQ))
/-- The `rDL` lowest base-`k` digits of `rDX`, written at `rDB`. -/
def decode : Stmt := forUp rDT rDL decBody

/-- The invariant of the decoding after `t` digits. -/
def DecInv (k x L b : ℕ) (mm : ℕ → ℕ) (t : ℕ) (c : Config) : Prop :=
  c.reg rDX = x / k ^ t ∧ c.reg rDB = b ∧ c.reg rK = k ∧ c.mem = wr mm b ((cfg k L x).take t)

theorem decBody_spec {S k x L b : ℕ} {mm : ℕ → ℕ} (hk : 0 < k) (hS : b + L ≤ S) (t : ℕ)
    (ht : t < L) :
    HTB S decBody (fun c => DecInv k x L b mm t c ∧ c.reg rDT = t ∧ c.reg rDL = L)
      (fun c => DecInv k x L b mm (t + 1) c ∧ c.reg rDT = t ∧ c.reg rDL = L) (7 * x + 9) := by
  have h₁ := (HTB.of_HT (S := S) rfl (divmod_spec (x := x / k ^ t) hk)).frameIndep (by decide)
    (by decide)
    (F := fun c => c.reg rDB = b ∧ c.mem = wr mm b ((cfg k L x).take t) ∧ c.reg rDT = t ∧
      c.reg rDL = L ∧ c.reg rK = k) (by indep)
  have h₂ : HTB S (.seq (st rDB rDT rDX) (mov rDX rDQ))
      (fun c => (c.reg rDX = x / k ^ t % k ∧ c.reg rDQ = x / k ^ t / k) ∧ c.reg rDB = b ∧
        c.mem = wr mm b ((cfg k L x).take t) ∧ c.reg rDT = t ∧ c.reg rDL = L ∧ c.reg rK = k)
      (fun c => DecInv k x L b mm (t + 1) c ∧ c.reg rDT = t ∧ c.reg rDL = L) 4 :=
    HTB.run_le (by decide) (by decide) fun c ⟨⟨h1, h2⟩, h3, h4, h5, h6, h7⟩ => by
      refine ⟨by addr_ok [h3, h5], ?_⟩
      simp +decide only [run_seq', run_st (show rDX ≠ rT by decide), run_mov (show rDQ ≠ rT by decide),
        setReg_reg, ↓reduceIte, setReg_mem, setMem_mem_upd, setMem_reg, DecInv, h1, h2, h3, h4, h5,
        h6, h7, true_and, and_true]
      refine ⟨div_pow_succ x k t, ?_⟩
      rw [cfg_take_succ k L x ht, wr_snoc, List.length_take, min_eq_left (by simp; omega)]
  refine (h₁.seq h₂).mono (fun c ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩ => ⟨⟨h1, h3⟩, h2, h4, h5, h6, h3⟩)
    (fun _ h => h) ?_
  have := Nat.div_le_self x (k ^ t)
  omega

/-- **Decoding** `x` into `L` digits at `b`. -/
theorem decode_spec {S k x L b : ℕ} {mm : ℕ → ℕ} (hk : 0 < k) (hS : b + L ≤ S) :
    HTB S decode (fun c => c.reg rDX = x ∧ c.reg rDL = L ∧ c.reg rDB = b ∧ c.reg rK = k ∧
      c.mem = mm)
      (fun c => c.mem = wr mm b (cfg k L x)) (L * (7 * x + 13) + 3) := by
  have hl := HTB.forUpC (S := S) (i := rDT) (n := rDL) (N := L) (body := decBody)
    (DecInv k x L b mm)
    (7 * x + 9) (by decide) (by decide) (by decide) (fun t => by indep [DecInv])
    (fun t ht => decBody_spec hk hS t ht)
  refine hl.mono (fun c ⟨h1, h2, h3, h4, h5⟩ => ⟨⟨by simp [h1], h3, h4, by simp [h5, wr_nil]⟩, h2⟩)
    (fun c ⟨⟨_, _, _, h⟩, _⟩ => by rw [h, List.take_of_length_le (by simp)]) (by ring_nf; omega)

/-! ### Looking up a digit -/

/-- The data read by `lookup`: the boundary list `l` of the segment (at `bidx + bo`), its
decoded digits `ds` (at `ad`), the range `[ts, te)` of its top cycles, whose values are at
`vb + i`. -/
structure LkEnv where
  bidx : ℕ
  bo : ℕ
  ad : ℕ
  ts : ℕ
  te : ℕ
  vb : ℕ
  l : List ℕ
  ds : List ℕ

/-- The registers holding the data of `lookup`. -/
@[mk_iff] structure LkRegs (E : LkEnv) (c : Config) : Prop where
  bidx : c.reg gBIDX = E.bidx
  bo : c.reg rBO = E.bo
  nb : c.reg rNB = E.l.length
  ad : c.reg rAD = E.ad
  ts : c.reg rTS = E.ts
  te : c.reg rTE = E.te
  vb : c.reg rVAL = E.vb

/-- The memory holding the data of `lookup`. -/
structure LkMem (E : LkEnv) (mm : ℕ → ℕ) : Prop where
  nodup : E.l.Nodup
  l : ∀ p (hp : p < E.l.length), mm (E.bidx + (E.bo + p)) = E.l[p]
  ds : ∀ p, p < E.l.length → mm (E.ad + p) = E.ds.getD p 0

/-- The addresses read by `lookup`, below the bound `S`. -/
structure LkBnd (S : ℕ) (E : LkEnv) : Prop where
  l : ∀ p, p < E.l.length → E.bidx + (E.bo + p) < S
  ds : E.ad + E.l.length ≤ S
  vb : E.vb + E.te ≤ S

/-- The digit found by `lookup` for `i`. -/
def LkEnv.dig (E : LkEnv) (mm : ℕ → ℕ) (i : ℕ) : ℕ := lkp E.l E.ds E.ts E.te (fun x => mm (E.vb + x)) i

/-- One entry of the scan: if `l[p] = i`, the digit is `ds[p]`. -/
def scanBody : Stmt :=
  .seq (.add rZ rBO rP) (.seq (ld rZ gBIDX rZ) (ifEq rZ rI (.seq (.const rF 1) (ld rD rAD rP)) .skip))
/-- Not in `l`: the value of `i` if `ts ≤ i < te`. -/
def notFound : Stmt := ifLe rTS rI (ifLt rI rTE (ld rD rVAL rI) .skip) .skip
/-- Initially not found. -/
def lkInit : Stmt := .seq (.const rF 0) (.const rD 0)
/-- **The digit of the pool index `rI`** into `rD`. -/
def lookup : Stmt := .seq lkInit (.seq (forUp rP rNB scanBody) (.ifz rF notFound .skip))

/-- The invariant of the scan after `p` entries. -/
def ScInv (E : LkEnv) (i : ℕ) (mm : ℕ → ℕ) (p : ℕ) (c : Config) : Prop :=
  LkRegs E c ∧ c.reg rI = i ∧ c.mem = mm ∧
    c.reg rF = (if i ∈ E.l.take p then 1 else 0) ∧
    c.reg rD = (if i ∈ E.l.take p then E.ds.getD (E.l.idxOf i) 0 else 0)

theorem scanBody_spec {S : ℕ} {E : LkEnv} {i : ℕ} {mm : ℕ → ℕ} (hM : LkMem E mm)
    (hB : LkBnd S E) (p : ℕ) (hp : p < E.l.length) :
    HTB S scanBody (fun c => ScInv E i mm p c ∧ c.reg rP = p ∧ c.reg rNB = E.l.length)
      (fun c => ScInv E i mm (p + 1) c ∧ c.reg rP = p ∧ c.reg rNB = E.l.length) 12 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hR, hi, hm, hf, hd⟩, hp', hn⟩ => ?_
  have hz : c.mem (E.bidx + (E.bo + p)) = E.l[p] := hm ▸ hM.l p hp
  have := hB.l p hp
  have := hB.ds
  refine ⟨by addr_ok [scanBody, hR.bo, hp', hR.bidx, hR.ad, hz], ?_⟩
  have hD : c.mem (E.ad + p) = E.ds.getD p 0 := hm ▸ hM.ds p hp
  have htake : E.l.take (p + 1) = E.l.take p ++ [E.l[p]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hp, Option.toList_some]
  have hRI : RegIndep (wregs scanBody) (fun c => LkRegs E c ∧ c.reg rI = i ∧ c.reg rP = p ∧
      c.reg rNB = E.l.length) := by indep [lkRegs_iff]
  obtain ⟨h1, h2, h3, h4⟩ := hRI.run (by decide) ⟨hR, hi, hp', hn⟩
  have hm' : (RAM.run scanBody c).mem = mm := by rw [run_mem_of_stores (by decide) (by decide), hm]
  refine ⟨⟨h1, h2, hm', ?_, ?_⟩, h3, h4⟩
  all_goals simp only [scanBody, run_seq', run_add, run_ld, run_ifEq (show rZ ≠ rT by decide)
    (show rI ≠ rT by decide), run_const, run_skip]
  all_goals simp +decide only [setReg_reg, ↓reduceIte, setReg_mem, hR.bo, hp', hR.bidx, hz, hi,
    hR.ad, hD, config_ite_reg]
  all_goals by_cases he : E.l[p] = i
  · simp +decide [htake, he]
  · have hmem : i ∈ E.l.take (p + 1) ↔ i ∈ E.l.take p := by
      rw [htake, List.mem_append, List.mem_singleton]
      exact ⟨fun h => h.resolve_right (fun h' => he h'.symm), Or.inl⟩
    simp only [he, ↓reduceIte, hf, hmem]
  · have hidx : E.l.idxOf i = p := by rw [← he]; exact hM.nodup.idxOf_getElem p hp
    simp +decide [htake, he, hidx]
  · have hmem : i ∈ E.l.take (p + 1) ↔ i ∈ E.l.take p := by
      rw [htake, List.mem_append, List.mem_singleton]
      exact ⟨fun h => h.resolve_right (fun h' => he h'.symm), Or.inl⟩
    simp only [he, ↓reduceIte, hd, hmem]

/-- **Looking up a digit.** -/
theorem lookup_spec {S : ℕ} {E : LkEnv} {i : ℕ} {mm : ℕ → ℕ} (hM : LkMem E mm)
    (hB : LkBnd S E) :
    HTB S lookup (fun c => LkRegs E c ∧ c.reg rI = i ∧ c.mem = mm)
      (fun c => c.reg rD = E.dig mm i) (16 * E.l.length + 15) := by
  have h₀ : HTB S lkInit (fun c => LkRegs E c ∧ c.reg rI = i ∧ c.mem = mm)
      (fun c => ScInv E i mm 0 c ∧ c.reg rNB = E.l.length) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hR, hi, hm⟩ => by
      have hRI : RegIndep (wregs lkInit)
          (fun c => LkRegs E c ∧ c.reg rI = i) := by indep [lkRegs_iff]
      obtain ⟨h1, h2⟩ := hRI.run (by decide) ⟨hR, hi⟩
      refine ⟨⟨h1, h2, by simp [lkInit, hm], ?_, ?_⟩, ?_⟩
      · simp +decide [lkInit]
      · simp +decide [lkInit]
      · simp +decide [lkInit, hR.nb]
  have hl := HTB.forUpC (S := S) (i := rP) (n := rNB) (N := E.l.length) (body := scanBody)
    (ScInv E i mm) 12
    (by decide) (by decide) (by decide) (fun p => by indep [ScInv, lkRegs_iff])
    (fun p hp => scanBody_spec hM hB p hp)
  have h₂ : HTB S (.ifz rF notFound .skip)
      (fun c => ScInv E i mm E.l.length c ∧ c.reg rP = E.l.length ∧ c.reg rNB = E.l.length)
      (fun c => c.reg rD = E.dig mm i) 10 :=
    HTB.run_le (by decide) (by decide) fun c ⟨⟨hR, hi, hm, hf, hd⟩, _, _⟩ => by
      have := hB.vb
      refine ⟨by addr_ok [notFound, hR.ts, hR.te, hR.vb, hi], ?_⟩
      rw [List.take_length] at hf hd
      simp only [run_ifz', notFound, run_ifLe, run_ifLt, run_ld, run_skip, LkEnv.dig, lkp]
      by_cases hil : i ∈ E.l
      · simp only [hil, ↓reduceIte] at hf hd
        simp +decide [hf, hd, hil]
      · simp only [hil, ↓reduceIte] at hf hd
        simp only [hf, ↓reduceIte, hil]
        simp +decide only [setReg_reg, ↓reduceIte, config_ite_reg, hR.ts, hR.te, hR.vb, hi, hd]
        by_cases h1 : E.ts ≤ i <;> by_cases h2 : i < E.te <;> simp [h1, h2, hm]
  exact (h₀.seq (hl.seq h₂)).weaken (by omega)

/-! ### The configuration passed to a child -/

/-- One boundary cycle of the child: its digit, accumulated with the power of `k`. -/
def digBody : Stmt :=
  .seq (.seq (.add rI rBW rQ2) (ld rI gBIDX rI)) (.seq lookup (.seq (mul rTMP rPW rD rMC)
    (.seq (.add rACC rACC rTMP) (.seq (mul rTMP rPW rK rMC) (mov rPW rTMP)))))

/-- The index of the child of the slot `rQ` (its slot id `FSID[rFO + rQ]` minus one) and its
boundary list. -/
def chHead : Stmt :=
  .seq (.add rJW rFO rQ) (.seq (ld rJW gFSID rJW) (.seq (dec rJW)
    (.seq (ld rBW gBOFF rJW) (.seq (addc rNW rJW 1) (.seq (ld rNW gBOFF rNW)
      (.seq (.sub rNW rNW rBW) (.seq (.const rACC 0) (.const rPW 1))))))))

/-- **The child of the slot `rQ`**: its configuration, stored at `rA + jw`. -/
def child : Stmt := .seq chHead (.seq (forUp rQ2 rNW digBody) (st rA rJW rACC))

/-- The invariant of the digit loop after `q` boundary cycles of the child. -/
def DgInv (E : LkEnv) (mm : ℕ → ℕ) (k bw : ℕ) (lw : List ℕ) (q : ℕ) (c : Config) : Prop :=
  LkRegs E c ∧ c.reg rK = k ∧ c.reg rBW = bw ∧ c.mem = mm ∧
    c.reg rACC = enc k ((lw.map (E.dig mm)).take q) ∧ c.reg rPW = k ^ q

theorem digBody_spec {S : ℕ} {E : LkEnv} {mm : ℕ → ℕ} {k bw : ℕ} {lw : List ℕ}
    (hM : LkMem E mm) (hB : LkBnd S E)
    (hlw : ∀ q (hq : q < lw.length), mm (E.bidx + (bw + q)) = lw[q])
    (hlwS : ∀ q, q < lw.length → E.bidx + (bw + q) < S)
    (hdig : ∀ i ∈ lw, E.dig mm i < k) (q : ℕ) (hq : q < lw.length) :
    HTB S digBody (fun c => DgInv E mm k bw lw q c ∧ c.reg rQ2 = q ∧ c.reg rNW = lw.length)
      (fun c => DgInv E mm k bw lw (q + 1) c ∧ c.reg rQ2 = q ∧ c.reg rNW = lw.length)
      (16 * E.l.length + 10 * k + 30) := by
  have hd := hdig _ (List.getElem_mem hq)
  have hA : HTB S (.seq (.add rI rBW rQ2) (ld rI gBIDX rI))
      (fun c => DgInv E mm k bw lw q c ∧ c.reg rQ2 = q ∧ c.reg rNW = lw.length)
      (fun c => (DgInv E mm k bw lw q c ∧ c.reg rQ2 = q ∧ c.reg rNW = lw.length) ∧
        c.reg rI = lw[q]) 3 :=
    HTB.run_le (by decide) (by decide) fun c hc => by
      have := hlwS q hq
      have hbw : c.reg rBW = bw := hc.1.2.2.1
      have hq2 : c.reg rQ2 = q := hc.2.1
      have hbi : c.reg gBIDX = E.bidx := hc.1.1.bidx
      refine ⟨by addr_ok [hbw, hq2, hbi], ?_⟩
      have hI : Indep (wregs (.seq (.add rI rBW rQ2) (ld rI gBIDX rI)))
          (fun c => DgInv E mm k bw lw q c ∧ c.reg rQ2 = q ∧ c.reg rNW = lw.length) := by
        indep [DgInv, lkRegs_iff]
      refine ⟨hI.run (by decide) (by decide) (by decide) hc, ?_⟩
      obtain ⟨⟨hR, -, hb, hm, -⟩, hq', -⟩ := hc
      simp +decide only [run_seq', run_add, run_ld, setReg_reg, ↓reduceIte, setReg_mem, hb, hq',
        hR.bidx, hm, hlw q hq]
  have hL := (lookup_spec hM hB (i := lw[q])).frameIndep (by decide) (by decide)
    (F := fun c => DgInv E mm k bw lw q c ∧ c.reg rQ2 = q ∧ c.reg rNW = lw.length)
    (by indep [DgInv, lkRegs_iff])
  have hC := HTB.mul (S := S) (d := rTMP) (a := rPW) (b := rD) (k := rMC) (x := k ^ q)
    (y := E.dig mm lw[q])
    (P := fun c => c.reg rD = E.dig mm lw[q] ∧
      (DgInv E mm k bw lw q c ∧ c.reg rQ2 = q ∧ c.reg rNW = lw.length))
    (by decide) (by indep [DgInv, lkRegs_iff]) (fun c h => h.2.1.2.2.2.2.2) (fun c h => h.1)
  have hD : HTB S (.add rACC rACC rTMP)
      (fun c => (c.reg rD = E.dig mm lw[q] ∧
        (DgInv E mm k bw lw q c ∧ c.reg rQ2 = q ∧ c.reg rNW = lw.length)) ∧
          c.reg rTMP = k ^ q * E.dig mm lw[q])
      (fun c => (LkRegs E c ∧ c.reg rK = k ∧ c.reg rBW = bw ∧ c.mem = mm ∧
        c.reg rACC = enc k ((lw.map (E.dig mm)).take (q + 1)) ∧ c.reg rPW = k ^ q) ∧
          c.reg rQ2 = q ∧ c.reg rNW = lw.length) 1 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
      fun c ⟨⟨_, ⟨hR, hk, hb, hm, ha, hp⟩, hq', hn⟩, ht⟩ => by
      have hI : Indep (wregs (.add rACC rACC rTMP)) (fun c => LkRegs E c ∧ c.reg rK = k ∧
          c.reg rBW = bw ∧ c.mem = mm ∧ c.reg rPW = k ^ q ∧ c.reg rQ2 = q ∧
          c.reg rNW = lw.length) := by indep [lkRegs_iff]
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
        hI.run (by decide) (by decide) (by decide) ⟨hR, hk, hb, hm, hp, hq', hn⟩
      refine ⟨⟨h1, h2, h3, h4, ?_, h5⟩, h6, h7⟩
      have he := enc_take_succ k (lw.map (E.dig mm)) (q := q) (by simpa using hq)
      simp only [List.getElem_map] at he
      simp +decide only [run_add, setReg_reg, ↓reduceIte, ha, ht, he]
      ring
  have hE := HTB.mul (S := S) (d := rTMP) (a := rPW) (b := rK) (k := rMC) (x := k ^ q) (y := k)
    (P := fun c => (LkRegs E c ∧ c.reg rK = k ∧ c.reg rBW = bw ∧ c.mem = mm ∧
        c.reg rACC = enc k ((lw.map (E.dig mm)).take (q + 1)) ∧ c.reg rPW = k ^ q) ∧
          c.reg rQ2 = q ∧ c.reg rNW = lw.length)
    (by decide) (by indep [lkRegs_iff]) (fun c h => h.1.2.2.2.2.2) (fun c h => h.1.2.1)
  have hF : HTB S (mov rPW rTMP)
      (fun c => ((LkRegs E c ∧ c.reg rK = k ∧ c.reg rBW = bw ∧ c.mem = mm ∧
        c.reg rACC = enc k ((lw.map (E.dig mm)).take (q + 1)) ∧ c.reg rPW = k ^ q) ∧
          c.reg rQ2 = q ∧ c.reg rNW = lw.length) ∧ c.reg rTMP = k ^ q * k)
      (fun c => DgInv E mm k bw lw (q + 1) c ∧ c.reg rQ2 = q ∧ c.reg rNW = lw.length) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
      fun c ⟨⟨⟨hR, hk, hb, hm, ha, _⟩, hq', hn⟩, ht⟩ => by
      have hI : Indep (wregs (mov rPW rTMP)) (fun c => LkRegs E c ∧ c.reg rK = k ∧
          c.reg rBW = bw ∧ c.mem = mm ∧ c.reg rACC = enc k ((lw.map (E.dig mm)).take (q + 1)) ∧
          c.reg rQ2 = q ∧ c.reg rNW = lw.length) := by indep [lkRegs_iff]
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
        hI.run (by decide) (by decide) (by decide) ⟨hR, hk, hb, hm, ha, hq', hn⟩
      refine ⟨⟨h1, h2, h3, h4, h5, ?_⟩, h6, h7⟩
      simp +decide only [run_mov (show rTMP ≠ rT by decide), setReg_reg, ↓reduceIte, ht, pow_succ]
  refine (hA.seq ((hL.pre fun c ⟨⟨hD, hq', hn⟩, hi⟩ => ⟨⟨hD.1, hi, hD.2.2.2.1⟩, hD, hq', hn⟩).seq
    (hC.seq (hD.seq (hE.seq hF))))).weaken ?_
  omega

/-- **The configuration of a child** (the slot `q` of the face at offset `fo`, slot id
`jw + 1` at `fsid + (fo + q)`, boundary list `lw` at offset `bw`): stored at `a + jw`. -/
theorem child_spec {S : ℕ} {E : LkEnv} {mm : ℕ → ℕ} {k fo q fsid jw boff bw a : ℕ}
    {lw : List ℕ} (hM : LkMem E mm) (hB : LkBnd S E) (hfs : mm (fsid + (fo + q)) = jw + 1)
    (hb1 : mm (boff + jw) = bw) (hb2 : mm (boff + (jw + 1)) = bw + lw.length)
    (hlw : ∀ q (hq : q < lw.length), mm (E.bidx + (bw + q)) = lw[q])
    (hlwS : ∀ q, q < lw.length → E.bidx + (bw + q) < S)
    (hfsS : fsid + (fo + q) < S) (hboS : boff + (jw + 1) < S) (haS : a + jw < S)
    (hdig : ∀ i ∈ lw, E.dig mm i < k) :
    HTB S child (fun c => LkRegs E c ∧ c.reg rK = k ∧ c.reg rFO = fo ∧ c.reg rQ = q ∧
        c.reg gFSID = fsid ∧ c.reg gBOFF = boff ∧ c.reg rA = a ∧ c.mem = mm)
      (fun c => c.mem = upd mm (a + jw) (enc k (lw.map (E.dig mm))))
      (lw.length * (16 * E.l.length + 10 * k + 34) + 20) := by
  have h₀ : HTB S chHead (fun c => LkRegs E c ∧ c.reg rK = k ∧ c.reg rFO = fo ∧ c.reg rQ = q ∧
        c.reg gFSID = fsid ∧ c.reg gBOFF = boff ∧ c.reg rA = a ∧ c.mem = mm)
      (fun c => (DgInv E mm k bw lw 0 c ∧ c.reg rNW = lw.length) ∧ (c.reg rA = a ∧ c.reg rJW = jw))
      15 :=
    HTB.run_le (by decide) (by decide) fun c ⟨hR, hk, hx, hy, hs, hb, ha, hm⟩ => by
      refine ⟨by addr_ok [chHead, hx, hm, hy, hs, hfs, hb], ?_⟩
      have hI : Indep (wregs chHead) (fun c => LkRegs E c ∧ c.reg rK = k ∧ c.mem = mm ∧
          c.reg rA = a) := by indep [lkRegs_iff]
      obtain ⟨h1, h2, h3, h4⟩ := hI.run (by decide) (by decide) (by decide) ⟨hR, hk, hm, ha⟩
      have hv : (RAM.run chHead c).reg rJW = jw ∧ (RAM.run chHead c).reg rBW = bw ∧
          (RAM.run chHead c).reg rNW = lw.length ∧ (RAM.run chHead c).reg rACC = 0 ∧
          (RAM.run chHead c).reg rPW = 1 := by
        simp +decide only [chHead, run_seq', run_ld, run_add, run_dec (show rJW ≠ rT by decide),
          run_addc (show rJW ≠ rT by decide), run_sub, run_const, setReg_reg, ↓reduceIte,
          setReg_mem, hx, hm, hy, hs, hfs, hb, Nat.add_sub_cancel, hb1, hb2,
          Nat.add_sub_cancel_left, and_true]
      refine ⟨⟨⟨h1, h2, hv.2.1, h3, ?_, ?_⟩, hv.2.2.1⟩, h4, hv.1⟩
      · rw [hv.2.2.2.1]; rfl
      · rw [hv.2.2.2.2, pow_zero]
  have hl := (HTB.forUpC (S := S) (i := rQ2) (n := rNW) (N := lw.length) (body := digBody)
    (DgInv E mm k bw lw) (16 * E.l.length + 10 * k + 30) (by decide) (by decide) (by decide)
    (fun q => by indep [DgInv, lkRegs_iff])
    (fun q hq => digBody_spec hM hB hlw hlwS hdig q hq)).frameReg
    (F := fun c => c.reg rA = a ∧ c.reg rJW = jw) (by indep)
  have h₂ : HTB S (st rA rJW rACC)
      (fun c => (DgInv E mm k bw lw lw.length c ∧ c.reg rQ2 = lw.length ∧ c.reg rNW = lw.length) ∧
        (c.reg rA = a ∧ c.reg rJW = jw))
      (fun c => c.mem = upd mm (a + jw) (enc k (lw.map (E.dig mm)))) 2 :=
    HTB.run_le (by decide) (by decide) fun c ⟨⟨⟨_, _, _, hm, hacc, _⟩, _, _⟩, ha, hj⟩ => by
      refine ⟨by addr_ok [ha, hj], ?_⟩
      rw [List.take_of_length_le (by simp)] at hacc
      simp +decide only [run_st (show rACC ≠ rT by decide), setReg_mem, setMem_mem_upd, ha, hj,
        hacc, hm]
  exact (h₀.seq (hl.seq h₂)).weaken (by ring_nf; omega)

end STACS2027.RAM.P4
