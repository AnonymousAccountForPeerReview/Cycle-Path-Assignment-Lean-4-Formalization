module

public import Runtimes.ConvexQP.RAM.ParseSpec
public import Runtimes.Sort.Front
import Mathlib.Tactic

/-!
# Lemma 16 on the RAM, the parser: the overlap matrix `H` (program, states)

After Corollary 5's phase 1 and the sorting front end (`Sort.front`, `FrontPost g k (bD g k)`:
`EID[q] = eidOf g k q` at `bEI g k`, no memory indexed by a label), the phase `stepH` writes the
`N × N` matrix `H` (`N = kt`, two cells per entry, row `a` at `bH + a·2N`) with a table `MARK` of
`nE` cells at `bMK g k` (the end of the front end's memory):

```
for b < N:                          -- hB, with hJB = b % k, hCB = (b/k)k, hCol = 2b + 1
  MARK[EID[occ b s]] := 1 (s < k−2)  -- markWalk with hV = 1
  for a < N:                        -- hA, with hJA = a % k, hCA = (a/k)k, hRow = bH + a·2N
    hCnt := Σ_{s<k−2} MARK[EID[occ a s]]   -- cntWalk
    mem[hRow + hCol] := hCnt              -- H[a][b]
  MARK[EID[occ b s]] := 0 (s < k−2)  -- markWalk with hV = 0
```
The positions `opos k j s` are advanced by `nextP` (`hP := next k hP`).

This file: registers, layout, the program, the states (`HG` globals, `HM` memory, `WInv`, `IInv`,
`CInv`, `OInv`), the memory step lemmas and the specifications of the loop-free blocks.
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Parse

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ConvexQP STACS2027.Runtimes.ZeroCost

/-! ### Registers -/

/-- The base of `MARK`. -/
abbrev hMK : ℕ := 540
/-- `k − 2`. -/
abbrev hK2 : ℕ := 541
/-- The outer index `b`. -/
abbrev hB : ℕ := 542
/-- `b % k`. -/
abbrev hJB : ℕ := 543
/-- `(b / k) k`. -/
abbrev hCB : ℕ := 544
/-- `2b + 1`. -/
abbrev hCol : ℕ := 545
/-- The inner index `a`. -/
abbrev hA : ℕ := 546
/-- `a % k`. -/
abbrev hJA : ℕ := 547
/-- `(a / k) k`. -/
abbrev hCA : ℕ := 548
/-- `bH + a · 2N`. -/
abbrev hRow : ℕ := 549
/-- The walk counter `s`. -/
abbrev hS : ℕ := 292
/-- The position `opos k j s`. -/
abbrev hP : ℕ := 293
/-- An occurrence or an address. -/
abbrev hQ : ℕ := 294
/-- An edge identifier. -/
abbrev hId : ℕ := 295
/-- A mark. -/
abbrev hX : ℕ := 296
/-- The count. -/
abbrev hCnt : ℕ := 297
/-- The value written into `MARK`. -/
abbrev hV : ℕ := 298
/-- The size of `H`. -/
abbrev hSz : ℕ := 299

/-! ### Layout -/

section layout

variable (g : Graph) (k : ℕ)

/-- `N = k t`. -/
abbrev nN : ℕ := k * (cycles g k).length
/-- The number of distinct edges on the cycles. -/
abbrev nE : ℕ := (edgesOnCycles g k).length
/-- The address of the edge identifiers `EID` (written by the front end). -/
def bEI : ℕ := Sort.fEID g k (bD g k)
/-- The address of `MARK`: the end of the front end's memory. -/
def bMK : ℕ := Sort.fEnd g k (bD g k)
/-- The address of `H`. -/
def bH : ℕ := bMK g k + nE g k
/-- The end of `H`. -/
def bEnd : ℕ := bH g k + nN g k * (2 * nN g k)

theorem hlayout : bEI g k + nN g k ≤ bMK g k ∧ bH g k = bMK g k + nE g k ∧
    bEnd g k = bH g k + nN g k * (2 * nN g k) := by
  refine ⟨?_, rfl, rfl⟩
  simp only [bEI, bMK, Sort.fEnd, Sort.fCNT, nN, Sort.fL]; omega

/-- The regions of `stepH` fit below `S ≥ bEnd` (one inequality per region). -/
theorem hfits {S : ℕ} (hS : bEnd g k ≤ S) :
    bEI g k + nN g k ≤ S ∧ bMK g k + nE g k ≤ S ∧ bH g k + nN g k * (2 * nN g k) ≤ S := by
  have := hlayout g k; omega

end layout

/-! ### Cells of `H` -/

theorem hcell_lt {N a b : ℕ} (ha : a < N) (hb : b < N) : a * (2 * N) + 2 * b + 1 < N * (2 * N) := by
  have : (a + 1) * (2 * N) ≤ N * (2 * N) := Nat.mul_le_mul_right _ ha
  rw [Nat.add_mul, one_mul] at this; omega

theorem hcell_inj {N a b a' b' h h' : ℕ} (hb : b < N) (hb' : b' < N) (hh : h < 2) (hh' : h' < 2)
    (e : a * (2 * N) + (2 * b + h) = a' * (2 * N) + (2 * b' + h')) : a = a' ∧ b = b' ∧ h = h' := by
  obtain ⟨h1, h2⟩ := cell_inj (N := 2 * N) (by omega) (by omega) e
  exact ⟨h1, by omega, by omega⟩

/-- The `N × N` matrix `F` of naturals as signed entries (sign cell `0`) at `base`. -/
def HPart (m : ℕ → ℕ) (base N : ℕ) (F : ℕ → ℕ → ℕ) : Prop :=
  ∀ a < N, ∀ b < N, m (base + a * (2 * N) + 2 * b) = 0 ∧ m (base + a * (2 * N) + 2 * b + 1) = F a b

theorem HPart.congr {m : ℕ → ℕ} {base N : ℕ} {F F' : ℕ → ℕ → ℕ} (h : HPart m base N F)
    (hF : ∀ a < N, ∀ b < N, F a b = F' a b) : HPart m base N F' := fun a ha b hb =>
  ⟨(h a ha b hb).1, (h a ha b hb).2.trans (hF a ha b hb)⟩

theorem HPart.upd_of_lt {m : ℕ → ℕ} {base N x v : ℕ} {F : ℕ → ℕ → ℕ} (h : HPart m base N F)
    (hx : x < base) : HPart (upd m x v) base N F := fun a ha b hb => by
  have h1 : base + a * (2 * N) + 2 * b ≠ x := by omega
  have h2 : base + a * (2 * N) + 2 * b + 1 ≠ x := by omega
  simp only [upd_apply, h1, h2, ↓reduceIte]
  exact h a ha b hb

theorem HPart.set {m : ℕ → ℕ} {base N a b v : ℕ} {F : ℕ → ℕ → ℕ} (h : HPart m base N F)
    (hb : b < N) : HPart (upd m (base + a * (2 * N) + 2 * b + 1) v) base N
      (fun a' b' => if a' = a ∧ b' = b then v else F a' b') := fun a' ha' b' hb' => by
  have h1 : base + a' * (2 * N) + 2 * b' ≠ base + a * (2 * N) + 2 * b + 1 := by
    intro e
    have := hcell_inj (N := N) (a := a') (a' := a) (h := 0) (h' := 1) hb' hb (by omega) (by omega)
      (by omega)
    omega
  simp only [upd_apply, h1, ↓reduceIte]
  refine ⟨(h a' ha' b' hb').1, ?_⟩
  by_cases hab : a' = a ∧ b' = b
  · simp only [hab, ↓reduceIte, and_self]
  · have h2 : base + a' * (2 * N) + 2 * b' + 1 ≠ base + a * (2 * N) + 2 * b + 1 := by
      intro e
      have := hcell_inj (N := N) (a := a') (a' := a) (h := 1) (h' := 1) hb' hb (by omega)
        (by omega) (by omega)
      exact hab ⟨this.1, this.2.1⟩
    simp only [h2, hab, ↓reduceIte]
    exact (h a' ha' b' hb').2

/-! ### Memory of the phase -/

/-- The memory during `stepH`: the identifiers `EID`, the table `MARK` (`f`), the matrix `H` so
far (`F`), zero from `bEnd`. -/
structure HM (g : Graph) (k : ℕ) (F : ℕ → ℕ → ℕ) (f : ℕ → ℕ) (m : ℕ → ℕ) : Prop where
  meid : Tab m (bEI g k) (nN g k) (eidOf g k)
  mmark : Tab m (bMK g k) (nE g k) f
  mh : HPart m (bH g k) (nN g k) F
  mzero : ZeroFrom m (bEnd g k)

theorem HM.mark {g : Graph} {k : ℕ} {F : ℕ → ℕ → ℕ} {f : ℕ → ℕ} {m : ℕ → ℕ} (h : HM g k F f m)
    {e : ℕ} (he : e < nE g k) (v : ℕ) :
    HM g k F (Function.update f e v) (upd m (bMK g k + e) v) := by
  have hL := hlayout g k
  have := Nat.zero_le (nN g k * (2 * nN g k))
  exact ⟨h.meid.upd_of_disjoint (by omega), h.mmark.upd rfl, h.mh.upd_of_lt (by omega),
    h.mzero.upd (by omega)⟩

theorem HM.hset {g : Graph} {k : ℕ} {F : ℕ → ℕ → ℕ} {f : ℕ → ℕ} {m : ℕ → ℕ} (h : HM g k F f m)
    {a b : ℕ} (ha : a < nN g k) (hb : b < nN g k) (v : ℕ) :
    HM g k (fun a' b' => if a' = a ∧ b' = b then v else F a' b') f
      (upd m (bH g k + a * (2 * nN g k) + 2 * b + 1) v) := by
  have hL := hlayout g k
  have hc := hcell_lt ha hb
  exact ⟨h.meid.upd_of_disjoint (by omega), h.mmark.upd_of_disjoint (by omega), h.mh.set hb,
    h.mzero.upd (by omega)⟩

theorem HM.congrH {g : Graph} {k : ℕ} {F F' : ℕ → ℕ → ℕ} {f : ℕ → ℕ} {m : ℕ → ℕ}
    (h : HM g k F f m) (hF : ∀ a < nN g k, ∀ b < nN g k, F a b = F' a b) : HM g k F' f m :=
  ⟨h.meid, h.mmark, h.mh.congr hF, h.mzero⟩

theorem HM.congrM {g : Graph} {k : ℕ} {F : ℕ → ℕ → ℕ} {f f' : ℕ → ℕ} {m : ℕ → ℕ}
    (h : HM g k F f m) (hf : f = f') : HM g k F f' m := hf ▸ h

/-! ### The program -/

/-- `hP := next k hP`. -/
def nextP : Stmt := .seq (addc hP hP 1) (ifLt hP gK .skip (.const hP 0))

/-- `hP := next k (reg j)`. -/
def startP (j : ℕ) : Stmt := .seq (mov hP j) nextP

/-- One step of the mark walk: `MARK[EID[hCB + hP]] := hV`. -/
def markBody : Stmt := .seq (.add hQ hCB hP) (.seq (ld hId gEID hQ) (.seq (st hMK hId hV) nextP))

/-- Writing `hV` at the identifiers of option `b`. -/
def markWalk : Stmt := .seq (startP hJB) (forUp hS hK2 markBody)

/-- One step of the count walk: `hCnt += MARK[EID[hCA + hP]]`. -/
def cntBody : Stmt :=
  .seq (.add hQ hCA hP) (.seq (ld hId gEID hQ) (.seq (ld hX hMK hId) (.seq (.add hCnt hCnt hX) nextP)))

/-- The count of option `a` against the marked option. -/
def cntWalk : Stmt := .seq (.const hCnt 0) (.seq (startP hJA) (forUp hS hK2 cntBody))

/-- `H[a][b] := hCnt`, then `a + 1`. -/
def advA : Stmt :=
  .seq (.add hQ hRow hCol) (.seq (.store hQ hCnt) (.seq (.add hRow hRow gNV) (.seq (inc hJA)
    (ifEq hJA gK (.seq (.const hJA 0) (.add hCA hCA gK)) .skip))))

/-- One step of the inner loop. -/
def innerBody : Stmt := .seq cntWalk advA

/-- The inner registers for `a = 0`. -/
def innerInit : Stmt := .seq (.const hJA 0) (.seq (.const hCA 0) (mov hRow qBH))

/-- `b + 1`. -/
def advB : Stmt :=
  .seq (addc hCol hCol 2) (.seq (inc hJB) (ifEq hJB gK (.seq (.const hJB 0) (.add hCB hCB gK)) .skip))

/-- One step of the outer loop: mark option `b`, count every option against it, unmark. -/
def outerBody : Stmt :=
  .seq (.const hV 1) (.seq markWalk (.seq innerInit (.seq (forUp hA gKT innerBody)
    (.seq (.const hV 0) (.seq markWalk advB)))))

/-- The allocation of `MARK` and `H`. -/
def hAlloc : Stmt := .seq (alloc hMK ZeroCost.gNE) (.seq (mul hSz gKT gNV hS) (alloc qBH hSz))

/-- The outer registers for `b = 0`, and `k − 2`. -/
def hRegs : Stmt :=
  .seq (subc hK2 gK 2) (.seq (.const hJB 0) (.seq (.const hCB 0) (.const hCol 1)))

/-- **The matrix `H`.** -/
def stepH : Stmt := .seq hAlloc (.seq hRegs (forUp hB gKT outerBody))

/-! ### States -/

/-- The registers fixed during `stepH`. -/
@[mk_iff] structure HG (g : Graph) (k : ℕ) (c : Config) : Prop where
  rk : c.reg gK = k
  rt : c.reg gT = (cycles g k).length
  rkt : c.reg gKT = nN g k
  rnv : c.reg gNV = 2 * nN g k
  reid : c.reg gEID = bEI g k
  rmk : c.reg hMK = bMK g k
  rbh : c.reg qBH = bH g k
  rfree : c.reg rFREE = bEnd g k
  rk2 : c.reg hK2 = k - 2

/-- The registers written by the loops of `stepH`. -/
def WH : List ℕ := [rT, hS, hP, hQ, hId, hX, hCnt, hV, hA, hJA, hCA, hRow, hB, hJB, hCB, hCol]

theorem HG.regIndep (g : Graph) (k : ℕ) : RegIndep WH (HG g k) := by indep [hG_iff]

/-- The registers of the outer index `b`. -/
def BR (k b : ℕ) (c : Config) : Prop :=
  c.reg hJB = b % k ∧ c.reg hCB = b / k * k ∧ c.reg hCol = 2 * b + 1

/-- The registers of the inner index `a`. -/
def AR (g : Graph) (k a : ℕ) (c : Config) : Prop :=
  c.reg hJA = a % k ∧ c.reg hCA = a / k * k ∧ c.reg hRow = bH g k + a * (2 * nN g k)

/-- `H` after the columns `b' < b` and, in column `b`, the rows `a' < a`. -/
def hv (g : Graph) (k b a : ℕ) (a' b' : ℕ) : ℕ :=
  if b' < b ∨ (b' = b ∧ a' < a) then hc g k a' b' (k - 2) else 0

/-- The mark walk on option `b` with value `v` from the table `f`, after `s` steps. -/
def WInv (g : Graph) (k b : ℕ) (F : ℕ → ℕ → ℕ) (f : ℕ → ℕ) (v s : ℕ) (c : Config) : Prop :=
  HG g k c ∧ HM g k F (mk g k f b s v) c.mem ∧ BR k b c ∧ c.out = [] ∧ c.reg hV = v ∧
    c.reg hP = opos k (b % k) s

/-- The inner loop (column `b`) before row `a`. -/
def IInv (g : Graph) (k b a : ℕ) (c : Config) : Prop :=
  HG g k c ∧ HM g k (hv g k b a) (mark g k b) c.mem ∧ BR k b c ∧ c.out = [] ∧ AR g k a c

/-- The count walk of row `a` (column `b`) after `s` steps. -/
def CInv (g : Graph) (k b a s : ℕ) (c : Config) : Prop :=
  IInv g k b a c ∧ c.reg hP = opos k (a % k) s ∧ c.reg hCnt = hc g k a b s

/-- The outer loop before column `b`. -/
def OInv (g : Graph) (k b : ℕ) (c : Config) : Prop :=
  HG g k c ∧ HM g k (hv g k b 0) (fun _ => 0) c.mem ∧ BR k b c ∧ c.out = []

/-! ### `nextP` -/

theorem config_ext {c c' : Config} (hr : ∀ i, c.reg i = c'.reg i) (hm : c.mem = c'.mem)
    (ho : c.out = c'.out) : c = c' := by
  cases c; cases c'
  simp only at hr hm ho
  rw [funext hr, hm, ho]

theorem run_nextP (c : Config) :
    run nextP c = (c.setReg rT (c.reg gK - (c.reg hP + 1))).setReg hP (next (c.reg gK) (c.reg hP)) := by
  simp only [nextP, run_seq', run_addc (show hP ≠ rT by decide), run_ifLt, run_skip, run_const]
  unfold next
  by_cases h : c.reg hP + 1 < c.reg gK
  · simp +decide only [setReg_reg, ↓reduceIte, h]
    refine config_ext (fun i => ?_) rfl rfl
    simp only [setReg_reg]; split_ifs <;> simp_all
  · simp +decide only [setReg_reg, ↓reduceIte, h]
    refine config_ext (fun i => ?_) rfl rfl
    simp only [setReg_reg]; split_ifs <;> simp_all

theorem run_startP {j : ℕ} (hj : j ≠ rT) (c : Config) :
    run (startP j) c =
      (c.setReg rT (c.reg gK - (c.reg j + 1))).setReg hP (next (c.reg gK) (c.reg j)) := by
  simp +decide only [startP, run_seq', run_mov hj, run_nextP, setReg_reg, ↓reduceIte]
  refine config_ext (fun i => ?_) rfl rfl
  simp only [setReg_reg]; split_ifs <;> simp_all

/-! ### Index steps -/

theorem idx_succ {k a : ℕ} (hk : 0 < k) :
    (a % k + 1 = k → (a + 1) % k = 0 ∧ (a + 1) / k * k = a / k * k + k) ∧
      (a % k + 1 ≠ k → (a + 1) % k = a % k + 1 ∧ (a + 1) / k * k = a / k * k) := by
  have h1 := Nat.div_add_mod a k
  have h2 := Nat.div_add_mod (a + 1) k
  have h3 := Nat.mod_lt a hk
  have h4 := Nat.mod_lt (a + 1) hk
  constructor
  · intro h
    have e : a + 1 = (a / k + 1) * k := by rw [Nat.add_mul, one_mul]; rw [Nat.mul_comm] at h1; omega
    rw [e, Nat.mul_mod_left, Nat.mul_div_cancel _ hk, Nat.add_mul, one_mul]
    exact ⟨rfl, rfl⟩
  · intro h
    have e : a + 1 = a / k * k + (a % k + 1) := by rw [Nat.mul_comm] at h1; omega
    have hlt : a % k + 1 < k := by omega
    rw [e, cell_mod hlt, cell_div hlt]
    exact ⟨rfl, rfl⟩

end STACS2027.Runtimes.QPRam.Parse
