module

public import Runtimes.ConvexQP.RAM.ArithMacros
import Mathlib.Tactic

/-!
# Big-number arithmetic on the add/subtract RAM: loops over signed arrays (1)

Signed arrays in memory: `SArr m b s n f` — entry `j < n` (the integer `f j`) occupies the cells
`b + j·s` (sign bit) and `b + j·s + 1` (magnitude); `s` is the stride in cells (`2` for a
contiguous vector; a row-major `r × c` matrix has rows `b + i·(2c)` and stride `2` inside a
row, its columns have stride `2c`). Writing: `sw m a z` (the two cells of `z` at `a`) and
`wrArr m₀ b s f k` (entries `0, …, k−1` of `f` written in order).

Kernels (cores on the library's registers, block `400–449`; set their input registers with
`mov`/`const` before the call):
* **`dotCore`**: `vAcc := ∑_{j<n} A_j · x_j` for strided `A` (at `vPA`, stride `vSA`) and `x`
  (at `vPX`, stride `vSX`), `n = reg vN`; `n · (31 B + 87) + 5` steps when all `|x_j|` have at
  most `B` bits (the `x_j` are the multipliers). The memory is unchanged (`dotCore_specB`).
* **`mvCore`**: `u_i := ∑_{j<c} M_{i,j} · x_j` for `i < r`, written as a contiguous signed
  vector at `vPU`; rows of `M` start at `vRow + i·vSI`, columns have stride `vSA`
  (so both `M x` and `Mᵀ x` are covered); `r · (c · (31 B + 87) + 25) + 1` steps (`mvCore_specB`).

**Space**: `dotCore_specB`, `mvCore_specB` are the bounded forms (scratch `2 B` cells above the
free address, the entries read below `S`: `addr_lt_of_stride`, `addr_lt_rows`, `addr_lt_cols`).
-/

@[expose] public section

namespace STACS2027.Runtimes.Arith

open STACS2027.RAM

/-! ### Signed arrays in memory -/

/-- The strided signed array `f` (length `n`, stride `s`) at `b`. -/
def SArr (m : ℕ → ℕ) (b s n : ℕ) (f : ℕ → ℤ) : Prop := ∀ j < n, SMem m (b + j * s) (f j)

/-- Write the integer `z` into the cells `a, a + 1`. -/
def sw (m : ℕ → ℕ) (a : ℕ) (z : ℤ) : ℕ → ℕ := upd (upd m a (sgnBit z)) (a + 1) z.natAbs

/-- The entries `0, …, k − 1` of `f` written (stride `s`) at `b`. -/
def wrArr (m₀ : ℕ → ℕ) (b s : ℕ) (f : ℕ → ℤ) : ℕ → ℕ → ℕ
  | 0 => m₀
  | k + 1 => sw (wrArr m₀ b s f k) (b + k * s) (f k)

theorem sw_apply_of_ne {m : ℕ → ℕ} {a i : ℕ} (z : ℤ) (h0 : i ≠ a) (h1 : i ≠ a + 1) :
    sw m a z i = m i := by simp [sw, h0, h1]

theorem smem_sw (m : ℕ → ℕ) (a : ℕ) (z : ℤ) : SMem (sw m a z) a z := by
  simp [SMem, sw]

/-- Cells outside the written block keep their values. -/
theorem wrArr_of_out {m₀ : ℕ → ℕ} {b s : ℕ} {f : ℕ → ℤ} (hs : 2 ≤ s) :
    ∀ {k i : ℕ}, (i < b ∨ b + k * s ≤ i) → wrArr m₀ b s f k i = m₀ i
  | 0, _, _ => rfl
  | k + 1, i, h => by
    have h' : b + k * s + s = b + (k + 1) * s := by ring
    simp only [wrArr]
    rw [sw_apply_of_ne _ (by omega) (by omega)]
    exact wrArr_of_out hs (by omega)

/-- The written block, read back. -/
theorem sarr_wrArr {m₀ : ℕ → ℕ} {b s : ℕ} {f : ℕ → ℤ} (hs : 2 ≤ s) :
    ∀ k, SArr (wrArr m₀ b s f k) b s k f
  | 0 => fun _ h => absurd h (Nat.not_lt_zero _)
  | k + 1 => fun j hj => by
    simp only [wrArr]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · have hk : j * s + s ≤ k * s := by
        have := Nat.mul_le_mul_right s (show j + 1 ≤ k by omega); rw [Nat.add_mul] at this; omega
      obtain ⟨h0, h1⟩ := sarr_wrArr hs k j hj
      exact ⟨by rw [sw_apply_of_ne _ (by omega) (by omega)]; exact h0,
        by rw [sw_apply_of_ne _ (by omega) (by omega)]; exact h1⟩
    · exact smem_sw _ _ _

/-- Writing keeps everything outside `[b, b + k s)`. -/
theorem sameOn_wrArr {m₀ : ℕ → ℕ} {b s : ℕ} {f : ℕ → ℤ} (hs : 2 ≤ s) (k : ℕ) :
    SameOn (fun a => ¬ (b ≤ a ∧ a < b + k * s)) m₀ (wrArr m₀ b s f k) := fun a ha =>
  wrArr_of_out hs (by omega)

/-- Writing below `F` keeps `ZeroFrom … F`. -/
theorem zeroFrom_wrArr {m₀ : ℕ → ℕ} {b s F : ℕ} {f : ℕ → ℤ} (hs : 2 ≤ s) (hz : ZeroFrom m₀ F)
    {k : ℕ} (hk : b + k * s ≤ F) : ZeroFrom (wrArr m₀ b s f k) F := fun a ha => by
  rw [wrArr_of_out hs (by omega)]; exact hz a ha

theorem wrArr_succ (m₀ : ℕ → ℕ) (b s : ℕ) (f : ℕ → ℤ) (k : ℕ) :
    wrArr m₀ b s f (k + 1) = sw (wrArr m₀ b s f k) (b + k * s) (f k) := rfl

/-! ### Addresses below a bound

The kernels read strided arrays; their bounded specifications ask that the two cells of every
entry read lie below the space bound `S` (`∀ j < n, b + j * s + 1 < S`). For the usual layouts: -/

/-- An array with stride `s ≥ 2` inside `[b, b + n s)`. -/
theorem addr_lt_of_stride {b s n S j : ℕ} (hs : 2 ≤ s) (h : b + n * s ≤ S) (hj : j < n) :
    b + j * s + 1 < S := by
  have := Nat.mul_le_mul_right s (show j + 1 ≤ n by omega)
  rw [Nat.add_mul] at this
  omega

/-- A row-major matrix: `r` rows at `p + i·si`, each of `nc` contiguous entries (`2 nc ≤ si`). -/
theorem addr_lt_rows {p si nc r S i j : ℕ} (hsi : nc * 2 ≤ si) (h : p + r * si ≤ S) (hi : i < r)
    (hj : j < nc) : p + i * si + j * 2 + 1 < S := by
  have := Nat.mul_le_mul_right si (show i + 1 ≤ r by omega)
  rw [Nat.add_mul] at this
  omega

/-- The columns of a row-major matrix (`nc` rows of stride `sj`, `r` contiguous entries each,
`2 r ≤ sj`), read as `r` vectors of stride `sj`: entry `j` of column `i` at `p + 2i + j·sj`. -/
theorem addr_lt_cols {p sj nc r S i j : ℕ} (hsj : r * 2 ≤ sj) (h : p + nc * sj ≤ S) (hi : i < r)
    (hj : j < nc) : p + i * 2 + j * sj + 1 < S := by
  have := Nat.mul_le_mul_right sj (show j + 1 ≤ nc by omega)
  rw [Nat.add_mul] at this
  omega

/-! ### Registers of the loops -/

/-- Loop counter. -/
abbrev vK : ℕ := 449
/-- Length / number of columns `n` (kept). -/
abbrev vN : ℕ := 431
/-- Pointer into the first array (advanced). -/
abbrev vPA : ℕ := 432
/-- Stride of the first array (kept). -/
abbrev vSA : ℕ := 433
/-- Pointer into the second array (advanced). -/
abbrev vPX : ℕ := 434
/-- Stride of the second array (kept). -/
abbrev vSX : ℕ := 435
/-- The dot product (pair `436, 437`). -/
abbrev vAcc : ℕ := 436
/-- Rows still to do (consumed). -/
abbrev vR : ℕ := 444
/-- Pointer to the current row (advanced). -/
abbrev vRow : ℕ := 445
/-- Row stride (kept). -/
abbrev vSI : ℕ := 446
/-- Output pointer (advanced). -/
abbrev vPU : ℕ := 447
/-- Base of the vector (kept). -/
abbrev vX0 : ℕ := 448

/-- The registers of the scalar cores: `rT` and `400–430`. -/
def coreW : List ℕ := rT :: List.range' 400 31

/-- The registers written by `dotCore`. -/
def dotW : List ℕ := vK :: vPA :: vPX :: vAcc :: (vAcc + 1) :: coreW

/-! ### The dot product -/

/-- One term: `vAcc += A_j · x_j`, advance both pointers. -/
def dotBody : Stmt :=
  .seq (sload mX vPA) (.seq (sload mY vPX) (.seq smulCore (.seq (smov sX vAcc) (.seq (smov sY mZ)
    (.seq saddCore (.seq (smov vAcc sZ) (.seq (.add vPA vPA vSA) (.add vPX vPX vSX))))))))

/-- `vAcc := ∑_{j < vN} A_j x_j`. -/
def dotCore : Stmt := .seq (sconst vAcc 0) (forUp vK vN dotBody)

/-- The frame of a dot step. -/
def DF (P : Config → Prop) (n sa sx j : ℕ) (c : Config) : Prop :=
  P c ∧ c.reg vN = n ∧ c.reg vSA = sa ∧ c.reg vSX = sx ∧ c.reg vK = j

theorem DF_indep {P : Config → Prop} (hP : Indep dotW P) (n sa sx j : ℕ) {W : List ℕ}
    (hW : ∀ r ∈ W, r ∈ dotW) (hW' : vN ∉ W ∧ vSA ∉ W ∧ vSX ∉ W ∧ vK ∉ W) :
    Indep W (DF P n sa sx j) :=
  (hP.mono hW).and ((Indep.reg hW'.1 (· = n)).and ((Indep.reg hW'.2.1 (· = sa)).and
    ((Indep.reg hW'.2.2.1 (· = sx)).and (Indep.reg hW'.2.2.2 (· = j)))))

/-- The frame with the two pointers. -/
def DG (P : Config → Prop) (n sa sx j pa px : ℕ) (c : Config) : Prop :=
  DF P n sa sx j c ∧ c.reg vPA = pa ∧ c.reg vPX = px

theorem DG_indep {P : Config → Prop} (hP : Indep dotW P) (n sa sx j pa px : ℕ) {W : List ℕ}
    (hW : ∀ r ∈ W, r ∈ vAcc :: (vAcc + 1) :: coreW) :
    Indep W (DG P n sa sx j pa px) :=
  have hW1 : ∀ r ∈ W, r ∈ dotW := fun r hr => by
    have := hW r hr
    simp only [dotW, List.mem_cons] at this ⊢; tauto
  have hn : ∀ r, r ∉ vAcc :: (vAcc + 1) :: coreW → r ∉ W := fun r h h' => h (hW r h')
  (DF_indep hP n sa sx j hW1 ⟨hn _ (by decide), hn _ (by decide), hn _ (by decide),
    hn _ (by decide)⟩).and ((Indep.reg (hn _ (by decide)) (· = pa)).and
      (Indep.reg (hn _ (by decide)) (· = px)))

/-- One dot step for a multiplier `v`, within the bound `S` (the two entries read below `S`, the
scratch table of the product, `2 · size |v|` cells from `rFREE`, below `S`). -/
theorem dotBody_specB {S : ℕ} {P : Config → Prop} (hP : Indep dotW P)
    (hZ : ∀ c, P c → ZeroFrom c.mem (c.reg rFREE)) (n sa sx j pa px : ℕ) (a v acc : ℤ)
    (hA : ∀ c, P c → SMem c.mem pa a) (hx : ∀ c, P c → SMem c.mem px v)
    (hS : ∀ c, P c → c.reg rFREE + 2 * Nat.size v.natAbs ≤ S) (hpa : pa + 1 < S)
    (hpx : px + 1 < S) :
    HTB S dotBody (fun c => DG P n sa sx j pa px c ∧ SReg c vAcc acc)
      (fun c => DG P n sa sx j (pa + sa) (px + sx) c ∧ SReg c vAcc (acc + a * v))
      (smulCost v + 48) := by
  have hG : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ vAcc :: (vAcc + 1) :: coreW) →
      Indep W (DG P n sa sx j pa px) :=
    fun hW => DG_indep hP n sa sx j pa px hW
  have hZG : ∀ c, DG P n sa sx j pa px c → ZeroFrom c.mem (c.reg rFREE) := fun c h => hZ c h.1.1
  -- loads
  have h1 := HTB.sload (S := S) (P := fun c => DG P n sa sx j pa px c ∧ SReg c vAcc acc) (d := mX)
    (p := vPA) (a := pa) (z := a) (by decide) (by decide) (by decide)
    ((hG (by decide)).and (indep_sreg (by decide) (by decide) acc)) hpa
  have h2 := HTB.sload (S := S)
    (P := fun c => (DG P n sa sx j pa px c ∧ SReg c vAcc acc) ∧ SReg c mX a)
    (d := mY) (p := vPX) (a := px) (z := v) (by decide) (by decide) (by decide)
    (((hG (by decide)).and (indep_sreg (by decide) (by decide) acc)).and
      (indep_sreg (by decide) (by decide) a)) hpx
  have h3 := smulCore_specB (S := S) (P := fun c => DG P n sa sx j pa px c ∧ SReg c vAcc acc)
    ((hG (by decide)).and (indep_sreg (by decide) (by decide) acc)) (fun c h => hZG c h.1) a v
    (fun c h => hS c h.1.1.1)
  have h4 := HTB.smov (S := S) (P := fun c => DG P n sa sx j pa px c ∧ SReg c mZ (a * v)) (d := sX)
    (x := vAcc)
    (z := acc) (by decide) (by decide) (by decide) (by decide)
    ((hG (by decide)).and (indep_sreg (by decide) (by decide) _))
  have h5 := HTB.smov (S := S) (P := fun c => DG P n sa sx j pa px c ∧ SReg c sX acc) (d := sY)
    (x := mZ)
    (z := a * v) (by decide) (by decide) (by decide) (by decide)
    ((hG (by decide)).and (indep_sreg (by decide) (by decide) _))
  have h6 := saddCore_specB (S := S) (P := DG P n sa sx j pa px) (hG (by decide)) acc (a * v)
  have h7 := HTB.smov (S := S) (P := DG P n sa sx j pa px) (d := vAcc) (x := sZ) (z := acc + a * v)
    (by decide) (by decide) (by decide) (by decide) (hG (by decide))
  have h8 : HTB S (.seq (.add vPA vPA vSA) (.add vPX vPX vSX))
      (fun c => DG P n sa sx j pa px c ∧ SReg c vAcc (acc + a * v))
      (fun c => DG P n sa sx j (pa + sa) (px + sx) c ∧ SReg c vAcc (acc + a * v)) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨⟨hc, hn, hsa, hsx, hj⟩, hpa, hpx⟩,
        hs0, hs1⟩ => by
      have hPc : P (RAM.run (.seq (.add vPA vPA vSA) (.add vPX vPX vSX)) c) :=
        (hP.mono (by decide)).run (by decide) rfl rfl hc
      refine ⟨⟨⟨hPc, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩ <;>
      simp +decide only [run_seq', run_add, setReg_reg, ↓reduceIte, hn, hsa, hsx, hj, hpa, hpx,
        hs0, hs1]
  refine (((h1.pre fun c ⟨hc, hacc⟩ => ⟨⟨hc, hacc⟩, hc.2.1, hA c hc.1.1⟩).seq
    ((h2.pre fun c h => ⟨h, h.1.1.2.2, hx c h.1.1.1.1⟩).seq
    ((h3.pre fun c ⟨⟨hc, hm⟩, hy⟩ => ⟨hc, hm, hy⟩).seq
    ((h4.pre fun c ⟨⟨hc, hacc⟩, hz⟩ => ⟨⟨hc, hz⟩, hacc⟩).seq
    ((h5.pre fun c ⟨⟨hc, hz⟩, hs⟩ => ⟨⟨hc, hs⟩, hz⟩).seq
    ((h6.pre fun c ⟨⟨hc, hs⟩, hz⟩ => ⟨hc, hs, hz⟩).seq (h7.seq h8)))))))).weaken (by omega)

/-- The dot-product state after `j` terms. -/
def DotInv (P : Config → Prop) (n pa sa px sx : ℕ) (A x : ℕ → ℤ) (j : ℕ) (c : Config) : Prop :=
  P c ∧ c.reg vN = n ∧ c.reg vSA = sa ∧ c.reg vSX = sx ∧ c.reg vPA = pa + j * sa ∧
    c.reg vPX = px + j * sx ∧ SReg c vAcc (∑ i ∈ Finset.range j, A i * x i)

/-- **Dot product within the bound** `vAcc := ∑_{j<n} A_j x_j` (strided `A` at `vPA`, `x` at
`vPX`) in `n · (31 B + 87) + 5` steps, `B` bounding the bit lengths of the `|x_j|`. `P` (the
caller's invariant, which must describe `A` and `x` in memory and give
`ZeroFrom c.mem (c.reg rFREE)`) survives; the memory is unchanged. Space: the scratch table of
the products (`2 B` cells from `rFREE`, `hS`) and the entries read (`hAS`, `hxS`) below `S`. -/
theorem dotCore_specB {S : ℕ} {P : Config → Prop} (hP : Indep dotW P)
    (hZ : ∀ c, P c → ZeroFrom c.mem (c.reg rFREE)) (n pa sa px sx B : ℕ) (A x : ℕ → ℤ)
    (hA : ∀ c, P c → SArr c.mem pa sa n A) (hx : ∀ c, P c → SArr c.mem px sx n x)
    (hB : ∀ j < n, Nat.size (x j).natAbs ≤ B) (hS : ∀ c, P c → c.reg rFREE + 2 * B ≤ S)
    (hAS : ∀ j < n, pa + j * sa + 1 < S) (hxS : ∀ j < n, px + j * sx + 1 < S) :
    HTB S dotCore (fun c => P c ∧ c.reg vN = n ∧ c.reg vPA = pa ∧ c.reg vSA = sa ∧
        c.reg vPX = px ∧ c.reg vSX = sx)
      (DotInv P n pa sa px sx A x n) (n * (31 * B + 87) + 5) := by
  have h0 : HTB S (sconst vAcc 0) (fun c => P c ∧ c.reg vN = n ∧ c.reg vPA = pa ∧ c.reg vSA = sa ∧
        c.reg vPX = px ∧ c.reg vSX = sx)
      (fun c => DotInv P n pa sa px sx A x 0 c ∧ c.reg vN = n) 2 :=
    (HTB.sconst (P := fun c => P c ∧ c.reg vN = n ∧ c.reg vPA = pa ∧ c.reg vSA = sa ∧
        c.reg vPX = px ∧ c.reg vSX = sx) 0
      ((hP.mono (by decide)).and (by indep))).post
      fun c ⟨⟨hc, hn, hpa, hsa, hpx, hsx⟩, hacc⟩ =>
        ⟨⟨hc, hn, hsa, hsx, by simpa using hpa, by simpa using hpx, by simpa using hacc⟩, hn⟩
  have hl := HTB.forUpC (S := S) (i := vK) (n := vN) (N := n) (body := dotBody)
    (DotInv P n pa sa px sx A x) (31 * B + 83) (by decide) (by decide) (by decide)
    (fun j => (hP.mono (by decide)).and (by indep [SReg]))
    (fun j hj => by
      have hb := dotBody_specB hP hZ n sa sx j (pa + j * sa) (px + j * sx) (A j) (x j)
        (∑ i ∈ Finset.range j, A i * x i) (fun c hc => hA c hc j hj)
        (fun c hc => hx c hc j hj) (fun c hc => by have := hS c hc; have := hB j hj; omega)
        (hAS j hj) (hxS j hj)
      refine hb.mono (fun c ⟨⟨hc, hn, hsa, hsx, hpa, hpx, hacc⟩, hk, _⟩ =>
          ⟨⟨⟨hc, hn, hsa, hsx, hk⟩, hpa, hpx⟩, hacc⟩)
        (fun c ⟨⟨⟨hc, hn, hsa, hsx, hk⟩, hpa, hpx⟩, hacc⟩ => ⟨⟨hc, hn, hsa, hsx,
          by rw [hpa]; ring, by rw [hpx]; ring, by rw [Finset.sum_range_succ]; exact hacc⟩, hk, hn⟩)
        ?_
      have := hB j hj
      simp only [smulCost, gCost]
      omega)
  exact (h0.seq hl).mono (fun _ h => h) (fun c ⟨h, _⟩ => h) (le_of_eq (by ring))

/-! ### Matrix–vector product -/

/-- One row: `u_i := ∑_j M_{i,j} x_j`, stored at `vPU`; advance the row and output pointers. -/
def mvBody : Stmt :=
  .seq (.seq (dec vR) (.seq (mov vPA vRow) (mov vPX vX0))) (.seq dotCore
    (.seq (sstore vPU vAcc) (.seq (addc vPU vPU 2) (.add vRow vRow vSI))))

/-- `u := M x` (`vR` rows, consumed). -/
def mvCore : Stmt := .loop vR mvBody

/-- The registers written by `mvCore`. -/
def mvW : List ℕ := vR :: vRow :: vPU :: dotW

/-- The product `M x` (`nc` columns). -/
def mulVec (M : ℕ → ℕ → ℤ) (x : ℕ → ℤ) (nc : ℕ) (i : ℕ) : ℤ := ∑ j ∈ Finset.range nc, M i j * x j

/-- The state of `mvCore` with `k` rows still to do. -/
def MvInv (R : Config → Prop) (m₀ : ℕ → ℕ) (r pm si nc sj px sx pu : ℕ) (M : ℕ → ℕ → ℤ)
    (x : ℕ → ℤ) (c : Config) : Prop :=
  R c ∧ c.reg vR ≤ r ∧ c.mem = wrArr m₀ pu 2 (mulVec M x nc) (r - c.reg vR) ∧
    c.reg vRow = pm + (r - c.reg vR) * si ∧ c.reg vPU = pu + (r - c.reg vR) * 2 ∧
    c.reg vSI = si ∧ c.reg vN = nc ∧ c.reg vSA = sj ∧ c.reg vX0 = px ∧ c.reg vSX = sx

/-- **Matrix–vector product within the bound** `u_i := ∑_{j<nc} M_{i,j} x_j` (`i < r`), written
as a contiguous signed vector at `pu` (below `rFREE = F`), in `r · (nc · (31 B + 87) + 19) + 1`
steps. Inputs: `vR = r` (consumed), `vRow = pm` (row `i` of `M` starts at `pm + i·si`), `vSI = si`,
`vN = nc`, `vSA = sj` (column stride), `vX0 = px`, `vSX = sx` (stride of `x`), `vPU = pu`. `M` and
`x` must be readable in every memory that agrees with the initial one `m₀` outside the output
block (`hM`, `hx`); `R` is any register-only assertion not about `mvW`. Space: the scratch table
(`2 B` cells from `F`, `hS`) and the entries of `M` and `x` (`hMS`, `hxS`; see `addr_lt_rows`,
`addr_lt_cols`, `addr_lt_of_stride`) below `S`. -/
theorem mvCore_specB {S : ℕ} {R : Config → Prop} (hR : RegIndep mvW R) (m₀ : ℕ → ℕ)
    (F r pm si nc sj px sx pu B : ℕ) (M : ℕ → ℕ → ℤ) (x : ℕ → ℤ) (hz : ZeroFrom m₀ F)
    (hF : ∀ c, R c → c.reg rFREE = F) (hpu : pu + r * 2 ≤ F)
    (hM : ∀ m, SameOn (fun a => ¬ (pu ≤ a ∧ a < pu + r * 2)) m₀ m →
      ∀ i < r, SArr m (pm + i * si) sj nc (M i))
    (hx : ∀ m, SameOn (fun a => ¬ (pu ≤ a ∧ a < pu + r * 2)) m₀ m → SArr m px sx nc x)
    (hB : ∀ j < nc, Nat.size (x j).natAbs ≤ B) (hS : F + 2 * B ≤ S)
    (hMS : ∀ i < r, ∀ j < nc, pm + i * si + j * sj + 1 < S)
    (hxS : ∀ j < nc, px + j * sx + 1 < S) :
    HTB S mvCore (fun c => R c ∧ c.mem = m₀ ∧ c.reg vR = r ∧ c.reg vRow = pm ∧ c.reg vSI = si ∧
        c.reg vN = nc ∧ c.reg vSA = sj ∧ c.reg vX0 = px ∧ c.reg vSX = sx ∧ c.reg vPU = pu)
      (fun c => MvInv R m₀ r pm si nc sj px sx pu M x c ∧ c.reg vR = 0)
      (r * (nc * (31 * B + 87) + 19) + 1) := by
  have hloop := HTB.loopT (S := S) (a := vR) (body := mvBody)
    (Inv := MvInv R m₀ r pm si nc sj px sx pu M x)
    (fun c => c.reg vR) (T := nc * (31 * B + 87) + 18) (fun v => by
      refine HTB.of_forall fun c₀ ⟨hI, hne, hv⟩ => ?_
      obtain ⟨hRc, hvr, hm, hrow, hpu', hsi, hn, hsa, hx0, hsx⟩ := hI
      set i := r - c₀.reg vR with hi
      have hir : i < r := by omega
      set mi := wrArr m₀ pu 2 (mulVec M x nc) i with hmi
      have hsame : SameOn (fun a => ¬ (pu ≤ a ∧ a < pu + r * 2)) m₀ mi := fun a ha =>
        sameOn_wrArr (le_refl 2) i a (by
          have : i * 2 ≤ r * 2 := by omega
          omega)
      have hzi : ZeroFrom mi F := zeroFrom_wrArr (le_refl 2) hz (by omega)
      -- the frame kept through the dot product
      let G : Config → Prop := fun c => R c ∧ c.mem = mi ∧ c.reg vR = c₀.reg vR - 1 ∧
        c.reg vRow = pm + i * si ∧ c.reg vPU = pu + i * 2 ∧ c.reg vSI = si ∧ c.reg vX0 = px
      have hGi : Indep dotW G := ((hR.mono fun r hr => by
          simp only [mvW, List.mem_cons]; tauto).indep).and
        ((Indep.mem (· = mi)).and (by indep))
      have h1 : HTB S (.seq (dec vR) (.seq (mov vPA vRow) (mov vPX vX0))) (fun c => c = c₀)
          (fun c => G c ∧ c.reg vN = nc ∧ c.reg vPA = pm + i * si ∧ c.reg vSA = sj ∧
            c.reg vPX = px ∧ c.reg vSX = sx) 6 :=
        HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => by
          subst hc
          refine ⟨⟨(hR.mono (by decide)).run (by decide) hRc, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
            ?_, ?_⟩ <;>
          simp +decide only [run_seq', run_dec, run_mov, setReg_reg, setReg_mem, ↓reduceIte, hm,
            hrow, hpu', hsi, hn, hsa, hx0, hsx, hmi]
      have h2 := dotCore_specB (S := S) (P := G) hGi
        (fun c hc => by rw [hc.2.1, hF c hc.1]; exact hzi) nc (pm + i * si) sj px sx B (M i) x
        (fun c hc => by rw [hc.2.1]; exact hM mi hsame i hir)
        (fun c hc => by rw [hc.2.1]; exact hx mi hsame) hB
        (fun c hc => by rw [hF c hc.1]; exact hS) (hMS i hir) hxS
      have h3 := HTB.sstore (S := S) (F := fun c => R c ∧ c.reg vR = c₀.reg vR - 1 ∧
          c.reg vRow = pm + i * si ∧ c.reg vSI = si ∧ c.reg vX0 = px ∧ c.reg vN = nc ∧
          c.reg vSA = sj ∧ c.reg vSX = sx) (p := vPU) (x := vAcc) (a := pu + i * 2)
        (z := mulVec M x nc i) (m := mi) (by decide) (by decide) (by decide)
        ((hR.mono (by decide)).and (by indep)) (by omega)
      have h4 : HTB S (.seq (addc vPU vPU 2) (.add vRow vRow vSI))
          (fun c => (R c ∧ c.reg vR = c₀.reg vR - 1 ∧ c.reg vRow = pm + i * si ∧
            c.reg vSI = si ∧ c.reg vX0 = px ∧ c.reg vN = nc ∧ c.reg vSA = sj ∧ c.reg vSX = sx) ∧
            SReg c vAcc (mulVec M x nc i) ∧ c.reg vPU = pu + i * 2 ∧
            c.mem = upd (upd mi (pu + i * 2) (sgnBit (mulVec M x nc i))) (pu + i * 2 + 1)
              (mulVec M x nc i).natAbs)
          (fun c => MvInv R m₀ r pm si nc sj px sx pu M x c ∧ c.reg vR < v) 3 :=
        HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
          fun c ⟨⟨hRc', hvR, hrow', hsi', hx0', hn', hsa', hsx'⟩, _, hpu'', hmem⟩ => by
          have hk : r - (c₀.reg vR - 1) = i + 1 := by omega
          refine ⟨⟨(hR.mono (by decide)).run (by decide) hRc', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
            ?_⟩ <;>
          simp +decide only [run_seq', run_addc, run_add, setReg_reg, setReg_mem, ↓reduceIte,
            hvR, hrow', hsi', hx0', hn', hsa', hsx', hpu'', hmem, hk]
          · omega
          · rw [wrArr_succ]; rfl
          · ring
          · ring
          · omega
      refine (h1.seq (h2.seq ((h3.pre fun c ⟨⟨hc, hm', hvR, hrow', hpu'', hsi', hx0'⟩, hn', hsa',
          hsx', _, _, hacc⟩ =>
            ⟨⟨hc, hvR, hrow', hsi', hx0', hn', hsa', hsx'⟩, hacc, hpu'', hm'⟩).seq
        h4))).weaken ?_
      omega) r
  refine (hloop.pre fun c ⟨hRc, hm, hvr, hrow, hsi, hn, hsa, hx0, hsx, hpu'⟩ =>
    ⟨⟨hRc, le_of_eq hvr, ?_, ?_, ?_, hsi, hn, hsa, hx0, hsx⟩, le_of_eq hvr⟩).weaken le_rfl
  · rw [hvr, Nat.sub_self]; exact hm
  · rw [hvr, Nat.sub_self]; simpa using hrow
  · rw [hvr, Nat.sub_self]; simpa using hpu'

end STACS2027.Runtimes.Arith
