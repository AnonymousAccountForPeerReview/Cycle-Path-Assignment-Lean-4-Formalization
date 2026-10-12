module

public import Runtimes.ConvexQP.RAM.Vec
import Mathlib.Tactic

/-!
# Big-number arithmetic on the add/subtract RAM: loops over signed arrays (2)

Elementwise updates with a final division, and rank-one updates of matrices.

* `rnd md w γ`: `roundDiv w γ` (mode `md = true`, `γ > 0`) or `w / γ` (`Int.ediv`, mode
  `false`, `γ ≠ 0`); `divStep md` computes it (`sZ`, `vGa` ↦ `mZ`).
* **`linCore md`**: `z_j := rnd md (α z_j + β w_j) γ` for `j < n`, in place on the contiguous
  signed vector `z` (at `vPA`), with `w` contiguous at `vPX` and `α, β, γ` in the pairs `vAl`,
  `vBe`, `vGa`; `n · (124 B + 302) + 3` steps when `α`, `β`, all `z_j` and `w_j` have at most `B`
  bits (`linCore_specB`).
* **`r1Core md`**: `A_{ij} := rnd md (α A_{ij} + β u_i v_j) γ` for `i < r`, `j < nc` (row `i` of
  `A` at `vRow + i·vSI`, contiguous inside the row; `u` at `vPU`, `v` at `vX0`, both contiguous;
  `β` in `vB0`) (`r1Core_specB`).

**Space**: `divStep_specB`, `linCore_specB` (scratch `8 B + 6` cells above `F`), `r1Core_specB`
(`16 B + 6`), `axCore_specB` (`10 B + 4`), with the vectors read below `S`.
-/

@[expose] public section

namespace STACS2027.Runtimes.Arith

open STACS2027.RAM

/-! ### Rounding modes -/

/-- `roundDiv w γ` (`md = true`) or `w / γ` (`Int.ediv`, `md = false`). -/
def rnd (md : Bool) (w γ : ℤ) : ℤ := if md then ConvexQP.roundDiv w γ else w / γ

/-- The admissible divisors: `γ > 0` for `roundDiv`, `γ ≠ 0` for `Int.ediv`. -/
def GoodDiv (md : Bool) (γ : ℤ) : Prop := if md then 0 < γ else γ ≠ 0

/-- `α` (pair `438, 439`). -/
abbrev vAl : ℕ := 438
/-- `β` (pair `440, 441`). -/
abbrev vBe : ℕ := 440
/-- `γ` (pair `442, 443`). -/
abbrev vGa : ℕ := 442
/-- `β` of the rank-one update (pair `436, 437`). -/
abbrev vB0 : ℕ := 436

/-- `mZ := rnd md sZ vGa`. -/
def divStep : Bool → Stmt
  | true => .seq (smov rU sZ) (.seq (mov rV (vGa + 1)) roundCore)
  | false => .seq (smov mX sZ) (.seq (smov mY vGa) sdivCore)

/-- **The division step** in `31 · size |u| + 123` steps, within the bound `S` when
`2 · (size |u| + 2)` cells from `rFREE` (the scratch table of the division) fit below `S`. -/
theorem divStep_specB (md : Bool) {S : ℕ} {P : Config → Prop} (hP : Indep coreW P)
    (hZ : ∀ c, P c → ZeroFrom c.mem (c.reg rFREE)) (u γ : ℤ) (hγ : GoodDiv md γ)
    (hS : ∀ c, P c → c.reg rFREE + 2 * (Nat.size u.natAbs + 2) ≤ S) :
    HTB S (divStep md) (fun c => P c ∧ SReg c sZ u ∧ SReg c vGa γ)
      (fun c => P c ∧ SReg c mZ (rnd md u γ)) (31 * Nat.size u.natAbs + 123) := by
  cases md with
  | true =>
    have hg : 0 < γ := by simpa [GoodDiv] using hγ
    have h1 := HTB.smov (S := S) (P := fun c => P c ∧ SReg c vGa γ) (d := rU) (x := sZ) (z := u)
      (by decide)
      (by decide) (by decide) (by decide)
      ((hP.mono (by decide)).and (indep_sreg (by decide) (by decide) γ))
    have h2 : HTB S (mov rV (vGa + 1)) (fun c => (P c ∧ SReg c vGa γ) ∧ SReg c rU u)
        (fun c => P c ∧ SReg c rU u ∧ c.reg rV = γ.natAbs) 2 :=
      HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨hc, _, hg1⟩, hu0, hu1⟩ => by
        refine ⟨(hP.mono (by decide)).run (by decide) rfl rfl hc, ⟨?_, ?_⟩, ?_⟩ <;>
        simp +decide only [run_mov, setReg_reg, ↓reduceIte, hu0, hu1, hg1]
    have h3 := roundCore_specB (P := P) (hP.mono (by decide)) hZ u γ.natAbs (by omega) hS
    refine (h1.seq (h2.seq h3)).mono (fun c ⟨hc, hu, hg'⟩ => ⟨⟨hc, hg'⟩, hu⟩)
      (fun c ⟨hc, hm⟩ => ⟨hc, by simpa [rnd, show ((γ.natAbs : ℕ) : ℤ) = γ by omega] using hm⟩) ?_
    simp only [roundCost, gCost]; omega
  | false =>
    have hg : γ ≠ 0 := by simpa [GoodDiv] using hγ
    have h1 := HTB.smov (S := S) (P := fun c => P c ∧ SReg c vGa γ) (d := mX) (x := sZ) (z := u)
      (by decide)
      (by decide) (by decide) (by decide)
      ((hP.mono (by decide)).and (indep_sreg (by decide) (by decide) γ))
    have h2 := HTB.smov (S := S) (P := fun c => P c ∧ SReg c mX u) (d := mY) (x := vGa) (z := γ)
      (by decide)
      (by decide) (by decide) (by decide)
      ((hP.mono (by decide)).and (indep_sreg (by decide) (by decide) u))
    have h3 := sdivCore_specB (S := S) (P := P) (hP.mono (by decide)) hZ u γ hg
      (fun c h => by have := hS c h; unfold entB; omega)
    refine (h1.seq ((h2.pre fun c ⟨⟨hc, hg'⟩, hu⟩ => ⟨⟨hc, hu⟩, hg'⟩).seq
      (h3.pre fun c ⟨⟨hc, hu⟩, hg'⟩ => ⟨hc, hu, hg'⟩))).mono
      (fun c ⟨hc, hu, hg'⟩ => ⟨⟨hc, hg'⟩, hu⟩)
      (fun c ⟨hc, hm, _⟩ => ⟨hc, by simpa [rnd] using hm⟩) ?_
    simp only [sdivCost, gCost, entB]; omega

/-- The numerator `a α + b β` of `B`-bit numbers has at most `2B + 1` bits. -/
theorem size_lin_le {a α b β : ℤ} {B : ℕ} (ha : Nat.size a.natAbs ≤ B)
    (hα : Nat.size α.natAbs ≤ B) (hb : Nat.size b.natAbs ≤ B) (hβ : Nat.size β.natAbs ≤ B) :
    Nat.size (a * α + b * β).natAbs ≤ 2 * B + 1 := by
  rw [Nat.size_le] at ha hα hb hβ ⊢
  have h1 : a.natAbs * α.natAbs < 2 ^ B * 2 ^ B := Nat.mul_lt_mul'' ha hα
  have h2 : b.natAbs * β.natAbs < 2 ^ B * 2 ^ B := Nat.mul_lt_mul'' hb hβ
  have h3 : (a * α + b * β).natAbs ≤ a.natAbs * α.natAbs + b.natAbs * β.natAbs := by
    rw [← Int.natAbs_mul, ← Int.natAbs_mul]; exact Int.natAbs_add_le _ _
  have h4 : 2 ^ (2 * B + 1) = 2 * (2 ^ B * 2 ^ B) := by ring
  omega

/-- A product of a `B`-bit and a `B'`-bit number has at most `B + B'` bits. -/
theorem size_mul_le {a b : ℤ} {B B' : ℕ} (ha : Nat.size a.natAbs ≤ B)
    (hb : Nat.size b.natAbs ≤ B') : Nat.size (a * b).natAbs ≤ B + B' := by
  rw [Nat.size_le] at ha hb ⊢
  rw [Int.natAbs_mul, pow_add]
  exact Nat.mul_lt_mul'' ha hb

/-! ### Elementwise update -/

/-- The registers written by `linCore`. -/
def linW : List ℕ := vK :: vPA :: vPX :: coreW

/-- One element: `z_j := rnd md (z_j α + w_j β) γ`, advance both pointers. -/
def linBody (md : Bool) : Stmt :=
  .seq (sload mX vPA) (.seq (smov mY vAl) (.seq smulCore
  (.seq (smov sX mZ)
  (.seq (sload mX vPX) (.seq (smov mY vBe) (.seq smulCore
  (.seq (smov sY mZ)
  (.seq saddCore
  (.seq (divStep md)
  (.seq (sstore vPA mZ)
  (.seq (addc vPA vPA 2) (addc vPX vPX 2))))))))))))

/-- `z_j := rnd md (α z_j + β w_j) γ` for `j < reg vN`. -/
def linCore (md : Bool) : Stmt := forUp vK vN (linBody md)

/-- The registers of an elementwise step (everything but the scalar cores' registers). -/
def LR (R : Config → Prop) (n j pz pw : ℕ) (α β γ : ℤ) (c : Config) : Prop :=
  R c ∧ c.reg vN = n ∧ c.reg vK = j ∧ SReg c vAl α ∧ SReg c vBe β ∧ SReg c vGa γ ∧
    c.reg vPA = pz ∧ c.reg vPX = pw

/-- The frame of an elementwise step. -/
def LF (R : Config → Prop) (m : ℕ → ℕ) (n j pz pw : ℕ) (α β γ : ℤ) (c : Config) : Prop :=
  LR R n j pz pw α β γ c ∧ c.mem = m

theorem LR_regIndep {R : Config → Prop} (hR : RegIndep linW R) (n j pz pw : ℕ) (α β γ : ℤ)
    {W : List ℕ} (hW : ∀ r ∈ W, r ∈ coreW) : RegIndep W (LR R n j pz pw α β γ) := by
  have hn : ∀ r, r ∉ coreW → r ∉ W := fun r h h' => h (hW r h')
  exact (hR.mono fun r hr => by
      have := hW r hr; simp only [linW, List.mem_cons]; tauto).and
    ((RegIndep.reg (hn _ (by decide)) (· = n)).and ((RegIndep.reg (hn _ (by decide)) (· = j)).and
    ((regIndep_sreg (hn _ (by decide)) (hn _ (by decide)) α).and
    ((regIndep_sreg (hn _ (by decide)) (hn _ (by decide)) β).and
    ((regIndep_sreg (hn _ (by decide)) (hn _ (by decide)) γ).and
    ((RegIndep.reg (hn _ (by decide)) (· = pz)).and (RegIndep.reg (hn _ (by decide)) (· = pw))))))))

theorem LF_indep {R : Config → Prop} (hR : RegIndep linW R) (m : ℕ → ℕ) (n j pz pw : ℕ)
    (α β γ : ℤ) {W : List ℕ} (hW : ∀ r ∈ W, r ∈ coreW) : Indep W (LF R m n j pz pw α β γ) :=
  (LR_regIndep hR n j pz pw α β γ hW).indep.and (Indep.mem (· = m))

/-- **One elementwise step**, for `a = z_j`, `b = w_j` in memory `m`, within the bound `S`
(the scratch tables from `F` and the two entries below `S`). -/
theorem linBody_specB (md : Bool) {S : ℕ} {R : Config → Prop} (hR : RegIndep linW R)
    (m : ℕ → ℕ) (F n j pz pw : ℕ) (α β γ a b : ℤ) (hz : ZeroFrom m F)
    (hF : ∀ c, R c → c.reg rFREE = F) (ha : SMem m pz a) (hb : SMem m pw b) (hγ : GoodDiv md γ)
    (hS : F + 2 * (Nat.size α.natAbs + Nat.size β.natAbs + Nat.size (a * α + b * β).natAbs + 2)
      ≤ S) (hpz : pz + 1 < S) (hpw : pw + 1 < S) :
    HTB S (linBody md) (LF R m n j pz pw α β γ)
      (LF R (sw m pz (rnd md (a * α + b * β) γ)) n j (pz + 2) (pw + 2) α β γ)
      (31 * (Nat.size α.natAbs + Nat.size β.natAbs + Nat.size (a * α + b * β).natAbs) + 251) := by
  have hL : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ coreW) → Indep W (LF R m n j pz pw α β γ) :=
    fun hW => LF_indep hR m n j pz pw α β γ hW
  have hZL : ∀ c, LF R m n j pz pw α β γ c → ZeroFrom c.mem (c.reg rFREE) := fun c h => by
    rw [h.2, hF c h.1.1]; exact hz
  have hRF : ∀ c, LF R m n j pz pw α β γ c → c.reg rFREE = F := fun c h => hF c h.1.1
  -- z_j · α
  have h1 := HTB.sload (S := S) (P := LF R m n j pz pw α β γ) (d := mX) (p := vPA) (a := pz)
    (z := a) (by decide) (by decide) (by decide) (hL (by decide)) hpz
  have h2 := HTB.smov (S := S) (P := fun c => LF R m n j pz pw α β γ c ∧ SReg c mX a) (d := mY)
    (x := vAl) (z := α) (by decide) (by decide) (by decide) (by decide)
    ((hL (by decide)).and (indep_sreg (by decide) (by decide) a))
  have h3 := smulCore_specB (S := S) (P := LF R m n j pz pw α β γ) (hL (by decide)) hZL a α
    (fun c h => by rw [hRF c h]; omega)
  have h4 := HTB.smov (S := S) (P := LF R m n j pz pw α β γ) (d := sX) (x := mZ) (z := a * α)
    (by decide)
    (by decide) (by decide) (by decide) (hL (by decide))
  -- w_j · β
  have hL' : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ coreW) → sX ∉ W → sX + 1 ∉ W →
      Indep W (fun c => LF R m n j pz pw α β γ c ∧ SReg c sX (a * α)) :=
    fun hW h0 h1 => (hL hW).and (indep_sreg h0 h1 _)
  have h5 := HTB.sload (S := S) (P := fun c => LF R m n j pz pw α β γ c ∧ SReg c sX (a * α))
    (d := mX) (p := vPX) (a := pw) (z := b) (by decide) (by decide) (by decide)
    (hL' (by decide) (by decide) (by decide)) hpw
  have h6 := HTB.smov (S := S)
    (P := fun c => (LF R m n j pz pw α β γ c ∧ SReg c sX (a * α)) ∧ SReg c mX b)
    (d := mY) (x := vBe) (z := β) (by decide) (by decide) (by decide) (by decide)
    ((hL' (by decide) (by decide) (by decide)).and (indep_sreg (by decide) (by decide) b))
  have h7 := smulCore_specB (S := S) (P := fun c => LF R m n j pz pw α β γ c ∧ SReg c sX (a * α))
    (hL' (by decide) (by decide) (by decide)) (fun c h => hZL c h.1) b β
    (fun c h => by rw [hRF c h.1]; omega)
  have h8 := HTB.smov (S := S) (P := fun c => LF R m n j pz pw α β γ c ∧ SReg c sX (a * α))
    (d := sY) (x := mZ) (z := b * β) (by decide) (by decide) (by decide) (by decide)
    (hL' (by decide) (by decide) (by decide))
  -- sum, division, store
  have h9 := saddCore_specB (S := S) (P := LF R m n j pz pw α β γ) (hL (by decide)) (a * α)
    (b * β)
  have h10 := divStep_specB md (S := S) (P := LF R m n j pz pw α β γ) (hL (by decide)) hZL
    (a * α + b * β) γ hγ (fun c h => by rw [hRF c h]; omega)
  have h11 := HTB.sstore (S := S) (F := LR R n j pz pw α β γ) (p := vPA) (x := mZ) (a := pz)
    (z := rnd md (a * α + b * β) γ) (m := m) (by decide) (by decide) (by decide)
    (LR_regIndep hR n j pz pw α β γ (by decide)) hpz
  have h12 : HTB S (.seq (addc vPA vPA 2) (addc vPX vPX 2))
      (fun c => LR R n j pz pw α β γ c ∧ SReg c mZ (rnd md (a * α + b * β) γ) ∧ c.reg vPA = pz ∧
        c.mem = upd (upd m pz (sgnBit (rnd md (a * α + b * β) γ))) (pz + 1)
          (rnd md (a * α + b * β) γ).natAbs)
      (LF R (sw m pz (rnd md (a * α + b * β) γ)) n j (pz + 2) (pw + 2) α β γ) 4 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
      fun c ⟨⟨hc, hn, hk, ⟨hal0, hal1⟩, ⟨hbe0, hbe1⟩, ⟨hga0, hga1⟩, hpz, hpw⟩, _, _, hm⟩ => by
      refine ⟨⟨(hR.mono (by decide)).run (by decide) hc, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_,
        ?_⟩, ?_⟩ <;>
      simp +decide only [run_seq', run_addc, setReg_reg, setReg_mem, ↓reduceIte, hn, hk, hal0,
        hal1, hbe0, hbe1, hga0, hga1, hpz, hpw, hm]
      rfl
  refine ((h1.pre fun c hc => ⟨hc, hc.1.2.2.2.2.2.2.1, by rw [hc.2]; exact ha⟩).seq
    ((h2.pre fun c ⟨hc, hx⟩ => ⟨⟨hc, hx⟩, hc.1.2.2.2.1⟩).seq
    ((h3.pre fun c ⟨⟨hc, hx⟩, hy⟩ => ⟨hc, hx, hy⟩).seq
    (h4.seq
    ((h5.pre fun c hc => ⟨hc, hc.1.1.2.2.2.2.2.2.2, by rw [hc.1.2]; exact hb⟩).seq
    ((h6.pre fun c ⟨hc, hx⟩ => ⟨⟨hc, hx⟩, hc.1.1.2.2.2.2.1⟩).seq
    ((h7.pre fun c ⟨⟨⟨hc, hs⟩, hx⟩, hy⟩ => ⟨⟨hc, hs⟩, hx, hy⟩).seq
    ((h8.pre fun c ⟨⟨hc, hs⟩, hz'⟩ => ⟨⟨hc, hs⟩, hz'⟩).seq
    ((h9.pre fun c ⟨⟨hc, hs⟩, hy⟩ => ⟨hc, hs, hy⟩).seq
    ((h10.pre fun c ⟨hc, hs⟩ => ⟨hc, hs, hc.1.2.2.2.2.2.1⟩).seq
    ((h11.pre fun c ⟨hc, hz'⟩ => ⟨hc.1, hz', hc.1.2.2.2.2.2.2.1, hc.2⟩).seq
      h12))))))))))).weaken ?_
  simp only [smulCost, gCost]
  omega

/-- The new entries `rnd md (α z_j + β w_j) γ`. -/
def linNew (md : Bool) (α β γ : ℤ) (z w : ℕ → ℤ) (j : ℕ) : ℤ := rnd md (α * z j + β * w j) γ

/-- The state of `linCore` after `j` elements. -/
def LInv (md : Bool) (R : Config → Prop) (m₀ : ℕ → ℕ) (n pz pw : ℕ) (α β γ : ℤ) (z w : ℕ → ℤ)
    (j : ℕ) (c : Config) : Prop :=
  R c ∧ c.reg vN = n ∧ SReg c vAl α ∧ SReg c vBe β ∧ SReg c vGa γ ∧ c.reg vPA = pz + j * 2 ∧
    c.reg vPX = pw + j * 2 ∧ c.mem = wrArr m₀ pz 2 (linNew md α β γ z w) j

/-- **Elementwise update within the bound** `z_j := rnd md (α z_j + β w_j) γ` (`j < n`) in place
on the contiguous signed vector `z` at `pz` (below `rFREE = F`), with `w` contiguous at `pw`
(readable in every memory agreeing with `m₀` outside `z`'s block), in `n · (124 B + 286) + 3`
steps, `B` bounding the bit lengths of `|α|, |β|, |z_j|, |w_j|`. Inputs: `vN = n`, `vPA = pz`,
`vPX = pw`, pairs `vAl = α`, `vBe = β`, `vGa = γ`. `R`: any register-only assertion not about
`linW`. Space: the scratch tables (`8 B + 6` cells from `F`, `hS`) and `w` (`hwS`) below `S`. -/
theorem linCore_specB (md : Bool) {S : ℕ} {R : Config → Prop} (hR : RegIndep linW R)
    (m₀ : ℕ → ℕ) (F n pz pw B : ℕ) (α β γ : ℤ) (z w : ℕ → ℤ) (hz : ZeroFrom m₀ F)
    (hF : ∀ c, R c → c.reg rFREE = F) (hpz : pz + n * 2 ≤ F) (hZr : SArr m₀ pz 2 n z)
    (hw : ∀ m, SameOn (fun a => ¬ (pz ≤ a ∧ a < pz + n * 2)) m₀ m → SArr m pw 2 n w)
    (hγ : GoodDiv md γ) (hα : Nat.size α.natAbs ≤ B) (hβ : Nat.size β.natAbs ≤ B)
    (hzB : ∀ j < n, Nat.size (z j).natAbs ≤ B) (hwB : ∀ j < n, Nat.size (w j).natAbs ≤ B)
    (hS : F + 8 * B + 6 ≤ S) (hwS : pw + n * 2 ≤ S) :
    HTB S (linCore md) (fun c => R c ∧ c.mem = m₀ ∧ c.reg vN = n ∧ c.reg vPA = pz ∧
        c.reg vPX = pw ∧ SReg c vAl α ∧ SReg c vBe β ∧ SReg c vGa γ)
      (LInv md R m₀ n pz pw α β γ z w n) (n * (124 * B + 286) + 3) := by
  have hl := HTB.forUpC (S := S) (i := vK) (n := vN) (N := n) (body := linBody md)
    (LInv md R m₀ n pz pw α β γ z w) (124 * B + 282) (by decide) (by decide) (by decide)
    (fun j => (hR.mono (by decide)).indep.and (by indep [SReg]))
    (fun j hj => by
      set mj := wrArr m₀ pz 2 (linNew md α β γ z w) j
      have hzj : ZeroFrom mj F := zeroFrom_wrArr (le_refl 2) hz (by omega)
      have hsame : SameOn (fun a => ¬ (pz ≤ a ∧ a < pz + n * 2)) m₀ mj := fun a ha =>
        sameOn_wrArr (le_refl 2) j a (by
          have : j * 2 ≤ n * 2 := by omega
          omega)
      have ha : SMem mj (pz + j * 2) (z j) := by
        obtain ⟨h0, h1⟩ := hZr j hj
        exact ⟨(wrArr_of_out (le_refl 2) (by omega)).trans h0,
          (wrArr_of_out (le_refl 2) (by omega)).trans h1⟩
      have hb : SMem mj (pw + j * 2) (w j) := hw mj hsame j hj
      have hs := size_lin_le (hzB j hj) hα (hwB j hj) hβ
      have hb' := linBody_specB md (S := S) hR mj F n j (pz + j * 2) (pw + j * 2) α β γ (z j) (w
          j) hzj hF
        ha hb hγ (by omega) (by omega) (by omega)
      refine hb'.mono (fun c ⟨⟨hc, hn, hal, hbe, hga, hpz', hpw', hm⟩, hk, _⟩ =>
          ⟨⟨hc, hn, hk, hal, hbe, hga, hpz', hpw'⟩, hm⟩)
        (fun c ⟨⟨hc, hn, hk, hal, hbe, hga, hpz', hpw'⟩, hm⟩ => ⟨⟨hc, hn, hal, hbe, hga,
          by rw [hpz']; ring, by rw [hpw']; ring, ?_⟩, hk, hn⟩) ?_
      · rw [hm, wrArr_succ]
        simp only [linNew, mj]
        rw [mul_comm (z j), mul_comm (w j)]
      · omega)
  refine (hl.pre fun c ⟨hc, hm, hn, hpz', hpw', hal, hbe, hga⟩ =>
    ⟨⟨hc, hn, hal, hbe, hga, by simpa using hpz', by simpa using hpw', hm⟩, hn⟩).mono
    (fun _ h => h) (fun c ⟨h, _⟩ => h) le_rfl

/-! ### Rank-one update -/

/-- The rows `0, …, i − 1` of `A'` written (row `k` at `pa + k·si`, `nc` contiguous entries). -/
def wrRows (m₀ : ℕ → ℕ) (pa si nc : ℕ) (A' : ℕ → ℕ → ℤ) : ℕ → ℕ → ℕ
  | 0 => m₀
  | i + 1 => wrArr (wrRows m₀ pa si nc A' i) (pa + i * si) 2 (A' i) nc

theorem wrRows_of_out {m₀ : ℕ → ℕ} {pa si nc : ℕ} {A' : ℕ → ℕ → ℤ} (hsi : nc * 2 ≤ si) :
    ∀ {i a : ℕ}, (a < pa ∨ pa + i * si ≤ a) → wrRows m₀ pa si nc A' i a = m₀ a
  | 0, _, _ => rfl
  | i + 1, a, h => by
    have e : pa + i * si + si = pa + (i + 1) * si := by ring
    simp only [wrRows]
    rw [wrArr_of_out (le_refl 2) (by omega)]
    exact wrRows_of_out hsi (by omega)

theorem sameOn_wrRows {m₀ : ℕ → ℕ} {pa si nc : ℕ} {A' : ℕ → ℕ → ℤ} (hsi : nc * 2 ≤ si) (i : ℕ) :
    SameOn (fun a => ¬ (pa ≤ a ∧ a < pa + i * si)) m₀ (wrRows m₀ pa si nc A' i) := fun a ha =>
  wrRows_of_out hsi (by omega)

theorem zeroFrom_wrRows {m₀ : ℕ → ℕ} {pa si nc F : ℕ} {A' : ℕ → ℕ → ℤ} (hsi : nc * 2 ≤ si)
    (hz : ZeroFrom m₀ F) {i : ℕ} (hi : pa + i * si ≤ F) : ZeroFrom (wrRows m₀ pa si nc A' i) F :=
  fun a ha => by rw [wrRows_of_out hsi (by omega)]; exact hz a ha

/-- Row `i < r` of the written matrix. -/
theorem sarr_wrRows {m₀ : ℕ → ℕ} {pa si nc : ℕ} {A' : ℕ → ℕ → ℤ} (hsi : nc * 2 ≤ si) {i : ℕ} :
    ∀ r, i < r → SArr (wrRows m₀ pa si nc A' r) (pa + i * si) 2 nc (A' i)
  | 0, h => absurd h (Nat.not_lt_zero _)
  | r + 1, h => by
    simp only [wrRows]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · intro j hj
      obtain ⟨h0, h1⟩ := sarr_wrRows hsi r h j hj
      have hr : i * si + si ≤ r * si := by
        have := Nat.mul_le_mul_right si (show i + 1 ≤ r by omega); rw [Nat.add_mul] at this; omega
      exact ⟨(wrArr_of_out (le_refl 2) (by omega)).trans h0,
        (wrArr_of_out (le_refl 2) (by omega)).trans h1⟩
    · exact sarr_wrArr (le_refl 2) nc

/-- The new matrix `rnd md (α A_{ij} + β u_i v_j) γ`. -/
def r1New (md : Bool) (α β γ : ℤ) (A : ℕ → ℕ → ℤ) (u v : ℕ → ℤ) (i j : ℕ) : ℤ :=
  rnd md (α * A i j + β * u i * v j) γ

/-- One row of the rank-one update. -/
def r1Body (md : Bool) : Stmt :=
  .seq (dec vR) (.seq (sload mX vPU) (.seq (smov mY vB0) (.seq smulCore (.seq (smov vBe mZ)
    (.seq (.seq (mov vPA vRow) (mov vPX vX0)) (.seq (linCore md)
      (.seq (addc vPU vPU 2) (.add vRow vRow vSI))))))))

/-- `A := rnd md (α A + β u vᵀ) γ` (`vR` rows, consumed). -/
def r1Core (md : Bool) : Stmt := .loop vR (r1Body md)

/-- The registers written by `r1Core`. -/
def r1W : List ℕ := vR :: vRow :: vPU :: vBe :: (vBe + 1) :: linW

/-- The state of `r1Core`. -/
def R1Inv (md : Bool) (R : Config → Prop) (m₀ : ℕ → ℕ) (r nc pa si pu pv : ℕ) (α β γ : ℤ)
    (A : ℕ → ℕ → ℤ) (u v : ℕ → ℤ) (c : Config) : Prop :=
  R c ∧ c.reg vR ≤ r ∧ c.mem = wrRows m₀ pa si nc (r1New md α β γ A u v) (r - c.reg vR) ∧
    c.reg vRow = pa + (r - c.reg vR) * si ∧ c.reg vPU = pu + (r - c.reg vR) * 2 ∧
    c.reg vSI = si ∧ c.reg vN = nc ∧ c.reg vX0 = pv ∧ SReg c vB0 β ∧ SReg c vAl α ∧ SReg c vGa γ

/-- **Rank-one update** `A_{ij} := rnd md (α A_{ij} + β u_i v_j) γ` (`i < r`, `j < nc`) in place:
row `i` of `A` is the contiguous signed vector at `pa + i·si` (`si ≥ 2 nc`, the whole below
`rFREE = F`), `u` (length `r`) at `pu`, `v` (length `nc`) at `pv`, both contiguous and readable
in every memory agreeing with `m₀` outside `[pa, pa + r·si)`; in
`r · (nc · (248 B + 286) + 31 B + 60) + 1` steps, `B` bounding the bit lengths of
`|α|, |β|, |A_{ij}|, |u_i|, |v_j|`. Inputs: `vR = r` (consumed), `vRow = pa`, `vSI = si`, `vN = nc`,
`vPU = pu`, `vX0 = pv`, pairs `vB0 = β`, `vAl = α`, `vGa = γ`. -/
theorem r1Core_specB (md : Bool) {S : ℕ} {R : Config → Prop} (hR : RegIndep r1W R)
    (m₀ : ℕ → ℕ) (F r nc pa si pu pv B : ℕ) (α β γ : ℤ) (A : ℕ → ℕ → ℤ) (u v : ℕ → ℤ)
    (hz : ZeroFrom m₀ F) (hF : ∀ c, R c → c.reg rFREE = F) (hsi : nc * 2 ≤ si)
    (hpa : pa + r * si ≤ F) (hA : ∀ i < r, SArr m₀ (pa + i * si) 2 nc (A i))
    (hu : ∀ m, SameOn (fun a => ¬ (pa ≤ a ∧ a < pa + r * si)) m₀ m → SArr m pu 2 r u)
    (hv : ∀ m, SameOn (fun a => ¬ (pa ≤ a ∧ a < pa + r * si)) m₀ m → SArr m pv 2 nc v)
    (hγ : GoodDiv md γ) (hα : Nat.size α.natAbs ≤ B) (hβ : Nat.size β.natAbs ≤ B)
    (hAB : ∀ i < r, ∀ j < nc, Nat.size (A i j).natAbs ≤ B)
    (huB : ∀ i < r, Nat.size (u i).natAbs ≤ B) (hvB : ∀ j < nc, Nat.size (v j).natAbs ≤ B)
    (hS : F + 16 * B + 6 ≤ S) (huS : pu + r * 2 ≤ S) (hvS : pv + nc * 2 ≤ S) :
    HTB S (r1Core md) (fun c => R c ∧ c.mem = m₀ ∧ c.reg vR = r ∧ c.reg vRow = pa ∧ c.reg vSI = si ∧
        c.reg vN = nc ∧ c.reg vPU = pu ∧ c.reg vX0 = pv ∧ SReg c vB0 β ∧ SReg c vAl α ∧
        SReg c vGa γ)
      (fun c => R1Inv md R m₀ r nc pa si pu pv α β γ A u v c ∧ c.reg vR = 0)
      (r * (nc * (248 * B + 286) + 31 * B + 60) + 1) := by
  have hloop := HTB.loopT (S := S) (a := vR) (body := r1Body md)
    (Inv := R1Inv md R m₀ r nc pa si pu pv α β γ A u v) (fun c => c.reg vR)
    (T := nc * (248 * B + 286) + 31 * B + 59) (fun w => by
      refine HTB.of_forall fun c₀ ⟨hI, hne, hw⟩ => ?_
      obtain ⟨hRc, hvr, hm, hrow, hpu', hsi', hn, hx0, hb0, hal, hga⟩ := hI
      set i := r - c₀.reg vR with hi
      have hir : i < r := by omega
      set mi := wrRows m₀ pa si nc (r1New md α β γ A u v) i with hmi
      have hisi : i * si + si ≤ r * si := by
        have := Nat.mul_le_mul_right si (show i + 1 ≤ r by omega); rw [Nat.add_mul] at this; omega
      have hsame : SameOn (fun a => ¬ (pa ≤ a ∧ a < pa + r * si)) m₀ mi := fun a ha =>
        sameOn_wrRows hsi i a (by omega)
      have hzi : ZeroFrom mi F := zeroFrom_wrRows hsi hz (by omega)
      have hui : SMem mi (pu + i * 2) (u i) := hu mi hsame i hir
      -- the frame kept through the row
      let G : Config → Prop := fun c => R c ∧ c.reg vR = c₀.reg vR - 1 ∧
        c.reg vRow = pa + i * si ∧ c.reg vPU = pu + i * 2 ∧ c.reg vSI = si ∧ c.reg vN = nc ∧
        c.reg vX0 = pv ∧ SReg c vB0 β ∧ SReg c vAl α ∧ SReg c vGa γ
      have hGr : RegIndep (vBe :: (vBe + 1) :: linW) G := (hR.mono fun r hr => by
          simp only [r1W, List.mem_cons] at hr ⊢; tauto).and (by indep [SReg])
      have hGm : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ vBe :: (vBe + 1) :: coreW) →
          Indep W (fun c => G c ∧ c.mem = mi) := fun hW =>
        ((hGr.mono fun r hr => by
          have := hW r hr; simp only [linW, List.mem_cons] at this ⊢; tauto).indep).and
          (Indep.mem (· = mi))
      have h1 : HTB S (dec vR) (fun c => c = c₀) (fun c => (G c ∧ c.mem = mi)) 2 :=
        HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => by
          subst hc
          obtain ⟨hb00, hb01⟩ := hb0
          obtain ⟨hal0, hal1⟩ := hal
          obtain ⟨hga0, hga1⟩ := hga
          refine ⟨⟨(hR.mono (by decide)).run (by decide) hRc, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩,
            ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩ <;>
          simp +decide only [run_dec, setReg_reg, setReg_mem, ↓reduceIte, hm, hrow, hpu', hsi', hn,
            hx0, hmi, hb00, hb01, hal0, hal1, hga0, hga1]
      have h2 := HTB.sload (S := S) (P := fun c => G c ∧ c.mem = mi) (d := mX) (p := vPU)
        (a := pu + i * 2) (z := u i) (by decide) (by decide) (by decide) (hGm (by decide))
        (by omega)
      have h3 := HTB.smov (S := S) (P := fun c => (G c ∧ c.mem = mi) ∧ SReg c mX (u i)) (d := mY)
        (x := vB0) (z := β) (by decide) (by decide) (by decide) (by decide)
        ((hGm (by decide)).and (indep_sreg (by decide) (by decide) _))
      have h4 := smulCore_specB (S := S) (P := fun c => G c ∧ c.mem = mi) (hGm (by decide))
        (fun c hc => by rw [hc.2, hF c hc.1.1]; exact hzi) (u i) β
        (fun c hc => by rw [hF c hc.1.1]; omega)
      have h5 := HTB.smov (S := S) (P := fun c => G c ∧ c.mem = mi) (d := vBe) (x := mZ)
        (z := u i * β) (by decide) (by decide) (by decide) (by decide) (hGm (by decide))
      have h6 : HTB S (.seq (mov vPA vRow) (mov vPX vX0))
          (fun c => (G c ∧ c.mem = mi) ∧ SReg c vBe (u i * β))
          (fun c => G c ∧ c.mem = mi ∧ c.reg vN = nc ∧ c.reg vPA = pa + i * si ∧ c.reg vPX = pv ∧
            SReg c vAl α ∧ SReg c vBe (u i * β) ∧ SReg c vGa γ) 4 :=
        HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨hc, hmm⟩, hbe⟩ => by
          have hc' : G (RAM.run (.seq (mov vPA vRow) (mov vPX vX0)) c) :=
            (hGr.mono (by decide)).run (by decide) hc
          have hbe' := (regIndep_sreg (W := [rT, vPA, rT, vPX]) (r := vBe) (by decide) (by decide)
            (u i * β)).run (s := .seq (mov vPA vRow) (mov vPX vX0)) (by decide) hbe
          refine ⟨hc', ?_, hc'.2.2.2.2.2.1, ?_, ?_, hc'.2.2.2.2.2.2.2.2.1, hbe',
            hc'.2.2.2.2.2.2.2.2.2⟩ <;>
          simp +decide only [run_seq', run_mov, setReg_reg, setReg_mem, ↓reduceIte, hmm, hc.2.2.1,
            hc.2.2.2.2.2.2.1]
      have h7 := linCore_specB md (S := S) (R := G) (hGr.mono fun r hr => List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ hr)) mi F nc (pa + i * si) pv (2 * B) α (u i * β) γ (A i) v hzi
        (fun c hc => hF c hc.1) (by omega)
        (fun j hj => by
          obtain ⟨h0, h1⟩ := hA i hir j hj
          exact ⟨(wrRows_of_out hsi (by omega)).trans h0, (wrRows_of_out hsi (by omega)).trans h1⟩)
        (fun m hm' => hv m fun a ha => by
          by_cases hrow : pa + i * si ≤ a ∧ a < pa + i * si + nc * 2
          · exact absurd ⟨by omega, by omega⟩ ha
          · rw [hm' a hrow]; exact hsame a ha)
        hγ (by omega) (le_trans (size_mul_le (huB i hir) hβ) (by omega))
        (fun j hj => by have := hAB i hir j hj; omega) (fun j hj => by have := hvB j hj; omega)
        (by omega) hvS
      have h8 : HTB S (.seq (addc vPU vPU 2) (.add vRow vRow vSI))
          (LInv md G mi nc (pa + i * si) pv α (u i * β) γ (A i) v nc)
          (fun c => R1Inv md R m₀ r nc pa si pu pv α β γ A u v c ∧ c.reg vR < w) 3 :=
        HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨hc, hvR, hrow', hpu'', hsi'',
            hn', hx0', hb0',
            hal', hga'⟩, _, _, _, _, _, _, hmem⟩ => by
          have hk : r - (c₀.reg vR - 1) = i + 1 := by omega
          have hrun := (regIndep_sreg (W := [rT, vPU, vRow]) (r := vB0) (by decide) (by decide)
            β).run (s := .seq (addc vPU vPU 2) (.add vRow vRow vSI)) (by decide) hb0'
          have hrun2 := (regIndep_sreg (W := [rT, vPU, vRow]) (r := vAl) (by decide) (by decide)
            α).run (s := .seq (addc vPU vPU 2) (.add vRow vRow vSI)) (by decide) hal'
          have hrun3 := (regIndep_sreg (W := [rT, vPU, vRow]) (r := vGa) (by decide) (by decide)
            γ).run (s := .seq (addc vPU vPU 2) (.add vRow vRow vSI)) (by decide) hga'
          refine ⟨⟨(hR.mono (by decide)).run (by decide) hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrun,
            hrun2,
            hrun3⟩, ?_⟩ <;>
          simp +decide only [run_seq', run_addc, run_add, setReg_reg, setReg_mem, ↓reduceIte, hvR,
            hrow', hpu'', hsi'', hn', hx0', hmem, hk]
          · omega
          · simp only [wrRows, mi]
            congr 1
            funext j
            simp only [linNew, r1New]
            ring_nf
          · ring
          · ring
          · omega
      refine (h1.seq ((h2.pre fun c hc => ⟨hc, hc.1.2.2.2.1, by rw [hc.2]; exact hui⟩).seq
        ((h3.pre fun c ⟨hc, hx⟩ => ⟨⟨hc, hx⟩, hc.1.2.2.2.2.2.2.2.1⟩).seq
        ((h4.pre fun c ⟨⟨hc, hx⟩, hy⟩ => ⟨hc, hx, hy⟩).seq (h5.seq (h6.seq (h7.seq h8))))))).weaken
        ?_
      have := size_mul_le (huB i hir) hβ
      simp only [smulCost, gCost]
      have : Nat.size β.natAbs * 31 ≤ B * 31 := Nat.mul_le_mul_right 31 hβ
      nlinarith) r
  refine (hloop.pre fun c ⟨hRc, hm, hvr, hrow, hsi', hn, hpu', hx0, hb0, hal, hga⟩ =>
    ⟨⟨hRc, le_of_eq hvr, ?_, ?_, ?_, hsi', hn, hx0, hb0, hal, hga⟩, le_of_eq hvr⟩).weaken le_rfl
  · rw [hvr, Nat.sub_self]; exact hm
  · rw [hvr, Nat.sub_self]; simpa using hrow
  · rw [hvr, Nat.sub_self]; simpa using hpu'

/-! ### Elementwise update with a divided term -/

/-- `δ` (pair `444, 445`). -/
abbrev vDe : ℕ := 444

/-- The registers written by `axCore`. -/
def axW : List ℕ := vK :: vPA :: vPX :: coreW

/-- One element: `z_j := z_j α + rnd md (w_j δ) γ · β`, advance both pointers. -/
def axBody (md : Bool) : Stmt :=
  .seq (sload mX vPX) (.seq (smov mY vDe) (.seq smulCore
  (.seq (smov sZ mZ) (.seq (divStep md)
  (.seq (smov mX mZ) (.seq (smov mY vBe) (.seq smulCore
  (.seq (smov sY mZ)
  (.seq (sload mX vPA) (.seq (smov mY vAl) (.seq smulCore
  (.seq (smov sX mZ) (.seq saddCore
  (.seq (sstore vPA sZ)
  (.seq (addc vPA vPA 2) (addc vPX vPX 2))))))))))))))))

/-- `z_j := α z_j + β · rnd md (δ w_j) γ` for `j < reg vN`. -/
def axCore (md : Bool) : Stmt := forUp vK vN (axBody md)

/-- The registers of an `axCore` step. -/
def AR (R : Config → Prop) (n j pz pw : ℕ) (α β γ δ : ℤ) (c : Config) : Prop :=
  R c ∧ c.reg vN = n ∧ c.reg vK = j ∧ SReg c vAl α ∧ SReg c vBe β ∧ SReg c vGa γ ∧
    SReg c vDe δ ∧ c.reg vPA = pz ∧ c.reg vPX = pw

theorem AR_regIndep {R : Config → Prop} (hR : RegIndep axW R) (n j pz pw : ℕ) (α β γ δ : ℤ)
    {W : List ℕ} (hW : ∀ r ∈ W, r ∈ coreW) : RegIndep W (AR R n j pz pw α β γ δ) := by
  have hn : ∀ r, r ∉ coreW → r ∉ W := fun r h h' => h (hW r h')
  exact (hR.mono fun r hr => by
      have := hW r hr; simp only [axW, List.mem_cons]; tauto).and
    ((RegIndep.reg (hn _ (by decide)) (· = n)).and ((RegIndep.reg (hn _ (by decide)) (· = j)).and
    ((regIndep_sreg (hn _ (by decide)) (hn _ (by decide)) α).and
    ((regIndep_sreg (hn _ (by decide)) (hn _ (by decide)) β).and
    ((regIndep_sreg (hn _ (by decide)) (hn _ (by decide)) γ).and
    ((regIndep_sreg (hn _ (by decide)) (hn _ (by decide)) δ).and
    ((RegIndep.reg (hn _ (by decide)) (· = pz)).and
      (RegIndep.reg (hn _ (by decide)) (· = pw)))))))))

/-- **One `axCore` step**, for `a = z_j`, `b = w_j` in memory `m`, within the bound `S` (the
scratch tables from `F` and the two entries below `S`). -/
theorem axBody_specB (md : Bool) {S : ℕ} {R : Config → Prop} (hR : RegIndep axW R) (m : ℕ → ℕ)
    (F n j pz pw : ℕ) (α β γ δ a b : ℤ) (hz : ZeroFrom m F) (hF : ∀ c, R c → c.reg rFREE = F)
    (ha : SMem m pz a) (hb : SMem m pw b) (hγ : GoodDiv md γ)
    (hS : F + 2 * (Nat.size α.natAbs + Nat.size β.natAbs + Nat.size δ.natAbs +
      Nat.size (b * δ).natAbs + 2) ≤ S) (hpz : pz + 1 < S) (hpw : pw + 1 < S) :
    HTB S (axBody md) (fun c => AR R n j pz pw α β γ δ c ∧ c.mem = m)
      (fun c => AR R n j (pz + 2) (pw + 2) α β γ δ c ∧
        c.mem = sw m pz (a * α + rnd md (b * δ) γ * β))
      (31 * (Nat.size α.natAbs + Nat.size β.natAbs + Nat.size δ.natAbs +
        Nat.size (b * δ).natAbs) + 298) := by
  set q := rnd md (b * δ) γ
  let L : Config → Prop := fun c => AR R n j pz pw α β γ δ c ∧ c.mem = m
  have hL : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ coreW) → Indep W L :=
    fun hW => (AR_regIndep hR n j pz pw α β γ δ hW).indep.and (Indep.mem (· = m))
  have hZL : ∀ c, L c → ZeroFrom c.mem (c.reg rFREE) := fun c h => by
    rw [h.2, hF c h.1.1]; exact hz
  have hRF : ∀ c, L c → c.reg rFREE = F := fun c h => hF c h.1.1
  have hLs : ∀ {W : List ℕ} {r : ℕ} (z : ℤ), (∀ r ∈ W, r ∈ coreW) → r ∉ W → r + 1 ∉ W →
      Indep W (fun c => L c ∧ SReg c r z) := fun z hW h0 h1 => (hL hW).and (indep_sreg h0 h1 z)
  -- w_j · δ, divided
  have h1 := HTB.sload (S := S) (P := L) (d := mX) (p := vPX) (a := pw) (z := b)
    (by decide) (by decide) (by decide) (hL (by decide)) hpw
  have h2 := HTB.smov (S := S) (P := fun c => L c ∧ SReg c mX b) (d := mY) (x := vDe) (z := δ)
    (by decide) (by decide) (by decide) (by decide) (hLs b (by decide) (by decide) (by decide))
  have h3 := smulCore_specB (S := S) (P := L) (hL (by decide)) hZL b δ
    (fun c h => by rw [hRF c h]; omega)
  have h4 := HTB.smov (S := S) (P := L) (d := sZ) (x := mZ) (z := b * δ) (by decide) (by decide)
    (by decide) (by decide) (hL (by decide))
  have h5 := divStep_specB md (S := S) (P := L) (hL (by decide)) hZL (b * δ) γ hγ
    (fun c h => by rw [hRF c h]; omega)
  -- times β
  have h6 := HTB.smov (S := S) (P := L) (d := mX) (x := mZ) (z := q) (by decide) (by decide)
    (by decide) (by decide) (hL (by decide))
  have h7 := HTB.smov (S := S) (P := fun c => L c ∧ SReg c mX q) (d := mY) (x := vBe) (z := β)
    (by decide) (by decide) (by decide) (by decide) (hLs q (by decide) (by decide) (by decide))
  have h8 := smulCore_specB (S := S) (P := L) (hL (by decide)) hZL q β
    (fun c h => by rw [hRF c h]; omega)
  have h9 := HTB.smov (S := S) (P := L) (d := sY) (x := mZ) (z := q * β) (by decide) (by decide)
    (by decide) (by decide) (hL (by decide))
  -- z_j · α
  have h10 := HTB.sload (S := S) (P := fun c => L c ∧ SReg c sY (q * β)) (d := mX) (p := vPA)
    (a := pz) (z := a) (by decide) (by decide) (by decide)
    (hLs _ (by decide) (by decide) (by decide)) hpz
  have h11 := HTB.smov (S := S) (P := fun c => (L c ∧ SReg c sY (q * β)) ∧ SReg c mX a) (d := mY)
    (x := vAl) (z := α) (by decide) (by decide) (by decide) (by decide)
    ((hLs _ (by decide) (by decide) (by decide)).and (indep_sreg (by decide) (by decide) a))
  have h12 := smulCore_specB (S := S) (P := fun c => L c ∧ SReg c sY (q * β))
    (hLs _ (by decide) (by decide) (by decide)) (fun c h => hZL c h.1) a α
    (fun c h => by rw [hRF c h.1]; omega)
  have h13 := HTB.smov (S := S) (P := fun c => L c ∧ SReg c sY (q * β)) (d := sX) (x := mZ)
    (z := a * α) (by decide) (by decide) (by decide) (by decide)
    (hLs _ (by decide) (by decide) (by decide))
  have h14 := saddCore_specB (S := S) (P := L) (hL (by decide)) (a * α) (q * β)
  have h15 := HTB.sstore (S := S) (F := AR R n j pz pw α β γ δ) (p := vPA) (x := sZ) (a := pz)
    (z := a * α + q * β) (m := m) (by decide) (by decide) (by decide)
    (AR_regIndep hR n j pz pw α β γ δ (by decide)) hpz
  have h16 : HTB S (.seq (addc vPA vPA 2) (addc vPX vPX 2))
      (fun c => AR R n j pz pw α β γ δ c ∧ SReg c sZ (a * α + q * β) ∧ c.reg vPA = pz ∧
        c.mem = upd (upd m pz (sgnBit (a * α + q * β))) (pz + 1) (a * α + q * β).natAbs)
      (fun c => AR R n j (pz + 2) (pw + 2) α β γ δ c ∧ c.mem = sw m pz (a * α + q * β)) 4 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
      fun c ⟨⟨hc, hn, hk, ⟨hal0, hal1⟩, ⟨hbe0, hbe1⟩, ⟨hga0, hga1⟩, ⟨hde0, hde1⟩, hpz, hpw⟩, _, _,
        hm⟩ => by
      refine ⟨⟨(hR.mono (by decide)).run (by decide) hc, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
        ⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩ <;>
      simp +decide only [run_seq', run_addc, setReg_reg, setReg_mem, ↓reduceIte, hn, hk, hal0,
        hal1, hbe0, hbe1, hga0, hga1, hde0, hde1, hpz, hpw, hm]
      rfl
  refine ((h1.pre fun c hc => ⟨hc, hc.1.2.2.2.2.2.2.2.2, by rw [hc.2]; exact hb⟩).seq
    ((h2.pre fun c ⟨hc, hx⟩ => ⟨⟨hc, hx⟩, hc.1.2.2.2.2.2.2.1⟩).seq
    ((h3.pre fun c ⟨⟨hc, hx⟩, hy⟩ => ⟨hc, hx, hy⟩).seq
    (h4.seq
    ((h5.pre fun c ⟨hc, hs⟩ => ⟨hc, hs, hc.1.2.2.2.2.2.1⟩).seq
    (h6.seq
    ((h7.pre fun c ⟨hc, hx⟩ => ⟨⟨hc, hx⟩, hc.1.2.2.2.2.1⟩).seq
    ((h8.pre fun c ⟨⟨hc, hx⟩, hy⟩ => ⟨hc, hx, hy⟩).seq
    (h9.seq
    ((h10.pre fun c hc => ⟨hc, hc.1.1.2.2.2.2.2.2.2.1, by rw [hc.1.2]; exact ha⟩).seq
    ((h11.pre fun c ⟨hc, hx⟩ => ⟨⟨hc, hx⟩, hc.1.1.2.2.2.1⟩).seq
    ((h12.pre fun c ⟨⟨hc, hx⟩, hy⟩ => ⟨hc, hx, hy⟩).seq
    ((h13.pre fun c ⟨⟨hc, hs⟩, hz'⟩ => ⟨⟨hc, hs⟩, hz'⟩).seq
    ((h14.pre fun c ⟨⟨hc, hs⟩, hy⟩ => ⟨hc, hy, hs⟩).seq
    ((h15.pre fun c ⟨hc, hz'⟩ => ⟨hc.1, hz', hc.1.2.2.2.2.2.2.2.1, hc.2⟩).seq
      h16))))))))))))))).weaken ?_
  simp only [smulCost, gCost]
  omega

/-- The new entries `α z_j + β · rnd md (δ w_j) γ`. -/
def axNew (md : Bool) (α β γ δ : ℤ) (z w : ℕ → ℤ) (j : ℕ) : ℤ :=
  α * z j + β * rnd md (δ * w j) γ

/-- The state of `axCore` after `j` elements. -/
def AInv (md : Bool) (R : Config → Prop) (m₀ : ℕ → ℕ) (n pz pw : ℕ) (α β γ δ : ℤ)
    (z w : ℕ → ℤ) (j : ℕ) (c : Config) : Prop :=
  R c ∧ c.reg vN = n ∧ SReg c vAl α ∧ SReg c vBe β ∧ SReg c vGa γ ∧ SReg c vDe δ ∧
    c.reg vPA = pz + j * 2 ∧ c.reg vPX = pw + j * 2 ∧
    c.mem = wrArr m₀ pz 2 (axNew md α β γ δ z w) j

/-- **Elementwise update with a divided term** `z_j := α z_j + β · rnd md (δ w_j) γ` (`j < n`) in
place on the contiguous signed vector `z` at `pz` (below `rFREE = F`), with `w` contiguous at
`pw` (readable in every memory agreeing with `m₀` outside `z`'s block), in
`n · (155 B + 302) + 3` steps, `B` bounding the bit lengths of `|α|, |β|, |δ|, |w_j|`. Inputs:
`vN = n`, `vPA = pz`, `vPX = pw`, pairs `vAl = α`, `vBe = β`, `vGa = γ`, `vDe = δ`. -/
theorem axCore_specB (md : Bool) {S : ℕ} {R : Config → Prop} (hR : RegIndep axW R)
    (m₀ : ℕ → ℕ) (F n pz pw B : ℕ) (α β γ δ : ℤ) (z w : ℕ → ℤ) (hz : ZeroFrom m₀ F)
    (hF : ∀ c, R c → c.reg rFREE = F) (hpz : pz + n * 2 ≤ F) (hZr : SArr m₀ pz 2 n z)
    (hw : ∀ m, SameOn (fun a => ¬ (pz ≤ a ∧ a < pz + n * 2)) m₀ m → SArr m pw 2 n w)
    (hγ : GoodDiv md γ) (hα : Nat.size α.natAbs ≤ B) (hβ : Nat.size β.natAbs ≤ B)
    (hδ : Nat.size δ.natAbs ≤ B) (hwB : ∀ j < n, Nat.size (w j).natAbs ≤ B)
    (hS : F + 10 * B + 4 ≤ S) (hwS : pw + n * 2 ≤ S) :
    HTB S (axCore md) (fun c => R c ∧ c.mem = m₀ ∧ c.reg vN = n ∧ c.reg vPA = pz ∧
        c.reg vPX = pw ∧ SReg c vAl α ∧ SReg c vBe β ∧ SReg c vGa γ ∧ SReg c vDe δ)
      (AInv md R m₀ n pz pw α β γ δ z w n) (n * (155 * B + 302) + 3) := by
  have hl := HTB.forUpC (S := S) (i := vK) (n := vN) (N := n) (body := axBody md)
    (AInv md R m₀ n pz pw α β γ δ z w) (155 * B + 298) (by decide) (by decide) (by decide)
    (fun j => (hR.mono (by decide)).indep.and (by indep [SReg]))
    (fun j hj => by
      set mj := wrArr m₀ pz 2 (axNew md α β γ δ z w) j
      have hzj : ZeroFrom mj F := zeroFrom_wrArr (le_refl 2) hz (by omega)
      have hsame : SameOn (fun a => ¬ (pz ≤ a ∧ a < pz + n * 2)) m₀ mj := fun a ha =>
        sameOn_wrArr (le_refl 2) j a (by
          have : j * 2 ≤ n * 2 := by omega
          omega)
      have ha : SMem mj (pz + j * 2) (z j) := by
        obtain ⟨h0, h1⟩ := hZr j hj
        exact ⟨(wrArr_of_out (le_refl 2) (by omega)).trans h0,
          (wrArr_of_out (le_refl 2) (by omega)).trans h1⟩
      have hb : SMem mj (pw + j * 2) (w j) := hw mj hsame j hj
      have hs := size_mul_le (hwB j hj) hδ
      have hb' := axBody_specB md (S := S) hR mj F n j (pz + j * 2) (pw + j * 2) α β γ δ (z j) (w
          j) hzj hF
        ha hb hγ (by omega) (by omega) (by omega)
      refine hb'.mono (fun c ⟨⟨hc, hn, hal, hbe, hga, hde, hpz', hpw', hm⟩, hk, _⟩ =>
          ⟨⟨hc, hn, hk, hal, hbe, hga, hde, hpz', hpw'⟩, hm⟩)
        (fun c ⟨⟨hc, hn, hk, hal, hbe, hga, hde, hpz', hpw'⟩, hm⟩ => ⟨⟨hc, hn, hal, hbe, hga, hde,
          by rw [hpz']; ring, by rw [hpw']; ring, ?_⟩, hk, hn⟩) ?_
      · rw [hm, wrArr_succ]
        simp only [axNew, mj]
        rw [mul_comm (z j), mul_comm (w j), mul_comm (rnd md (δ * w j) γ)]
      · omega)
  refine (hl.pre fun c ⟨hc, hm, hn, hpz', hpw', hal, hbe, hga, hde⟩ =>
    ⟨⟨hc, hn, hal, hbe, hga, hde, by simpa using hpz', by simpa using hpw', hm⟩, hn⟩).mono
    (fun _ h => h) (fun c ⟨h, _⟩ => h) le_rfl

end STACS2027.Runtimes.Arith
