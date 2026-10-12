module

public import Runtimes.ConvexQP.RAM.ArithSigned
public import Runtimes.ConvexQP.RAM.ArithSqrt
import Mathlib.Tactic

/-!
# Big-number arithmetic on the add/subtract RAM: the public macros

The macros of this file take their arguments in registers **outside** the library's block
`400–449` (a signed argument `x` is the pair `(x, x + 1)`, `SArg x`); they copy them into the
fixed registers of the cores (`ArithCore`, `ArithSigned`, `ArithSqrt`), run the core and copy
the result out, so the destination may coincide with an argument. Every triple is in frame
style: an assertion `P` independent of the destination registers and of `arithW` (`rT` and
`400–449`) survives; the macros that multiply, divide or take square roots also need
`ZeroFrom c.mem (c.reg rFREE)` from `P` (their scratch table lives there and is zeroed again;
the memory is unchanged).

| macro | effect | steps |
|---|---|---|
| `smov d x` | `d := x` (pair) | `4` |
| `sconst d z` | `d := z` | `2` |
| `sofNat d x` | `d := (reg x : ℤ)` | `3` |
| `sadd d x y`, `ssub d x y` | `d := x ± y` | `38`, `42` |
| `sneg d x` | `d := −x` | `12` |
| `sle d x y`, `slt d x y` | `reg d := [x ≤ y]`, `[x < y]` (`1`/`0`) | `23`, `25` |
| `isz d x` | `reg d := [x = 0]` | `3` |
| `smul d x y` | `d := x · y` | `smulCost y + 12` |
| `sdivmod q r x y` | `q := x / y`, `reg r := x % y` (`ediv/emod`, `y ≠ 0`) | `sdivCost x y + 14` |
| `sround d u v` | `d := roundDiv u (reg v)` (`reg v ≥ 1`) | `roundCost u + 10` |
| `isqrtN d x` | `reg d := Nat.sqrt (reg x)` | `isqrtCost (reg x) + 4` |
| `sload d p`, `sstore p x` | pair `d :=` cells `reg p, reg p + 1`; and back | `4`, `4` |

**Space.** Every macro has a bounded twin `HTB.foo` (same arguments, then the space hypotheses):
the memory-free ones by `HTB.of_HT rfl`; `HTB.smul`, `HTB.sdivmod`, `HTB.sround`, `HTB.isqrtN`
with `hS : ∀ c, P c → c.reg rFREE + K ≤ S` for their scratch table (masters `HTB.foo_pre` with
the bound in the precondition); `HTB.sload`, `HTB.sstore`
with `a + 1 < S` for the two cells.
-/

@[expose] public section

namespace STACS2027.Runtimes.Arith

open STACS2027.RAM

/-! ### Arguments and frames -/

/-- A signed argument: the pair `(x, x + 1)` lies outside the library's block (and `rT`). -/
def SArg (x : ℕ) : Prop := x ∉ arithW ∧ x + 1 ∉ arithW

instance (x : ℕ) : Decidable (SArg x) := inferInstanceAs (Decidable (_ ∧ _))

theorem SArg.indep {x : ℕ} (hx : SArg x) {W : List ℕ} (hW : ∀ r ∈ W, r ∈ arithW) (z : ℤ) :
    Indep W (fun c => SReg c x z) :=
  indep_sreg (fun h => hx.1 (hW _ h)) (fun h => hx.2 (hW _ h)) z

theorem SArg.ne {x r : ℕ} (hx : SArg x) (hr : r ∈ arithW) : x ≠ r ∧ x + 1 ≠ r :=
  ⟨fun h => hx.1 (h ▸ hr), fun h => hx.2 (h ▸ hr)⟩

/-- A frame for destinations `d₁, d₂` is a frame for every list of library registers. -/
theorem indep_ofArith {P : Config → Prop} {d₁ d₂ : ℕ} (hP : Indep (d₁ :: d₂ :: arithW) P)
    {W : List ℕ} (hW : ∀ r ∈ W, r ∈ arithW) : Indep W P :=
  hP.mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hW r hr))

/-- The free address is not a register of the library. -/
theorem free_not_mem {W : List ℕ} (hW : ∀ r ∈ W, r ∈ arithW) : rFREE ∉ W :=
  fun h => (by decide : rFREE ∉ arithW) (hW _ h)

/-- A frame `P` together with a bound on the free address. -/
theorem indep_and_free {P : Config → Prop} {W : List ℕ} (hP : Indep W P)
    (hW : ∀ r ∈ W, r ∈ arithW) (K S : ℕ) : Indep W (fun c => P c ∧ c.reg rFREE + K ≤ S) :=
  hP.and (indep_free (free_not_mem hW) K S)

/-! ### Copies -/

/-- `d := x` for pairs (`x + 1 ≠ d`). -/
def smov (d x : ℕ) : Stmt := .seq (mov d x) (mov (d + 1) (x + 1))

/-- **Pair copy** (`4` steps). -/
theorem HT.smov {P : Config → Prop} {d x : ℕ} {z : ℤ} (hx : x ≠ rT) (hx1 : x + 1 ≠ rT)
    (hdT : d ≠ rT) (hxd : x + 1 ≠ d) (hP : Indep [rT, d, d + 1] P) :
    HT (Arith.smov d x) (fun c => P c ∧ SReg c x z) (fun c => P c ∧ SReg c d z) 4 :=
  HT.run_le (by simp [Arith.smov, LoopFree]) (by simp [Arith.smov, size])
    fun c ⟨hc, h0, h1⟩ => by
      simp only [Arith.smov, run_seq', run_mov hx, run_mov hx1]
      refine ⟨hP.setReg (by simp) _ (hP.setReg (by simp) _ (hP.setReg (by simp) _
        (hP.setReg (by simp) _ hc))), ?_, ?_⟩
      · simp [hdT, h0]
      · simp [hxd, hx1, h1]

/-- **Pair copy** within any bound (memory-free). -/
theorem HTB.smov {S : ℕ} {P : Config → Prop} {d x : ℕ} {z : ℤ} (hx : x ≠ rT) (hx1 : x + 1 ≠ rT)
    (hdT : d ≠ rT) (hxd : x + 1 ≠ d) (hP : Indep [rT, d, d + 1] P) :
    HTB S (Arith.smov d x) (fun c => P c ∧ SReg c x z) (fun c => P c ∧ SReg c d z) 4 :=
  HTB.of_HT rfl (HT.smov hx hx1 hdT hxd hP)

/-- `d := z` (a constant). -/
def sconst (d : ℕ) (z : ℤ) : Stmt := .seq (.const d (sgnBit z)) (.const (d + 1) z.natAbs)

theorem HT.sconst {P : Config → Prop} {d : ℕ} (z : ℤ) (hP : Indep [d, d + 1] P) :
    HT (Arith.sconst d z) P (fun c => P c ∧ SReg c d z) 2 :=
  HT.run_le (by simp [Arith.sconst, LoopFree]) (by simp [Arith.sconst, size]) fun c hc => by
    exact ⟨hP.setReg (by simp) _ (hP.setReg (by simp) _ hc), by simp [Arith.sconst], by
      simp [Arith.sconst]⟩

theorem HTB.sconst {S : ℕ} {P : Config → Prop} {d : ℕ} (z : ℤ) (hP : Indep [d, d + 1] P) :
    HTB S (Arith.sconst d z) P (fun c => P c ∧ SReg c d z) 2 :=
  HTB.of_HT rfl (HT.sconst z hP)

/-- `d := (reg x : ℤ)` (`x ≠ rT`, `x ≠ d`). -/
def sofNat (d x : ℕ) : Stmt := .seq (.const d 0) (mov (d + 1) x)

theorem HT.sofNat {P : Config → Prop} {d x n : ℕ} (hx : x ≠ rT) (hdT : d ≠ rT) (hxd : x ≠ d)
    (hP : Indep [rT, d, d + 1] P) :
    HT (Arith.sofNat d x) (fun c => P c ∧ c.reg x = n) (fun c => P c ∧ SReg c d (n : ℤ)) 3 :=
  HT.run_le (by simp [Arith.sofNat, LoopFree]) (by simp [Arith.sofNat, size]) fun c ⟨hc, hn⟩ => by
    simp only [Arith.sofNat, run_seq', run_const, run_mov hx]
    refine ⟨hP.setReg (by simp) _ (hP.setReg (by simp) _ (hP.setReg (by simp) _ hc)), ?_, ?_⟩
    · simp [hdT, sgnBit]
    · simp [hxd, hn]

theorem HTB.sofNat {S : ℕ} {P : Config → Prop} {d x n : ℕ} (hx : x ≠ rT) (hdT : d ≠ rT)
    (hxd : x ≠ d) (hP : Indep [rT, d, d + 1] P) :
    HTB S (Arith.sofNat d x) (fun c => P c ∧ c.reg x = n) (fun c => P c ∧ SReg c d (n : ℤ)) 3 :=
  HTB.of_HT rfl (HT.sofNat hx hdT hxd hP)

/-! ### Addition, negation, comparison -/

/-- `d := x + y`. -/
def sadd (d x y : ℕ) : Stmt := .seq (smov sX x) (.seq (smov sY y) (.seq saddCore (smov d sZ)))

/-- **Signed addition** `d := x + y` (`38` steps). -/
theorem HT.sadd {P : Config → Prop} {d x y : ℕ} {u v : ℤ} (hx : SArg x) (hy : SArg y)
    (hd : SArg d) (hP : Indep (d :: (d + 1) :: arithW) P) :
    HT (Arith.sadd d x y) (fun c => P c ∧ SReg c x u ∧ SReg c y v)
      (fun c => P c ∧ SReg c d (u + v)) 38 := by
  have hW : ∀ r ∈ [rT, sX, sX + 1], r ∈ arithW := by decide
  have h1 := HT.smov (P := fun c => P c ∧ SReg c y v) (d := sX) (x := x) (z := u)
    (hx.ne (by decide)).1 (hx.ne (by decide)).2 (by decide) (hx.ne (by decide)).2
    ((indep_ofArith hP hW).and (hy.indep hW v))
  have h2 := HT.smov (P := fun c => P c ∧ SReg c sX u) (d := sY) (x := y) (z := v)
    (hy.ne (by decide)).1 (hy.ne (by decide)).2 (by decide) (hy.ne (by decide)).2
    ((indep_ofArith hP (by decide)).and (indep_sreg (by decide) (by decide) u))
  have h3 := saddCore_spec (P := P) (indep_ofArith hP (by decide)) u v
  have h4 := HT.smov (P := P) (d := d) (x := sZ) (z := u + v) (by decide) (by decide)
    (hd.ne (by decide)).1 (Ne.symm (hd.ne (show sZ + 1 ∈ arithW by decide)).1)
    (hP.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by decide))
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self)
  exact (h1.seq ((h2.pre fun c ⟨⟨hc, hy'⟩, hx'⟩ => ⟨⟨hc, hx'⟩, hy'⟩).seq
    ((h3.pre fun c ⟨⟨hc, hx'⟩, hy'⟩ => ⟨hc, hx', hy'⟩).seq h4))).mono
    (fun c ⟨hc, hx', hy'⟩ => ⟨⟨hc, hy'⟩, hx'⟩) (fun _ h => h) (by omega)

/-- **Signed addition** within any bound (memory-free). -/
theorem HTB.sadd {S : ℕ} {P : Config → Prop} {d x y : ℕ} {u v : ℤ} (hx : SArg x) (hy : SArg y)
    (hd : SArg d) (hP : Indep (d :: (d + 1) :: arithW) P) :
    HTB S (Arith.sadd d x y) (fun c => P c ∧ SReg c x u ∧ SReg c y v)
      (fun c => P c ∧ SReg c d (u + v)) 38 :=
  HTB.of_HT rfl (HT.sadd hx hy hd hP)

/-- Membership in `d :: (d + 1) :: arithW` of `rT, d, d + 1`. -/
theorem mem_dW {d r : ℕ} (hr : r ∈ [rT, d, d + 1]) : r ∈ d :: (d + 1) :: arithW := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by decide))
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

/-- Copy a library pair `z` out to an argument pair `d`. -/
theorem HT.smovOut {P : Config → Prop} {d z : ℕ} {w : ℤ} (hd : SArg d) (hz1 : z + 1 ∈ arithW)
    (hzT : z ≠ rT) (hz1T : z + 1 ≠ rT)
    (hP : Indep (d :: (d + 1) :: arithW) P) :
    HT (Arith.smov d z) (fun c => P c ∧ SReg c z w) (fun c => P c ∧ SReg c d w) 4 :=
  HT.smov hzT hz1T (hd.ne (by decide)).1 (Ne.symm (hd.ne hz1).1) (hP.mono fun _ => mem_dW)

theorem HTB.smovOut {S : ℕ} {P : Config → Prop} {d z : ℕ} {w : ℤ} (hd : SArg d)
    (hz1 : z + 1 ∈ arithW) (hzT : z ≠ rT) (hz1T : z + 1 ≠ rT)
    (hP : Indep (d :: (d + 1) :: arithW) P) :
    HTB S (Arith.smov d z) (fun c => P c ∧ SReg c z w) (fun c => P c ∧ SReg c d w) 4 :=
  HTB.of_HT rfl (HT.smovOut hd hz1 hzT hz1T hP)

/-- Copy an argument pair `x` into a library pair `z`, keeping a frame `F`. -/
theorem HT.smovIn {F : Config → Prop} {x z : ℕ} {w : ℤ} (hx : SArg x) (hz : z ∈ arithW)
    (hzT : z ≠ rT) (hF : Indep [rT, z, z + 1] F) :
    HT (Arith.smov z x) (fun c => F c ∧ SReg c x w) (fun c => F c ∧ SReg c z w) 4 :=
  HT.smov (hx.ne (by decide)).1 (hx.ne (by decide)).2 hzT (hx.ne hz).2 hF

theorem HTB.smovIn {S : ℕ} {F : Config → Prop} {x z : ℕ} {w : ℤ} (hx : SArg x) (hz : z ∈ arithW)
    (hzT : z ≠ rT) (hF : Indep [rT, z, z + 1] F) :
    HTB S (Arith.smov z x) (fun c => F c ∧ SReg c x w) (fun c => F c ∧ SReg c z w) 4 :=
  HTB.of_HT rfl (HT.smovIn hx hz hzT hF)

/-- `d := x − y`. -/
def ssub (d x y : ℕ) : Stmt :=
  .seq (smov sX x) (.seq (smov sY y) (.seq (sflip sY) (.seq saddCore (smov d sZ))))

/-- **Signed subtraction** `d := x − y` (`42` steps). -/
theorem HT.ssub {P : Config → Prop} {d x y : ℕ} {u v : ℤ} (hx : SArg x) (hy : SArg y)
    (hd : SArg d) (hP : Indep (d :: (d + 1) :: arithW) P) :
    HT (Arith.ssub d x y) (fun c => P c ∧ SReg c x u ∧ SReg c y v)
      (fun c => P c ∧ SReg c d (u - v)) 42 := by
  have hW : ∀ r ∈ [rT, sX, sX + 1], r ∈ arithW := by decide
  have h1 := HT.smovIn (F := fun c => P c ∧ SReg c y v) (z := sX) (w := u) hx (by decide)
    (by decide) ((indep_ofArith hP hW).and (hy.indep hW v))
  have h2 := HT.smovIn (F := fun c => P c ∧ SReg c sX u) (z := sY) (w := v) hy (by decide)
    (by decide) ((indep_ofArith hP (by decide)).and (indep_sreg (by decide) (by decide) u))
  have h2' := sflip_spec (P := fun c => P c ∧ SReg c sX u) (r := sY) (by decide) (by decide)
    ((indep_ofArith hP (by decide)).and (indep_sreg (by decide) (by decide) u)) v
  have h3 := saddCore_spec (P := P) (indep_ofArith hP (by decide)) u (-v)
  have h4 := HT.smovOut (P := P) (z := sZ) (w := u + -v) hd (by decide) (by decide)
    (by decide) hP
  refine (h1.seq ((h2.pre fun c ⟨⟨hc, hy'⟩, hx'⟩ => ⟨⟨hc, hx'⟩, hy'⟩).seq (h2'.seq
    ((h3.pre fun c ⟨⟨hc, hx'⟩, hy'⟩ => ⟨hc, hx', hy'⟩).seq h4)))).mono
    (fun c ⟨hc, hx', hy'⟩ => ⟨⟨hc, hy'⟩, hx'⟩) (fun c h => ?_) (by omega)
  rw [sub_eq_add_neg]; exact h

/-- **Signed subtraction** within any bound (memory-free). -/
theorem HTB.ssub {S : ℕ} {P : Config → Prop} {d x y : ℕ} {u v : ℤ} (hx : SArg x) (hy : SArg y)
    (hd : SArg d) (hP : Indep (d :: (d + 1) :: arithW) P) :
    HTB S (Arith.ssub d x y) (fun c => P c ∧ SReg c x u ∧ SReg c y v)
      (fun c => P c ∧ SReg c d (u - v)) 42 :=
  HTB.of_HT rfl (HT.ssub hx hy hd hP)

/-- `d := −x`. -/
def sneg (d x : ℕ) : Stmt := .seq (smov sX x) (.seq (sflip sX) (smov d sX))

/-- **Negation** `d := −x` (`12` steps). -/
theorem HT.sneg {P : Config → Prop} {d x : ℕ} {u : ℤ} (hx : SArg x) (hd : SArg d)
    (hP : Indep (d :: (d + 1) :: arithW) P) :
    HT (Arith.sneg d x) (fun c => P c ∧ SReg c x u) (fun c => P c ∧ SReg c d (-u)) 12 :=
  (HT.smovIn (z := sX) hx (by decide) (by decide) (indep_ofArith hP (by decide))).seq
    ((sflip_spec (by decide) (by decide) (indep_ofArith hP (by decide)) u).seq
      (HT.smovOut hd (by decide) (by decide) (by decide) hP))

/-- **Negation** within any bound (memory-free). -/
theorem HTB.sneg {S : ℕ} {P : Config → Prop} {d x : ℕ} {u : ℤ} (hx : SArg x) (hd : SArg d)
    (hP : Indep (d :: (d + 1) :: arithW) P) :
    HTB S (Arith.sneg d x) (fun c => P c ∧ SReg c x u) (fun c => P c ∧ SReg c d (-u)) 12 :=
  HTB.of_HT rfl (HT.sneg hx hd hP)

/-- `reg d := 1` if `x ≤ y`, else `0`. -/
def sle (d x y : ℕ) : Stmt := .seq (smov sX x) (.seq (smov sY y) (.seq sleCore (mov d sB)))

/-- **Comparison** `reg d := [x ≤ y]` (`23` steps). -/
theorem HT.sle {P : Config → Prop} {d x y : ℕ} {u v : ℤ} (hx : SArg x) (hy : SArg y)
    (hP : Indep (d :: arithW) P) :
    HT (Arith.sle d x y) (fun c => P c ∧ SReg c x u ∧ SReg c y v)
      (fun c => P c ∧ c.reg d = if u ≤ v then 1 else 0) 23 := by
  have hP' : Indep (d :: d :: arithW) P := hP.mono fun r hr => by
    simp only [List.mem_cons] at hr ⊢; tauto
  have hW : ∀ r ∈ [rT, sX, sX + 1], r ∈ arithW := by decide
  have h1 := HT.smovIn (F := fun c => P c ∧ SReg c y v) (z := sX) (w := u) hx (by decide)
    (by decide) ((indep_ofArith hP' hW).and (hy.indep hW v))
  have h2 := HT.smovIn (F := fun c => P c ∧ SReg c sX u) (z := sY) (w := v) hy (by decide)
    (by decide) ((indep_ofArith hP' (by decide)).and (indep_sreg (by decide) (by decide) u))
  have h3 := sleCore_spec (P := P) (indep_ofArith hP' (by decide)) u v
  have h4 : HT (mov d sB) (fun c => P c ∧ c.reg sB = if u ≤ v then 1 else 0)
      (fun c => P c ∧ c.reg d = if u ≤ v then 1 else 0) 2 :=
    HT.run_le (by simp) (by simp) fun c ⟨hc, hb⟩ => by
      rw [run_mov (by decide)]
      exact ⟨hP.setReg List.mem_cons_self _ (hP.setReg (List.mem_cons_of_mem _ (by decide)) _ hc),
        by simp [hb]⟩
  exact (h1.seq ((h2.pre fun c ⟨⟨hc, hy'⟩, hx'⟩ => ⟨⟨hc, hx'⟩, hy'⟩).seq
    ((h3.pre fun c ⟨⟨hc, hx'⟩, hy'⟩ => ⟨hc, hx', hy'⟩).seq h4))).mono
    (fun c ⟨hc, hx', hy'⟩ => ⟨⟨hc, hy'⟩, hx'⟩) (fun _ h => h) (by omega)

/-- **Comparison** within any bound (memory-free). -/
theorem HTB.sle {S : ℕ} {P : Config → Prop} {d x y : ℕ} {u v : ℤ} (hx : SArg x) (hy : SArg y)
    (hP : Indep (d :: arithW) P) :
    HTB S (Arith.sle d x y) (fun c => P c ∧ SReg c x u ∧ SReg c y v)
      (fun c => P c ∧ c.reg d = if u ≤ v then 1 else 0) 23 :=
  HTB.of_HT rfl (HT.sle hx hy hP)

/-- `reg d := 1` if `x < y`, else `0`. -/
def slt (d x y : ℕ) : Stmt :=
  .seq (smov sX y) (.seq (smov sY x) (.seq sleCore (.seq (.const rT 1) (.sub d rT sB))))

/-- **Strict comparison** `reg d := [x < y]` (`23` steps). -/
theorem HT.slt {P : Config → Prop} {d x y : ℕ} {u v : ℤ} (hx : SArg x) (hy : SArg y)
    (hP : Indep (d :: arithW) P) :
    HT (Arith.slt d x y) (fun c => P c ∧ SReg c x u ∧ SReg c y v)
      (fun c => P c ∧ c.reg d = if u < v then 1 else 0) 23 := by
  have hP' : Indep (d :: d :: arithW) P := hP.mono fun r hr => by
    simp only [List.mem_cons] at hr ⊢; tauto
  have hW : ∀ r ∈ [rT, sX, sX + 1], r ∈ arithW := by decide
  have h1 := HT.smovIn (F := fun c => P c ∧ SReg c x u) (z := sX) (w := v) hy (by decide)
    (by decide) ((indep_ofArith hP' hW).and (hx.indep hW u))
  have h2 := HT.smovIn (F := fun c => P c ∧ SReg c sX v) (z := sY) (w := u) hx (by decide)
    (by decide) ((indep_ofArith hP' (by decide)).and (indep_sreg (by decide) (by decide) v))
  have h3 := sleCore_spec (P := P) (indep_ofArith hP' (by decide)) v u
  have h4 : HT (.seq (.const rT 1) (.sub d rT sB))
      (fun c => P c ∧ c.reg sB = if v ≤ u then 1 else 0)
      (fun c => P c ∧ c.reg d = if u < v then 1 else 0) 2 :=
    HT.run_le (by simp [LoopFree]) (by simp [size]) fun c ⟨hc, hb⟩ => by
      refine ⟨hP.setReg List.mem_cons_self _ (hP.setReg (List.mem_cons_of_mem _ (by decide)) _ hc),
        ?_⟩
      simp +decide only [run_seq', run_const, run_sub, setReg_reg, ↓reduceIte, hb]
      split_ifs <;> omega
  exact (h1.seq ((h2.pre fun c ⟨⟨hc, hx'⟩, hy'⟩ => ⟨⟨hc, hy'⟩, hx'⟩).seq
    ((h3.pre fun c ⟨⟨hc, hy'⟩, hx'⟩ => ⟨hc, hy', hx'⟩).seq h4))).mono
    (fun c ⟨hc, hx', hy'⟩ => ⟨⟨hc, hx'⟩, hy'⟩) (fun _ h => h) (by omega)

/-- **Strict comparison** within any bound (memory-free). -/
theorem HTB.slt {S : ℕ} {P : Config → Prop} {d x y : ℕ} {u v : ℤ} (hx : SArg x) (hy : SArg y)
    (hP : Indep (d :: arithW) P) :
    HTB S (Arith.slt d x y) (fun c => P c ∧ SReg c x u ∧ SReg c y v)
      (fun c => P c ∧ c.reg d = if u < v then 1 else 0) 23 :=
  HTB.of_HT rfl (HT.slt hx hy hP)

/-- `reg d := 1` if `x = 0`, else `0`. -/
def isz (d x : ℕ) : Stmt := .ifz (x + 1) (.const d 1) (.const d 0)

/-- **Zero test** `reg d := [x = 0]` (`3` steps; any registers). -/
theorem HT.isz {P : Config → Prop} {d x : ℕ} {u : ℤ} (hP : Indep [d] P) :
    HT (Arith.isz d x) (fun c => P c ∧ SReg c x u) (fun c => P c ∧ c.reg d = if u = 0 then 1 else 0)
      3 :=
  HT.run_le (by simp [Arith.isz, LoopFree]) (by simp [Arith.isz, size]) fun c ⟨hc, _, h1⟩ => by
    simp only [Arith.isz, run_ifz', h1, Int.natAbs_eq_zero]
    split_ifs <;> exact ⟨hP.setReg (by simp) _ hc, by simp⟩

/-- **Zero test** within any bound (memory-free). -/
theorem HTB.isz {S : ℕ} {P : Config → Prop} {d x : ℕ} {u : ℤ} (hP : Indep [d] P) :
    HTB S (Arith.isz d x) (fun c => P c ∧ SReg c x u)
      (fun c => P c ∧ c.reg d = if u = 0 then 1 else 0) 3 :=
  HTB.of_HT rfl (HT.isz hP)

/-! ### Multiplication and division -/

/-- `d := x · y`. -/
def smul (d x y : ℕ) : Stmt := .seq (smov mX x) (.seq (smov mY y) (.seq smulCore (smov d mZ)))

/-- **Signed multiplication within the bound, scratch bound in the precondition** (the master form
of `HTB.smul`): `d := x · y` in `smulCost y + 12 = 31 · size |y| + 47` steps, the
scratch table (`2 · size |y|` cells from `rFREE`) below `S`; `P` must give
`ZeroFrom c.mem (c.reg rFREE)`. -/
theorem HTB.smul_pre {S : ℕ} {P : Config → Prop} {d x y : ℕ} {u v : ℤ} (hx : SArg x) (hy : SArg y)
    (hd : SArg d) (hP : Indep (d :: (d + 1) :: arithW) P)
    (hZ : ∀ c, P c → ZeroFrom c.mem (c.reg rFREE)) :
    HTB S (Arith.smul d x y)
      (fun c => (P c ∧ SReg c x u ∧ SReg c y v) ∧ c.reg rFREE + 2 * Nat.size v.natAbs ≤ S)
      (fun c => P c ∧ SReg c d (u * v)) (smulCost v + 12) := by
  have hG : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ arithW) →
      Indep W (fun c => P c ∧ c.reg rFREE + 2 * Nat.size v.natAbs ≤ S) :=
    fun hW => indep_and_free (indep_ofArith hP hW) hW _ _
  have hW : ∀ r ∈ [rT, mX, mX + 1], r ∈ arithW := by decide
  have h1 := HTB.smovIn (S := S)
    (F := fun c => (P c ∧ c.reg rFREE + 2 * Nat.size v.natAbs ≤ S) ∧ SReg c y v) (z := mX) (w := u)
    hx (by decide) (by decide) ((hG hW).and (hy.indep hW v))
  have h2 := HTB.smovIn (S := S)
    (F := fun c => (P c ∧ c.reg rFREE + 2 * Nat.size v.natAbs ≤ S) ∧ SReg c mX u) (z := mY)
    (w := v) hy (by decide) (by decide) ((hG (by decide)).and (indep_sreg (by decide) (by decide)
        u))
  have h3 := smulCore_specB (P := fun c => P c ∧ c.reg rFREE + 2 * Nat.size v.natAbs ≤ S)
    (hG (by decide)) (fun c h => hZ c h.1) u v (fun c h => h.2)
  have h4 := HTB.smovOut (S := S) (P := P) (z := mZ) (w := u * v) hd (by decide) (by decide)
    (by decide) hP
  exact (h1.seq ((h2.pre fun c ⟨⟨hc, hy'⟩, hx'⟩ => ⟨⟨hc, hx'⟩, hy'⟩).seq
    ((h3.pre fun c ⟨⟨hc, hx'⟩, hy'⟩ => ⟨hc, hx', hy'⟩).seq
      (h4.pre fun c ⟨hc, hz⟩ => ⟨hc.1, hz⟩)))).mono
    (fun c ⟨⟨hc, hx', hy'⟩, hg⟩ => ⟨⟨⟨hc, hg⟩, hy'⟩, hx'⟩) (fun _ h => h) (by omega)

/-- **Signed multiplication within the bound** `d := x · y` (`hS`: the scratch table,
`2 · size |y|` cells from `rFREE`, below `S`). -/
theorem HTB.smul {S : ℕ} {P : Config → Prop} {d x y : ℕ} {u v : ℤ} (hx : SArg x) (hy : SArg y)
    (hd : SArg d) (hP : Indep (d :: (d + 1) :: arithW) P)
    (hZ : ∀ c, P c → ZeroFrom c.mem (c.reg rFREE))
    (hS : ∀ c, P c → c.reg rFREE + 2 * Nat.size v.natAbs ≤ S) :
    HTB S (Arith.smul d x y) (fun c => P c ∧ SReg c x u ∧ SReg c y v)
      (fun c => P c ∧ SReg c d (u * v)) (smulCost v + 12) :=
  (HTB.smul_pre hx hy hd hP hZ).pre fun c hc => ⟨hc, hS c hc.1⟩

/-- `q := x / y`, `reg r := x % y` (`Int.ediv`, `Int.emod`). -/
def sdivmod (q r x y : ℕ) : Stmt :=
  .seq (smov mX x) (.seq (smov mY y) (.seq sdivCore (.seq (smov q mZ) (mov r mRm))))

/-- **Signed division within the bound, scratch bound in the precondition** (the master form of
`HTB.sdivmod`): `q := x / y`, `reg r := x % y` (`Int.ediv`, `Int.emod`,
`y ≠ 0`) in `sdivCost x y + 14 = 31 · (size |x| + 1 − size |y|) + 57` steps, the scratch table
(`2 · entB |y| |x| = 2 · (size |x| + 1 − size |y|)` cells from `rFREE`) below `S`. `r` is a single
register outside the block, different from `q` and `q + 1`. -/
theorem HTB.sdivmod_pre {S : ℕ} {P : Config → Prop} {q r x y : ℕ} {u v : ℤ} (hx : SArg x)
    (hy : SArg y) (hq : SArg q) (hr : r ∉ arithW) (hrq : r ≠ q ∧ r ≠ q + 1)
    (hP : Indep (q :: (q + 1) :: r :: arithW) P)
    (hZ : ∀ c, P c → ZeroFrom c.mem (c.reg rFREE)) (hv : v ≠ 0) :
    HTB S (Arith.sdivmod q r x y)
      (fun c => (P c ∧ SReg c x u ∧ SReg c y v) ∧ c.reg rFREE + 2 * entB v.natAbs u.natAbs ≤ S)
      (fun c => P c ∧ SReg c q (u / v) ∧ (c.reg r : ℤ) = u % v) (sdivCost u v + 14) := by
  have hPa : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ arithW) → Indep W P := fun hW =>
    hP.mono fun r' hr' => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (hW r' hr')))
  have hG : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ arithW) →
      Indep W (fun c => P c ∧ c.reg rFREE + 2 * entB v.natAbs u.natAbs ≤ S) :=
    fun hW => indep_and_free (hPa hW) hW _ _
  have hW : ∀ r ∈ [rT, mX, mX + 1], r ∈ arithW := by decide
  have h1 := HTB.smovIn (S := S)
    (F := fun c => (P c ∧ c.reg rFREE + 2 * entB v.natAbs u.natAbs ≤ S) ∧ SReg c y v) (z := mX)
    (w := u) hx (by decide) (by decide) ((hG hW).and (hy.indep hW v))
  have h2 := HTB.smovIn (S := S)
    (F := fun c => (P c ∧ c.reg rFREE + 2 * entB v.natAbs u.natAbs ≤ S) ∧ SReg c mX u) (z := mY)
    (w := v) hy (by decide) (by decide) ((hG (by decide)).and (indep_sreg (by decide) (by decide)
        u))
  have h3 := sdivCore_specB (P := fun c => P c ∧ c.reg rFREE + 2 * entB v.natAbs u.natAbs ≤ S)
    (hG (by decide)) (fun c h => hZ c h.1) u v hv (fun c h => h.2)
  have hrT := ne_of_not_mem_arithW hr (show rT ∈ arithW by decide)
  have hrm := ne_of_not_mem_arithW hr (show mRm ∈ arithW by decide)
  have h4 := HTB.smov (S := S) (P := fun c => P c ∧ (c.reg mRm : ℤ) = u % v) (d := q) (x := mZ)
    (z := u / v) (by decide) (by decide) (hq.ne (by decide)).1 (Ne.symm (hq.ne (show mZ + 1 ∈
        arithW by
      decide)).1) ((hP.mono fun r' hr' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢
        rcases hr' with rfl | rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (by decide)))
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)).and
      (Indep.reg (r := mRm) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨by decide, (hq.ne (by decide)).1.symm, (hq.ne (by decide)).2.symm⟩)
        (fun n => (n : ℤ) = u % v)))
  have h5 : HTB S (mov r mRm) (fun c => (P c ∧ (c.reg mRm : ℤ) = u % v) ∧ SReg c q (u / v))
      (fun c => P c ∧ SReg c q (u / v) ∧ (c.reg r : ℤ) = u % v) 2 :=
    HTB.of_HT rfl <| HT.run_le (by simp) (by simp) fun c ⟨⟨hc, hm⟩, hq0, hq1⟩ => by
      rw [run_mov (by decide)]
      refine ⟨hP.setReg (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) _
        (hP.setReg (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (by decide)))) _ hc), ⟨?_, ?_⟩, ?_⟩
      · simp [hrq.1.symm, hq0, (hq.ne (show rT ∈ arithW by decide)).1]
      · simp [hrq.2.symm, hq1, (hq.ne (show rT ∈ arithW by decide)).2]
      · simp [hm]
  exact (h1.seq ((h2.pre fun c ⟨⟨hc, hy'⟩, hx'⟩ => ⟨⟨hc, hx'⟩, hy'⟩).seq
    ((h3.pre fun c ⟨⟨hc, hx'⟩, hy'⟩ => ⟨hc, hx', hy'⟩).seq
      ((h4.pre fun c ⟨hc, hz, hm⟩ => ⟨⟨hc.1, hm⟩, hz⟩).seq h5)))).mono
    (fun c ⟨⟨hc, hx', hy'⟩, hg⟩ => ⟨⟨⟨hc, hg⟩, hy'⟩, hx'⟩) (fun _ h => h) (by omega)

/-- **Signed division within the bound** (`hS`: the scratch table, `2 · entB |y| |x|` cells from
`rFREE`, below `S`). Conditions as `HTB.sdivmod_pre`. -/
theorem HTB.sdivmod {S : ℕ} {P : Config → Prop} {q r x y : ℕ} {u v : ℤ} (hx : SArg x) (hy : SArg y)
    (hq : SArg q) (hr : r ∉ arithW) (hrq : r ≠ q ∧ r ≠ q + 1)
    (hP : Indep (q :: (q + 1) :: r :: arithW) P)
    (hZ : ∀ c, P c → ZeroFrom c.mem (c.reg rFREE)) (hv : v ≠ 0)
    (hS : ∀ c, P c → c.reg rFREE + 2 * entB v.natAbs u.natAbs ≤ S) :
    HTB S (Arith.sdivmod q r x y) (fun c => P c ∧ SReg c x u ∧ SReg c y v)
      (fun c => P c ∧ SReg c q (u / v) ∧ (c.reg r : ℤ) = u % v) (sdivCost u v + 14) :=
  (HTB.sdivmod_pre hx hy hq hr hrq hP hZ hv).pre fun c hc => ⟨hc, hS c hc.1⟩

/-- `d := roundDiv u (reg v)`. -/
def sround (d u v : ℕ) : Stmt := .seq (smov rU u) (.seq (mov rV v) (.seq roundCore (smov d mZ)))

/-- **Rounded division within the bound, scratch bound in the precondition** (the master form of
`HTB.sround`): `d := roundDiv u v = ⌊(2u + v)/(2v)⌋` (`v = reg v ≥ 1`, a natural
in a register outside the block) in `roundCost u + 10 = 31 · size |u| + 127` steps, the scratch
table (`2 · (size |u| + 2)` cells from `rFREE`) below `S`. -/
theorem HTB.sround_pre {S : ℕ} {P : Config → Prop} {d u v : ℕ} {a : ℤ} {b : ℕ} (hu : SArg u)
    (hv : v ∉ arithW) (hd : SArg d) (hP : Indep (d :: (d + 1) :: arithW) P)
    (hZ : ∀ c, P c → ZeroFrom c.mem (c.reg rFREE)) (hb : 1 ≤ b) :
    HTB S (Arith.sround d u v)
      (fun c => (P c ∧ SReg c u a ∧ c.reg v = b) ∧ c.reg rFREE + 2 * (Nat.size a.natAbs + 2) ≤ S)
      (fun c => P c ∧ SReg c d (ConvexQP.roundDiv a b)) (roundCost a + 10) := by
  have hG : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ arithW) →
      Indep W (fun c => P c ∧ c.reg rFREE + 2 * (Nat.size a.natAbs + 2) ≤ S) :=
    fun hW => indep_and_free (indep_ofArith hP hW) hW _ _
  have hW : ∀ r ∈ [rT, rU, rU + 1], r ∈ arithW := by decide
  have hvT := ne_of_not_mem_arithW hv (show rT ∈ arithW by decide)
  have h1 := HTB.smovIn (S := S)
    (F := fun c => (P c ∧ c.reg rFREE + 2 * (Nat.size a.natAbs + 2) ≤ S) ∧ c.reg v = b) (z := rU)
    (w := a) hu (by decide) (by decide)
    ((hG hW).and (Indep.reg (r := v) (fun h => hv (hW _ h)) (· = b)))
  have h2 : HTB S (mov rV v)
      (fun c => ((P c ∧ c.reg rFREE + 2 * (Nat.size a.natAbs + 2) ≤ S) ∧ c.reg v = b) ∧
        SReg c rU a)
      (fun c => (P c ∧ c.reg rFREE + 2 * (Nat.size a.natAbs + 2) ≤ S) ∧ SReg c rU a ∧
        c.reg rV = b) 2 :=
    HTB.of_HT rfl <| HT.run_le (by simp) (by simp) fun c ⟨⟨hc, hb'⟩, hu0, hu1⟩ => by
      rw [run_mov hvT]
      refine ⟨(hG (show ∀ r ∈ [rV, rT], r ∈ arithW by decide)).setReg (by simp) _
        ((hG (show ∀ r ∈ [rV, rT], r ∈ arithW by decide)).setReg (by simp) _ hc),
        ⟨?_, ?_⟩, ?_⟩
      · simp +decide [hu0]
      · simp +decide [hu1]
      · simp +decide [hb']
  have h3 := roundCore_specB (P := fun c => P c ∧ c.reg rFREE + 2 * (Nat.size a.natAbs + 2) ≤ S)
    (hG (by decide)) (fun c h => hZ c h.1) a b hb (fun c h => h.2)
  have h4 := HTB.smovOut (S := S) (P := P) (z := mZ) (w := ConvexQP.roundDiv a b) hd (by decide)
    (by decide) (by decide) hP
  exact (h1.seq (h2.seq (h3.seq (h4.pre fun c ⟨hc, hz⟩ => ⟨hc.1, hz⟩)))).mono
    (fun c ⟨⟨hc, hu', hv'⟩, hg⟩ => ⟨⟨⟨hc, hg⟩, hv'⟩, hu'⟩) (fun _ h => h) (by omega)

/-- **Rounded division within the bound** (`hS`: the scratch table, `2 · (size |u| + 2)` cells
from `rFREE`, below `S`). Conditions as `HTB.sround_pre`. -/
theorem HTB.sround {S : ℕ} {P : Config → Prop} {d u v : ℕ} {a : ℤ} {b : ℕ} (hu : SArg u)
    (hv : v ∉ arithW) (hd : SArg d) (hP : Indep (d :: (d + 1) :: arithW) P)
    (hZ : ∀ c, P c → ZeroFrom c.mem (c.reg rFREE)) (hb : 1 ≤ b)
    (hS : ∀ c, P c → c.reg rFREE + 2 * (Nat.size a.natAbs + 2) ≤ S) :
    HTB S (Arith.sround d u v) (fun c => P c ∧ SReg c u a ∧ c.reg v = b)
      (fun c => P c ∧ SReg c d (ConvexQP.roundDiv a b)) (roundCost a + 10) :=
  (HTB.sround_pre hu hv hd hP hZ hb).pre fun c hc => ⟨hc, hS c hc.1⟩

/-- `reg d := Nat.sqrt (reg x)`. -/
def isqrtN (d x : ℕ) : Stmt := .seq (mov qN x) (.seq isqrtCore (mov d qR))

/-- **Integer square root within the bound, scratch bound in the precondition** (the master form
of `HTB.isqrtN`): `reg d := Nat.sqrt (reg x)` in
`isqrtCost N + 4 ≤ 40 (size N + 1)² + 4` steps, the scratch table (`2 · (size N + 1)` cells from
`rFREE`) below `S`. -/
theorem HTB.isqrtN_pre {S : ℕ} {P : Config → Prop} {d x N : ℕ} (hx : x ∉ arithW)
    (hP : Indep (d :: arithW) P) (hZ : ∀ c, P c → ZeroFrom c.mem (c.reg rFREE)) :
    HTB S (Arith.isqrtN d x)
      (fun c => (P c ∧ c.reg x = N) ∧ c.reg rFREE + 2 * (Nat.size N + 1) ≤ S)
      (fun c => P c ∧ c.reg d = Nat.sqrt N) (isqrtCost N + 4) := by
  have hPa : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ arithW) → Indep W P := fun hW =>
    hP.mono fun r' hr' => List.mem_cons_of_mem _ (hW r' hr')
  have hG : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ arithW) →
      Indep W (fun c => P c ∧ c.reg rFREE + 2 * (Nat.size N + 1) ≤ S) :=
    fun hW => indep_and_free (hPa hW) hW _ _
  have hxT := ne_of_not_mem_arithW hx (show rT ∈ arithW by decide)
  have h1 : HTB S (mov qN x) (fun c => (P c ∧ c.reg x = N) ∧ c.reg rFREE + 2 * (Nat.size N + 1) ≤ S)
      (fun c => (P c ∧ c.reg rFREE + 2 * (Nat.size N + 1) ≤ S) ∧ c.reg qN = N) 2 :=
    HTB.of_HT rfl <| HT.run_le (by simp) (by simp) fun c ⟨⟨hc, hN⟩, hg⟩ => by
      rw [run_mov hxT]
      exact ⟨(hG (show ∀ r ∈ [qN, rT], r ∈ arithW by decide)).setReg (by simp) _
        ((hG (show ∀ r ∈ [qN, rT], r ∈ arithW by decide)).setReg (by simp) _ ⟨hc, hg⟩),
        by simp [hN]⟩
  have h2 := isqrtCore_specB (P := fun c => P c ∧ c.reg rFREE + 2 * (Nat.size N + 1) ≤ S)
    (hG (by decide)) (fun c h => hZ c h.1) N (fun c h => h.2)
  have h3 : HTB S (mov d qR) (fun c => (P c ∧ c.reg rFREE + 2 * (Nat.size N + 1) ≤ S) ∧
        c.reg qR = Nat.sqrt N)
      (fun c => P c ∧ c.reg d = Nat.sqrt N) 2 :=
    HTB.of_HT rfl <| HT.run_le (by simp) (by simp) fun c ⟨⟨hc, _⟩, hN⟩ => by
      rw [run_mov (by decide)]
      exact ⟨hP.setReg List.mem_cons_self _ (hP.setReg (List.mem_cons_of_mem _ (by decide)) _ hc),
        by simp [hN]⟩
  exact (h1.seq (h2.seq h3)).weaken (by omega)

/-- **Integer square root within the bound** (`hS`: the scratch table, `2 · (size N + 1)` cells
from `rFREE`, below `S`). -/
theorem HTB.isqrtN {S : ℕ} {P : Config → Prop} {d x N : ℕ} (hx : x ∉ arithW)
    (hP : Indep (d :: arithW) P) (hZ : ∀ c, P c → ZeroFrom c.mem (c.reg rFREE))
    (hS : ∀ c, P c → c.reg rFREE + 2 * (Nat.size N + 1) ≤ S) :
    HTB S (Arith.isqrtN d x) (fun c => P c ∧ c.reg x = N) (fun c => P c ∧ c.reg d = Nat.sqrt N)
      (isqrtCost N + 4) :=
  (HTB.isqrtN_pre hx hP hZ).pre fun c hc => ⟨hc, hS c hc.1⟩

/-! ### Signed cells in memory -/

/-- `d := (mem[reg p], mem[reg p + 1])`. -/
def sload (d p : ℕ) : Stmt := .seq (.load d p) (.seq (addc rT p 1) (.load (d + 1) rT))

/-- **Load a signed cell pair** (`4` steps; `p ≠ rT`, `p ≠ d`, `d ≠ rT`). -/
theorem HT.sload {P : Config → Prop} {d p a : ℕ} {z : ℤ} (hp : p ≠ rT) (hpd : p ≠ d) (hd : d ≠ rT)
    (hP : Indep [rT, d, d + 1] P) :
    HT (Arith.sload d p) (fun c => P c ∧ c.reg p = a ∧ SMem c.mem a z)
      (fun c => P c ∧ SReg c d z) 4 :=
  HT.run_le (by simp [Arith.sload, LoopFree]) (by simp [Arith.sload, size])
    fun c ⟨hc, hpa, h0, h1⟩ => by
      simp only [Arith.sload, run_seq', run_load, run_addc hp]
      refine ⟨hP.setReg (by simp) _ (hP.setReg (by simp) _ (hP.setReg (by simp) _
        (hP.setReg (by simp) _ hc))), ?_, ?_⟩
      · simp [hd, hpd, hpa, h0]
      · simp [hpd, hpa, h1]

/-- **Load a signed cell pair within the bound** (the cells `a`, `a + 1` below `S`). -/
theorem HTB.sload {S : ℕ} {P : Config → Prop} {d p a : ℕ} {z : ℤ} (hp : p ≠ rT) (hpd : p ≠ d)
    (hd : d ≠ rT) (hP : Indep [rT, d, d + 1] P) (ha : a + 1 < S) :
    HTB S (Arith.sload d p) (fun c => P c ∧ c.reg p = a ∧ SMem c.mem a z)
      (fun c => P c ∧ SReg c d z) 4 :=
  HTB.of_HT_addrOK (by simp [Arith.sload, LoopFree]) (fun c ⟨_, hpa, _⟩ => by
    addr_ok [Arith.sload, run_addc hp, hpa, hp, hpd]) (HT.sload hp hpd hd hP)

/-- `(mem[reg p], mem[reg p + 1]) := x`. -/
def sstore (p x : ℕ) : Stmt := .seq (.store p x) (.seq (addc rT p 1) (.store rT (x + 1)))

/-- **Store a signed pair** into the cells `a = reg p` and `a + 1` (`4` steps; `p, x, x + 1 ≠ rT`).
`F` is any assertion on the registers other than `rT`. -/
theorem HT.sstore {F : Config → Prop} {p x a : ℕ} {z : ℤ} {m : ℕ → ℕ} (hp : p ≠ rT) (hx : x ≠ rT)
    (hx1 : x + 1 ≠ rT) (hF : RegIndep [rT] F) :
    HT (Arith.sstore p x) (fun c => F c ∧ SReg c x z ∧ c.reg p = a ∧ c.mem = m)
      (fun c => F c ∧ SReg c x z ∧ c.reg p = a ∧
        c.mem = upd (upd m a (sgnBit z)) (a + 1) z.natAbs) 4 :=
  HT.run_le (by simp [Arith.sstore, LoopFree]) (by simp [Arith.sstore, size])
    fun c ⟨hc, ⟨h0, h1⟩, hpa, hm⟩ => by
      have hFS : RegIndep [rT] (fun c => F c ∧ SReg c x z ∧ c.reg p = a) :=
        hF.and ((regIndep_sreg (W := [rT]) (r := x) (by simp [hx]) (by simp [hx1]) z).and
          (RegIndep.reg (r := p) (by simp [hp]) (· = a)))
      have := hFS.setReg (d := rT) (by simp) (c.reg p + 1)
        (hFS.setReg (d := rT) (by simp) 1 (hFS.setMem (c.reg p) (c.reg x) ⟨hc, ⟨h0, h1⟩, hpa⟩))
      simp only [Arith.sstore, run_seq', run_store, run_addc hp]
      refine ⟨(hFS.setMem _ _ this).1, (hFS.setMem _ _ this).2.1, (hFS.setMem _ _ this).2.2, ?_⟩
      simp [hpa, hm, h0, h1, hx1]

/-- **Store a signed pair within the bound** (the cells `a`, `a + 1` below `S`). -/
theorem HTB.sstore {S : ℕ} {F : Config → Prop} {p x a : ℕ} {z : ℤ} {m : ℕ → ℕ} (hp : p ≠ rT)
    (hx : x ≠ rT) (hx1 : x + 1 ≠ rT) (hF : RegIndep [rT] F) (ha : a + 1 < S) :
    HTB S (Arith.sstore p x) (fun c => F c ∧ SReg c x z ∧ c.reg p = a ∧ c.mem = m)
      (fun c => F c ∧ SReg c x z ∧ c.reg p = a ∧
        c.mem = upd (upd m a (sgnBit z)) (a + 1) z.natAbs) 4 :=
  HTB.of_HT_addrOK (by simp [Arith.sstore, LoopFree]) (fun c ⟨_, _, hpa, _⟩ => by
    addr_ok [Arith.sstore, run_addc hp, hpa, hp]) (HT.sstore hp hx hx1 hF)

end STACS2027.Runtimes.Arith
