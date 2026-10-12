module

public import Runtimes.ConvexQP.RAM.KmoLoops
public import Runtimes.ConvexQP.Exact
import Mathlib.Tactic

/-!
# Phases K, M, O on the RAM: the layout and the state of Phase M

* `lay I F₀`: the regions above `F₀` (`NOTE-kmo.md`); `lay_eqs` lists the defining equations
  (with the atoms `M · gs` and `d · as`) for `omega`.
* `Glob I F₀ c`: the constant registers (`QRegs`, the region pointers, the strides, `E`,
  `rFREE`).
* `StRegs I F₀ s c`: `Δ`, `q`, the row pointer `pAj + r · as` of the state `s` after `r` steps.
* `MemCore I Xs F₀ s m`: `G` (rows `Gx`), `h'`, `Zn`, `T`, the top-left `r × r` block of `Aj`,
  and `ZeroFrom m fe`; `WZero I F₀ r m`: `w` is zero from `r` on.
* `MInv I Xs F₀ r c`: the invariant of the main loop before step `r`.
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Kmo

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

/-! ### Dimensions and layout -/

/-- `d = (k + 1) t`. -/
abbrev dd (I : Inst) : ℕ := dimKKT I.t I.k
/-- `M = 2t + 3tk`. -/
abbrev MM (I : Inst) : ℕ := nRows I.t I.k
/-- Row stride of `G` (with the extra column `h`). -/
abbrev gsz (I : Inst) : ℕ := 2 * dd I + 2
/-- Row stride of `Aj`. -/
abbrev asz (I : Inst) : ℕ := 2 * dd I

/-- The regions of Phases K, M, O. -/
structure Lay where
  /-- `G`. -/
  pG : ℕ
  /-- `Aj`. -/
  pAj : ℕ
  /-- `Zn`. -/
  pZn : ℕ
  /-- `col`. -/
  pcol : ℕ
  /-- `u`. -/
  pu : ℕ
  /-- `v`. -/
  pv : ℕ
  /-- `w`. -/
  pw : ℕ
  /-- `ω`. -/
  pom : ℕ
  /-- `G Zn`, `σ`. -/
  psg : ℕ
  /-- `h'`. -/
  php : ℕ
  /-- `T`. -/
  pT : ℕ
  /-- `L` (Phase K). -/
  pL : ℕ
  /-- The constant `1`. -/
  pOne : ℕ
  /-- The end of the regions (the new `rFREE`). -/
  fe : ℕ

/-- The layout above `F₀`. -/
def lay (I : Inst) (F₀ : ℕ) : Lay where
  pG := F₀
  pAj := F₀ + MM I * gsz I
  pZn := F₀ + MM I * gsz I + dd I * asz I
  pcol := F₀ + MM I * gsz I + dd I * asz I + asz I
  pu := F₀ + MM I * gsz I + dd I * asz I + 2 * asz I
  pv := F₀ + MM I * gsz I + dd I * asz I + 3 * asz I
  pw := F₀ + MM I * gsz I + dd I * asz I + 4 * asz I
  pom := F₀ + MM I * gsz I + dd I * asz I + 5 * asz I
  psg := F₀ + MM I * gsz I + dd I * asz I + 5 * asz I + 2 * MM I
  php := F₀ + MM I * gsz I + dd I * asz I + 5 * asz I + 4 * MM I
  pT := F₀ + MM I * gsz I + dd I * asz I + 5 * asz I + 6 * MM I
  pL := F₀ + MM I * gsz I + dd I * asz I + 5 * asz I + 6 * MM I + dd I
  pOne := F₀ + MM I * gsz I + dd I * asz I + 5 * asz I + 6 * MM I + dd I + 2 * (I.t * I.k)
  fe := F₀ + MM I * gsz I + dd I * asz I + 5 * asz I + 6 * MM I + dd I + 2 * (I.t * I.k) + 2

/-- The defining equations of the layout, for `omega`. -/
theorem lay_eqs (I : Inst) (F₀ : ℕ) :
    (lay I F₀).pG = F₀ ∧ (lay I F₀).pAj = F₀ + MM I * gsz I ∧
    (lay I F₀).pZn = (lay I F₀).pAj + dd I * asz I ∧ (lay I F₀).pcol = (lay I F₀).pZn + 2 * dd I ∧
    (lay I F₀).pu = (lay I F₀).pcol + 2 * dd I ∧ (lay I F₀).pv = (lay I F₀).pu + 2 * dd I ∧
    (lay I F₀).pw = (lay I F₀).pv + 2 * dd I ∧ (lay I F₀).pom = (lay I F₀).pw + 2 * dd I ∧
    (lay I F₀).psg = (lay I F₀).pom + 2 * MM I ∧ (lay I F₀).php = (lay I F₀).psg + 2 * MM I ∧
    (lay I F₀).pT = (lay I F₀).php + 2 * MM I ∧ (lay I F₀).pL = (lay I F₀).pT + dd I ∧
    (lay I F₀).pOne = (lay I F₀).pL + 2 * (I.t * I.k) ∧ (lay I F₀).fe = (lay I F₀).pOne + 2 ∧
    dd I = I.t * I.k + I.t ∧ MM I = 2 * I.t + 3 * (I.t * I.k) ∧ gsz I = 2 * dd I + 2 ∧
    asz I = 2 * dd I := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, dimKKT_eq _ _,
    nRows_eq _ _, rfl, rfl⟩ <;> simp only [lay] <;> ring

/-! ### The constant registers -/

/-- The registers that stay constant during Phases M and O. -/
@[mk_iff]
structure Glob (I : Inst) (F₀ : ℕ) (c : Config) : Prop where
  qregs : QRegs I c
  pG : c.reg kPG = (lay I F₀).pG
  gs : c.reg kGS = gsz I
  pAj : c.reg kPAJ = (lay I F₀).pAj
  as : c.reg kAS = asz I
  pZn : c.reg kPZN = (lay I F₀).pZn
  pcol : c.reg kPCOL = (lay I F₀).pcol
  pu : c.reg kPU = (lay I F₀).pu
  pv : c.reg kPV = (lay I F₀).pv
  pw : c.reg kPW = (lay I F₀).pw
  pom : c.reg kPOM = (lay I F₀).pom
  psg : c.reg kPSG = (lay I F₀).psg
  php : c.reg kPHP = (lay I F₀).php
  pT : c.reg kPT = (lay I F₀).pT
  e : SReg c kE (bigE I.t I.k)
  free : c.reg rFREE = (lay I F₀).fe

theorem qregs_iff (I : Inst) (c : Config) : QRegs I c ↔
    c.reg qT = I.t ∧ c.reg qK = I.k ∧ c.reg qKT = I.t * I.k ∧ c.reg qN = nDim I.t I.k ∧
    c.reg qD = dimKKT I.t I.k ∧ c.reg qM = nRows I.t I.k ∧ c.reg qIt = iters I.t I.k ∧
    c.reg qP = prec I.t I.k ∧ c.reg qE = bigE I.t I.k ∧ c.reg qCN = cNum I.t I.k ∧
    c.reg qCD = cDen I.t I.k := Iff.rfl

/-- The registers of Phases K, M, O and of the library are not those of `Glob`. -/
def globFree : List ℕ := rT :: (List.range' 400 50 ++ List.range' 515 25)

theorem Glob.regIndep (I : Inst) (F₀ : ℕ) : RegIndep globFree (Glob I F₀) := by
  indep [glob_iff, qregs_iff, SReg]

theorem Glob.regIndep' (I : Inst) (F₀ : ℕ) {W : List ℕ} (hW : ∀ r ∈ W, r ∈ globFree) :
    RegIndep W (Glob I F₀) := (Glob.regIndep I F₀).mono hW

/-! ### The state of Phase M -/

section State

variable (I : Inst) (Xs : Fin I.t → Fin I.k → ℤ) (F₀ : ℕ)

/-- The registers of the state after `r` steps: `Δ`, `q`, and `pAj + r · as`. -/
def StRegs {r : ℕ} (s : MState (MM I) (dd I) r) (c : Config) : Prop :=
  SReg c kDL s.Δ ∧ SReg c kQ (s.q : ℤ) ∧ c.reg kROW = (lay I F₀).pAj + r * asz I

/-- The memory of the state after `r` steps. -/
structure MemCore {r : ℕ} (s : MState (MM I) (dd I) r) (m : ℕ → ℕ) : Prop where
  gmem : ∀ i < MM I, SArr m ((lay I F₀).pG + i * gsz I) 2 (dd I + 1) (Gx I Xs i)
  hp : SArr m (lay I F₀).php 2 (MM I) (hpf I)
  zn : SArr m (lay I F₀).pZn 2 (dd I) (ZnF s)
  tt : ∀ a < r, m ((lay I F₀).pT + a) = (lay I F₀).pG + TF s a * gsz I
  aj : ∀ a < r, SArr m ((lay I F₀).pAj + a * asz I) 2 r (AjF s a)
  zero : ZeroFrom m (lay I F₀).fe

/-- `w` is zero from `r` on. -/
def WZero (r : ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ a, (lay I F₀).pw + 2 * r ≤ a → a < (lay I F₀).pw + 2 * dd I → m a = 0

/-- The KKT data of Phase M: `G`, `h`, `E`, the start `(Zn₀, q₀)`. -/
abbrev KG : Matrix (Fin (MM I)) (Fin (dd I)) ℤ := kktG I (kktZ I Xs)

/-- The invariant of the main loop before step `r`. -/
def MInv (r : ℕ) (c : Config) : Prop :=
  ∃ (hr : r ≤ dd I) (s : MState (MM I) (dd I) r),
    moveAux (KG I Xs) (kktH I) (bigE I.t I.k) (kktZn I Xs) (2 ^ prec I.t I.k) r hr = some s ∧
    Glob I F₀ c ∧ StRegs I F₀ s c ∧ MemCore I Xs F₀ s c.mem ∧ WZero I F₀ r c.mem

end State

/-! ### Memory agreement outside a region -/

/-- `m'` agrees with `m` outside `[x, y)`. -/
def Out (x y : ℕ) (m m' : ℕ → ℕ) : Prop := ∀ a, (a < x ∨ y ≤ a) → m' a = m a

theorem Out.refl (x y : ℕ) (m : ℕ → ℕ) : Out x y m m := fun _ _ => rfl

theorem Out.trans {x y : ℕ} {m₁ m₂ m₃ : ℕ → ℕ} (h₁ : Out x y m₁ m₂) (h₂ : Out x y m₂ m₃) :
    Out x y m₁ m₃ := fun a ha => (h₂ a ha).trans (h₁ a ha)

theorem Out.mono {x y x' y' : ℕ} {m m' : ℕ → ℕ} (h : Out x y m m') (hx : x' ≤ x) (hy : y ≤ y') :
    Out x' y' m m' := fun a ha => h a (by omega)

theorem out_wrArr {x y b s n : ℕ} {m : ℕ → ℕ} {f : ℕ → ℤ} (hs : 2 ≤ s) (hx : x ≤ b)
    (hy : b + n * s ≤ y) : Out x y m (wrArr m b s f n) := fun a ha =>
  wrArr_of_out hs (by omega)

theorem out_sw {x y a : ℕ} {m : ℕ → ℕ} {z : ℤ} (hx : x ≤ a) (hy : a + 2 ≤ y) :
    Out x y m (sw m a z) := fun i hi => sw_of_out z (by omega)

theorem out_wrRows {x y pa si nc i : ℕ} {m : ℕ → ℕ} {A : ℕ → ℕ → ℤ} (hsi : nc * 2 ≤ si)
    (hx : x ≤ pa) (hy : pa + i * si ≤ y) : Out x y m (wrRows m pa si nc A i) := fun a ha =>
  wrRows_of_out hsi (by omega)

theorem out_upd {x y a v : ℕ} {m : ℕ → ℕ} (hx : x ≤ a) (hy : a < y) :
    Out x y m (upd m a v) := fun i hi => by simp only [upd_apply, show i ≠ a by omega, ↓reduceIte]

/-- An array outside `[x, y)` survives. -/
theorem sarr_of_out {x y b s n : ℕ} {m m' : ℕ → ℕ} {f : ℕ → ℤ} (h : SArr m b s n f) (hs : 2 ≤ s)
    (ho : Out x y m m') (hd : b + n * s ≤ x ∨ y ≤ b) : SArr m' b s n f :=
  sarr_of_eq h fun j hj => by
    have := entry_lt (b := b) hs hj
    exact ⟨ho _ (by omega), ho _ (by omega)⟩

/-- `SameOn` (the form of the kernels' hypotheses) gives `Out`-agreement. -/
theorem out_of_sameOn {x y : ℕ} {m m' : ℕ → ℕ} (h : SameOn (fun a => ¬ (x ≤ a ∧ a < y)) m m') :
    Out x y m m' := fun a ha => h a (by omega)

theorem Out.zeroFrom {x y F : ℕ} {m m' : ℕ → ℕ} (h : Out x y m m') (hz : ZeroFrom m F)
    (hy : y ≤ F) : ZeroFrom m' F := fun a ha => (h a (by omega)).trans (hz a ha)

end STACS2027.Runtimes.QPRam.Kmo
