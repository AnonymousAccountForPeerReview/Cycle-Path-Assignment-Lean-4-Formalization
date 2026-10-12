module

public import Outerplanar.RAM.Layout
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# Macros for the unit-cost RAM, with their specifications

The machine has only `const add sub load store write`, sequencing, a zero test and a
`while ≠ 0` loop. The macros below provide moves, constants, indexed loads and stores,
comparisons, counted loops, `while` loops, multiplication and allocation. Every macro may
clobber the **macro temporary** `rT` (and nothing else beyond the registers it is asked to
write); no macro reads `rONE` or register `0`, so the macros need no global invariant.

For each loop-free macro `X` there are
* `run_X`: its effect as an equation for `run` (simp lemma; side conditions such as `a ≠ rT`
  are discharged by `decide` for concrete registers, e.g. with `simp +decide`);
* `loopFree_X`, `size_X`, `wregs_X`, `stores_X`, `writes_X` (simp lemmas);
* `HT.X`: a forward Hoare triple in the *frame style*
  `HT X P (fun c => P c ∧ new facts) bound`, for any assertion `P` independent of the
  registers the macro writes (`Indep W P`, usually proved by the tactic `indep`).

Loops:
* `forUp i n body` (`i = 0, 1, …, reg n - 1`): rule `HT.forUp` with an invariant indexed by the
  iteration and a per-iteration bound, total `∑ j < N, (T j + 4) + 3`; `HT.forUpC` for a
  constant bound;
* `forRange i a n body` (`i = reg a, …, reg n - 1`): rule `HT.forRange`, total
  `∑ j ∈ [A, N), (T j + 4) + 4`; both are built on `upLoop` (rule `HT.upLoop`);
* `whileC cond body` (`cond` computes the test into `rT`): rules `HT.whileC` (decreasing
  measure, fixed bound per round) and `HT.whileCPot` (potential, amortized bounds);
* `mul d a b k`: `d := a * b` in `5 b + 4` steps (`HT.mul`).

Allocation: `alloc d n` (`d := rFREE; rFREE += reg n`, `HT.alloc`, `run_alloc`).
-/

@[expose] public section

namespace STACS2027.RAM

/-! ### Configurations -/

@[simp] theorem setReg_setReg (c : Config) (d x y : ℕ) : (c.setReg d x).setReg d y = c.setReg d y := by
  cases c
  simp only [Config.setReg, Config.mk.injEq, and_true]
  funext r
  split <;> rfl

theorem setReg_comm (c : Config) {d e : ℕ} (h : d ≠ e) (x y : ℕ) :
    (c.setReg d x).setReg e y = (c.setReg e y).setReg d x := by
  cases c
  simp only [Config.setReg, Config.mk.injEq, and_true]
  funext r
  by_cases hd : r = d <;> by_cases he : r = e <;> simp_all

/-- Setting a register to its value does nothing. -/
theorem setReg_self (c : Config) (d : ℕ) : c.setReg d (c.reg d) = c := by
  cases c
  simp only [Config.setReg, Config.mk.injEq, and_true]
  funext r
  split <;> simp_all

@[simp] theorem run_const (d v : ℕ) (c : Config) : run (.const d v) c = c.setReg d v := rfl
@[simp] theorem run_add (d a b : ℕ) (c : Config) : run (.add d a b) c = c.setReg d (c.reg a + c.reg b) := rfl
@[simp] theorem run_sub (d a b : ℕ) (c : Config) : run (.sub d a b) c = c.setReg d (c.reg a - c.reg b) := rfl
@[simp] theorem run_load (d a : ℕ) (c : Config) : run (.load d a) c = c.setReg d (c.mem (c.reg a)) := rfl
@[simp] theorem run_store (a b : ℕ) (c : Config) : run (.store a b) c = c.setMem (c.reg a) (c.reg b) := rfl
@[simp] theorem run_write (a : ℕ) (c : Config) : run (.write a) c = c.emit (c.reg a) := rfl
@[simp] theorem run_skip (c : Config) : run .skip c = c := rfl
@[simp] theorem run_seq' (s t : Stmt) (c : Config) : run (.seq s t) c = run t (run s c) := rfl
@[simp] theorem run_ifz' (a : ℕ) (s t : Stmt) (c : Config) :
    run (.ifz a s t) c = if c.reg a = 0 then run s c else run t c := rfl

@[simp] theorem config_ite_reg {p : Prop} [Decidable p] (a b : Config) (i : ℕ) :
    (if p then a else b).reg i = if p then a.reg i else b.reg i := by split <;> rfl
@[simp] theorem config_ite_mem {p : Prop} [Decidable p] (a b : Config) :
    (if p then a else b).mem = if p then a.mem else b.mem := by split <;> rfl
@[simp] theorem config_ite_out {p : Prop} [Decidable p] (a b : Config) :
    (if p then a else b).out = if p then a.out else b.out := by split <;> rfl

/-! ### Basic instructions as triples -/

namespace HT

variable {P Q : Config → Prop}

/-- `d := v`. -/
theorem const {d v : ℕ} (hP : Indep [d] P) : HT (.const d v) P (fun c => P c ∧ c.reg d = v) 1 :=
  HT.run_le trivial le_rfl fun c hc => ⟨hP.setReg (by simp) _ hc, by simp⟩

/-- `d := reg a + reg b`. -/
theorem add {d a b x y : ℕ} (hP : Indep [d] P) (ha : ∀ c, P c → c.reg a = x)
    (hb : ∀ c, P c → c.reg b = y) : HT (.add d a b) P (fun c => P c ∧ c.reg d = x + y) 1 :=
  HT.run_le trivial le_rfl fun c hc => ⟨hP.setReg (by simp) _ hc, by simp [ha c hc, hb c hc]⟩

/-- `d := reg a - reg b`. -/
theorem sub {d a b x y : ℕ} (hP : Indep [d] P) (ha : ∀ c, P c → c.reg a = x)
    (hb : ∀ c, P c → c.reg b = y) : HT (.sub d a b) P (fun c => P c ∧ c.reg d = x - y) 1 :=
  HT.run_le trivial le_rfl fun c hc => ⟨hP.setReg (by simp) _ hc, by simp [ha c hc, hb c hc]⟩

/-- `d := mem[reg a]`. -/
theorem load {d a v : ℕ} (hP : Indep [d] P) (hv : ∀ c, P c → c.mem (c.reg a) = v) :
    HT (.load d a) P (fun c => P c ∧ c.reg d = v) 1 :=
  HT.run_le trivial le_rfl fun c hc => ⟨hP.setReg (by simp) _ hc, by simp [hv c hc]⟩

/-- `mem[reg a] := reg b`, with the postcondition given by its weakest precondition. -/
theorem store {a b : ℕ} (h : ∀ c, P c → Q (c.setMem (c.reg a) (c.reg b))) : HT (.store a b) P Q 1 :=
  HT.run_le trivial le_rfl h

/-- Output `reg a`. -/
theorem write {a : ℕ} (h : ∀ c, P c → Q (c.emit (c.reg a))) : HT (.write a) P Q 1 :=
  HT.run_le trivial le_rfl h

end HT

/-! ### Moves and arithmetic with constants -/

/-- `d := reg a` (`a ≠ rT`). -/
def mov (d a : ℕ) : Stmt := .seq (.const rT 0) (.add d a rT)
/-- `d := reg a + k` (`a ≠ rT`). -/
def addc (d a k : ℕ) : Stmt := .seq (.const rT k) (.add d a rT)
/-- `d := reg a - k`, truncated (`a ≠ rT`). -/
def subc (d a k : ℕ) : Stmt := .seq (.const rT k) (.sub d a rT)
/-- `d := reg d + 1` (`d ≠ rT`). -/
def inc (d : ℕ) : Stmt := addc d d 1
/-- `d := reg d - 1`, truncated (`d ≠ rT`). -/
def dec (d : ℕ) : Stmt := subc d d 1
/-- Exchange registers `a` and `b` (`a ≠ b`), without temporary. -/
def swap (a b : ℕ) : Stmt := .seq (.add a a b) (.seq (.sub b a b) (.sub a a b))

theorem run_mov {d a : ℕ} (ha : a ≠ rT) (c : Config) : run (mov d a) c = (c.setReg rT 0).setReg d (c.reg a) := by
  simp [mov, ha]
theorem run_addc {d a : ℕ} (ha : a ≠ rT) (k : ℕ) (c : Config) :
    run (addc d a k) c = (c.setReg rT k).setReg d (c.reg a + k) := by
  simp [addc, ha]
theorem run_subc {d a : ℕ} (ha : a ≠ rT) (k : ℕ) (c : Config) :
    run (subc d a k) c = (c.setReg rT k).setReg d (c.reg a - k) := by
  simp [subc, ha]
theorem run_inc {d : ℕ} (hd : d ≠ rT) (c : Config) : run (inc d) c = (c.setReg rT 1).setReg d (c.reg d + 1) :=
  run_addc hd 1 c
theorem run_dec {d : ℕ} (hd : d ≠ rT) (c : Config) : run (dec d) c = (c.setReg rT 1).setReg d (c.reg d - 1) :=
  run_subc hd 1 c
theorem run_swap {a b : ℕ} (hab : a ≠ b) (c : Config) :
    run (swap a b) c = (c.setReg a (c.reg b)).setReg b (c.reg a) := by
  cases c with
  | mk reg mem out =>
    simp only [swap, run_seq', run_add, run_sub, ↓reduceIte, Config.setReg, Config.mk.injEq,
      and_true, hab, Ne.symm hab]
    funext r
    by_cases ha : r = a <;> by_cases hb : r = b <;> simp_all

/-! ### Indexed loads and stores -/

/-- `d := mem[reg b + reg i]` (any registers; `d` serves as the temporary). -/
def ld (d b i : ℕ) : Stmt := .seq (.add d b i) (.load d d)
/-- `mem[reg b + reg i] := reg v` (`b, i, v ≠ rT`). -/
def st (b i v : ℕ) : Stmt := .seq (.add rT b i) (.store rT v)

@[simp] theorem run_ld (d b i : ℕ) (c : Config) : run (ld d b i) c = c.setReg d (c.mem (c.reg b + c.reg i)) := by
  simp [ld]
theorem run_st {b i v : ℕ} (hv : v ≠ rT) (c : Config) :
    run (st b i v) c = (c.setMem (c.reg b + c.reg i) (c.reg v)).setReg rT (c.reg b + c.reg i) := by
  simp [st, hv]; rfl

/-! ### Comparisons -/

/-- `if reg a < reg b then s else u` (`a, b ≠ rT`). -/
def ifLt (a b : ℕ) (s u : Stmt) : Stmt := .seq (.sub rT b a) (.ifz rT u s)
/-- `if reg a ≤ reg b then s else u` (`a, b ≠ rT`). -/
def ifLe (a b : ℕ) (s u : Stmt) : Stmt := ifLt b a u s
/-- `if reg a = reg b then s else u` (`a, b ≠ rT`). -/
def ifEq (a b : ℕ) (s u : Stmt) : Stmt :=
  .seq (.sub rT a b) (.ifz rT (.seq (.sub rT b a) (.ifz rT s u)) u)

theorem run_ifLt (a b : ℕ) (s u : Stmt) (c : Config) :
    run (ifLt a b s u) c = if c.reg a < c.reg b then run s (c.setReg rT (c.reg b - c.reg a))
      else run u (c.setReg rT (c.reg b - c.reg a)) := by
  simp only [ifLt, run_seq', run_sub, run_ifz', setReg_reg, ↓reduceIte]
  by_cases h : c.reg a < c.reg b
  · have e : c.reg b - c.reg a ≠ 0 := by omega
    simp only [e, h, ↓reduceIte]
  · have e : c.reg b - c.reg a = 0 := by omega
    simp only [e, h, ↓reduceIte]

theorem run_ifLe (a b : ℕ) (s u : Stmt) (c : Config) :
    run (ifLe a b s u) c = if c.reg a ≤ c.reg b then run s (c.setReg rT (c.reg a - c.reg b))
      else run u (c.setReg rT (c.reg a - c.reg b)) := by
  rw [ifLe, run_ifLt]
  by_cases h : c.reg b < c.reg a
  · have e : ¬ c.reg a ≤ c.reg b := by omega
    simp only [e, h, ↓reduceIte]
  · have e : c.reg a ≤ c.reg b := by omega
    simp only [e, h, ↓reduceIte]

theorem run_ifEq {a b : ℕ} (ha : a ≠ rT) (hb : b ≠ rT) (s u : Stmt) (c : Config) :
    run (ifEq a b s u) c = if c.reg a = c.reg b then run s (c.setReg rT 0)
      else run u (c.setReg rT (c.reg a - c.reg b + (c.reg b - c.reg a))) := by
  simp only [ifEq, run_seq', run_sub, run_ifz', setReg_reg, ↓reduceIte, setReg_setReg, ha, hb]
  rcases lt_trichotomy (c.reg a) (c.reg b) with h | h | h
  · have e₁ : c.reg a - c.reg b = 0 := by omega
    have e₂ : c.reg b - c.reg a ≠ 0 := by omega
    have e₃ : c.reg a ≠ c.reg b := by omega
    simp only [e₁, e₂, e₃, ↓reduceIte, Nat.zero_add]
  · simp only [h, Nat.sub_self, ↓reduceIte]
  · have e₁ : c.reg a - c.reg b ≠ 0 := by omega
    have e₂ : c.reg b - c.reg a = 0 := by omega
    have e₃ : c.reg a ≠ c.reg b := by omega
    simp only [e₁, e₂, e₃, ↓reduceIte, Nat.add_zero]

/-! ### Footprints, loop-freeness and sizes of the macros -/

section footprint
variable (a b d i k v : ℕ) (s u : Stmt)

@[simp] theorem loopFree_mov : LoopFree (mov d a) := ⟨trivial, trivial⟩
@[simp] theorem loopFree_addc : LoopFree (addc d a k) := ⟨trivial, trivial⟩
@[simp] theorem loopFree_subc : LoopFree (subc d a k) := ⟨trivial, trivial⟩
@[simp] theorem loopFree_inc : LoopFree (inc d) := ⟨trivial, trivial⟩
@[simp] theorem loopFree_dec : LoopFree (dec d) := ⟨trivial, trivial⟩
@[simp] theorem loopFree_swap : LoopFree (swap a b) := ⟨trivial, trivial, trivial⟩
@[simp] theorem loopFree_ld : LoopFree (ld d b i) := ⟨trivial, trivial⟩
@[simp] theorem loopFree_st : LoopFree (st b i v) := ⟨trivial, trivial⟩
@[simp] theorem loopFree_ifLt : LoopFree (ifLt a b s u) ↔ LoopFree s ∧ LoopFree u :=
  ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨trivial, h.2, h.1⟩⟩
@[simp] theorem loopFree_ifLe : LoopFree (ifLe a b s u) ↔ LoopFree s ∧ LoopFree u := by
  rw [ifLe, loopFree_ifLt, and_comm]
@[simp] theorem loopFree_ifEq : LoopFree (ifEq a b s u) ↔ LoopFree s ∧ LoopFree u :=
  ⟨fun h => ⟨h.2.1.2.1, h.2.2⟩, fun h => ⟨trivial, ⟨trivial, h.1, h.2⟩, h.2⟩⟩

@[simp] theorem size_mov : size (mov d a) = 2 := rfl
@[simp] theorem size_addc : size (addc d a k) = 2 := rfl
@[simp] theorem size_subc : size (subc d a k) = 2 := rfl
@[simp] theorem size_inc : size (inc d) = 2 := rfl
@[simp] theorem size_dec : size (dec d) = 2 := rfl
@[simp] theorem size_swap : size (swap a b) = 3 := rfl
@[simp] theorem size_ld : size (ld d b i) = 2 := rfl
@[simp] theorem size_st : size (st b i v) = 2 := rfl
@[simp] theorem size_ifLt : size (ifLt a b s u) = size s + size u + 2 := by
  simp only [ifLt, size]; omega
@[simp] theorem size_ifLe : size (ifLe a b s u) = size s + size u + 2 := by
  simp only [ifLe, ifLt, size]; omega
@[simp] theorem size_ifEq : size (ifEq a b s u) = size s + 2 * size u + 4 := by
  simp only [ifEq, size]; omega

@[simp] theorem wregs_mov : wregs (mov d a) = [rT, d] := rfl
@[simp] theorem wregs_addc : wregs (addc d a k) = [rT, d] := rfl
@[simp] theorem wregs_subc : wregs (subc d a k) = [rT, d] := rfl
@[simp] theorem wregs_inc : wregs (inc d) = [rT, d] := rfl
@[simp] theorem wregs_dec : wregs (dec d) = [rT, d] := rfl
@[simp] theorem wregs_swap : wregs (swap a b) = [a, b, a] := rfl
@[simp] theorem wregs_ld : wregs (ld d b i) = [d, d] := rfl
@[simp] theorem wregs_st : wregs (st b i v) = [rT] := rfl
@[simp] theorem wregs_ifLt : wregs (ifLt a b s u) = rT :: (wregs u ++ wregs s) := rfl
@[simp] theorem wregs_ifEq : wregs (ifEq a b s u) = rT :: (rT :: (wregs s ++ wregs u) ++ wregs u) := rfl

@[simp] theorem stores_mov : stores (mov d a) = false := rfl
@[simp] theorem stores_addc : stores (addc d a k) = false := rfl
@[simp] theorem stores_subc : stores (subc d a k) = false := rfl
@[simp] theorem stores_inc : stores (inc d) = false := rfl
@[simp] theorem stores_dec : stores (dec d) = false := rfl
@[simp] theorem stores_swap : stores (swap a b) = false := rfl
@[simp] theorem stores_ld : stores (ld d b i) = false := rfl
@[simp] theorem stores_st : stores (st b i v) = true := rfl
@[simp] theorem stores_ifLt : stores (ifLt a b s u) = (stores u || stores s) := rfl
@[simp] theorem stores_ifEq : stores (ifEq a b s u) = ((stores s || stores u) || stores u) := rfl

@[simp] theorem writes_mov : writes (mov d a) = false := rfl
@[simp] theorem writes_addc : writes (addc d a k) = false := rfl
@[simp] theorem writes_subc : writes (subc d a k) = false := rfl
@[simp] theorem writes_inc : writes (inc d) = false := rfl
@[simp] theorem writes_dec : writes (dec d) = false := rfl
@[simp] theorem writes_swap : writes (swap a b) = false := rfl
@[simp] theorem writes_ld : writes (ld d b i) = false := rfl
@[simp] theorem writes_st : writes (st b i v) = false := rfl
@[simp] theorem writes_ifLt : writes (ifLt a b s u) = (writes u || writes s) := rfl
@[simp] theorem writes_ifEq : writes (ifEq a b s u) = ((writes s || writes u) || writes u) := rfl

end footprint

/-! ### Forward triples of the loop-free macros -/

namespace HT

variable {P Q : Config → Prop}

/-- `d := reg a`. -/
theorem mov {d a x : ℕ} (ha : a ≠ rT) (hP : Indep [rT, d] P) (hx : ∀ c, P c → c.reg a = x) :
    HT (RAM.mov d a) P (fun c => P c ∧ c.reg d = x) 2 :=
  HT.run_le (by simp) le_rfl fun c hc => by
    rw [run_mov ha]
    exact ⟨hP.setReg (by simp) _ (hP.setReg (by simp) _ hc), by simp [hx c hc]⟩

/-- `d := reg a + k`. -/
theorem addc {d a k x : ℕ} (ha : a ≠ rT) (hP : Indep [rT, d] P) (hx : ∀ c, P c → c.reg a = x) :
    HT (RAM.addc d a k) P (fun c => P c ∧ c.reg d = x + k) 2 :=
  HT.run_le (by simp) le_rfl fun c hc => by
    rw [run_addc ha]
    exact ⟨hP.setReg (by simp) _ (hP.setReg (by simp) _ hc), by simp [hx c hc]⟩

/-- `d := reg a - k`. -/
theorem subc {d a k x : ℕ} (ha : a ≠ rT) (hP : Indep [rT, d] P) (hx : ∀ c, P c → c.reg a = x) :
    HT (RAM.subc d a k) P (fun c => P c ∧ c.reg d = x - k) 2 :=
  HT.run_le (by simp) le_rfl fun c hc => by
    rw [run_subc ha]
    exact ⟨hP.setReg (by simp) _ (hP.setReg (by simp) _ hc), by simp [hx c hc]⟩

/-- `d := mem[reg b + reg i]`. -/
theorem ld {d b i v : ℕ} (hP : Indep [d] P) (hv : ∀ c, P c → c.mem (c.reg b + c.reg i) = v) :
    HT (RAM.ld d b i) P (fun c => P c ∧ c.reg d = v) 2 :=
  HT.run_le (by simp) le_rfl fun c hc => by
    rw [run_ld]
    exact ⟨hP.setReg (by simp) _ hc, by simp [hv c hc]⟩

/-- `mem[reg b + reg i] := reg v`, with the postcondition given by its weakest precondition
(`Q` must not mention `rT`). -/
theorem st {b i v : ℕ} (hv : v ≠ rT) (hQ : Indep [rT] Q)
    (h : ∀ c, P c → Q (c.setMem (c.reg b + c.reg i) (c.reg v))) : HT (RAM.st b i v) P Q 2 :=
  HT.run_le (by simp) le_rfl fun c hc => by
    rw [run_st hv]
    exact hQ.setReg (by simp) _ (h c hc)

/-- `if reg a < reg b then s else u`. -/
theorem ifLt {a b : ℕ} {s u : Stmt} {B : ℕ} (ha : a ≠ rT) (hb : b ≠ rT) (hP : Indep [rT] P)
    (hs : HT s (fun c => P c ∧ c.reg a < c.reg b) Q B)
    (hu : HT u (fun c => P c ∧ c.reg b ≤ c.reg a) Q B) : HT (RAM.ifLt a b s u) P Q (B + 2) := by
  have h₁ : HT (.sub rT b a) P (fun c => P c ∧ (c.reg rT = 0 ↔ c.reg b ≤ c.reg a)) 1 :=
    HT.run_le trivial le_rfl fun c hc => ⟨hP.setReg (by simp) _ hc, by simp [ha, hb]; omega⟩
  refine (h₁.seq (HT.ifz (hu.pre ?_) (hs.pre ?_))).weaken (by omega)
  · rintro c ⟨⟨hc, hiff⟩, h0⟩; exact ⟨hc, hiff.mp h0⟩
  · rintro c ⟨⟨hc, hiff⟩, h0⟩; exact ⟨hc, by have := fun h => h0 (hiff.mpr h); omega⟩

/-- `if reg a ≤ reg b then s else u`. -/
theorem ifLe {a b : ℕ} {s u : Stmt} {B : ℕ} (ha : a ≠ rT) (hb : b ≠ rT) (hP : Indep [rT] P)
    (hs : HT s (fun c => P c ∧ c.reg a ≤ c.reg b) Q B)
    (hu : HT u (fun c => P c ∧ c.reg b < c.reg a) Q B) : HT (RAM.ifLe a b s u) P Q (B + 2) :=
  HT.ifLt hb ha hP hu hs

/-- `if reg a = reg b then s else u`. -/
theorem ifEq {a b : ℕ} {s u : Stmt} {B : ℕ} (ha : a ≠ rT) (hb : b ≠ rT) (hP : Indep [rT] P)
    (hs : HT s (fun c => P c ∧ c.reg a = c.reg b) Q B)
    (hu : HT u (fun c => P c ∧ c.reg a ≠ c.reg b) Q B) : HT (RAM.ifEq a b s u) P Q (B + 4) := by
  have h₁ : HT (.sub rT a b) P (fun c => P c ∧ (c.reg rT = 0 ↔ c.reg a ≤ c.reg b)) 1 :=
    HT.run_le trivial le_rfl fun c hc => ⟨hP.setReg (by simp) _ hc, by simp [ha, hb]; omega⟩
  have h₂ : HT (.sub rT b a) (fun c => P c ∧ c.reg a ≤ c.reg b)
      (fun c => (P c ∧ c.reg a ≤ c.reg b) ∧ (c.reg rT = 0 ↔ c.reg b ≤ c.reg a)) 1 :=
    HT.run_le trivial le_rfl fun c hc =>
      ⟨⟨hP.setReg (by simp) _ hc.1, by simp [ha, hb]; exact hc.2⟩, by simp [ha, hb]; omega⟩
  have hin : HT (.seq (.sub rT b a) (.ifz rT s u)) (fun c => P c ∧ c.reg a ≤ c.reg b) Q (B + 2) := by
    refine (h₂.seq (HT.ifz (hs.pre ?_) (hu.pre ?_))).weaken (by omega)
    · rintro c ⟨⟨⟨hc, hle⟩, hiff⟩, h0⟩; exact ⟨hc, by have := hiff.mp h0; omega⟩
    · rintro c ⟨⟨⟨hc, _⟩, hiff⟩, h0⟩; exact ⟨hc, by have := fun h => h0 (hiff.mpr h); omega⟩
  refine (h₁.seq (HT.ifz (hin.pre ?_) ((hu.weaken (show B ≤ B + 2 by omega)).pre ?_))).weaken (by omega)
  · rintro c ⟨⟨hc, hiff⟩, h0⟩; exact ⟨hc, hiff.mp h0⟩
  · rintro c ⟨⟨hc, hiff⟩, h0⟩; exact ⟨hc, by have := fun h => h0 (hiff.mpr h); omega⟩

end HT

/-! ### Counted loops -/

/-- The loop shared by `forUp` and `forRange`: `while reg n - reg i ≠ 0 do (body; i := i + 1)`,
the test being computed into `rT`. -/
def upLoop (i n : ℕ) (body : Stmt) : Stmt := .loop rT (.seq body (.seq (inc i) (.sub rT n i)))

/-- `for i = 0, 1, …, reg n - 1 do body`. The body must leave `i` and `n` unchanged; `i, n ≠ rT`,
`i ≠ n`. After the loop `reg i = reg n`. -/
def forUp (i n : ℕ) (body : Stmt) : Stmt := .seq (.const i 0) (.seq (.sub rT n i) (upLoop i n body))

/-- `for i = reg a, …, reg n - 1 do body` (for `reg a ≤ reg n`). The body must leave `i` and `n`
unchanged; `i, n, a ≠ rT`, `i ≠ n`. After the loop `reg i = reg n`. -/
def forRange (i a n : ℕ) (body : Stmt) : Stmt := .seq (mov i a) (.seq (.sub rT n i) (upLoop i n body))

@[simp] theorem wregs_upLoop (i n : ℕ) (body : Stmt) :
    wregs (upLoop i n body) = wregs body ++ [rT, i, rT] := rfl
@[simp] theorem stores_upLoop (i n : ℕ) (body : Stmt) : stores (upLoop i n body) = stores body := by
  simp [upLoop, stores]
@[simp] theorem writes_upLoop (i n : ℕ) (body : Stmt) : writes (upLoop i n body) = writes body := by
  simp [upLoop, writes]
@[simp] theorem wregs_forUp (i n : ℕ) (body : Stmt) :
    wregs (forUp i n body) = i :: rT :: (wregs body ++ [rT, i, rT]) := rfl
@[simp] theorem stores_forUp (i n : ℕ) (body : Stmt) : stores (forUp i n body) = stores body := by
  simp [forUp, stores]
@[simp] theorem writes_forUp (i n : ℕ) (body : Stmt) : writes (forUp i n body) = writes body := by
  simp [forUp, writes]
@[simp] theorem wregs_forRange (i a n : ℕ) (body : Stmt) :
    wregs (forRange i a n body) = rT :: i :: rT :: (wregs body ++ [rT, i, rT]) := rfl
@[simp] theorem stores_forRange (i a n : ℕ) (body : Stmt) : stores (forRange i a n body) = stores body := by
  simp [forRange, mov, stores]
@[simp] theorem writes_forRange (i a n : ℕ) (body : Stmt) : writes (forRange i a n body) = writes body := by
  simp [forRange, mov, writes]

namespace HT

/-- **The counting loop** from iteration `A` to `N`: `Inv j` is the invariant before iteration `j`
(it must not mention `i` and `rT`); iteration `j` costs at most `T j` steps. -/
theorem upLoop {i n A N : ℕ} {body : Stmt} (Inv : ℕ → Config → Prop) (T : ℕ → ℕ)
    (hi : i ≠ rT) (hn : n ≠ rT) (hin : n ≠ i) (hInv : ∀ j, Indep [i, rT] (Inv j))
    (hbody : ∀ j, A ≤ j → j < N → HT body (fun c => Inv j c ∧ c.reg i = j ∧ c.reg n = N)
      (fun c => Inv (j + 1) c ∧ c.reg i = j ∧ c.reg n = N) (T j)) (hAN : A ≤ N) :
    HT (RAM.upLoop i n body) (fun c => Inv A c ∧ c.reg i = A ∧ c.reg n = N ∧ c.reg rT = N - A)
      (fun c => Inv N c ∧ c.reg i = N ∧ c.reg n = N) (∑ j ∈ Finset.Ico A N, (T j + 4) + 1) := by
  suffices key : ∀ r j c, j + r = N → A ≤ j → Inv j c → c.reg i = j → c.reg n = N → c.reg rT = N - j →
      ∃ c' t, Exec (RAM.upLoop i n body) c t c' ∧
        (Inv N c' ∧ c'.reg i = N ∧ c'.reg n = N) ∧ t ≤ ∑ k ∈ Finset.Ico j N, (T k + 4) + 1 from
    fun c ⟨hI, hi', hn', hT⟩ => key (N - A) A c (by omega) le_rfl hI hi' hn' hT
  intro r
  induction r with
  | zero =>
    intro j c hj _ hI hi' hn' hT
    refine ⟨c, 1, Exec.loopDone (by omega), ?_, by simp⟩
    obtain rfl : j = N := by omega
    exact ⟨hI, hi', hn'⟩
  | succ r ih =>
    intro j c hj hAj hI hi' hn' hT
    obtain ⟨c₁, t₁, he₁, ⟨hI₁, hi₁, hn₁⟩, ht₁⟩ := hbody j hAj (by omega) c ⟨hI, hi', hn'⟩
    let c₂ := RAM.run (.seq (RAM.inc i) (.sub rT n i)) c₁
    have he₂ : Exec (.seq (RAM.inc i) (.sub rT n i)) c₁ 3 c₂ := exec_run _ (by simp [LoopFree]) c₁
    have hc₂ : c₂ = ((c₁.setReg rT 1).setReg i (j + 1)).setReg rT (N - (j + 1)) := by
      simp only [c₂, run_seq', run_inc hi, run_sub, setReg_reg, hi₁, hn₁, ↓reduceIte, hin, hn]
    have hI₂ : Inv (j + 1) c₂ := by
      rw [hc₂]
      exact (hInv _).setReg (by simp) _ ((hInv _).setReg (by simp) _ ((hInv _).setReg (by simp) _ hI₁))
    obtain ⟨c', t', he', hq, ht'⟩ := ih (j + 1) c₂ (by omega) (by omega) hI₂
      (by rw [hc₂]; simp [hi]) (by rw [hc₂]; simp [hn, hin, hn₁]) (by rw [hc₂]; simp)
    refine ⟨c', t₁ + 3 + t' + 1, Exec.loopNext (by omega) (Exec.seq he₁ he₂) he', hq, ?_⟩
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    omega

/-- **Counted loop** `forUp i n body`: `Inv j` is the invariant before iteration `j` (it must not
mention `i` and `rT`); iteration `j < N` costs at most `T j` steps. -/
theorem forUp {i n N : ℕ} {body : Stmt} (Inv : ℕ → Config → Prop) (T : ℕ → ℕ)
    (hi : i ≠ rT) (hn : n ≠ rT) (hin : n ≠ i) (hInv : ∀ j, Indep [i, rT] (Inv j))
    (hbody : ∀ j, j < N → HT body (fun c => Inv j c ∧ c.reg i = j ∧ c.reg n = N)
      (fun c => Inv (j + 1) c ∧ c.reg i = j ∧ c.reg n = N) (T j)) :
    HT (RAM.forUp i n body) (fun c => Inv 0 c ∧ c.reg n = N)
      (fun c => Inv N c ∧ c.reg i = N ∧ c.reg n = N) (∑ j ∈ Finset.range N, (T j + 4) + 3) := by
  have hl := HT.upLoop (A := 0) Inv T hi hn hin hInv (fun j _ hj => hbody j hj) (Nat.zero_le N)
  have h₀ : HT (.const i 0) (fun c => Inv 0 c ∧ c.reg n = N)
      (fun c => Inv 0 c ∧ c.reg i = 0 ∧ c.reg n = N) 1 :=
    HT.run_le trivial le_rfl fun c ⟨hI, hn'⟩ =>
      ⟨(hInv 0).setReg (by simp) _ hI, by simp, by simp [hin, hn']⟩
  have h₁ : HT (.sub rT n i) (fun c => Inv 0 c ∧ c.reg i = 0 ∧ c.reg n = N)
      (fun c => Inv 0 c ∧ c.reg i = 0 ∧ c.reg n = N ∧ c.reg rT = N - 0) 1 :=
    HT.run_le trivial le_rfl fun c ⟨hI, hi', hn'⟩ =>
      ⟨(hInv 0).setReg (by simp) _ hI, by simp [hi, hi'], by simp [hn, hn'], by simp [hi', hn']⟩
  refine (h₀.seq (h₁.seq hl)).weaken (le_of_eq ?_)
  rw [Finset.range_eq_Ico]; omega

/-- Counted loop with a constant bound `T` per iteration: total `N * (T + 4) + 3`. -/
theorem forUpC {i n N : ℕ} {body : Stmt} (Inv : ℕ → Config → Prop) (T : ℕ)
    (hi : i ≠ rT) (hn : n ≠ rT) (hin : n ≠ i) (hInv : ∀ j, Indep [i, rT] (Inv j))
    (hbody : ∀ j, j < N → HT body (fun c => Inv j c ∧ c.reg i = j ∧ c.reg n = N)
      (fun c => Inv (j + 1) c ∧ c.reg i = j ∧ c.reg n = N) T) :
    HT (RAM.forUp i n body) (fun c => Inv 0 c ∧ c.reg n = N)
      (fun c => Inv N c ∧ c.reg i = N ∧ c.reg n = N) (N * (T + 4) + 3) := by
  have := HT.forUp Inv (fun _ => T) hi hn hin hInv hbody
  simpa [Finset.sum_const, Finset.card_range, smul_eq_mul] using this

/-- **Range loop** `forRange i a n body` (`i = A, …, N - 1` for `reg a = A ≤ N = reg n`): as
`forUp`, with the sum of the bounds over `[A, N)`. -/
theorem forRange {i a n A N : ℕ} {body : Stmt} (Inv : ℕ → Config → Prop) (T : ℕ → ℕ)
    (hi : i ≠ rT) (hn : n ≠ rT) (ha : a ≠ rT) (hin : n ≠ i) (hInv : ∀ j, Indep [i, rT] (Inv j))
    (hbody : ∀ j, A ≤ j → j < N → HT body (fun c => Inv j c ∧ c.reg i = j ∧ c.reg n = N)
      (fun c => Inv (j + 1) c ∧ c.reg i = j ∧ c.reg n = N) (T j)) :
    HT (RAM.forRange i a n body) (fun c => Inv A c ∧ c.reg a = A ∧ c.reg n = N ∧ A ≤ N)
      (fun c => Inv N c ∧ c.reg i = N ∧ c.reg n = N) (∑ j ∈ Finset.Ico A N, (T j + 4) + 4) := by
  refine HT.prop_pre (P := fun c => Inv A c ∧ c.reg a = A ∧ c.reg n = N) ?_ |>.pre
    (fun c ⟨hI, ha', hn', hAN⟩ => ⟨hAN, hI, ha', hn'⟩)
  intro hAN
  have hl := HT.upLoop Inv T hi hn hin hInv hbody hAN
  have h₀ : HT (RAM.mov i a) (fun c => Inv A c ∧ c.reg a = A ∧ c.reg n = N)
      (fun c => Inv A c ∧ c.reg i = A ∧ c.reg n = N) 2 :=
    HT.run_le ⟨trivial, trivial⟩ le_rfl fun c ⟨hI, ha', hn'⟩ => by
      rw [run_mov ha]
      exact ⟨(hInv A).setReg (by simp) _ ((hInv A).setReg (by simp) _ hI), by simp [ha'],
        by simp [hn, hin, hn']⟩
  have h₁ : HT (.sub rT n i) (fun c => Inv A c ∧ c.reg i = A ∧ c.reg n = N)
      (fun c => Inv A c ∧ c.reg i = A ∧ c.reg n = N ∧ c.reg rT = N - A) 1 :=
    HT.run_le trivial le_rfl fun c ⟨hI, hi', hn'⟩ =>
      ⟨(hInv A).setReg (by simp) _ hI, by simp [hi, hi'], by simp [hn, hn'], by simp [hi', hn']⟩
  exact (h₀.seq (h₁.seq hl)).weaken (by omega)

end HT

/-! ### Multiplication -/

/-- `d := reg a * reg b`, by `reg b` additions, counting in the register `k`. Requires
`d, k, rT` pairwise distinct and `a, b ∉ {d, k, rT}`. -/
def mul (d a b k : ℕ) : Stmt := .seq (.const d 0) (forUp k b (.add d d a))

@[simp] theorem wregs_mul (d a b k : ℕ) : wregs (mul d a b k) = d :: (k :: rT :: ([d] ++ [rT, k, rT])) := rfl
@[simp] theorem stores_mul (d a b k : ℕ) : stores (mul d a b k) = false := rfl
@[simp] theorem writes_mul (d a b k : ℕ) : writes (mul d a b k) = false := rfl

/-- **Multiplication** in `5 * y + 4` steps. -/
theorem HT.mul {P : Config → Prop} {d a b k x y : ℕ}
    (hreg : d ≠ k ∧ d ≠ rT ∧ k ≠ rT ∧ a ≠ d ∧ a ≠ k ∧ a ≠ rT ∧ b ≠ d ∧ b ≠ k ∧ b ≠ rT)
    (hP : Indep [d, k, rT] P) (hx : ∀ c, P c → c.reg a = x) (hy : ∀ c, P c → c.reg b = y) :
    HT (RAM.mul d a b k) P (fun c => P c ∧ c.reg d = x * y) (5 * y + 4) := by
  obtain ⟨hdk, hdT, hkT, had, hak, haT, hbd, hbk, hbT⟩ := hreg
  let Inv : ℕ → Config → Prop := fun j c => P c ∧ c.reg d = x * j
  have hInv : ∀ j, Indep [k, rT] (Inv j) := fun j =>
    (hP.mono (by simp)).and (Indep.reg (by simp [hdk, hdT]) (· = x * j))
  have h₀ : HT (.const d 0) P (fun c => Inv 0 c ∧ c.reg b = y) 1 :=
    HT.run_le trivial le_rfl fun c hc =>
      ⟨⟨hP.setReg (by simp) _ hc, by simp⟩, by simp [hbd, hy c hc]⟩
  have hl := HT.forUpC (i := k) (n := b) (N := y) Inv 1 hkT hbT hbk hInv fun j _ =>
    HT.run_le (s := .add d d a) trivial le_rfl fun c ⟨⟨hc, hd⟩, hk, hb⟩ => by
      refine ⟨⟨hP.setReg (by simp) _ hc, ?_⟩, ?_, ?_⟩
      · simp [hx c hc, hd]; ring
      · simp [Ne.symm hdk, hk]
      · simp [hbd, hb]
  refine (h₀.seq hl).mono (fun _ h => h) (fun c ⟨⟨hc, hd⟩, _⟩ => ⟨hc, hd⟩) (by omega)

/-! ### `while` loops -/

/-- `cond; while reg rT ≠ 0 do (body; cond)`: `cond` computes the test into `rT`. -/
def whileC (cond body : Stmt) : Stmt := .seq cond (.loop rT (.seq body cond))

@[simp] theorem wregs_whileC (cond body : Stmt) :
    wregs (whileC cond body) = wregs cond ++ (wregs body ++ wregs cond) := rfl
@[simp] theorem stores_whileC (cond body : Stmt) :
    stores (whileC cond body) = (stores cond || (stores body || stores cond)) := rfl
@[simp] theorem writes_whileC (cond body : Stmt) :
    writes (whileC cond body) = (writes cond || (writes body || writes cond)) := rfl

/-- **`while` loop with a decreasing measure.** `Inv` holds after every evaluation of the test
(and typically relates `reg rT ≠ 0` to the loop guard); each round `body; cond` costs at most `T`
steps and lowers `μ`, which is at most `K` initially. -/
theorem HT.whileC {cond body : Stmt} {P Inv : Config → Prop} (μ : Config → ℕ) {Tc T K : ℕ}
    (hinit : HT cond P (fun c => Inv c ∧ μ c ≤ K) Tc)
    (hstep : ∀ v, HT (.seq body cond) (fun c => Inv c ∧ c.reg rT ≠ 0 ∧ μ c = v)
      (fun c => Inv c ∧ μ c < v) T) :
    HT (RAM.whileC cond body) P (fun c => Inv c ∧ c.reg rT = 0) (Tc + (K * (T + 1) + 1)) :=
  hinit.seq (HT.loopT μ hstep K)

/-- **`while` loop with a potential** (amortized bounds): every round `body; cond` from the
invariant costs `t` steps and lowers the potential `Φ` by more than `t`. The loop costs at most
`Φ + 1` from where the test is first evaluated. -/
theorem HT.whileCPot {cond body : Stmt} {P Inv : Config → Prop} (Φ : Config → ℕ) {Tc K : ℕ}
    (hinit : HT cond P (fun c => Inv c ∧ Φ c ≤ K) Tc)
    (hstep : ∀ v, HTt (.seq body cond) (fun c => Inv c ∧ c.reg rT ≠ 0 ∧ Φ c = v)
      (fun c' t => Inv c' ∧ Φ c' + t + 1 ≤ v)) :
    HT (RAM.whileC cond body) P (fun c => Inv c ∧ c.reg rT = 0) (Tc + (K + 1)) := by
  have hl : HT (.loop rT (.seq body cond)) (fun c => Inv c ∧ Φ c ≤ K)
      (fun c => Inv c ∧ c.reg rT = 0) (K + 1) := by
    intro c ⟨hc, hK⟩
    obtain ⟨c', t, he, hi, h0, ht⟩ := HT.loopPot Φ hstep c hc
    exact ⟨c', t, he, ⟨hi, h0⟩, by omega⟩
  exact hinit.seq hl

/-! ### Allocation -/

/-- `d := reg rFREE; rFREE := reg rFREE + reg n` (`d, n ∉ {rT, rFREE}`, `d ≠ n`). -/
def alloc (d n : ℕ) : Stmt := .seq (mov d rFREE) (.add rFREE rFREE n)

@[simp] theorem wregs_alloc (d n : ℕ) : wregs (alloc d n) = [rT, d, rFREE] := rfl
@[simp] theorem stores_alloc (d n : ℕ) : stores (alloc d n) = false := rfl
@[simp] theorem writes_alloc (d n : ℕ) : writes (alloc d n) = false := rfl
@[simp] theorem loopFree_alloc (d n : ℕ) : LoopFree (alloc d n) := ⟨⟨trivial, trivial⟩, trivial⟩
@[simp] theorem size_alloc (d n : ℕ) : size (alloc d n) = 3 := rfl

theorem run_alloc {d n : ℕ} (hn : n ≠ rT) (hdn : d ≠ n) (c : Config) :
    run (alloc d n) c = ((c.setReg rT 0).setReg d (c.reg rFREE)).setReg rFREE (c.reg rFREE + c.reg n) := by
  simp [alloc, run_mov, hn, Ne.symm hdn]

/-- **Allocation** of `len = reg n` cells at `F = reg rFREE`: afterwards `reg d = F` and
`reg rFREE = F + len`; with `ZeroFrom c.mem F` the new region is zero (`ZeroFrom.arr`,
`ZeroFrom.tab`) and `ZeroFrom c.mem (F + len)` still holds (`ZeroFrom.mono`). -/
theorem HT.alloc {P : Config → Prop} {d n len F : ℕ} (hd : d ≠ rFREE) (hn : n ≠ rT) (hdn : d ≠ n)
    (hP : Indep [rT, d, rFREE] P) (hlen : ∀ c, P c → c.reg n = len) (hF : ∀ c, P c → c.reg rFREE = F) :
    HT (RAM.alloc d n) P (fun c => P c ∧ c.reg d = F ∧ c.reg rFREE = F + len) 3 :=
  HT.run_le (by simp) le_rfl fun c hc => by
    rw [run_alloc hn hdn]
    refine ⟨hP.setReg (by simp) _ (hP.setReg (by simp) _ (hP.setReg (by simp) _ hc)), ?_, ?_⟩
    · simp [hd, hF c hc]
    · simp [hF c hc, hlen c hc]

end STACS2027.RAM
