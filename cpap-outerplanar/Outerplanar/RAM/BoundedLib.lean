module

public import Outerplanar.RAM.BoundedHT
public import Outerplanar.RAM.Lib
import Mathlib.Tactic

/-!
# Space-bounded specifications of the instructions and macros of `Lib.lean`

For every triple `HT.X` of `Lib.lean` there is a twin `HTB.X` with the same hypotheses; the
triples of instructions and macros that access the memory take one more hypothesis, **last**,
saying that the accessed address is below the bound `S`:

| rule | address hypothesis |
|---|---|
| `HTB.load hP hv ha` | `ha : ∀ c, P c → c.reg a < S` |
| `HTB.store h ha` | `ha : ∀ c, P c → c.reg a < S` |
| `HTB.ld hP hv ha` | `ha : ∀ c, P c → c.reg b + c.reg i < S` |
| `HTB.st hv hQ h ha` | `ha : ∀ c, P c → c.reg b + c.reg i < S` |

The macros without memory access (`mov addc subc inc dec swap alloc mul`, the loop control of
`upLoop forUp forRange whileC`) are `memFree` (simp lemmas `memFree_X`); their triples are
obtained from the `HT` ones by `HTB.of_HT`.

Also the twins `HTB.loopG`, `HTB.whileG`, `HTB.toG` of the ghost-indexed loop rules of
`EarLL.lean`.

`AddrOK` simp lemmas for the loop-free macros (`addrOK_mov : AddrOK S (mov d a) c ↔ True`,
`addrOK_ld : AddrOK S (ld d b i) c ↔ c.reg b + c.reg i < S`, `addrOK_st`, `addrOK_ifLt`, …)
reduce the address obligation of a block to arithmetic.

## The tactic `addr_ok`

`addr_ok [l₁, …, lₙ]` proves a goal `AddrOK S s c` (or any goal that the same `simp` call turns
into linear arithmetic): it runs
`simp +decide only [<AddrOK lemmas>, <run lemmas of Lib.lean>, <register lemmas>, Nat.add_sub_cancel, l₁, …, lₙ]`,
then `split_ifs` if `if`s remain, then `omega` (with all hypotheses of the context). Pass as `lᵢ`
* the definitions of the user-defined blocks occurring in `s` (`addr_ok [body, readEdge]`), so
  that they are unfolded;
* register values that are not hypotheses of the context (`hG.deg : c.reg rDEG = F`), and the
  values of memory cells read by the block whose results enter an address
  (`hx : c.mem (F + j) = x`, stated at the address as it appears after the rewriting).

Limits: `omega` sees `c.mem a` and every non-linear term as atoms, and does not unfold
definitions — put the facts it needs in the context (bounds on the indices and on the values
read, and the layout as **one inequality per region**, `base + size ≤ S`: a chain of layout
equations in the context makes `omega` slow). Memory reads after a store of the same block are
left as `upd m a v x` (add `upd_apply` to the list, together with the facts deciding the address
comparisons; slow — prefer splitting the block). Register numbers given as variables (not
concrete `abbrev`s) cannot be decided: provide the needed disequalities. `addr_simp [l₁, …]`
performs only the `simp` step and leaves the arithmetic goal for inspection. See
`GUIDE-SPACE.md`.
-/

@[expose] public section

namespace STACS2027.RAM

/-! ### Memory-freeness of the macros -/

section memFree
variable (a b d i k n v : ℕ) (s u body cond : Stmt)

@[simp] theorem memFree_mov : memFree (mov d a) = true := rfl
@[simp] theorem memFree_addc : memFree (addc d a k) = true := rfl
@[simp] theorem memFree_subc : memFree (subc d a k) = true := rfl
@[simp] theorem memFree_inc : memFree (inc d) = true := rfl
@[simp] theorem memFree_dec : memFree (dec d) = true := rfl
@[simp] theorem memFree_swap : memFree (swap a b) = true := rfl
@[simp] theorem memFree_alloc : memFree (alloc d n) = true := rfl
@[simp] theorem memFree_mul : memFree (mul d a b k) = true := rfl
@[simp] theorem memFree_ld : memFree (ld d b i) = false := rfl
@[simp] theorem memFree_st : memFree (st b i v) = false := rfl
@[simp] theorem memFree_ifLt : memFree (ifLt a b s u) = (memFree u && memFree s) := rfl
@[simp] theorem memFree_ifLe : memFree (ifLe a b s u) = (memFree s && memFree u) := rfl
@[simp] theorem memFree_ifEq : memFree (ifEq a b s u) = ((memFree s && memFree u) && memFree u) := rfl
@[simp] theorem memFree_upLoop : memFree (upLoop i n body) = memFree body := by
  simp [upLoop, inc, addc, memFree]
@[simp] theorem memFree_forUp : memFree (forUp i n body) = memFree body := by
  simp [forUp, upLoop, inc, addc, memFree]
@[simp] theorem memFree_forRange : memFree (forRange i a n body) = memFree body := by
  simp [forRange, upLoop, mov, inc, addc, memFree]
@[simp] theorem memFree_whileC : memFree (whileC cond body) = (memFree cond && (memFree body && memFree cond)) :=
  rfl

end memFree

/-! ### Address safety of the loop-free macros -/

section addrOK

variable {S : ℕ} {c : Config}

@[simp] theorem addrOK_mov (d a : ℕ) : AddrOK S (mov d a) c ↔ True := iff_true_intro ⟨trivial, trivial⟩
@[simp] theorem addrOK_addc (d a k : ℕ) : AddrOK S (addc d a k) c ↔ True :=
  iff_true_intro ⟨trivial, trivial⟩
@[simp] theorem addrOK_subc (d a k : ℕ) : AddrOK S (subc d a k) c ↔ True :=
  iff_true_intro ⟨trivial, trivial⟩
@[simp] theorem addrOK_inc (d : ℕ) : AddrOK S (inc d) c ↔ True := iff_true_intro ⟨trivial, trivial⟩
@[simp] theorem addrOK_dec (d : ℕ) : AddrOK S (dec d) c ↔ True := iff_true_intro ⟨trivial, trivial⟩
@[simp] theorem addrOK_swap (a b : ℕ) : AddrOK S (swap a b) c ↔ True :=
  iff_true_intro ⟨trivial, trivial, trivial⟩
@[simp] theorem addrOK_alloc (d n : ℕ) : AddrOK S (alloc d n) c ↔ True :=
  iff_true_intro ⟨⟨trivial, trivial⟩, trivial⟩

@[simp] theorem addrOK_ld (d b i : ℕ) : AddrOK S (ld d b i) c ↔ c.reg b + c.reg i < S := by
  simp [ld]

@[simp] theorem addrOK_st (b i v : ℕ) : AddrOK S (st b i v) c ↔ c.reg b + c.reg i < S := by
  simp [st]

@[simp] theorem addrOK_ifLt (a b : ℕ) (s u : Stmt) :
    AddrOK S (ifLt a b s u) c ↔ (c.reg a < c.reg b → AddrOK S s (c.setReg rT (c.reg b - c.reg a))) ∧
      (c.reg b ≤ c.reg a → AddrOK S u (c.setReg rT (c.reg b - c.reg a))) := by
  simp only [ifLt, addrOK_seq, addrOK_sub, addrOK_ifz, run_sub, setReg_reg, ↓reduceIte, true_and]
  constructor
  · rintro ⟨h₁, h₂⟩; exact ⟨fun h => h₂ (by omega), fun h => h₁ (by omega)⟩
  · rintro ⟨h₁, h₂⟩; exact ⟨fun h => h₂ (by omega), fun h => h₁ (by omega)⟩

@[simp] theorem addrOK_ifLe (a b : ℕ) (s u : Stmt) :
    AddrOK S (ifLe a b s u) c ↔ (c.reg a ≤ c.reg b → AddrOK S s (c.setReg rT (c.reg a - c.reg b))) ∧
      (c.reg b < c.reg a → AddrOK S u (c.setReg rT (c.reg a - c.reg b))) := by
  rw [ifLe, addrOK_ifLt, and_comm]

theorem addrOK_ifEq {a b : ℕ} (ha : a ≠ rT) (hb : b ≠ rT) (s u : Stmt) :
    AddrOK S (ifEq a b s u) c ↔ (c.reg a = c.reg b → AddrOK S s (c.setReg rT 0)) ∧
      (c.reg a ≠ c.reg b → AddrOK S u (c.setReg rT (c.reg a - c.reg b + (c.reg b - c.reg a)))) := by
  simp only [ifEq, addrOK_seq, addrOK_sub, addrOK_ifz, run_sub, setReg_reg, ↓reduceIte,
    setReg_setReg, ha, hb, true_and]
  rcases lt_trichotomy (c.reg a) (c.reg b) with h | h | h
  · have e₁ : c.reg a - c.reg b = 0 := by omega
    have e₂ : c.reg b - c.reg a ≠ 0 := by omega
    have e₃ : c.reg a ≠ c.reg b := by omega
    simp [e₁, e₂, e₃]
  · simp [h]
  · have e₁ : c.reg a - c.reg b ≠ 0 := by omega
    have e₂ : c.reg b - c.reg a = 0 := by omega
    have e₃ : c.reg a ≠ c.reg b := by omega
    simp [e₁, e₂, e₃]

/-- The branches of `ifLt` (in the states after the test). -/
theorem AddrOK.ifLt {a b : ℕ} {s u : Stmt}
    (h₁ : c.reg a < c.reg b → AddrOK S s (c.setReg rT (c.reg b - c.reg a)))
    (h₂ : c.reg b ≤ c.reg a → AddrOK S u (c.setReg rT (c.reg b - c.reg a))) :
    AddrOK S (ifLt a b s u) c := (addrOK_ifLt a b s u).mpr ⟨h₁, h₂⟩

/-- The branches of `ifLe` (in the states after the test). -/
theorem AddrOK.ifLe {a b : ℕ} {s u : Stmt}
    (h₁ : c.reg a ≤ c.reg b → AddrOK S s (c.setReg rT (c.reg a - c.reg b)))
    (h₂ : c.reg b < c.reg a → AddrOK S u (c.setReg rT (c.reg a - c.reg b))) :
    AddrOK S (ifLe a b s u) c := (addrOK_ifLe a b s u).mpr ⟨h₁, h₂⟩

/-- The branches of `ifEq` (in the states after the test). -/
theorem AddrOK.ifEq {a b : ℕ} {s u : Stmt} (ha : a ≠ rT) (hb : b ≠ rT)
    (h₁ : c.reg a = c.reg b → AddrOK S s (c.setReg rT 0))
    (h₂ : c.reg a ≠ c.reg b → AddrOK S u (c.setReg rT (c.reg a - c.reg b + (c.reg b - c.reg a)))) :
    AddrOK S (ifEq a b s u) c := (addrOK_ifEq ha hb s u).mpr ⟨h₁, h₂⟩

end addrOK

/-! ### Basic instructions -/

namespace HTB

variable {S : ℕ} {P Q : Config → Prop}

/-- `d := v`. -/
theorem const {d v : ℕ} (hP : Indep [d] P) : HTB S (.const d v) P (fun c => P c ∧ c.reg d = v) 1 :=
  of_HT rfl (HT.const hP)

/-- `d := reg a + reg b`. -/
theorem add {d a b x y : ℕ} (hP : Indep [d] P) (ha : ∀ c, P c → c.reg a = x)
    (hb : ∀ c, P c → c.reg b = y) : HTB S (.add d a b) P (fun c => P c ∧ c.reg d = x + y) 1 :=
  of_HT rfl (HT.add hP ha hb)

/-- `d := reg a - reg b`. -/
theorem sub {d a b x y : ℕ} (hP : Indep [d] P) (ha : ∀ c, P c → c.reg a = x)
    (hb : ∀ c, P c → c.reg b = y) : HTB S (.sub d a b) P (fun c => P c ∧ c.reg d = x - y) 1 :=
  of_HT rfl (HT.sub hP ha hb)

/-- `d := mem[reg a]`, for `reg a < S`. -/
theorem load {d a v : ℕ} (hP : Indep [d] P) (hv : ∀ c, P c → c.mem (c.reg a) = v)
    (ha : ∀ c, P c → c.reg a < S) : HTB S (.load d a) P (fun c => P c ∧ c.reg d = v) 1 :=
  run_le trivial le_rfl fun c hc => ⟨ha c hc, hP.setReg (by simp) _ hc, by simp [hv c hc]⟩

/-- `mem[reg a] := reg b` (weakest-precondition form), for `reg a < S`. -/
theorem store {a b : ℕ} (h : ∀ c, P c → Q (c.setMem (c.reg a) (c.reg b)))
    (ha : ∀ c, P c → c.reg a < S) : HTB S (.store a b) P Q 1 :=
  run_le trivial le_rfl fun c hc => ⟨ha c hc, h c hc⟩

/-- Output `reg a`. -/
theorem write {a : ℕ} (h : ∀ c, P c → Q (c.emit (c.reg a))) : HTB S (.write a) P Q 1 :=
  of_HT rfl (HT.write h)

/-! ### Loop-free macros -/

/-- `d := reg a`. -/
theorem mov {d a x : ℕ} (ha : a ≠ rT) (hP : Indep [rT, d] P) (hx : ∀ c, P c → c.reg a = x) :
    HTB S (RAM.mov d a) P (fun c => P c ∧ c.reg d = x) 2 :=
  of_HT rfl (HT.mov ha hP hx)

/-- `d := reg a + k`. -/
theorem addc {d a k x : ℕ} (ha : a ≠ rT) (hP : Indep [rT, d] P) (hx : ∀ c, P c → c.reg a = x) :
    HTB S (RAM.addc d a k) P (fun c => P c ∧ c.reg d = x + k) 2 :=
  of_HT rfl (HT.addc ha hP hx)

/-- `d := reg a - k`. -/
theorem subc {d a k x : ℕ} (ha : a ≠ rT) (hP : Indep [rT, d] P) (hx : ∀ c, P c → c.reg a = x) :
    HTB S (RAM.subc d a k) P (fun c => P c ∧ c.reg d = x - k) 2 :=
  of_HT rfl (HT.subc ha hP hx)

/-- `d := mem[reg b + reg i]`, for `reg b + reg i < S`. -/
theorem ld {d b i v : ℕ} (hP : Indep [d] P) (hv : ∀ c, P c → c.mem (c.reg b + c.reg i) = v)
    (ha : ∀ c, P c → c.reg b + c.reg i < S) :
    HTB S (RAM.ld d b i) P (fun c => P c ∧ c.reg d = v) 2 :=
  run_le (by simp) le_rfl fun c hc => by
    refine ⟨(addrOK_ld d b i).mpr (ha c hc), ?_⟩
    rw [run_ld]
    exact ⟨hP.setReg (by simp) _ hc, by simp [hv c hc]⟩

/-- `mem[reg b + reg i] := reg v` (weakest-precondition form; `Q` must not mention `rT`), for
`reg b + reg i < S`. -/
theorem st {b i v : ℕ} (hv : v ≠ rT) (hQ : Indep [rT] Q)
    (h : ∀ c, P c → Q (c.setMem (c.reg b + c.reg i) (c.reg v)))
    (ha : ∀ c, P c → c.reg b + c.reg i < S) : HTB S (RAM.st b i v) P Q 2 :=
  run_le (by simp) le_rfl fun c hc => by
    refine ⟨(addrOK_st b i v).mpr (ha c hc), ?_⟩
    rw [run_st hv]
    exact hQ.setReg (by simp) _ (h c hc)

/-- `if reg a < reg b then s else u`. -/
theorem ifLt {a b : ℕ} {s u : Stmt} {B : ℕ} (ha : a ≠ rT) (hb : b ≠ rT) (hP : Indep [rT] P)
    (hs : HTB S s (fun c => P c ∧ c.reg a < c.reg b) Q B)
    (hu : HTB S u (fun c => P c ∧ c.reg b ≤ c.reg a) Q B) : HTB S (RAM.ifLt a b s u) P Q (B + 2) := by
  have h₁ : HTB S (.sub rT b a) P (fun c => P c ∧ (c.reg rT = 0 ↔ c.reg b ≤ c.reg a)) 1 :=
    run_le trivial le_rfl fun c hc => ⟨trivial, hP.setReg (by simp) _ hc, by simp [ha, hb]; omega⟩
  refine (h₁.seq (HTB.ifz (hu.pre ?_) (hs.pre ?_))).weaken (by omega)
  · rintro c ⟨⟨hc, hiff⟩, h0⟩; exact ⟨hc, hiff.mp h0⟩
  · rintro c ⟨⟨hc, hiff⟩, h0⟩; exact ⟨hc, by have := fun h => h0 (hiff.mpr h); omega⟩

/-- `if reg a ≤ reg b then s else u`. -/
theorem ifLe {a b : ℕ} {s u : Stmt} {B : ℕ} (ha : a ≠ rT) (hb : b ≠ rT) (hP : Indep [rT] P)
    (hs : HTB S s (fun c => P c ∧ c.reg a ≤ c.reg b) Q B)
    (hu : HTB S u (fun c => P c ∧ c.reg b < c.reg a) Q B) : HTB S (RAM.ifLe a b s u) P Q (B + 2) :=
  HTB.ifLt hb ha hP hu hs

/-- `if reg a = reg b then s else u`. -/
theorem ifEq {a b : ℕ} {s u : Stmt} {B : ℕ} (ha : a ≠ rT) (hb : b ≠ rT) (hP : Indep [rT] P)
    (hs : HTB S s (fun c => P c ∧ c.reg a = c.reg b) Q B)
    (hu : HTB S u (fun c => P c ∧ c.reg a ≠ c.reg b) Q B) : HTB S (RAM.ifEq a b s u) P Q (B + 4) := by
  have h₁ : HTB S (.sub rT a b) P (fun c => P c ∧ (c.reg rT = 0 ↔ c.reg a ≤ c.reg b)) 1 :=
    run_le trivial le_rfl fun c hc => ⟨trivial, hP.setReg (by simp) _ hc, by simp [ha, hb]; omega⟩
  have h₂ : HTB S (.sub rT b a) (fun c => P c ∧ c.reg a ≤ c.reg b)
      (fun c => (P c ∧ c.reg a ≤ c.reg b) ∧ (c.reg rT = 0 ↔ c.reg b ≤ c.reg a)) 1 :=
    run_le trivial le_rfl fun c hc =>
      ⟨trivial, ⟨hP.setReg (by simp) _ hc.1, by simp [ha, hb]; exact hc.2⟩, by simp [ha, hb]; omega⟩
  have hin : HTB S (.seq (.sub rT b a) (.ifz rT s u)) (fun c => P c ∧ c.reg a ≤ c.reg b) Q (B + 2) := by
    refine (h₂.seq (HTB.ifz (hs.pre ?_) (hu.pre ?_))).weaken (by omega)
    · rintro c ⟨⟨⟨hc, hle⟩, hiff⟩, h0⟩; exact ⟨hc, by have := hiff.mp h0; omega⟩
    · rintro c ⟨⟨⟨hc, _⟩, hiff⟩, h0⟩; exact ⟨hc, by have := fun h => h0 (hiff.mpr h); omega⟩
  refine (h₁.seq (HTB.ifz (hin.pre ?_) ((hu.weaken (show B ≤ B + 2 by omega)).pre ?_))).weaken
    (by omega)
  · rintro c ⟨⟨hc, hiff⟩, h0⟩; exact ⟨hc, hiff.mp h0⟩
  · rintro c ⟨⟨hc, hiff⟩, h0⟩; exact ⟨hc, by have := fun h => h0 (hiff.mpr h); omega⟩

/-! ### Counted loops -/

/-- **The counting loop** from iteration `A` to `N` (see `HT.upLoop`). -/
theorem upLoop {i n A N : ℕ} {body : Stmt} (Inv : ℕ → Config → Prop) (T : ℕ → ℕ)
    (hi : i ≠ rT) (hn : n ≠ rT) (hin : n ≠ i) (hInv : ∀ j, Indep [i, rT] (Inv j))
    (hbody : ∀ j, A ≤ j → j < N → HTB S body (fun c => Inv j c ∧ c.reg i = j ∧ c.reg n = N)
      (fun c => Inv (j + 1) c ∧ c.reg i = j ∧ c.reg n = N) (T j)) (hAN : A ≤ N) :
    HTB S (RAM.upLoop i n body) (fun c => Inv A c ∧ c.reg i = A ∧ c.reg n = N ∧ c.reg rT = N - A)
      (fun c => Inv N c ∧ c.reg i = N ∧ c.reg n = N) (∑ j ∈ Finset.Ico A N, (T j + 4) + 1) := by
  suffices key : ∀ r j c, j + r = N → A ≤ j → Inv j c → c.reg i = j → c.reg n = N →
      c.reg rT = N - j → ∃ c' t, ExecB S (RAM.upLoop i n body) c t c' ∧
        (Inv N c' ∧ c'.reg i = N ∧ c'.reg n = N) ∧ t ≤ ∑ k ∈ Finset.Ico j N, (T k + 4) + 1 from
    fun c ⟨hI, hi', hn', hT⟩ => key (N - A) A c (by omega) le_rfl hI hi' hn' hT
  intro r
  induction r with
  | zero =>
    intro j c hj _ hI hi' hn' hT
    refine ⟨c, 1, ExecB.loopDone (by omega), ?_, by simp⟩
    obtain rfl : j = N := by omega
    exact ⟨hI, hi', hn'⟩
  | succ r ih =>
    intro j c hj hAj hI hi' hn' hT
    obtain ⟨c₁, t₁, he₁, ⟨hI₁, hi₁, hn₁⟩, ht₁⟩ := hbody j hAj (by omega) c ⟨hI, hi', hn'⟩
    let c₂ := RAM.run (.seq (RAM.inc i) (.sub rT n i)) c₁
    have he₂ : ExecB S (.seq (RAM.inc i) (.sub rT n i)) c₁ 3 c₂ :=
      execB_run _ (by simp [LoopFree]) c₁ (addrOK_of_memFree rfl _)
    have hc₂ : c₂ = ((c₁.setReg rT 1).setReg i (j + 1)).setReg rT (N - (j + 1)) := by
      simp only [c₂, run_seq', run_inc hi, run_sub, setReg_reg, hi₁, hn₁, ↓reduceIte, hin, hn]
    have hI₂ : Inv (j + 1) c₂ := by
      rw [hc₂]
      exact (hInv _).setReg (by simp) _ ((hInv _).setReg (by simp) _ ((hInv _).setReg (by simp) _ hI₁))
    obtain ⟨c', t', he', hq, ht'⟩ := ih (j + 1) c₂ (by omega) (by omega) hI₂
      (by rw [hc₂]; simp [hi]) (by rw [hc₂]; simp [hn, hin, hn₁]) (by rw [hc₂]; simp)
    refine ⟨c', t₁ + 3 + t' + 1, ExecB.loopNext (by omega) (ExecB.seq he₁ he₂) he', hq, ?_⟩
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    omega

/-- **Counted loop** `forUp i n body` (see `HT.forUp`). -/
theorem forUp {i n N : ℕ} {body : Stmt} (Inv : ℕ → Config → Prop) (T : ℕ → ℕ)
    (hi : i ≠ rT) (hn : n ≠ rT) (hin : n ≠ i) (hInv : ∀ j, Indep [i, rT] (Inv j))
    (hbody : ∀ j, j < N → HTB S body (fun c => Inv j c ∧ c.reg i = j ∧ c.reg n = N)
      (fun c => Inv (j + 1) c ∧ c.reg i = j ∧ c.reg n = N) (T j)) :
    HTB S (RAM.forUp i n body) (fun c => Inv 0 c ∧ c.reg n = N)
      (fun c => Inv N c ∧ c.reg i = N ∧ c.reg n = N) (∑ j ∈ Finset.range N, (T j + 4) + 3) := by
  have hl := HTB.upLoop (A := 0) Inv T hi hn hin hInv (fun j _ hj => hbody j hj) (Nat.zero_le N)
  have h₀ : HTB S (.const i 0) (fun c => Inv 0 c ∧ c.reg n = N)
      (fun c => Inv 0 c ∧ c.reg i = 0 ∧ c.reg n = N) 1 :=
    run_le trivial le_rfl fun c ⟨hI, hn'⟩ =>
      ⟨trivial, (hInv 0).setReg (by simp) _ hI, by simp, by simp [hin, hn']⟩
  have h₁ : HTB S (.sub rT n i) (fun c => Inv 0 c ∧ c.reg i = 0 ∧ c.reg n = N)
      (fun c => Inv 0 c ∧ c.reg i = 0 ∧ c.reg n = N ∧ c.reg rT = N - 0) 1 :=
    run_le trivial le_rfl fun c ⟨hI, hi', hn'⟩ =>
      ⟨trivial, (hInv 0).setReg (by simp) _ hI, by simp [hi, hi'], by simp [hn, hn'],
        by simp [hi', hn']⟩
  refine (h₀.seq (h₁.seq hl)).weaken (le_of_eq ?_)
  rw [Finset.range_eq_Ico]; omega

/-- Counted loop with a constant bound `T` per iteration: total `N * (T + 4) + 3`. -/
theorem forUpC {i n N : ℕ} {body : Stmt} (Inv : ℕ → Config → Prop) (T : ℕ)
    (hi : i ≠ rT) (hn : n ≠ rT) (hin : n ≠ i) (hInv : ∀ j, Indep [i, rT] (Inv j))
    (hbody : ∀ j, j < N → HTB S body (fun c => Inv j c ∧ c.reg i = j ∧ c.reg n = N)
      (fun c => Inv (j + 1) c ∧ c.reg i = j ∧ c.reg n = N) T) :
    HTB S (RAM.forUp i n body) (fun c => Inv 0 c ∧ c.reg n = N)
      (fun c => Inv N c ∧ c.reg i = N ∧ c.reg n = N) (N * (T + 4) + 3) := by
  have := HTB.forUp Inv (fun _ => T) hi hn hin hInv hbody
  simpa [Finset.sum_const, Finset.card_range, smul_eq_mul] using this

/-- **Range loop** `forRange i a n body` (see `HT.forRange`). -/
theorem forRange {i a n A N : ℕ} {body : Stmt} (Inv : ℕ → Config → Prop) (T : ℕ → ℕ)
    (hi : i ≠ rT) (hn : n ≠ rT) (ha : a ≠ rT) (hin : n ≠ i) (hInv : ∀ j, Indep [i, rT] (Inv j))
    (hbody : ∀ j, A ≤ j → j < N → HTB S body (fun c => Inv j c ∧ c.reg i = j ∧ c.reg n = N)
      (fun c => Inv (j + 1) c ∧ c.reg i = j ∧ c.reg n = N) (T j)) :
    HTB S (RAM.forRange i a n body) (fun c => Inv A c ∧ c.reg a = A ∧ c.reg n = N ∧ A ≤ N)
      (fun c => Inv N c ∧ c.reg i = N ∧ c.reg n = N) (∑ j ∈ Finset.Ico A N, (T j + 4) + 4) := by
  refine HTB.prop_pre (P := fun c => Inv A c ∧ c.reg a = A ∧ c.reg n = N) ?_ |>.pre
    (fun c ⟨hI, ha', hn', hAN⟩ => ⟨hAN, hI, ha', hn'⟩)
  intro hAN
  have hl := HTB.upLoop Inv T hi hn hin hInv hbody hAN
  have h₀ : HTB S (RAM.mov i a) (fun c => Inv A c ∧ c.reg a = A ∧ c.reg n = N)
      (fun c => Inv A c ∧ c.reg i = A ∧ c.reg n = N) 2 :=
    run_le ⟨trivial, trivial⟩ le_rfl fun c ⟨hI, ha', hn'⟩ => by
      refine ⟨⟨trivial, trivial⟩, ?_⟩
      rw [run_mov ha]
      exact ⟨(hInv A).setReg (by simp) _ ((hInv A).setReg (by simp) _ hI), by simp [ha'],
        by simp [hn, hin, hn']⟩
  have h₁ : HTB S (.sub rT n i) (fun c => Inv A c ∧ c.reg i = A ∧ c.reg n = N)
      (fun c => Inv A c ∧ c.reg i = A ∧ c.reg n = N ∧ c.reg rT = N - A) 1 :=
    run_le trivial le_rfl fun c ⟨hI, hi', hn'⟩ =>
      ⟨trivial, (hInv A).setReg (by simp) _ hI, by simp [hi, hi'], by simp [hn, hn'],
        by simp [hi', hn']⟩
  exact (h₀.seq (h₁.seq hl)).weaken (by omega)

/-! ### Multiplication, `while` loops, allocation -/

/-- **Multiplication** in `5 * y + 4` steps (memory-free: from `HT.mul`). -/
theorem mul {d a b k x y : ℕ}
    (hreg : d ≠ k ∧ d ≠ rT ∧ k ≠ rT ∧ a ≠ d ∧ a ≠ k ∧ a ≠ rT ∧ b ≠ d ∧ b ≠ k ∧ b ≠ rT)
    (hP : Indep [d, k, rT] P) (hx : ∀ c, P c → c.reg a = x) (hy : ∀ c, P c → c.reg b = y) :
    HTB S (RAM.mul d a b k) P (fun c => P c ∧ c.reg d = x * y) (5 * y + 4) :=
  of_HT rfl (HT.mul hreg hP hx hy)

/-- **`while` loop with a decreasing measure** (see `HT.whileC`). -/
theorem whileC {cond body : Stmt} {Inv : Config → Prop} (μ : Config → ℕ) {Tc T K : ℕ}
    (hinit : HTB S cond P (fun c => Inv c ∧ μ c ≤ K) Tc)
    (hstep : ∀ v, HTB S (.seq body cond) (fun c => Inv c ∧ c.reg rT ≠ 0 ∧ μ c = v)
      (fun c => Inv c ∧ μ c < v) T) :
    HTB S (RAM.whileC cond body) P (fun c => Inv c ∧ c.reg rT = 0) (Tc + (K * (T + 1) + 1)) :=
  hinit.seq (HTB.loopT μ hstep K)

/-- **`while` loop with a potential** (see `HT.whileCPot`). -/
theorem whileCPot {cond body : Stmt} {Inv : Config → Prop} (Φ : Config → ℕ) {Tc K : ℕ}
    (hinit : HTB S cond P (fun c => Inv c ∧ Φ c ≤ K) Tc)
    (hstep : ∀ v, HTBt S (.seq body cond) (fun c => Inv c ∧ c.reg rT ≠ 0 ∧ Φ c = v)
      (fun c' t => Inv c' ∧ Φ c' + t + 1 ≤ v)) :
    HTB S (RAM.whileC cond body) P (fun c => Inv c ∧ c.reg rT = 0) (Tc + (K + 1)) := by
  have hl : HTB S (.loop rT (.seq body cond)) (fun c => Inv c ∧ Φ c ≤ K)
      (fun c => Inv c ∧ c.reg rT = 0) (K + 1) := by
    intro c ⟨hc, hK⟩
    obtain ⟨c', t, he, hi, h0, ht⟩ := HTB.loopPot Φ hstep c hc
    exact ⟨c', t, he, ⟨hi, h0⟩, by omega⟩
  exact hinit.seq hl

/-- **Loop with a ghost-indexed invariant** (twin of `EarR.HT.loopG`): every round from `Inv x`
(test register nonzero) ends in some `Inv y` and costs at most `Φ x - Φ y - 1` steps. -/
theorem loopG {a : ℕ} {body : Stmt} {α : Type*} (Inv : α → Config → Prop) (Φ : α → ℕ)
    (hbody : ∀ x, HTBt S body (fun c => Inv x c ∧ c.reg a ≠ 0)
      (fun c' t => ∃ y, Inv y c' ∧ Φ y + t + 1 ≤ Φ x)) (x : α) :
    HTB S (.loop a body) (Inv x) (fun c => ∃ y, Inv y c ∧ c.reg a = 0) (Φ x + 1) := by
  suffices key : ∀ v x c, Φ x = v → Inv x c →
      ∃ c' t, ExecB S (.loop a body) c t c' ∧ (∃ y, Inv y c' ∧ c'.reg a = 0) ∧ t ≤ Φ x + 1 from
    fun c hc => key _ x c rfl hc
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  intro x c hv hc
  by_cases ha : c.reg a = 0
  · exact ⟨c, 1, ExecB.loopDone ha, ⟨x, hc, ha⟩, by omega⟩
  · obtain ⟨c₁, t₁, he₁, y, hi₁, hΦ⟩ := hbody x c ⟨hc, ha⟩
    obtain ⟨c', t₂, he₂, hq, ht⟩ := ih (Φ y) (by omega) y c₁ rfl hi₁
    exact ⟨c', t₁ + t₂ + 1, ExecB.loopNext ha he₁ he₂, hq, by omega⟩

/-- **`while` loop with a ghost-indexed invariant** (twin of `EarR.HT.whileG`). -/
theorem whileG {cond body : Stmt} {α : Type*} (Inv : α → Config → Prop) (Φ : α → ℕ) (x₀ : α)
    {Tc : ℕ} (hinit : HTB S cond P (Inv x₀) Tc)
    (hstep : ∀ x, HTBt S (.seq body cond) (fun c => Inv x c ∧ c.reg rT ≠ 0)
      (fun c' t => ∃ y, Inv y c' ∧ Φ y + t + 1 ≤ Φ x)) :
    HTB S (RAM.whileC cond body) P (fun c => ∃ y, Inv y c ∧ c.reg rT = 0) (Tc + (Φ x₀ + 1)) :=
  hinit.seq (HTB.loopG Inv Φ hstep x₀)

/-- A round of a ghost-indexed loop from an ordinary triple (twin of `EarR.HT.toG`). -/
theorem toG {s : Stmt} {α : Type*} {Inv : α → Config → Prop} {Φ : α → ℕ} {y : α} {b v : ℕ}
    (h : HTB S s P (Inv y) b) (hb : Φ y + b + 1 ≤ v) :
    HTBt S s P (fun c' t => ∃ y, Inv y c' ∧ Φ y + t + 1 ≤ v) := fun c hc => by
  obtain ⟨c', t, he, hq, ht⟩ := h c hc
  exact ⟨c', t, he, y, hq, by omega⟩

/-- **Allocation** (memory-free: from `HT.alloc`). The bound `S` is not checked here: the
allocated region counts when it is accessed. -/
theorem alloc {d n len F : ℕ} (hd : d ≠ rFREE) (hn : n ≠ rT) (hdn : d ≠ n)
    (hP : Indep [rT, d, rFREE] P) (hlen : ∀ c, P c → c.reg n = len) (hF : ∀ c, P c → c.reg rFREE = F) :
    HTB S (RAM.alloc d n) P (fun c => P c ∧ c.reg d = F ∧ c.reg rFREE = F + len) 3 :=
  of_HT rfl (HT.alloc hd hn hdn hP hlen hF)

end HTB

/-! ### The tactic `addr_ok` -/

/-- `addr_simp [l₁, …]`: the `simp` step of `addr_ok` (reduces `AddrOK S s c` for a loop-free
block `s` to arithmetic, unfolding the definitions `lᵢ` and rewriting with the facts `lᵢ`). -/
syntax (name := addrSimpTac) "addr_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| addr_simp) => `(tactic| addr_simp [])
  | `(tactic| addr_simp [$ls,*]) => `(tactic|
      simp +decide -failIfUnchanged only [addrOK_skip, addrOK_const, addrOK_add, addrOK_sub, addrOK_write,
        addrOK_load, addrOK_store, addrOK_seq, addrOK_ifz, addrOK_mov, addrOK_addc, addrOK_subc,
        addrOK_inc, addrOK_dec, addrOK_swap, addrOK_alloc, addrOK_ld, addrOK_st, addrOK_ifLt,
        addrOK_ifLe, addrOK_ifEq, run_seq', run_ifz', run_const, run_add, run_sub, run_load,
        run_store, run_write, run_skip, run_mov, run_addc, run_subc, run_inc, run_dec, run_swap,
        run_ld, run_st, run_ifLt, run_ifLe, run_ifEq, run_alloc, setReg_reg, setReg_mem,
        setReg_out, setMem_reg, setMem_mem_upd, emit_reg, emit_mem, config_ite_reg,
        config_ite_mem, ↓reduceIte, true_and, and_true, true_implies, implies_true,
        Nat.add_sub_cancel, $ls,*])

/-- `addr_ok [l₁, …]` proves address obligations `AddrOK S s c` of loop-free blocks: `addr_simp
[l₁, …]` (the `AddrOK` and `run` lemmas of the library, register reads, and the lemmas `lᵢ`:
definitions of blocks to unfold, register and memory values), then `omega` with the hypotheses
of the context. See the module documentation for its limits. -/
syntax (name := addrOkTac) "addr_ok" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| addr_ok) => `(tactic| addr_ok [])
  | `(tactic| addr_ok [$ls,*]) => `(tactic| (addr_simp [$ls,*] <;> (try split_ifs) <;> omega))

end STACS2027.RAM
