module

public import ApproximationHardness.Sim.Memory
public import ApproximationHardness.Sim.XRAM
import Lean.Elab.Tactic.Omega

/-!
# Simulating the RAM on the registered stack machines

`sim D s` is a structured stack command simulating the program `s` of the RAM with bit input and
output: the register `i < 192` of the RAM is the stack register `rr i = 64 + i` holding the
canonical binary numeral of its value, the memory is the register `MEM` (`ApproximationHardness.Sim.Memory`),
the input is the register `INP` and the output, last bit first, the register `OUTB`. A loop of
nesting depth `j` counts its iterations with the register `ctr j`, loaded from `FUEL`: every loop
runs at most `F = |FUEL|` iterations, so that `sim` follows the fuel semantics `xrun F`
(`sim_correct`). The number of instructions is bounded by a polynomial in `F`, the sizes and the
program (`icount`, `per`).
-/

@[expose] public section

namespace STACS2027.Sim

open Complexity
open Complexity.StackTableauProgram (Command Exec)
open Complexity.StackMachine (Registers set)
open Complexity.Restricted (writes exec_frame)

/-! ### The layout -/

/-- The stack register of the RAM register `i < 192`. -/
def rr (i : Nat) : Reg := ⟨64 + i % 192, by show 64 + i % 192 < 256; omega⟩

/-- The loop counter of nesting depth `j < 16`. -/
def ctr (j : Nat) : Reg := ⟨48 + j % 16, by show 48 + j % 16 < 256; omega⟩

theorem rr_val {i : Nat} (h : i < 192) : (rr i).val = 64 + i := by simp [rr, Nat.mod_eq_of_lt h]

theorem ctr_val {j : Nat} (h : j < 16) : (ctr j).val = 48 + j := by simp [ctr, Nat.mod_eq_of_lt h]

theorem rr_ge (i : Nat) : 64 ≤ (rr i).val := by simp [rr]

theorem rr_inj {i j : Nat} (hi : i < 192) (hj : j < 192) (h : rr i = rr j) : i = j := by
  have := congrArg Fin.val h; rw [rr_val hi, rr_val hj] at this; omega

theorem rr_ne_ctr (i j : Nat) : rr i ≠ ctr j := by
  intro h; have := congrArg Fin.val h; simp [rr, ctr] at this; omega

/-! ### Static conditions on programs -/

/-- All registers below `192`. -/
def RegsOK : XStmt → Prop
  | .skip => True
  | .const d _ => d < 192
  | .add d a b => d < 192 ∧ a < 192 ∧ b < 192
  | .sub d a b => d < 192 ∧ a < 192 ∧ b < 192
  | .load d a => d < 192 ∧ a < 192
  | .store a b => a < 192 ∧ b < 192
  | .getBit d => d < 192
  | .emit a => a < 192
  | .seq s t => RegsOK s ∧ RegsOK t
  | .ifz a s t => a < 192 ∧ RegsOK s ∧ RegsOK t
  | .loop a body => a < 192 ∧ RegsOK body

/-- The nesting depth of the loops. -/
def depth : XStmt → Nat
  | .seq s t => max (depth s) (depth t)
  | .ifz _ s t => max (depth s) (depth t)
  | .loop _ body => depth body + 1
  | _ => 0

/-- The longest numeral of a constant. -/
def constBits : XStmt → Nat
  | .const _ v => (bin v).length
  | .seq s t => max (constBits s) (constBits t)
  | .ifz _ s t => max (constBits s) (constBits t)
  | .loop _ body => constBits body
  | _ => 0

/-- A bound on the number of simulated instructions with fuel `F`. -/
def icount (F : Nat) : XStmt → Nat
  | .seq s t => icount F s + icount F t
  | .ifz _ s t => icount F s + icount F t + 1
  | .loop _ body => F * (icount F body + 1) + 1
  | _ => 1

/-- A bound on the stack instructions of one simulated instruction: numerals of at most `B` bits,
at most `E` memory entries, fuel `F`. -/
def per (B E F : Nat) : Nat := (E * (4 * B + 4) + 1) * (24 * B + 60) + 200 * (B + 1) + 10 * F + 20

theorem per_mono {B E F B' E' : Nat} (hB : B ≤ B') (hE : E ≤ E') : per B E F ≤ per B' E' F := by
  unfold per
  have h1 : E * (4 * B + 4) ≤ E' * (4 * B' + 4) := Nat.mul_le_mul hE (by omega)
  have h2 : (E * (4 * B + 4) + 1) * (24 * B + 60) ≤ (E' * (4 * B' + 4) + 1) * (24 * B' + 60) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

/-! ### The representation -/

/-- The stack registers `q` represent the configuration `c`: the scratch registers are empty, the
loop counters from depth `D` on are empty, numerals have at most `B` bits, the memory has at most
`E` entries. -/
def Rep (F : Nat) (c : XConfig) (q : Regs) (D B E : Nat) : Prop :=
  Clean q ∧ q INP = c.inp ∧ q OUTB = c.out.reverse ∧ q FUEL = List.replicate F true ∧
  (∀ i, i < 192 → q (rr i) = bin (c.reg i) ∧ (bin (c.reg i)).length ≤ B) ∧
  (∃ L : List (Nat × Nat), q MEM = encMem L ∧ L.length ≤ E ∧
    (∀ e ∈ L, (bin e.1).length ≤ B ∧ (bin e.2).length ≤ B) ∧ ∀ a, c.mem a = lookup L a) ∧
  (∀ j, D ≤ j → j < 16 → q (ctr j) = [])

theorem Rep.mono {F : Nat} {c : XConfig} {q : Regs} {D B E B' E' : Nat} (h : Rep F c q D B E) (hB : B ≤ B')
    (hE : E ≤ E') : Rep F c q D B' E' := by
  obtain ⟨h1, h2, h3, h4, h5, ⟨L, h6, h7, h8, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, fun i hi => ⟨(h5 i hi).1, by have := (h5 i hi).2; omega⟩,
    ⟨L, h6, by omega, fun e he => by have := h8 e he; omega, h9⟩, h10⟩

theorem encNum_length (bs : List Bool) : (encNum bs).length = 2 * bs.length + 1 := by
  unfold encNum
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at ih ⊢; omega

theorem encMem_length_le {B : Nat} : ∀ (L : List (Nat × Nat)), (∀ e ∈ L, (bin e.1).length ≤ B ∧ (bin e.2).length ≤ B) →
    (encMem L).length ≤ L.length * (4 * B + 4) := by
  intro L
  induction L with
  | nil => intro _; simp [encMem, memToks]
  | cons e L ih =>
    intro h
    obtain ⟨k, v⟩ := e
    rw [encMem_cons]
    obtain ⟨h1, h1'⟩ := h (k, v) (by simp)
    have h2 := ih (fun e he => h e (by simp [he]))
    simp only [List.length_append, encNum_length, List.length_cons]
    rw [Nat.add_mul, Nat.one_mul]
    simp only at h1 h1'
    omega

theorem lookup_bound {B : Nat} : ∀ (L : List (Nat × Nat)), (∀ e ∈ L, (bin e.2).length ≤ B) → ∀ a,
    (bin (lookup L a)).length ≤ B := by
  intro L
  induction L with
  | nil => intro _ a; simp [lookup_nil]
  | cons e L ih =>
    intro h a
    obtain ⟨k, v⟩ := e
    rw [lookup_cons]
    split
    · exact h (k, v) (by simp)
    · exact ih (fun e he => h e (by simp [he])) a

theorem bin_eq_nil_iff (n : Nat) : bin n = [] ↔ n = 0 := by
  constructor
  · intro h; have := congrArg num h; rwa [num_bin] at this
  · intro h; subst h; rfl

theorem bin_length_add {x y B : Nat} (hx : (bin x).length ≤ B) (hy : (bin y).length ≤ B) :
    (bin (x + y)).length ≤ B + 1 := by
  apply bin_length_le
  have := lt_pow_bin_length x; have := lt_pow_bin_length y
  have h1 : 2 ^ (bin x).length ≤ 2 ^ B := Nat.pow_le_pow_right (by omega) hx
  have h2 : 2 ^ (bin y).length ≤ 2 ^ B := Nat.pow_le_pow_right (by omega) hy
  rw [Nat.pow_succ]; omega

theorem bin_length_sub {x y B : Nat} (hx : (bin x).length ≤ B) : (bin (x - y)).length ≤ B := by
  apply bin_length_le
  have := lt_pow_bin_length x
  have h1 : 2 ^ (bin x).length ≤ 2 ^ B := Nat.pow_le_pow_right (by omega) hx
  omega

/-! ### The primitive commands -/

/-- Push the bits `bs` onto `d`, so that `d` starts with `bs`. -/
def pushList (d : Reg) : List Bool → Command K
  | [] => skipC
  | b :: bs => .seq (pushList d bs) (.push d b)

theorem ok_pushList (d : Reg) : ∀ (bs : List Bool) (q : Regs), Ok (pushList d bs) q (set q d (bs ++ q d)) (2 * bs.length + 1) := by
  intro bs
  induction bs with
  | nil =>
    intro q
    have : set q d ([] ++ q d) = q := by funext i; simp [set_apply]; intro h; subst h; rfl
    rw [this]; exact ok_skip q
  | cons b bs ih =>
    intro q
    have h := (ih q).seq (ok_push d b (set q d (bs ++ q d)))
    have e : set (set q d (bs ++ q d)) d (b :: set q d (bs ++ q d) d) = set q d ((b :: bs) ++ q d) := by
      funext i; simp [set_apply]; split <;> rfl
    rw [e] at h; exact h.mono (by simp; omega)

/-- `d := v`. -/
def constC (d : Reg) (v : Nat) : Command K := .seq (.clear d) (pushList d (bin v))

/-- `d :=` the next input bit (`2` at the end), and drop it from the input. -/
def getBitC (d : Reg) : Command K :=
  .branch INP (.seq (.clear d) (.seq (.push d true) (.push d false))) (.seq (.pop INP) (.clear d))
    (.seq (.pop INP) (.seq (.clear d) (.push d true)))

/-- Append the bit `a ≠ 0` to the output. -/
def emitC (a : Reg) : Command K := .branch a (.push OUTB false) (.push OUTB true) (.push OUTB true)

/-- The simulation of a program; `D` is the nesting depth of the loops around it. -/
def sim : Nat → XStmt → Command K
  | _, .skip => skipC
  | _, .const d v => constC (rr d) v
  | _, .add d a b => addB (rr a) (rr b) (rr d)
  | _, .sub d a b => subB (rr a) (rr b) (rr d)
  | _, .load d a => loadB (rr a) (rr d)
  | _, .store a b => storeB (rr a) (rr b)
  | _, .getBit d => getBitC (rr d)
  | _, .emit a => emitC (rr a)
  | D, .seq s t => .seq (sim D s) (sim D t)
  | D, .ifz a s t => .branch (rr a) (sim D s) (sim D t) (sim D t)
  | D, .loop a body => .seq (.copy FUEL (ctr D) XU)
      (.repeat (ctr D) (.branch (rr a) skipC (sim (D + 1) body) (sim (D + 1) body)))

/-! ### Updating the representation -/

theorem outer_rr (i : Nat) : Outer (rr i) := Or.inr (by have := rr_ge i; omega)

theorem outer_ctr {j : Nat} (h : j < 16) : Outer (ctr j) := Or.inr (by rw [ctr_val h]; omega)

theorem Outer.arithFree {i : Reg} (h : Outer i) : ArithFree i :=
  ⟨h.ne XA, h.ne XB, h.ne XC, h.ne XZ, h.ne XT, h.ne XU⟩

theorem Clean.arithEmpty {q : Regs} (h : Clean q) : ArithEmpty q :=
  ⟨h.at XA, h.at XB, h.at XC, h.at XZ, h.at XT, h.at XU⟩

theorem Clean.of_arith {q q' : Regs} (hc : Clean q) (he : ArithEmpty q') {d : Reg} (hd : Outer d)
    (hf : ∀ i, ArithFree i → i ≠ d → q' i = q i) : Clean q' := by
  intro i h1 h2
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := he
  by_cases hA : i = XA; · subst hA; exact a1
  by_cases hB : i = XB; · subst hB; exact a2
  by_cases hC : i = XC; · subst hC; exact a3
  by_cases hZ : i = XZ; · subst hZ; exact a4
  by_cases hT : i = XT; · subst hT; exact a5
  by_cases hU : i = XU; · subst hU; exact a6
  have hid : i ≠ d := fun e => by subst e; rcases hd with h | h <;> omega
  rw [hf i ⟨hA, hB, hC, hZ, hT, hU⟩ hid, hc i h1 h2]

theorem Rep.setReg {F : Nat} {c : XConfig} {q q' : Regs} {D B E B' : Nat} (h : Rep F c q D B E) {d v : Nat}
    (hd : d < 192) (hc : Clean q') (hf : ∀ i, Outer i → i ≠ rr d → q' i = q i) (hv : q' (rr d) = bin v)
    (hvB : (bin v).length ≤ B') (hB : B ≤ B') : Rep F (c.setReg d v) q' D B' E := by
  obtain ⟨h1, h2, h3, h4, h5, ⟨L, h6, h7, h8, h9⟩, h10⟩ := h
  have ne : ∀ j : Reg, j.val < 4 → j ≠ rr d := fun j hj e => by subst e; have := rr_ge d; omega
  refine ⟨hc, by rw [hf INP (Or.inl (by decide)) (ne INP (by decide)), h2]; rfl,
    by rw [hf OUTB (Or.inl (by decide)) (ne OUTB (by decide)), h3]; rfl,
    by rw [hf FUEL (Or.inl (by decide)) (ne FUEL (by decide)), h4], ?_,
    ⟨L, by rw [hf MEM (Or.inl (by decide)) (ne MEM (by decide)), h6], h7,
      fun e he => by have := h8 e he; omega, h9⟩, ?_⟩
  · intro i hi
    by_cases hid : i = d
    · subst hid; simp [XConfig.setReg, hv, hvB]
    · have hne : rr i ≠ rr d := fun e => hid (rr_inj hi hd e)
      rw [hf (rr i) (outer_rr i) hne]
      simp only [XConfig.setReg, hid, ite_false]
      exact ⟨(h5 i hi).1, by have := (h5 i hi).2; omega⟩
  · intro j hj1 hj2
    rw [hf (ctr j) (outer_ctr hj2) (Ne.symm (rr_ne_ctr d j)), h10 j hj1 hj2]

theorem ok_constC {F : Nat} {c : XConfig} {q : Regs} {D B E : Nat} (h : Rep F c q D B E) {d v : Nat}
    (hd : d < 192) (hvB : (bin v).length ≤ B) :
    ∃ q', Ok (constC (rr d) v) q q' (3 * B + 3) ∧ Rep F (c.setReg d v) q' D B E ∧
      ∀ i, Outer i → i ≠ rr d → q' i = q i := by
  have s := (ok_clear (rr d) q).seq (ok_pushList (rr d) (bin v) (set q (rr d) []))
  have hlen : (q (rr d)).length ≤ B := by rw [(h.2.2.2.2.1 d hd).1]; exact (h.2.2.2.2.1 d hd).2
  have hf : ∀ i, Outer i → i ≠ rr d → set (set q (rr d) []) (rr d) (bin v ++ set q (rr d) [] (rr d)) i = q i := by
    intro i _ hi; simp [hi]
  have hc : Clean (set (set q (rr d) []) (rr d) (bin v ++ set q (rr d) [] (rr d))) := by
    intro i h1 h2
    have : i ≠ rr d := fun e => by subst e; have := rr_ge d; omega
    simp [this, h.1 i h1 h2]
  refine ⟨_, s.mono (by omega), h.setReg hd hc hf (by simp) hvB (Nat.le_refl _), hf⟩

theorem ok_addC {F : Nat} {c : XConfig} {q : Regs} {D B E : Nat} (h : Rep F c q D B E) {d a b : Nat}
    (hd : d < 192) (ha : a < 192) (hb : b < 192) :
    ∃ q', Ok (addB (rr a) (rr b) (rr d)) q q' (100 * (B + 1)) ∧
      Rep F (c.setReg d (c.reg a + c.reg b)) q' D (B + 1) E ∧ ∀ i, Outer i → i ≠ rr d → q' i = q i := by
  obtain ⟨q', s, hv, he, hf⟩ := ok_addB (outer_rr a).arithFree (outer_rr b).arithFree (outer_rr d).arithFree q
    h.1.arithEmpty (h.2.2.2.2.1 a ha).1 (h.2.2.2.2.1 b hb).1 (h.2.2.2.2.1 a ha).2 (h.2.2.2.2.1 b hb).2
    (by rw [(h.2.2.2.2.1 d hd).1]; exact (h.2.2.2.2.1 d hd).2)
  have hf' : ∀ i, Outer i → i ≠ rr d → q' i = q i := fun i hi hid => hf i hi.arithFree hid
  exact ⟨q', s, h.setReg hd (h.1.of_arith he (outer_rr d) hf) hf' hv
    (bin_length_add (h.2.2.2.2.1 a ha).2 (h.2.2.2.2.1 b hb).2) (by omega), hf'⟩

theorem ok_subC {F : Nat} {c : XConfig} {q : Regs} {D B E : Nat} (h : Rep F c q D B E) {d a b : Nat}
    (hd : d < 192) (ha : a < 192) (hb : b < 192) :
    ∃ q', Ok (subB (rr a) (rr b) (rr d)) q q' (100 * (B + 1)) ∧
      Rep F (c.setReg d (c.reg a - c.reg b)) q' D B E ∧ ∀ i, Outer i → i ≠ rr d → q' i = q i := by
  obtain ⟨q', s, hv, he, hf⟩ := ok_subB (outer_rr a).arithFree (outer_rr b).arithFree (outer_rr d).arithFree q
    h.1.arithEmpty (h.2.2.2.2.1 a ha).1 (h.2.2.2.2.1 b hb).1 (h.2.2.2.2.1 a ha).2 (h.2.2.2.2.1 b hb).2
    (by rw [(h.2.2.2.2.1 d hd).1]; exact (h.2.2.2.2.1 d hd).2)
  have hf' : ∀ i, Outer i → i ≠ rr d → q' i = q i := fun i hi hid => hf i hi.arithFree hid
  exact ⟨q', s, h.setReg hd (h.1.of_arith he (outer_rr d) hf) hf' hv
    (bin_length_sub (h.2.2.2.2.1 a ha).2) (Nat.le_refl _), hf'⟩

theorem ok_loadC {F : Nat} {c : XConfig} {q : Regs} {D B E : Nat} (h : Rep F c q D B E) {d a : Nat}
    (hd : d < 192) (ha : a < 192) :
    ∃ q', Ok (loadB (rr a) (rr d)) q q' ((E * (4 * B + 4) + 1) * (24 * B + 60)) ∧
      Rep F (c.setReg d (c.mem (c.reg a))) q' D B E ∧ ∀ i, Outer i → i ≠ rr d → q' i = q i := by
  obtain ⟨h1, h2, h3, h4, h5, ⟨L, h6, h7, h8, h9⟩, h10⟩ := h
  have hv := lookup_bound L (fun e he => (h8 e he).2) (c.reg a)
  obtain ⟨q', s, hd', hc, hf⟩ := ok_loadB (a := rr a) (d := rr d) (B := B) (by have := rr_ge a; omega)
    (by have := rr_ge d; omega) q h1 h6 (h5 a ha).1 (h5 a ha).2 (by rw [(h5 d hd).1]; exact (h5 d hd).2) hv
  have hW := encMem_length_le L h8
  have hW' : (encMem L).length ≤ E * (4 * B + 4) := Nat.le_trans hW (Nat.mul_le_mul_right _ h7)
  refine ⟨q', s.mono (Nat.mul_le_mul_right (24 * B + 60) (Nat.add_le_add_right hW' 1)), ?_, hf⟩
  rw [h9 (c.reg a)]
  exact Rep.setReg ⟨h1, h2, h3, h4, h5, ⟨L, h6, h7, h8, h9⟩, h10⟩ hd hc hf hd' hv (Nat.le_refl _)

theorem rr_ne (i : Nat) (j : Reg) (hj : j.val < 64 := by decide) : rr i ≠ j := fun e => by
  have := congrArg Fin.val e; have := rr_ge i; omega

theorem ctr_ne {j : Nat} (hj : j < 16) (k : Reg) (hk : k.val < 48 := by decide) : ctr j ≠ k := fun e => by
  have := congrArg Fin.val e; rw [ctr_val hj] at this; omega

theorem ok_storeC {F : Nat} {c : XConfig} {q : Regs} {D B E : Nat} (h : Rep F c q D B E) {a b : Nat}
    (ha : a < 192) (hb : b < 192) :
    ∃ q', Ok (storeB (rr a) (rr b)) q q' (60 * B + 60) ∧
      Rep F (c.setMem (c.reg a) (c.reg b)) q' D B (E + 1) ∧ ∀ i, Outer i → i ≠ MEM → q' i = q i := by
  obtain ⟨h1, h2, h3, h4, h5, ⟨L, h6, h7, h8, h9⟩, h10⟩ := h
  obtain ⟨q', s, hm, hc, hf⟩ := ok_storeB (a := rr a) (b := rr b) (by have := rr_ge a; omega)
    (by have := rr_ge b; omega) q h1 h6 (h5 a ha).1 (h5 b hb).1
  refine ⟨q', s.mono (by have := (h5 a ha).2; have := (h5 b hb).2; omega), ⟨hc, ?_, ?_, ?_, ?_, ?_, ?_⟩, hf⟩
  · rw [hf INP (Or.inl (by decide)) (by decide), h2]; rfl
  · rw [hf OUTB (Or.inl (by decide)) (by decide), h3]; rfl
  · rw [hf FUEL (Or.inl (by decide)) (by decide), h4]
  · intro i hi
    rw [hf (rr i) (outer_rr i) (rr_ne i MEM)]
    exact h5 i hi
  · refine ⟨(c.reg a, c.reg b) :: L, hm, by simp; omega, ?_, ?_⟩
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨(h5 a ha).2, (h5 b hb).2⟩
      · exact h8 e he
    · intro x
      simp only [XConfig.setMem, lookup_cons, h9 x]
      by_cases hx : x = c.reg a
      · subst hx; simp
      · simp [hx, Ne.symm hx]
  · intro j hj1 hj2
    rw [hf (ctr j) (outer_ctr hj2) (ctr_ne hj2 MEM), h10 j hj1 hj2]

theorem ok_getBitRaw (d : Reg) (dI : d ≠ INP) (q : Regs) :
    ∃ q', Ok (getBitC d) q q' ((q d).length + 8) ∧ q' INP = (q INP).tail ∧ q' d = bin (bitVal (q INP)) ∧
      ∀ i, i ≠ d → i ≠ INP → q' i = q i := by
  cases hi : q INP with
  | nil =>
    refine ⟨_, (Ok.branch_nil hi ((ok_clear d q).seq ((ok_push d true _).seq (ok_push d false _)))).mono
      (by omega), ?_, ?_, ?_⟩
    · simp [Ne.symm dI, hi]
    · simp [bitVal]; rfl
    · intro i h1 h2; simp [h1]
  | cons b w =>
    cases b with
    | false =>
      refine ⟨_, (Ok.branch_false hi ((ok_pop INP q).seq (ok_clear d _))).mono (by simp [dI]; omega),
        ?_, ?_, ?_⟩
      · simp [Ne.symm dI, hi]
      · simp [bitVal]
      · intro i h1 h2; simp [h1, h2]
    | true =>
      refine ⟨_, (Ok.branch_true hi ((ok_pop INP q).seq ((ok_clear d _).seq (ok_push d true _)))).mono
        (by simp [dI]; omega), ?_, ?_, ?_⟩
      · simp [Ne.symm dI, hi]
      · simp [bitVal]; rfl
      · intro i h1 h2; simp [h1, h2]

theorem ok_getBitC {F : Nat} {c : XConfig} {q : Regs} {D B E : Nat} (h : Rep F c q D B E) {d : Nat}
    (hd : d < 192) (hB : 2 ≤ B) :
    ∃ q', Ok (getBitC (rr d)) q q' (B + 10) ∧ Rep F (c.getBit d) q' D B E ∧
      ∀ i, Outer i → i ≠ rr d → i ≠ INP → q' i = q i := by
  obtain ⟨h1, h2, h3, h4, h5, ⟨L, h6, h7, h8, h9⟩, h10⟩ := h
  have hdl : (q (rr d)).length ≤ B := by rw [(h5 d hd).1]; exact (h5 d hd).2
  obtain ⟨q', s, hI, hv, hf⟩ := ok_getBitRaw (rr d) (rr_ne d INP) q
  have hf' : ∀ i, Outer i → i ≠ rr d → i ≠ INP → q' i = q i := fun i _ h1 h2 => hf i h1 h2
  refine ⟨q', s.mono (by omega), ⟨?_, ?_, ?_, ?_, ?_, ⟨L, ?_, h7, h8, h9⟩, ?_⟩, hf'⟩
  · intro i i1 i2
    have a1 : i ≠ rr d := fun e => by subst e; have := rr_ge d; omega
    have a2 : i ≠ INP := fun e => by subst e; simp at i1
    rw [hf i a1 a2, h1 i i1 i2]
  · rw [hI, h2]; rfl
  · rw [hf OUTB (Ne.symm (rr_ne d OUTB)) (by decide), h3]; rfl
  · rw [hf FUEL (Ne.symm (rr_ne d FUEL)) (by decide), h4]
  · intro i hi
    by_cases hid : i = d
    · subst hid
      simp only [XConfig.getBit, ite_true]
      rw [hv, h2]
      refine ⟨rfl, ?_⟩
      have : (bin (bitVal c.inp)).length ≤ 2 := by
        apply bin_length_le; cases c.inp with
        | nil => simp [bitVal]
        | cons b w => cases b <;> simp [bitVal]
      omega
    · have hne : rr i ≠ rr d := fun e => hid (rr_inj hi hd e)
      rw [hf (rr i) hne (rr_ne i INP)]
      simp only [XConfig.getBit, hid, ite_false]
      exact h5 i hi
  · rw [hf MEM (Ne.symm (rr_ne d MEM)) (by decide), h6]
  · intro j hj1 hj2
    rw [hf (ctr j) (Ne.symm (rr_ne_ctr d j)) (ctr_ne hj2 INP), h10 j hj1 hj2]

theorem ok_emitC {F : Nat} {c : XConfig} {q : Regs} {D B E : Nat} (h : Rep F c q D B E) {a : Nat} (ha : a < 192) :
    ∃ q', Ok (emitC (rr a)) q q' 3 ∧ Rep F (c.emit a) q' D B E ∧ ∀ i, i ≠ OUTB → q' i = q i := by
  obtain ⟨h1, h2, h3, h4, h5, ⟨L, h6, h7, h8, h9⟩, h10⟩ := h
  have key : ∃ q', Ok (emitC (rr a)) q q' 3 ∧ q' OUTB = decide (c.reg a ≠ 0) :: q OUTB ∧
      ∀ i, i ≠ OUTB → q' i = q i := by
    have hv := (h5 a ha).1
    cases hq : q (rr a) with
    | nil =>
      rw [hq] at hv
      have : c.reg a = 0 := (bin_eq_nil_iff _).mp hv.symm
      exact ⟨_, Ok.branch_nil hq (ok_push OUTB false q), by simp [this], fun i hi => by simp [hi]⟩
    | cons b w =>
      rw [hq] at hv
      have : c.reg a ≠ 0 := fun e => by rw [e] at hv; simp at hv
      cases b
      · exact ⟨_, Ok.branch_false hq (ok_push OUTB true q), by simp [this], fun i hi => by simp [hi]⟩
      · exact ⟨_, Ok.branch_true hq (ok_push OUTB true q), by simp [this], fun i hi => by simp [hi]⟩
  obtain ⟨q', s, hO, hf⟩ := key
  refine ⟨q', s, ⟨?_, ?_, ?_, ?_, ?_, ⟨L, ?_, h7, h8, h9⟩, ?_⟩, hf⟩
  · intro i i1 i2
    rw [hf i (fun e => by subst e; simp at i1), h1 i i1 i2]
  · rw [hf INP (by decide), h2]; rfl
  · rw [hO, h3]; simp [XConfig.emit]
  · rw [hf FUEL (by decide), h4]
  · intro i hi
    rw [hf (rr i) (rr_ne i OUTB)]
    exact h5 i hi
  · rw [hf MEM (by decide), h6]
  · intro j hj1 hj2
    rw [hf (ctr j) (ctr_ne hj2 OUTB), h10 j hj1 hj2]

/-! ### Depths of the representation -/

theorem ctr_inj {j k : Nat} (hj : j < 16) (hk : k < 16) (h : ctr j = ctr k) : j = k := by
  have := congrArg Fin.val h; rw [ctr_val hj, ctr_val hk] at this; omega

theorem Rep.succ {F : Nat} {c : XConfig} {q : Regs} {D B E : Nat} (h : Rep F c q D B E) : Rep F c q (D + 1) B E :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, fun j hj1 hj2 => h.2.2.2.2.2.2 j (by omega) hj2⟩

theorem Rep.pred {F : Nat} {c : XConfig} {q : Regs} {D B E : Nat} (h : Rep F c q (D + 1) B E) (hD : q (ctr D) = []) :
    Rep F c q D B E := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, fun j hj1 hj2 => ?_⟩
  by_cases hj : j = D
  · subst hj; exact hD
  · exact h.2.2.2.2.2.2 j (by omega) hj2

theorem Rep.setCtr {F : Nat} {c : XConfig} {q : Regs} {D B E : Nat} (h : Rep F c q (D + 1) B E) (hD : D < 16)
    (w : List Bool) : Rep F c (set q (ctr D) w) (D + 1) B E := by
  obtain ⟨h1, h2, h3, h4, h5, ⟨L, h6, h7, h8, h9⟩, h10⟩ := h
  refine ⟨fun i i1 i2 => ?_, ?_, ?_, ?_, fun i hi => ?_, ⟨L, ?_, h7, h8, h9⟩, fun j hj1 hj2 => ?_⟩
  · have : i ≠ ctr D := fun e => by subst e; rw [ctr_val hD] at i2; omega
    simp [this, h1 i i1 i2]
  · simp [Ne.symm (ctr_ne hD INP), h2]
  · simp [Ne.symm (ctr_ne hD OUTB), h3]
  · simp [Ne.symm (ctr_ne hD FUEL), h4]
  · simp [rr_ne_ctr i D, h5 i hi]
  · simp [Ne.symm (ctr_ne hD MEM), h6]
  · have : ctr j ≠ ctr D := fun e => by have := ctr_inj hj2 hD e; omega
    simp [this, h10 j hj1 hj2]

/-! ### The simulation theorem -/

theorem prim_ok {F D B E : Nat} {cmd : Command K} {q q' : Regs} {c' : XConfig} {b B' E' : Nat} (hs : Ok cmd q q' b)
    (hb : b ≤ per B E F) (hr : Rep F c' q' D B' E') (hB : B' ≤ B + 1) (hE : E' ≤ E + 1)
    (hc : ∀ j, j < D → q' (ctr j) = q (ctr j)) :
    ∃ q'', Ok cmd q q'' (1 * per (B + 1) (E + 1) F) ∧ Rep F c' q'' D (B + 1) (E + 1) ∧
      ∀ j, j < D → q'' (ctr j) = q (ctr j) :=
  ⟨q', hs.mono (by have := per_mono (F := F) (show B ≤ B + 1 by omega) (show E ≤ E + 1 by omega); omega),
    hr.mono hB hE, hc⟩

theorem per_ge (B E F : Nat) : 200 * (B + 1) + 10 * F + 20 ≤ per B E F := by unfold per; omega

theorem per_ge_load (B E F : Nat) : (E * (4 * B + 4) + 1) * (24 * B + 60) ≤ per B E F := by unfold per; omega

theorem icount_pos (F : Nat) : ∀ s : XStmt, 1 ≤ icount F s := by
  intro s
  induction s <;> simp only [icount] <;> omega

/-- **The simulation.** From stack registers representing `c` at loop depth `D`, `sim D s` halts in
stack registers representing `xrun F s c`, within `icount F s · per (B + icount F s) (E + icount F s) F`
instructions, and leaves the counters of the enclosing loops alone. -/
theorem sim_correct (F : Nat) : ∀ (s : XStmt) (D : Nat) (c : XConfig) (q : Regs) (B E : Nat),
    RegsOK s → D + depth s ≤ 16 → 2 ≤ B → constBits s ≤ B → Rep F c q D B E →
    ∃ q', Ok (sim D s) q q' (icount F s * per (B + icount F s) (E + icount F s) F) ∧
      Rep F (xrun F s c) q' D (B + icount F s) (E + icount F s) ∧ ∀ j, j < D → q' (ctr j) = q (ctr j) := by
  intro s
  induction s with
  | skip =>
    intro D c q B E _ _ _ _ h
    exact prim_ok (ok_skip q) (by have := per_ge B E F; omega) h (by omega) (by omega) (fun _ _ => rfl)
  | const d v =>
    intro D c q B E hR hD _ hK h
    simp only [RegsOK] at hR; simp only [constBits] at hK
    obtain ⟨q', s, hr, hf⟩ := ok_constC h hR hK
    exact prim_ok s (by have := per_ge B E F; omega) hr (by omega) (by omega)
      (fun j hj => hf _ (outer_ctr (by simp [depth] at hD; omega)) (Ne.symm (rr_ne_ctr d j)))
  | add d a b =>
    intro D c q B E hR hD _ _ h
    simp only [RegsOK] at hR
    obtain ⟨q', s, hr, hf⟩ := ok_addC h hR.1 hR.2.1 hR.2.2
    exact prim_ok s (by have := per_ge B E F; omega) hr (by omega) (by omega)
      (fun j hj => hf _ (outer_ctr (by simp [depth] at hD; omega)) (Ne.symm (rr_ne_ctr d j)))
  | sub d a b =>
    intro D c q B E hR hD _ _ h
    simp only [RegsOK] at hR
    obtain ⟨q', s, hr, hf⟩ := ok_subC h hR.1 hR.2.1 hR.2.2
    exact prim_ok s (by have := per_ge B E F; omega) hr (by omega) (by omega)
      (fun j hj => hf _ (outer_ctr (by simp [depth] at hD; omega)) (Ne.symm (rr_ne_ctr d j)))
  | load d a =>
    intro D c q B E hR hD _ _ h
    simp only [RegsOK] at hR
    obtain ⟨q', s, hr, hf⟩ := ok_loadC h hR.1 hR.2
    exact prim_ok s (per_ge_load B E F) hr (by omega) (by omega)
      (fun j hj => hf _ (outer_ctr (by simp [depth] at hD; omega)) (Ne.symm (rr_ne_ctr d j)))
  | store a b =>
    intro D c q B E hR hD _ _ h
    simp only [RegsOK] at hR
    obtain ⟨q', s, hr, hf⟩ := ok_storeC h hR.1 hR.2
    exact prim_ok s (by have := per_ge B E F; omega) hr (by omega) (by omega)
      (fun j hj => hf _ (outer_ctr (by simp [depth] at hD; omega)) (ctr_ne (by simp [depth] at hD; omega) MEM))
  | getBit d =>
    intro D c q B E hR hD hB _ h
    simp only [RegsOK] at hR
    obtain ⟨q', s, hr, hf⟩ := ok_getBitC h hR hB
    exact prim_ok s (by have := per_ge B E F; omega) hr (by omega) (by omega)
      (fun j hj => hf _ (outer_ctr (by simp [depth] at hD; omega)) (Ne.symm (rr_ne_ctr d j))
        (ctr_ne (by simp [depth] at hD; omega) INP))
  | emit a =>
    intro D c q B E hR hD _ _ h
    simp only [RegsOK] at hR
    obtain ⟨q', s, hr, hf⟩ := ok_emitC h hR
    exact prim_ok s (by have := per_ge B E F; omega) hr (by omega) (by omega)
      (fun j hj => hf _ (ctr_ne (by simp [depth] at hD; omega) OUTB))
  | seq s t ihs iht =>
    intro D c q B E hR hD hB hK h
    simp only [RegsOK] at hR; simp only [depth] at hD; simp only [constBits] at hK
    obtain ⟨q1, s1, h1, f1⟩ := ihs D c q B E hR.1 (by omega) hB (by omega) h
    obtain ⟨q2, s2, h2, f2⟩ := iht D _ q1 (B + icount F s) (E + icount F s) hR.2 (by omega) (by omega) (by omega) h1
    refine ⟨q2, (s1.seq s2).mono ?_, ?_, fun j hj => by rw [f2 j hj, f1 j hj]⟩
    · simp only [icount]
      have p1 := per_mono (F := F) (show B + icount F s ≤ B + (icount F s + icount F t) by omega)
        (show E + icount F s ≤ E + (icount F s + icount F t) by omega)
      have e2 : B + icount F s + icount F t = B + (icount F s + icount F t) := by omega
      have e3 : E + icount F s + icount F t = E + (icount F s + icount F t) := by omega
      rw [e2, e3]
      have := Nat.mul_le_mul_left (icount F s) p1
      rw [Nat.add_mul]; omega
    · simp only [icount, xrun]
      have e2 : B + icount F s + icount F t = B + (icount F s + icount F t) := by omega
      have e3 : E + icount F s + icount F t = E + (icount F s + icount F t) := by omega
      rw [← e2, ← e3]; exact h2
  | ifz a s t ihs iht =>
    intro D c q B E hR hD hB hK h
    simp only [RegsOK] at hR; simp only [depth] at hD; simp only [constBits] at hK
    have hra := (h.2.2.2.2.1 a hR.1).1
    have pS := per_mono (F := F) (show B + icount F s ≤ B + (icount F s + icount F t + 1) by omega)
        (show E + icount F s ≤ E + (icount F s + icount F t + 1) by omega)
    have pT := per_mono (F := F) (show B + icount F t ≤ B + (icount F s + icount F t + 1) by omega)
        (show E + icount F t ≤ E + (icount F s + icount F t + 1) by omega)
    have p1 : 1 ≤ per (B + (icount F s + icount F t + 1)) (E + (icount F s + icount F t + 1)) F := by
      have := per_ge (B + (icount F s + icount F t + 1)) (E + (icount F s + icount F t + 1)) F; omega
    by_cases h0 : c.reg a = 0
    · obtain ⟨q1, s1, h1, f1⟩ := ihs D c q B E hR.2.1 (by omega) hB (by omega) h
      have hq : q (rr a) = [] := by rw [hra, h0]; rfl
      refine ⟨q1, (Ok.branch_nil hq s1).mono ?_, ?_, f1⟩
      · simp only [icount]
        have := Nat.mul_le_mul_left (icount F s) pS
        rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; omega
      · simp only [icount, xrun, h0, ite_true]; exact h1.mono (by omega) (by omega)
    · obtain ⟨q1, s1, h1, f1⟩ := iht D c q B E hR.2.2 (by omega) hB (by omega) h
      have hcost : icount F t * per (B + icount F t) (E + icount F t) F + 1 ≤
          icount F (.ifz a s t) * per (B + icount F (.ifz a s t)) (E + icount F (.ifz a s t)) F := by
        simp only [icount]
        have := Nat.mul_le_mul_left (icount F t) pT
        rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; omega
      have hx : xrun F (.ifz a s t) c = xrun F t c := by simp only [xrun, h0, ite_false]
      rw [hx]
      cases hq : q (rr a) with
      | nil => rw [hra] at hq; exact absurd ((bin_eq_nil_iff _).mp hq) h0
      | cons x w =>
        refine ⟨q1, ?_, h1.mono (by simp only [icount]; omega) (by simp only [icount]; omega), f1⟩
        cases x
        · exact (Ok.branch_false hq s1).mono hcost
        · exact (Ok.branch_true hq s1).mono hcost
  | loop a body ih =>
    intro D c q B E hR hD hB hK h
    simp only [RegsOK] at hR; simp only [depth] at hD; simp only [constBits] at hK
    obtain ⟨ha, hRb⟩ := hR
    have hD16 : D < 16 := by omega
    have hcopy := ok_copy (s := FUEL) (d := ctr D) (t := XU) (Ne.symm (ctr_ne hD16 FUEL)) (by decide)
      (ctr_ne hD16 XU) q (h.1.at XU)
    have hF := h.2.2.2.1
    have hq1 : Rep F c (set q (ctr D) (q FUEL)) (D + 1) B E := h.succ.setCtr hD16 _
    generalize hib : icount F body = ib
    let g := fun c => if c.reg a = 0 then c else xrun F body c
    let I : Nat → Regs → Prop := fun i r => Rep F (iter g i c) r (D + 1) (B + i * ib) (E + i * ib) ∧
      ∀ j, j < D → r (ctr j) = q (ctr j)
    have hstep : ∀ i r, i < F → I i r → ∃ r', Ok (.branch (rr a) skipC (sim (D + 1) body) (sim (D + 1) body)) r r'
        (ib * per (B + F * ib) (E + F * ib) F + 1) ∧ I (i + 1) r' ∧ r' (ctr D) = r (ctr D) := by
      intro i r hi ⟨hr, hfr⟩
      have hra := (hr.2.2.2.2.1 a ha).1
      have hmono : B + i * ib ≤ B + (i + 1) * ib := by rw [Nat.add_mul, Nat.one_mul]; omega
      have hmonoE : E + i * ib ≤ E + (i + 1) * ib := by rw [Nat.add_mul, Nat.one_mul]; omega
      have hpos : 1 ≤ ib * per (B + F * ib) (E + F * ib) F := by
        have h1 : 1 ≤ ib := by rw [← hib]; exact icount_pos F body
        have h2 : 20 ≤ per (B + F * ib) (E + F * ib) F := by have := per_ge (B + F * ib) (E + F * ib) F; omega
        exact Nat.le_trans h1 (Nat.le_mul_of_pos_right ib (by omega))
      by_cases h0 : (iter g i c).reg a = 0
      · have hq : r (rr a) = [] := by rw [hra, h0]; rfl
        refine ⟨r, (Ok.branch_nil hq (ok_skip r)).mono (by omega), ⟨?_, hfr⟩, rfl⟩
        rw [iter_succ']
        have : g (iter g i c) = iter g i c := by simp only [g, h0, ite_true]
        rw [this]; exact hr.mono hmono hmonoE
      · obtain ⟨r', s', hr', hf'⟩ := ih (D + 1) (iter g i c) r (B + i * ib) (E + i * ib) hRb (by omega)
          (by omega) (by omega) hr
        rw [hib] at s' hr'
        have hcost : ib * per (B + i * ib + ib) (E + i * ib + ib) F + 1 ≤ ib * per (B + F * ib) (E + F * ib) F + 1 := by
          have : i * ib + ib ≤ F * ib := by
            have h1 : (i + 1) * ib ≤ F * ib := Nat.mul_le_mul_right _ hi
            rw [Nat.add_mul, Nat.one_mul] at h1; exact h1
          have := Nat.mul_le_mul_left ib (per_mono (F := F) (show B + i * ib + ib ≤ B + F * ib by omega)
            (show E + i * ib + ib ≤ E + F * ib by omega))
          omega
        have hg : iter g (i + 1) c = xrun F body (iter g i c) := by
          rw [iter_succ']; simp only [g, h0, ite_false]
        have e1 : B + i * ib + ib = B + (i + 1) * ib := by rw [Nat.add_mul, Nat.one_mul]; omega
        have e2 : E + i * ib + ib = E + (i + 1) * ib := by rw [Nat.add_mul, Nat.one_mul]; omega
        rw [e1, e2] at hr'
        refine ⟨r', ?_, ⟨by rw [hg]; exact hr', fun j hj => by rw [hf' j (by omega), hfr j hj]⟩,
          hf' D (by omega)⟩
        cases hq : r (rr a) with
        | nil => rw [hra] at hq; exact absurd ((bin_eq_nil_iff _).mp hq) h0
        | cons x w =>
          cases x
          · exact (Ok.branch_false hq s').mono hcost
          · exact (Ok.branch_true hq s').mono hcost
    obtain ⟨q2, s2, ⟨hr2, hf2⟩, hc2⟩ := ok_repeatN (j := ctr D)
      (body := .branch (rr a) skipC (sim (D + 1) body) (sim (D + 1) body)) F I (ib * per (B + F * ib) (E + F * ib) F + 1)
      (fun i r w ⟨hr, hfr⟩ => ⟨hr.setCtr hD16 w, fun j hj => by
        have : ctr j ≠ ctr D := fun e => by have := ctr_inj (by omega) hD16 e; omega
        simp [this, hfr j hj]⟩)
      hstep (set q (ctr D) (q FUEL)) ⟨by simp only [iter, Nat.zero_mul, Nat.add_zero]; exact hq1,
        fun j hj => by
          have : ctr j ≠ ctr D := fun e => by have := ctr_inj (by omega) hD16 e; omega
          simp [this]⟩ (by simp [hF])
    refine ⟨q2, (hcopy.seq s2).mono ?_, ?_, hf2⟩
    · simp only [icount, hib]
      rw [h.2.2.2.2.2.2 D (Nat.le_refl _) hD16, hF]
      simp only [List.length_nil, List.length_replicate, Nat.zero_add]
      have hP : per (B + F * ib) (E + F * ib) F ≤ per (B + (F * (ib + 1) + 1)) (E + (F * (ib + 1) + 1)) F :=
        per_mono (show B + F * ib ≤ B + (F * (ib + 1) + 1) by rw [Nat.mul_succ]; omega)
          (show E + F * ib ≤ E + (F * (ib + 1) + 1) by rw [Nat.mul_succ]; omega)
      generalize per (B + (F * (ib + 1) + 1)) (E + (F * (ib + 1) + 1)) F = P' at hP ⊢
      have hP' : 20 ≤ P' := by have := per_ge (B + F * ib) (E + F * ib) F; omega
      have e1 : F * (ib * per (B + F * ib) (E + F * ib) F) ≤ F * (ib * P') := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hP)
      have e2 : 7 * F ≤ F * P' := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
      have rhs : (F * (ib + 1) + 1) * P' = F * (ib * P') + F * P' + P' := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.add_mul, Nat.one_mul, Nat.mul_add]
      have lhs : F * (ib * per (B + F * ib) (E + F * ib) F + 1 + 1) = F * (ib * per (B + F * ib) (E + F * ib) F) + F + F := by rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      rw [rhs, lhs]; omega
    · simp only [icount, hib, xrun]
      have hr2' := hr2.pred hc2
      exact hr2'.mono (by rw [Nat.mul_succ]; omega) (by rw [Nat.mul_succ]; omega)

end STACS2027.Sim
