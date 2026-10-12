module

public import ApproximationHardness.Sim.Arith
import Lean.Elab.Tactic.Omega

/-!
# The memory on a stack register

The memory of the simulated RAM is the register `MEM`, a list of entries `(address, value)`,
newest first: the code of an entry is the code of the address and the code of the value, where a
numeral `bs` is coded as `true, b` for every bit `b` and a final `false`. The value at an address is
the value of its newest entry (`lookup`), `0` without an entry.

`storeB a b` adds the entry `(a, b)` in front (`ok_storeB`); `loadB a d` scans the entries for the
address `a` (`ok_loadB`).
-/

@[expose] public section

namespace STACS2027.Sim

open Complexity
open Complexity.StackTableauProgram (Command Exec)
open Complexity.StackMachine (Registers set)
open Complexity.Restricted (writes exec_frame)

/-! ### Codes -/

/-- A flag register: `[true]` for set, empty for unset. -/
def flag (b : Bool) : List Bool := if b then [true] else []

@[simp] theorem flag_true : flag true = [true] := rfl
@[simp] theorem flag_false : flag false = [] := rfl

/-- A token of the memory code: a bit of a numeral, or the end of a numeral. -/
abbrev Tok := Option Bool

def tokEnc : Tok → List Bool
  | none => [false]
  | some b => [true, b]

/-- The tokens of an entry. -/
def entryToks (k v : Nat) : List Tok := (bin k).map some ++ [none] ++ (bin v).map some ++ [none]

/-- The tokens of a memory. -/
def memToks (L : List (Nat × Nat)) : List Tok := L.flatMap fun e => entryToks e.1 e.2

/-- The code of a memory. -/
def encMem (L : List (Nat × Nat)) : List Bool := (memToks L).flatMap tokEnc

/-- The value at the address `a`: that of the newest entry for `a`, `0` without an entry. -/
def lookup (L : List (Nat × Nat)) (a : Nat) : Nat :=
  match L.find? (fun e => e.1 == a) with
  | some e => e.2
  | none => 0

theorem lookup_nil (a : Nat) : lookup [] a = 0 := rfl

theorem lookup_cons (k v : Nat) (L : List (Nat × Nat)) (a : Nat) :
    lookup ((k, v) :: L) a = if k = a then v else lookup L a := by
  unfold lookup
  by_cases h : k = a
  · simp [h]
  · simp [h]

/-! ### The scan, abstractly -/

/-- The state of the scan: in the value part of an entry; the address of the entry differs from
the key so far; the key bits still to compare; the value of this entry is taken; a value was
found; the bits of the value taken, last first. -/
structure ScanSt where
  phase : Bool
  mis : Bool
  kc : List Bool
  take : Bool
  found : Bool
  val : List Bool

/-- The next key bit is missing or differs from `b`. -/
def mismatchBit : List Bool → Bool → Bool
  | [], _ => true
  | c :: _, b => c != b

@[simp] theorem mismatchBit_nil (b : Bool) : mismatchBit [] b = true := rfl
@[simp] theorem mismatchBit_cons (c b : Bool) (l : List Bool) : mismatchBit (c :: l) b = (c != b) := rfl

/-- One token of the scan for the key `KEY`. -/
def scanStep (KEY : List Bool) (st : ScanSt) : Tok → ScanSt
  | some b =>
    if st.phase then (if st.take then { st with val := b :: st.val } else st)
    else { st with mis := st.mis || mismatchBit st.kc b, kc := st.kc.tail }
  | none =>
    if st.phase then ⟨false, false, KEY, false, st.found || st.take, st.val⟩
    else ⟨true, st.mis || !st.kc.isEmpty, [], !(st.mis || !st.kc.isEmpty) && !st.found, st.found, st.val⟩

theorem scan_keyBits (KEY : List Bool) : ∀ (ks : List Bool) (m : Bool) (kc : List Bool) (tk fd : Bool)
    (val : List Bool), (ks.map some).foldl (scanStep KEY) ⟨false, m, kc, tk, fd, val⟩ =
      ⟨false, m || !(ks.isPrefixOf kc), kc.drop ks.length, tk, fd, val⟩ := by
  intro ks
  induction ks with
  | nil => intro m kc tk fd val; simp [List.isPrefixOf]
  | cons b ks ih =>
    intro m kc tk fd val
    simp only [List.map_cons, List.foldl_cons, scanStep, Bool.false_eq_true, ite_false]
    rw [ih]
    cases kc with
    | nil => simp [List.isPrefixOf]
    | cons c kc =>
      simp only [List.tail_cons, List.isPrefixOf, List.length_cons, List.drop_succ_cons]
      cases b <;> cases c <;> cases m <;> simp

theorem scan_valBits (KEY : List Bool) : ∀ (vs : List Bool) (m tk fd : Bool) (val : List Bool),
    (vs.map some).foldl (scanStep KEY) ⟨true, m, [], tk, fd, val⟩ =
      ⟨true, m, [], tk, fd, if tk then vs.reverse ++ val else val⟩ := by
  intro vs
  induction vs with
  | nil => intro m tk fd val; cases tk <;> simp
  | cons b vs ih =>
    intro m tk fd val
    simp only [List.map_cons, List.foldl_cons, scanStep, ite_true]
    cases tk
    · simp only [Bool.false_eq_true, ite_false]; rw [ih]; simp
    · simp only [ite_true]; rw [ih]; simp

theorem isPrefixOf_drop_eq (ks kc : List Bool) :
    (ks.isPrefixOf kc && (kc.drop ks.length).isEmpty) = (ks == kc) := by
  induction ks generalizing kc with
  | nil => cases kc <;> simp [List.isPrefixOf]
  | cons b ks ih =>
    cases kc with
    | nil => simp [List.isPrefixOf]
    | cons c kc =>
      simp only [List.isPrefixOf, List.length_cons, List.drop_succ_cons, Bool.and_assoc, ih]
      cases b <;> cases c <;> simp

theorem bin_inj {a b : Nat} (h : bin a = bin b) : a = b := by
  have := congrArg num h; rwa [num_bin, num_bin] at this

/-- One entry of the scan, from the start of the entry. -/
theorem scan_entry (a k v : Nat) (fd : Bool) (val : List Bool) :
    (entryToks k v).foldl (scanStep (bin a)) ⟨false, false, bin a, false, fd, val⟩ =
      ⟨false, false, bin a, false, fd || k == a, if k == a && !fd then (bin v).reverse ++ val else val⟩ := by
  unfold entryToks
  simp only [List.foldl_append, scan_keyBits, Bool.false_or]
  simp only [List.foldl_cons, List.foldl_nil, scanStep, Bool.false_eq_true, ite_false]
  have hk : (!(bin k).isPrefixOf (bin a) || !((bin a).drop (bin k).length).isEmpty) = !(k == a) := by
    have := isPrefixOf_drop_eq (bin k) (bin a)
    have e : ((bin k == bin a) = (k == a)) := by
      by_cases h : k = a
      · subst h; simp only [beq_self_eq_true]
      · have : bin k ≠ bin a := fun h' => h (bin_inj h')
        rw [beq_false_of_ne this, beq_false_of_ne h]
    rw [← e, ← this]
    cases (bin k).isPrefixOf (bin a) <;> cases hd : (bin a).drop (bin k).length <;> simp
  rw [hk, scan_valBits]
  cases hka : k == a <;> cases fd <;> simp []

theorem scan_mem (a : Nat) : ∀ (L : List (Nat × Nat)) (val : List Bool),
    (memToks L).foldl (scanStep (bin a)) ⟨false, false, bin a, false, true, val⟩ =
      ⟨false, false, bin a, false, true, val⟩ ∧
    (memToks L).foldl (scanStep (bin a)) ⟨false, false, bin a, false, false, []⟩ =
      ⟨false, false, bin a, false, L.any (fun e => e.1 == a), (bin (lookup L a)).reverse⟩ := by
  intro L
  induction L with
  | nil => intro val; simp [memToks, lookup_nil]
  | cons e L ih =>
    intro val
    obtain ⟨k, v⟩ := e
    simp only [memToks, List.flatMap_cons, List.foldl_append] at ih ⊢
    rw [scan_entry, scan_entry]
    refine ⟨by simp [(ih val).1], ?_⟩
    cases hka : k == a
    · simp only [Bool.or_false, Bool.false_and, Bool.false_eq_true, ite_false]
      rw [(ih []).2]
      have : k ≠ a := by simpa using hka
      simp [lookup_cons, this, hka]
    · simp only [Bool.or_true, Bool.and_true, Bool.not_false, ite_true, List.append_nil]
      rw [(ih _).1]
      have : k = a := by simpa using hka
      simp [lookup_cons, this]

/-! ### The scan on the registers -/

def setMis : Command K := .seq (.clear XM) (.push XM true)

/-- A bit of the address of an entry: compare it with the next key bit. -/
def keyBit (b : Bool) : Command K :=
  .branch XQ setMis (.seq (.pop XQ) (if b then setMis else skipC)) (.seq (.pop XQ) (if b then skipC else setMis))

/-- A bit of the value of an entry: keep it if the value is taken. -/
def valBit (b : Bool) : Command K := .branch XE skipC skipC (.push XV b)

/-- The end of the address of an entry. -/
def keyEnd : Command K :=
  .seq (.clear XE) (.seq (.branch XQ skipC setMis setMis) (.seq (.clear XQ) (.seq (.push XP true)
    (.branch XM (.branch XF (.push XE true) skipC skipC) skipC skipC))))

/-- The end of the value of an entry. -/
def valEnd : Command K :=
  .seq (.branch XE skipC skipC (.seq (.pop XE) (.seq (.clear XF) (.push XF true))))
    (.seq (.clear XP) (.seq (.clear XM) (.copy XK XQ XU)))

def termC : Command K := .branch XP keyEnd keyEnd valEnd
def bitC (b : Bool) : Command K := .branch XP (keyBit b) (keyBit b) (valBit b)

/-- One token of the memory code in `XW`. -/
def scanBody : Command K :=
  .branch XW skipC (.seq (.pop XW) termC)
    (.seq (.pop XW) (.branch XW skipC (.seq (.pop XW) (bitC false)) (.seq (.pop XW) (bitC true))))

/-- A register that the memory scan does not use. -/
abbrev ScanFree (i : Reg) : Prop :=
  i ≠ XK ∧ i ≠ XP ∧ i ≠ XM ∧ i ≠ XQ ∧ i ≠ XE ∧ i ≠ XF ∧ i ≠ XV ∧ i ≠ XW ∧ i ≠ XT

/-- The scan registers hold the scan state `st` for the key `KEY`. -/
def ScanRegs (KEY : List Bool) (st : ScanSt) (q : Regs) : Prop :=
  q XK = KEY ∧ q XP = flag st.phase ∧ q XM = flag st.mis ∧ q XQ = st.kc ∧ q XE = flag st.take ∧
    q XF = flag st.found ∧ q XV = st.val ∧ q XU = [] ∧ st.kc.length ≤ KEY.length

/-- ... and the registers agree with `r0` elsewhere. -/
def ScanAt (r0 : Regs) (KEY : List Bool) (st : ScanSt) (q : Regs) : Prop :=
  ScanRegs KEY st q ∧ ∀ i, ScanFree i → q i = r0 i

theorem ScanAt.set_other {r0 : Regs} {KEY : List Bool} {st : ScanSt} {q : Regs} (h : ScanAt r0 KEY st q)
    (j : Reg) (hj : j = XW ∨ j = XT) (w : List Bool) : ScanAt r0 KEY st (set q j w) := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, h10⟩ := h
  rcases hj with rfl | rfl <;>
  exact ⟨⟨by simp [h1], by simp [h2], by simp [h3], by simp [h4],
    by simp [h5], by simp [h6], by simp [h7], by simp [h8], h9⟩,
    fun i hi => by simp [hi.2.2.2.2.2.2.2.1, hi.2.2.2.2.2.2.2.2, h10 i hi]⟩

theorem ok_termC' {KEY : List Bool} {st : ScanSt} {q : Regs} (h : ScanRegs KEY st q) :
    ∃ q', Ok termC q q' (6 * KEY.length + 25) ∧ ScanRegs KEY (scanStep KEY st none) q' := by
  obtain ⟨phase, mis, kc, take, found, val⟩ := st
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  simp only at h2 h3 h4 h5 h6 h7 h9
  apply ok_of_evalP 0
  cases phase <;> cases mis <;> cases take <;> cases found <;> rcases kc with _ | ⟨_ | _, kc⟩ <;>
    simp +decide [eval, termC, keyEnd, valEnd, setMis, skipC, scanStep, ScanRegs, h1, h2, h3, h4, h5, h6,
      h7, h8] at h9 ⊢ <;> omega

theorem ok_bitC' (b : Bool) {KEY : List Bool} {st : ScanSt} {q : Regs} (h : ScanRegs KEY st q) :
    ∃ q', Ok (bitC b) q q' 12 ∧ ScanRegs KEY (scanStep KEY st (some b)) q' := by
  obtain ⟨phase, mis, kc, take, found, val⟩ := st
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  simp only at h2 h3 h4 h5 h6 h7 h9
  apply ok_of_evalP 0
  cases b <;> cases phase <;> cases mis <;> cases take <;> rcases kc with _ | ⟨_ | _, kc⟩ <;>
    simp +decide [eval, bitC, keyBit, valBit, setMis, skipC, scanStep, ScanRegs, h1, h2, h3, h4, h5, h6,
      h7, h8] at h9 ⊢ <;> omega

theorem termC_writes (i : Reg) (hi : ScanFree i) : writes termC i = false := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hi
  simp [writes, termC, keyEnd, valEnd, setMis, skipC, h2, h3, h4, h5, h6]

theorem bitC_writes (b : Bool) (i : Reg) (hi : ScanFree i) : writes (bitC b) i = false := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hi
  cases b <;> simp [writes, bitC, keyBit, valBit, setMis, skipC, h3, h4, h7]

theorem ok_termC {r0 : Regs} {KEY : List Bool} {st : ScanSt} {q : Regs} (h : ScanAt r0 KEY st q) :
    ∃ q', Ok termC q q' (6 * KEY.length + 25) ∧ ScanAt r0 KEY (scanStep KEY st none) q' ∧
      q' XW = q XW ∧ q' XT = q XT := by
  obtain ⟨q', hq, hr⟩ := ok_termC' h.1
  refine ⟨q', hq, ⟨hr, fun i hi => by rw [hq.frame i (termC_writes i hi), h.2 i hi]⟩,
    hq.frame XW (by simp [writes, termC, keyEnd, valEnd, setMis, skipC]),
    hq.frame XT (by simp [writes, termC, keyEnd, valEnd, setMis, skipC])⟩

theorem ok_bitC (b : Bool) {r0 : Regs} {KEY : List Bool} {st : ScanSt} {q : Regs} (h : ScanAt r0 KEY st q) :
    ∃ q', Ok (bitC b) q q' 12 ∧ ScanAt r0 KEY (scanStep KEY st (some b)) q' ∧ q' XW = q XW ∧ q' XT = q XT := by
  obtain ⟨q', hq, hr⟩ := ok_bitC' b h.1
  refine ⟨q', hq, ⟨hr, fun i hi => by rw [hq.frame i (bitC_writes b i hi), h.2 i hi]⟩,
    hq.frame XW (by cases b <;> simp [writes, bitC, keyBit, valBit, setMis, skipC]),
    hq.frame XT (by cases b <;> simp [writes, bitC, keyBit, valBit, setMis, skipC])⟩

/-- The scan loop on the remaining tokens. -/
def scanIter (KEY : List Bool) : List Tok × ScanSt → List Tok × ScanSt
  | ([], st) => ([], st)
  | (t :: ts, st) => (ts, scanStep KEY st t)

theorem iter_scanIter (KEY : List Bool) : ∀ (ts : List Tok) (st : ScanSt) (n : Nat), ts.length ≤ n →
    iter (scanIter KEY) n (ts, st) = ([], ts.foldl (scanStep KEY) st) := by
  intro ts
  induction ts with
  | nil =>
    intro st n _
    induction n with
    | zero => rfl
    | succ n ih => simp only [iter, scanIter]; exact ih (by simp)
  | cons t ts ih =>
    intro st n hn
    cases n with
    | zero => simp at hn
    | succ n => simp only [iter, scanIter, List.foldl_cons]; exact ih _ n (by simp at hn; omega)

theorem ok_scanBody {r0 : Regs} {KEY : List Bool} (s : List Tok × ScanSt) (q : Regs)
    (h : q XW = s.1.flatMap tokEnc ∧ ScanAt r0 KEY s.2 q) :
    ∃ q', Ok scanBody q q' (6 * KEY.length + 32) ∧
      (q' XW = (scanIter KEY s).1.flatMap tokEnc ∧ ScanAt r0 KEY (scanIter KEY s).2 q') := by
  obtain ⟨ts, st⟩ := s
  obtain ⟨hW, hS⟩ := h
  cases ts with
  | nil =>
    exact ⟨q, (Ok.branch_nil hW (ok_skip q)).mono (by omega), hW, hS⟩
  | cons t ts =>
    cases t with
    | none =>
      simp only [List.flatMap_cons, tokEnc, List.cons_append, List.nil_append] at hW
      obtain ⟨q', hq, hS', hW', -⟩ := ok_termC (hS.set_other XW (Or.inl rfl) (q XW).tail)
      refine ⟨q', (Ok.branch_false hW ((ok_pop XW q).seq hq)).mono (by omega), ?_, hS'⟩
      rw [hW']; simp [hW, scanIter]
    | some b =>
      simp only [List.flatMap_cons, tokEnc, List.cons_append, List.nil_append] at hW
      have hS1 := hS.set_other XW (Or.inl rfl) (q XW).tail
      have hS2 := hS1.set_other XW (Or.inl rfl) (set q XW (q XW).tail XW).tail
      obtain ⟨q', hq, hS', hW', -⟩ := ok_bitC b hS2
      have hW1 : set q XW (q XW).tail XW = b :: ts.flatMap tokEnc := by simp [hW]
      have hW2 : set (set q XW (q XW).tail) XW (set q XW (q XW).tail XW).tail XW = ts.flatMap tokEnc := by
        simp [hW]
      have inner := (ok_pop XW (set q XW (q XW).tail)).seq hq
      refine ⟨q', ?_, ?_, hS'⟩
      · cases b
        · exact (Ok.branch_true hW ((ok_pop XW q).seq (Ok.branch_false hW1 inner))).mono (by omega)
        · exact (Ok.branch_true hW ((ok_pop XW q).seq (Ok.branch_true hW1 inner))).mono (by omega)
      · rw [hW', hW2]; rfl

theorem scanBody_writes : writes scanBody XT = false := by
  simp [writes, scanBody, termC, bitC, keyEnd, valEnd, keyBit, valBit, setMis, skipC]

theorem length_le_flatMap_tokEnc (ts : List Tok) : ts.length ≤ (ts.flatMap tokEnc).length := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    cases t <;> simp only [List.flatMap_cons, List.length_append, List.length_cons, tokEnc, List.length_nil] <;> omega

/-! ### Loading -/

/-- All scratch registers (`4, …, 47`) are empty. -/
def Clean (q : Regs) : Prop := ∀ i : Reg, 4 ≤ i.val → i.val < 48 → q i = []

/-- A register outside the scratch registers. -/
abbrev Outer (i : Reg) : Prop := i.val < 4 ∨ 48 ≤ i.val

theorem Clean.at {q : Regs} (h : Clean q) (i : Reg) (h1 : 4 ≤ i.val := by decide) (h2 : i.val < 48 := by decide) :
    q i = [] := h i h1 h2

theorem Outer.ne {i : Reg} (h : Outer i) (j : Reg) (h1 : 4 ≤ j.val := by decide) (h2 : j.val < 48 := by decide) :
    i ≠ j := by
  intro e; subst e; rcases h with h | h <;> omega

def loadClean : Command K :=
  .seq (.clear XK) (.seq (.clear XQ) (.seq (.clear XP) (.seq (.clear XM) (.seq (.clear XE) (.clear XF)))))

/-- `d := mem[a]`. -/
def loadB (a d : Reg) : Command K :=
  .seq (.copy MEM XW XU) (.seq (.copy a XK XU) (.seq (.copy XK XQ XU) (.seq (.length XW XT XU)
    (.seq (.repeat XT scanBody) (.seq (.clear d) (.seq (revOnto XV d XT) loadClean))))))

theorem ok_loadB {a d : Reg} (ha : 48 ≤ a.val) (hd : 48 ≤ d.val) (q : Regs) (hc : Clean q)
    {L : List (Nat × Nat)} {x B : Nat} (hm : q MEM = encMem L) (hx : q a = bin x)
    (hxB : (bin x).length ≤ B) (hdB : (q d).length ≤ B) (hvB : (bin (lookup L x)).length ≤ B) :
    ∃ q', Ok (loadB a d) q q' (((encMem L).length + 1) * (24 * B + 60)) ∧ q' d = bin (lookup L x) ∧
      Clean q' ∧ ∀ i, Outer i → i ≠ d → q' i = q i := by
  have ao : Outer a := Or.inr ha
  have dO : Outer d := Or.inr hd
  have s1 := ok_copy (s := MEM) (d := XW) (t := XU) (by decide) (by decide) (by decide) q (hc.at XU)
  have s2 := ok_copy (s := a) (d := XK) (t := XU) (ao.ne XK) (ao.ne XU) (by decide) (set q XW (q MEM))
    (by simp [hc.at XU])
  have s3 := ok_copy (s := XK) (d := XQ) (t := XU) (by decide) (by decide) (by decide)
    (set (set q XW (q MEM)) XK (set q XW (q MEM) a)) (by simp [set_apply, hc.at XU])
  have s4 := ok_length (s := XW) (d := XT) (t := XU) (by decide) (by decide) (by decide)
    (set (set (set q XW (q MEM)) XK (set q XW (q MEM) a)) XQ (set (set q XW (q MEM)) XK (set q XW (q MEM) a) XK))
    (by simp [set_apply, hc.at XU])
  generalize hq4 : set (set (set (set q XW (q MEM)) XK (set q XW (q MEM) a)) XQ
    (set (set q XW (q MEM)) XK (set q XW (q MEM) a) XK)) XT (List.replicate (set (set (set q XW (q MEM)) XK
    (set q XW (q MEM) a)) XQ (set (set q XW (q MEM)) XK (set q XW (q MEM) a) XK) XW).length true) = q4 at s4
  have a1 : set q XW (q MEM) a = q a := by simp [ao.ne XW]
  have q4W : q4 XW = encMem L := by rw [← hq4]; simp [set_apply, hm]
  have q4T : (q4 XT).length = (encMem L).length := by rw [← hq4]; simp [set_apply, hm]
  have q4f : ∀ i, Outer i → q4 i = q i := by
    intro i hi
    rw [← hq4]; simp [set_apply, hi.ne XW, hi.ne XK, hi.ne XQ, hi.ne XT]
  have hS4 : ScanAt q4 (bin x) ⟨false, false, bin x, false, false, []⟩ q4 := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Nat.le_refl _⟩, fun _ _ => rfl⟩ <;> rw [← hq4] <;>
      simp [hx, ao.ne XW, hc.at XP, hc.at XM, hc.at XE, hc.at XF, hc.at XV, hc.at XU]
  obtain ⟨q5, s5, hE5, q5T⟩ := ok_repeat scanBody_writes
    (fun (s : List Tok × ScanSt) (p : Regs) => p XW = s.1.flatMap tokEnc ∧ ScanAt q4 (bin x) s.2 p)
    (scanIter (bin x)) (6 * (bin x).length + 32)
    (fun s p w h => ⟨by simp [h.1], h.2.set_other XT (Or.inr rfl) w⟩)
    (fun s p h => ok_scanBody s p h) _ (memToks L, ⟨false, false, bin x, false, false, []⟩) q4 ⟨q4W, hS4⟩ q4T
  rw [iter_scanIter (bin x) (memToks L) _ (encMem L).length (length_le_flatMap_tokEnc _), (scan_mem x L []).2] at hE5
  obtain ⟨q5W, ⟨q5K, q5P, q5M, q5Q, q5E, q5F, q5V, q5U, -⟩, q5f⟩ := hE5
  simp only at q5W q5K q5P q5M q5Q q5E q5F q5V
  have s6 := ok_clear d q5
  obtain ⟨q7, s7, q7V, q7d, q7T, q7f⟩ := ok_revOnto (src := XV) (dst := d) (ct := XT) (Ne.symm (dO.ne XV))
    (by decide) (dO.ne XT) (by decide) (dO.ne XU) (by decide) (set q5 d []) (by simp [set_apply, q5U])
  have s8 : Ok loadClean q7 (set (set (set (set (set (set q7 XK []) XQ []) XP []) XM []) XE []) XF [])
      ((q7 XK).length + (q7 XQ).length + (q7 XP).length + (q7 XM).length + (q7 XE).length + (q7 XF).length + 12) :=
    ((ok_clear XK _).seq ((ok_clear XQ _).seq ((ok_clear XP _).seq ((ok_clear XM _).seq ((ok_clear XE _).seq
      (ok_clear XF _)))))).mono (by simp []; omega)
  have q7o : ∀ i, i ≠ XV → i ≠ d → i ≠ XT → q7 i = q5 i := by
    intro i h1 h2 h3; rw [q7f i h1 h2 h3]; simp [h2]
  have q5fr : ∀ i, Outer i → q5 i = q i := fun i hi => by
    rw [q5f i ⟨hi.ne XK, hi.ne XP, hi.ne XM, hi.ne XQ, hi.ne XE, hi.ne XF, hi.ne XV, hi.ne XW, hi.ne XT⟩, q4f i hi]
  have b1 := s1.mono (b' := 5 * (encMem L).length + 6) (by simp [hc.at XW, hm])
  have b2 := s2.mono (b' := 5 * (bin x).length + 6) (by simp [hc.at XK, ao.ne XW, hx])
  have b3 := s3.mono (b' := 5 * (bin x).length + 6) (by simp [hc.at XQ, ao.ne XW, hx])
  have b4 := s4.mono (b' := 5 * (encMem L).length + 6) (by simp [set_apply, hc.at XT, hm])
  have b6 := s6.mono (b' := (q d).length + 2) (by rw [q5fr d dO]; exact Nat.le_refl _)
  have b7 := s7.mono (b' := 11 * (bin (lookup L x)).length + 8)
    (by simp [(dO.ne XT).symm, (dO.ne XV).symm, q5T, q5V])
  have b8 := s8.mono (b' := 2 * (bin x).length + 13) (by
    rw [q7o XK (by decide) (dO.ne XK).symm (by decide), q7o XQ (by decide) (dO.ne XQ).symm (by decide),
      q7o XP (by decide) (dO.ne XP).symm (by decide), q7o XM (by decide) (dO.ne XM).symm (by decide),
      q7o XE (by decide) (dO.ne XE).symm (by decide), q7o XF (by decide) (dO.ne XF).symm (by decide),
      q5K, q5Q, q5P, q5M, q5E, q5F]
    cases L.any (fun e => e.1 == x) <;> simp <;> omega)
  refine ⟨_, (b1.seq (b2.seq (b3.seq (b4.seq (s5.seq (b6.seq (b7.seq b8))))))).mono ?_, ?_, ?_, ?_⟩
  · have hW : ((encMem L).length + 1) * (24 * B + 60) = (encMem L).length * (24 * B + 60) + (24 * B + 60) := by
      rw [Nat.add_mul, Nat.one_mul]
    have hW2 : (encMem L).length * (6 * (bin x).length + 32 + 1) + 12 * (encMem L).length ≤
        (encMem L).length * (24 * B + 60) := by
      have h := Nat.mul_le_mul_left (encMem L).length (show 6 * (bin x).length + 32 + 1 + 12 ≤ 24 * B + 60 by omega)
      rw [Nat.mul_add (encMem L).length (6 * (bin x).length + 32 + 1) 12] at h; omega
    omega
  · simp [(dO.ne XF), (dO.ne XE), (dO.ne XM), (dO.ne XP), (dO.ne XQ), (dO.ne XK), q7d, q5V,
      (dO.ne XV).symm]
  · intro i h1 h2
    by_cases hi : i = XK ∨ i = XQ ∨ i = XP ∨ i = XM ∨ i = XE ∨ i = XF
    · rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp []
    · simp only [not_or] at hi
      simp only [set_apply, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2, ite_false]
      by_cases hv : i = XV
      · subst hv; exact q7V
      · by_cases ht : i = XT
        · subst ht; exact q7T
        · have hid : i ≠ d := fun e => by subst e; omega
          rw [q7o i hv hid ht]
          by_cases hw : i = XW
          · subst hw; simp [q5W]
          · by_cases hu : i = XU
            · subst hu; exact q5U
            · rw [q5f i ⟨hi.1, hi.2.2.1, hi.2.2.2.1, hi.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2, hv, hw, ht⟩, ← hq4]
              simp [set_apply, hi.1, hi.2.1, hw, ht, hc i h1 h2]
  · intro i hi hid
    simp only [set_apply, hi.ne XK, hi.ne XQ, hi.ne XP, hi.ne XM, hi.ne XE, hi.ne XF, ite_false]
    rw [q7o i (hi.ne XV) hid (hi.ne XT), q5fr i hi]

/-! ### Storing -/

/-- The code of a numeral. -/
def encNum (bs : List Bool) : List Bool := bs.flatMap (fun b => [true, b]) ++ [false]

theorem encMem_cons (k v : Nat) (L : List (Nat × Nat)) :
    encMem ((k, v) :: L) = encNum (bin k) ++ encNum (bin v) ++ encMem L := by
  have h : ∀ bs : List Bool, (bs.map some).flatMap tokEnc = bs.flatMap (fun b => [true, b]) := by
    intro bs; induction bs with
    | nil => rfl
    | cons b bs ih => simp only [List.map_cons, List.flatMap_cons, ih]; rfl
  simp only [encMem, memToks, List.flatMap_cons, entryToks, List.flatMap_append, h, encNum]
  simp [tokEnc]

/-- Prepend the code of one bit of `XB` (taken from the top) to `MEM`. -/
def encBit : Command K :=
  .branch XB skipC (.seq (.pop XB) (.seq (.push MEM false) (.push MEM true)))
    (.seq (.pop XB) (.seq (.push MEM true) (.push MEM true)))

def encStep : List Bool × List Bool → List Bool × List Bool
  | ([], m) => ([], m)
  | (b :: xs, m) => (xs, true :: b :: m)

theorem iter_encStep : ∀ (xs m : List Bool) (n : Nat), xs.length ≤ n →
    iter encStep n (xs, m) = ([], xs.reverse.flatMap (fun b => [true, b]) ++ m) := by
  intro xs
  induction xs with
  | nil =>
    intro m n _
    induction n with
    | zero => rfl
    | succ n ih => simp only [iter, encStep]; exact ih (by simp)
  | cons b xs ih =>
    intro m n hn
    cases n with
    | zero => simp at hn
    | succ n =>
      simp only [iter, encStep]; rw [ih _ n (by simp at hn; omega)]
      simp [List.flatMap_append]

theorem ok_encBit (q : Regs) :
    ∃ q', Ok encBit q q' 7 ∧ (q' XB, q' MEM) = encStep (q XB, q MEM) ∧ ∀ i, i ≠ XB → i ≠ MEM → q' i = q i := by
  apply ok_of_evalP 0
  cases hs : q XB with
  | nil => simp [eval, encBit, skipC, hs, encStep]
  | cons b s =>
    cases b <;> simp [eval, encBit, skipC, hs, encStep, set_apply] <;> intro i h1 h2 <;> simp [h1, h2]

/-- Prepend the code of the numeral in `r` to `MEM`. -/
def pushEnc (r : Reg) : Command K :=
  .seq (.copy r XA XU) (.seq (revOnto XA XB XT) (.seq (.push MEM false) (.seq (.length XB XT XU)
    (.repeat XT encBit))))

theorem ok_pushEnc {r : Reg} (hr : 48 ≤ r.val) (q : Regs) (hc : Clean q) :
    ∃ q', Ok (pushEnc r) q q' (30 * (q r).length + 30) ∧ q' MEM = encNum (q r) ++ q MEM ∧ Clean q' ∧
      ∀ i, Outer i → i ≠ MEM → q' i = q i := by
  have ro : Outer r := Or.inr hr
  have s1 := ok_copy (s := r) (d := XA) (t := XU) (ro.ne XA) (ro.ne XU) (by decide) q (hc.at XU)
  obtain ⟨q2, s2, a2, b2, t2, f2⟩ := ok_revOnto (src := XA) (dst := XB) (ct := XT) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (set q XA (q r)) (by simp [hc.at XU])
  have s3 := ok_push MEM false q2
  have s4 := ok_length (s := XB) (d := XT) (t := XU) (by decide) (by decide) (by decide) (set q2 MEM (false :: q2 MEM))
    (by simp [f2 XU (by decide) (by decide) (by decide), hc.at XU])
  have hw : writes encBit XT = false := by simp [writes, encBit, skipC]
  generalize hq4 : set (set q2 MEM (false :: q2 MEM)) XT
    (List.replicate ((set q2 MEM (false :: q2 MEM)) XB).length true) = q4 at s4
  have hB2 : q2 XB = (q r).reverse := by rw [b2]; simp [hc.at XB]
  obtain ⟨q5, s5, hE5, t5⟩ := ok_repeat hw (fun (st : List Bool × List Bool) (p : Regs) =>
      p XB = st.1 ∧ p MEM = st.2 ∧ ∀ i, i ≠ XB → i ≠ MEM → i ≠ XT → p i = q4 i) encStep 7
    (fun st p w h => ⟨by simp [h.1], by simp [h.2.1],
      fun i i1 i2 i3 => by simp [i3, h.2.2 i i1 i2 i3]⟩)
    (fun ⟨s1', s2'⟩ p h => by
      obtain ⟨p', hp, hst, hfr⟩ := ok_encBit p
      rw [h.1, h.2.1] at hst
      exact ⟨p', hp, congrArg Prod.fst hst, congrArg Prod.snd hst, fun i i1 i2 i3 => by
        rw [hfr i i1 i2, h.2.2 i i1 i2 i3]⟩)
    _ (q4 XB, q4 MEM) q4 ⟨rfl, rfl, fun _ _ _ _ => rfl⟩ rfl
  have q4B : q4 XB = (q r).reverse := by rw [← hq4]; simp [hB2]
  have q4M : q4 MEM = false :: q MEM := by
    rw [← hq4]; simp [f2 MEM (by decide) (by decide) (by decide)]
  have q4T : (q4 XT).length = (q r).length := by rw [← hq4]; simp [hB2]
  rw [q4T, q4B, q4M, iter_encStep _ _ _ (by simp)] at hE5
  obtain ⟨b5, m5, f5⟩ := hE5
  simp only at b5 m5
  refine ⟨q5, (s1.seq (s2.seq (s3.seq (s4.seq s5)))).mono ?_, ?_, ?_, ?_⟩
  · simp [hc.at XA, hc.at XT, hB2, t2]; rw [q4T]; omega
  · rw [m5]; simp [encNum]
  · intro i h1 h2
    by_cases hb : i = XB
    · subst hb; exact b5
    · by_cases ht : i = XT
      · subst ht; exact t5
      · have hm : i ≠ MEM := fun e => by subst e; simp at h1
        rw [f5 i hb hm ht, ← hq4]
        simp only [set_apply, ht, hm, ite_false]
        by_cases ha : i = XA
        · subst ha; exact a2
        · rw [f2 i ha hb ht]; simp [ha, hc i h1 h2]
  · intro i hi hm
    rw [f5 i (hi.ne XB) hm (hi.ne XT), ← hq4]
    simp only [set_apply, hi.ne XT, hm, ite_false]
    rw [f2 i (hi.ne XA) (hi.ne XB) (hi.ne XT)]; simp [hi.ne XA]

/-- Add the entry `(a, b)` in front of the memory. -/
def storeB (a b : Reg) : Command K := .seq (pushEnc b) (pushEnc a)

theorem ok_storeB {a b : Reg} (ha : 48 ≤ a.val) (hb : 48 ≤ b.val) (q : Regs) (hc : Clean q)
    {L : List (Nat × Nat)} {x y : Nat} (hm : q MEM = encMem L) (hx : q a = bin x) (hy : q b = bin y) :
    ∃ q', Ok (storeB a b) q q' (30 * (bin x).length + 30 * (bin y).length + 60) ∧ q' MEM = encMem ((x, y) :: L) ∧
      Clean q' ∧ ∀ i, Outer i → i ≠ MEM → q' i = q i := by
  obtain ⟨q1, s1, m1, c1, f1⟩ := ok_pushEnc hb q hc
  obtain ⟨q2, s2, m2, c2, f2⟩ := ok_pushEnc ha q1 c1
  have ha1 : q1 a = bin x := by rw [f1 a (Or.inr ha) (fun e => by subst e; simp at ha), hx]
  refine ⟨q2, (s1.seq s2).mono (by rw [hy, ha1]; omega), ?_, c2, fun i hi hm => by rw [f2 i hi hm, f1 i hi hm]⟩
  rw [m2, m1, ha1, hy, hm, encMem_cons, List.append_assoc]

end STACS2027.Sim
