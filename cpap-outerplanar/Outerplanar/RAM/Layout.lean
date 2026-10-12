module

public import Outerplanar.RAM.Frame
public import NPHardness.FiniteCycles
public import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/-!
# Conventions of the linear-time RAM: registers, memory predicates, the input

## Registers
* `rZERO = 0` is never written, so it stays `0`;
* `rONE = 1` holds `1` once the first instruction of the program has run;
* `rFREE = 2` holds the first free memory address (bump allocation);
* `rT = 3` is the **macro temporary**: every macro of `Lib.lean` may clobber it, and no
  assertion that has to survive a macro may mention it; registers `4`–`9` are reserved;
* `10`–`99` are **global registers** carrying data between phases. Each phase owns a block:
  R0 `10`–`19`, R1 (DFS) `20`–`29`, R2 (low/head) `30`–`39`, R3 (blocks) `40`–`49`,
  R4 (per block) `50`–`99`. The R0 names are fixed; the names given for R1–R3 are suggestions
  (a phase may name further globals of its block by `abbrev`s in its own file);
* registers `≥ 100` are **scratch**: any phase may clobber them.

## Memory
* `Arr m b l`: the list `l` is stored at `b, b + 1, …`;
* `Tab m b n f`: the function `f` is stored on `[b, b + n)` (`m (b + i) = f i` for `i < n`);
* `ZeroFrom m F`: all cells at or above `F` are `0` — the invariant `ZeroFrom c.mem
  (c.reg rFREE)` makes freshly allocated arrays zero;
* `SameOn S m m'`: `m'` agrees with `m` on the cells satisfying `S` (memory frames of
  programs that store).

All memory predicates take the memory `c.mem : ℕ → ℕ`, not the configuration, so that they
are unaffected by register writes (`(c.setReg d v).mem = c.mem` is a simp lemma). The memory
after a store is `upd c.mem a v` (simp lemma `setMem_mem_upd`), and the update lemmas
(`Arr.upd_of_disjoint`, `Arr.upd_set`, `Arr.push`, `Tab.upd_of_disjoint`, `Tab.upd`,
`ZeroFrom.upd`, `SameOn.upd`) are stated for `upd`.

Matrices: cell `(u, v)` of an `N × N` matrix is at offset `u * N + v` (`cell_lt`, `cell_div`,
`cell_mod`, `cell_inj`).

## The input
`graphInput g = g.length :: g.flatMap fun e => [e.1, e.2]`; the machine starts in
`initial (graphInput g)`: `Arr (initial l).mem 0 l` and `ZeroFrom (initial l).mem l.length`.
-/

@[expose] public section

namespace STACS2027.RAM

/-! ### Registers -/

/-- Register `0`: never written, it stays `0`. -/
abbrev rZERO : ℕ := 0
/-- Holds `1` (set by the first instruction of the program). -/
abbrev rONE : ℕ := 1
/-- The first free memory address: every cell at or above it is `0`. -/
abbrev rFREE : ℕ := 2
/-- The macro temporary, clobbered by every macro of `Lib.lean`. -/
abbrev rT : ℕ := 3

/-- Global registers of phase R0 (parsing). -/
abbrev gM : ℕ := 10
/-- R0: the largest label `M` of the input. -/
abbrev gMX : ℕ := 11
/-- R0: the base `D = 2m + 1` of the label dictionary (`mem[D + x] = idOf x + 1`). -/
abbrev gD : ℕ := 12
/-- R0: the number of vertices `numV g`. -/
abbrev gN : ℕ := 13
/-- R0: the number of id edges `(idEdges g).length`. -/
abbrev gNE : ℕ := 14
/-- R0: the base of the label array `labels g`. -/
abbrev gLB : ℕ := 15
/-- R0: the base of the array of first ends of the id edges. -/
abbrev gEU : ℕ := 16
/-- R0: the base of the array of second ends of the id edges. -/
abbrev gEV : ℕ := 17
/-- A global register of the R0 block, not written by R0 since R0 has no adjacency matrix (it
held the row starts `u ↦ u * N`). -/
abbrev gROW : ℕ := 18
/-- A global register of the R0 block, not written by R0 since R0 has no adjacency matrix (it
held the base of the `N × N` matrix). -/
abbrev gMAT : ℕ := 19

/-- The first global register of phase R1 (DFS); its block is `20`–`29`. -/
abbrev gR1 : ℕ := 20
/-- R1 (suggested): base of the CSR offsets (`N + 1` cells; the neighbours of `v` are at
`[OFF[v], OFF[v + 1])` of the CSR array). -/
abbrev gOFF : ℕ := 20
/-- R1 (suggested): base of the CSR neighbour array (`nbOf (idEdges g) v`, concatenated). -/
abbrev gADJ : ℕ := 21
/-- R1 (suggested): base of the preorder numbers `DFS.State.pre` (`0` = unvisited). -/
abbrev gPRE : ℕ := 22
/-- R1 (suggested): base of the parents `DFS.State.par`. -/
abbrev gPAR : ℕ := 23
/-- R1 (suggested): base of the neighbour pointers `DFS.State.ptr`. -/
abbrev gPTR : ℕ := 24
/-- R1 (suggested): base of the vertices in preorder `DFS.State.ord`. -/
abbrev gORD : ℕ := 25
/-- R1 (suggested): base of the DFS stack. -/
abbrev gSTK : ℕ := 26
/-- R1 (suggested): the size of the DFS stack. -/
abbrev gSP : ℕ := 27
/-- R1 (suggested): the visit counter `DFS.State.cnt`. -/
abbrev gCNT : ℕ := 28
/-- R1: spare global. -/
abbrev gR1x : ℕ := 29

/-- The first global register of phase R2 (low points, heads); its block is `30`–`39`. -/
abbrev gR2 : ℕ := 30
/-- R2 (suggested): base of the low points `lowOf` (indexed by vertex). -/
abbrev gLOW : ℕ := 30
/-- R2 (suggested): base of the heads `headOf` (indexed by vertex). -/
abbrev gHEAD : ℕ := 31

/-- The first global register of phase R3 (blocks); its block is `40`–`49`. -/
abbrev gR3 : ℕ := 40
/-- R3 (suggested): base of the bucket starts (`N + 1` cells, bucket `h` at
`[BST[h], BST[h + 1])`). -/
abbrev gBST : ℕ := 40
/-- R3 (suggested): base of the first ends of the bucketed edges. -/
abbrev gBU : ℕ := 41
/-- R3 (suggested): base of the second ends of the bucketed edges. -/
abbrev gBV : ℕ := 42

/-- The first global register of phase R4 (per block); its block is `50`–`99`, named by the R4
phases as `gR4 + k`. -/
abbrev gR4 : ℕ := 50
/-- The first scratch register; registers `≥ rS` may be clobbered by any phase. -/
abbrev rS : ℕ := 100

/-! ### Memory predicates -/

/-- The list `l` is stored at `b, b + 1, …, b + l.length - 1`. -/
def Arr (m : ℕ → ℕ) (b : ℕ) (l : List ℕ) : Prop := ∀ i (h : i < l.length), m (b + i) = l[i]

/-- The function `f` is stored on `[b, b + n)`. -/
def Tab (m : ℕ → ℕ) (b n : ℕ) (f : ℕ → ℕ) : Prop := ∀ i, i < n → m (b + i) = f i

/-- All cells at or above `F` are zero. -/
def ZeroFrom (m : ℕ → ℕ) (F : ℕ) : Prop := ∀ a, F ≤ a → m a = 0

/-- `m'` agrees with `m` on the cells satisfying `S`. -/
def SameOn (S : ℕ → Prop) (m m' : ℕ → ℕ) : Prop := ∀ a, S a → m' a = m a

/-- The memory `m` with the cell `a` set to `v`: the memory after a `store`
(`(c.setMem a v).mem = upd c.mem a v` is a simp lemma, so that the memory after several
stores is the plain term `upd (upd c.mem a₁ v₁) a₂ v₂`). -/
def upd (m : ℕ → ℕ) (a v : ℕ) : ℕ → ℕ := fun i => if i = a then v else m i

@[simp] theorem upd_apply (m : ℕ → ℕ) (a v i : ℕ) : upd m a v i = if i = a then v else m i := rfl
@[simp] theorem setMem_mem_upd (c : Config) (a v : ℕ) : (c.setMem a v).mem = upd c.mem a v := rfl
theorem upd_same (m : ℕ → ℕ) (a v : ℕ) : upd m a v a = v := by simp
theorem upd_ne (m : ℕ → ℕ) {a i : ℕ} (v : ℕ) (h : i ≠ a) : upd m a v i = m i := by simp [h]

theorem getD_eq_getElem' {l : List ℕ} {i : ℕ} (hi : i < l.length) : l.getD i 0 = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-! #### `Arr` -/

namespace Arr

variable {m m' : ℕ → ℕ} {b : ℕ} {l : List ℕ}

theorem get (h : Arr m b l) {i : ℕ} (hi : i < l.length) : m (b + i) = l[i] := h i hi

theorem getD (h : Arr m b l) {i : ℕ} (hi : i < l.length) : m (b + i) = l.getD i 0 := by
  rw [h i hi, getD_eq_getElem' hi]

/-- Reading at an address given as `a = b + i`. -/
theorem get' (h : Arr m b l) {i a : ℕ} (hi : i < l.length) (ha : a = b + i) : m a = l[i] := by
  rw [ha]; exact h i hi

theorem congr (h : Arr m b l) (h' : ∀ i, i < l.length → m' (b + i) = m (b + i)) : Arr m' b l :=
  fun i hi => (h' i hi).trans (h i hi)

theorem of_sameOn {S : ℕ → Prop} (h : Arr m b l) (hS : SameOn S m m')
    (hb : ∀ i, i < l.length → S (b + i)) : Arr m' b l :=
  h.congr fun i hi => hS _ (hb i hi)

/-- Two lists stored at the same place with the same length are equal. -/
theorem ext {l' : List ℕ} (h : Arr m b l) (h' : Arr m b l') (hl : l.length = l'.length) : l = l' :=
  List.ext_getElem hl fun i hi hi' => (h i hi).symm.trans (h' i hi')

end Arr

@[simp] theorem arr_nil (m : ℕ → ℕ) (b : ℕ) : Arr m b [] := fun _ h => absurd h (Nat.not_lt_zero _)

theorem arr_cons {m : ℕ → ℕ} {b x : ℕ} {l : List ℕ} : Arr m b (x :: l) ↔ m b = x ∧ Arr m (b + 1) l := by
  constructor
  · intro h
    have h0 := h 0 (by simp)
    refine ⟨by simpa using h0, fun i hi => ?_⟩
    have := h (i + 1) (by simp; omega)
    rw [show b + 1 + i = b + (i + 1) by omega, this]; simp
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => simpa using h0
    | succ i =>
      rw [show b + (i + 1) = b + 1 + i by omega, h i (by simp at hi; omega)]; simp

theorem arr_append {m : ℕ → ℕ} {b : ℕ} {l₁ l₂ : List ℕ} :
    Arr m b (l₁ ++ l₂) ↔ Arr m b l₁ ∧ Arr m (b + l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [h i (by simp; omega), List.getElem_append_left hi]
    · rw [show b + l₁.length + i = b + (l₁.length + i) by omega, h _ (by simp; omega),
        List.getElem_append_right (by omega)]
      simp
  · rintro ⟨h₁, h₂⟩ i hi
    by_cases hi' : i < l₁.length
    · rw [h₁ i hi', List.getElem_append_left hi']
    · have := h₂ (i - l₁.length) (by simp at hi; omega)
      rw [show b + l₁.length + (i - l₁.length) = b + i by omega] at this
      rw [this, List.getElem_append_right (by omega)]

@[simp] theorem arr_singleton {m : ℕ → ℕ} {b x : ℕ} : Arr m b [x] ↔ m b = x := by
  simp [arr_cons]

theorem arr_replicate {m : ℕ → ℕ} {b n v : ℕ} : Arr m b (List.replicate n v) ↔ ∀ i, i < n → m (b + i) = v := by
  constructor
  · intro h i hi; rw [h i (by simpa using hi)]; simp
  · intro h i hi; rw [h i (by simpa using hi)]; simp

/-- An array as a table. -/
theorem arr_iff_tab {m : ℕ → ℕ} {b : ℕ} {l : List ℕ} : Arr m b l ↔ Tab m b l.length (fun i => l.getD i 0) := by
  constructor
  · intro h i hi; exact h.getD hi
  · intro h i hi; exact (h i hi).trans (getD_eq_getElem' hi)

/-- Storing outside an array keeps it. -/
theorem Arr.upd_of_disjoint {m : ℕ → ℕ} {b a v : ℕ} {l : List ℕ} (h : Arr m b l)
    (ha : a < b ∨ b + l.length ≤ a) : Arr (upd m a v) b l :=
  fun i hi => by
    have hne : b + i ≠ a := by omega
    simp only [upd_apply, hne, ↓reduceIte]; exact h i hi

/-- Storing into an array updates it by `List.set`. -/
theorem Arr.upd_set {m : ℕ → ℕ} {b a i v : ℕ} {l : List ℕ} (h : Arr m b l) (ha : a = b + i) :
    Arr (upd m a v) b (l.set i v) := by
  intro j hj
  simp only [List.length_set] at hj
  rw [List.getElem_set]
  by_cases hij : i = j
  · subst hij; simp [ha]
  · have hne : b + j ≠ a := by omega
    simp only [upd_apply, hne, ↓reduceIte, hij]; exact h j hj

/-- Appending to a growing array: `l` followed by `k + 1` zeros becomes `l ++ [x]` followed by
`k` zeros. -/
theorem Arr.push {m : ℕ → ℕ} {b a x k : ℕ} {l : List ℕ} (h : Arr m b (l ++ List.replicate (k + 1) 0))
    (ha : a = b + l.length) : Arr (upd m a x) b ((l ++ [x]) ++ List.replicate k 0) := by
  have := h.upd_set (i := l.length) (v := x) (by omega)
  rw [List.set_append_right _ _ le_rfl, Nat.sub_self, List.replicate_succ, List.set_cons_zero] at this
  simpa using this

/-- Appending to an array (a stack push): store at the end. -/
theorem Arr.upd_snoc {m : ℕ → ℕ} {b a x : ℕ} {l : List ℕ} (h : Arr m b l) (ha : a = b + l.length) :
    Arr (upd m a x) b (l ++ [x]) :=
  arr_append.mpr ⟨h.upd_of_disjoint (by omega), by simp [ha]⟩

/-- Extending an array by a cell already holding the value. -/
theorem Arr.snoc {m : ℕ → ℕ} {b x : ℕ} {l : List ℕ} (h : Arr m b l) (hx : m (b + l.length) = x) :
    Arr m b (l ++ [x]) := arr_append.mpr ⟨h, by simpa using hx⟩

theorem Arr.take {m : ℕ → ℕ} {b : ℕ} {l : List ℕ} (h : Arr m b l) (k : ℕ) : Arr m b (l.take k) :=
  fun i hi => by
    simp only [List.length_take] at hi
    rw [List.getElem_take]; exact h i (by omega)

/-- The first `k` entries of a growing array (prefix form). -/
theorem Arr.prefix {m : ℕ → ℕ} {b : ℕ} {l₁ l₂ : List ℕ} (h : Arr m b (l₁ ++ l₂)) : Arr m b l₁ :=
  (arr_append.mp h).1

/-! #### `Tab` -/

namespace Tab

variable {m m' : ℕ → ℕ} {b n : ℕ} {f g : ℕ → ℕ}

theorem get (h : Tab m b n f) {i : ℕ} (hi : i < n) : m (b + i) = f i := h i hi

theorem get' (h : Tab m b n f) {i a : ℕ} (hi : i < n) (ha : a = b + i) : m a = f i := by
  rw [ha]; exact h i hi

theorem mono (h : Tab m b n f) {n' : ℕ} (hn : n' ≤ n) : Tab m b n' f := fun i _ => h i (by omega)

theorem congr_fun (h : Tab m b n f) (hfg : ∀ i, i < n → f i = g i) : Tab m b n g :=
  fun i hi => (h i hi).trans (hfg i hi)

theorem congr (h : Tab m b n f) (h' : ∀ i, i < n → m' (b + i) = m (b + i)) : Tab m' b n f :=
  fun i hi => (h' i hi).trans (h i hi)

theorem of_sameOn {S : ℕ → Prop} (h : Tab m b n f) (hS : SameOn S m m')
    (hb : ∀ i, i < n → S (b + i)) : Tab m' b n f :=
  h.congr fun i hi => hS _ (hb i hi)

/-- Extending a table by one cell. -/
theorem snoc (h : Tab m b n f) (hn : m (b + n) = f n) : Tab m b (n + 1) f := fun i hi => by
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · exact h i hi
  · exact hn

/-- Two tables stored at the same place agree. -/
theorem ext (h : Tab m b n f) (h' : Tab m b n g) {i : ℕ} (hi : i < n) : f i = g i :=
  (h i hi).symm.trans (h' i hi)

theorem toArr (h : Tab m b n f) : Arr m b ((List.range n).map f) := fun i hi => by
  simp only [List.length_map, List.length_range] at hi
  simp [h i hi]

end Tab

@[simp] theorem tab_zero (m : ℕ → ℕ) (b : ℕ) (f : ℕ → ℕ) : Tab m b 0 f := fun _ h => absurd h (Nat.not_lt_zero _)

/-- Storing outside a table keeps it. -/
theorem Tab.upd_of_disjoint {m : ℕ → ℕ} {b n a v : ℕ} {f : ℕ → ℕ} (h : Tab m b n f)
    (ha : a < b ∨ b + n ≤ a) : Tab (upd m a v) b n f :=
  fun i hi => by
    have hne : b + i ≠ a := by omega
    simp only [upd_apply, hne, ↓reduceIte]; exact h i hi

/-- Storing into a table updates it by `Function.update`. -/
theorem Tab.upd {m : ℕ → ℕ} {b n a i v : ℕ} {f : ℕ → ℕ} (h : Tab m b n f) (ha : a = b + i) :
    Tab (RAM.upd m a v) b n (Function.update f i v) := by
  intro j hj
  by_cases hij : j = i
  · subst hij; simp [ha]
  · have hne : b + j ≠ a := by omega
    simp only [upd_apply, hne, ↓reduceIte, Function.update_of_ne hij]; exact h j hj

/-! #### `ZeroFrom` -/

namespace ZeroFrom

variable {m : ℕ → ℕ} {F : ℕ}

theorem get (h : ZeroFrom m F) {a : ℕ} (ha : F ≤ a) : m a = 0 := h a ha

theorem mono (h : ZeroFrom m F) {F' : ℕ} (hF : F ≤ F') : ZeroFrom m F' := fun a ha => h a (by omega)

/-- A fresh region is all zeros. -/
theorem arr (h : ZeroFrom m F) {b : ℕ} (hb : F ≤ b) (n : ℕ) : Arr m b (List.replicate n 0) :=
  arr_replicate.mpr fun _ _ => h _ (by omega)

/-- A fresh region is the zero table. -/
theorem tab (h : ZeroFrom m F) {b : ℕ} (hb : F ≤ b) (n : ℕ) : Tab m b n (fun _ => 0) :=
  fun _ _ => h _ (by omega)

theorem upd {a v : ℕ} (h : ZeroFrom m F) (ha : a < F) : ZeroFrom (RAM.upd m a v) F := fun x hx => by
  have hne : x ≠ a := by omega
  simp only [upd_apply, hne, ↓reduceIte]; exact h x hx

theorem of_sameOn {S : ℕ → Prop} {m' : ℕ → ℕ} (h : ZeroFrom m F) (hS : SameOn S m m')
    (hF : ∀ a, F ≤ a → S a) : ZeroFrom m' F := fun a ha => (hS a (hF a ha)).trans (h a ha)

end ZeroFrom

/-! #### `SameOn` -/

namespace SameOn

variable {S S' : ℕ → Prop} {m₁ m₂ m₃ : ℕ → ℕ}

theorem refl (S : ℕ → Prop) (m : ℕ → ℕ) : SameOn S m m := fun _ _ => rfl

theorem trans (h₁ : SameOn S m₁ m₂) (h₂ : SameOn S m₂ m₃) : SameOn S m₁ m₃ :=
  fun a ha => (h₂ a ha).trans (h₁ a ha)

theorem mono (h : SameOn S m₁ m₂) (hS : ∀ a, S' a → S a) : SameOn S' m₁ m₂ := fun a ha => h a (hS a ha)

/-- A store outside `S` keeps `SameOn S`. -/
theorem upd {a v : ℕ} (h : SameOn S m₁ m₂) (ha : ¬ S a) : SameOn S m₁ (RAM.upd m₂ a v) := fun x hx => by
  have hne : x ≠ a := fun h' => ha (h' ▸ hx)
  simp only [upd_apply, hne, ↓reduceIte]; exact h x hx

end SameOn

/-! #### Phase frames: memory unchanged below `F` -/

/-- An array below `F` survives a memory change that keeps all cells below `F`. -/
theorem Arr.of_below {m m' : ℕ → ℕ} {F b : ℕ} {l : List ℕ} (h : Arr m b l) (hS : SameOn (· < F) m m')
    (hb : b + l.length ≤ F) : Arr m' b l :=
  h.of_sameOn hS fun _ hi => by show _ < F; omega

/-- A table below `F` survives a memory change that keeps all cells below `F`. -/
theorem Tab.of_below {m m' : ℕ → ℕ} {F b n : ℕ} {f : ℕ → ℕ} (h : Tab m b n f) (hS : SameOn (· < F) m m')
    (hb : b + n ≤ F) : Tab m' b n f :=
  h.of_sameOn hS fun _ hi => by show _ < F; omega

/-- Storing at or above `F` keeps all cells below `F`. -/
theorem SameOn.upd_of_ge {m₁ m₂ : ℕ → ℕ} {F a : ℕ} (h : SameOn (· < F) m₁ m₂) (ha : F ≤ a) (v : ℕ) :
    SameOn (· < F) m₁ (RAM.upd m₂ a v) := h.upd (by show ¬ a < F; omega)

/-- Allocation: below a `ZeroFrom` bound, `n` fresh zero cells, and the bound moves up by `n`. -/
theorem ZeroFrom.alloc {m : ℕ → ℕ} {F : ℕ} (h : ZeroFrom m F) (n : ℕ) :
    Arr m F (List.replicate n 0) ∧ ZeroFrom m (F + n) := ⟨h.arr le_rfl n, h.mono (by omega)⟩

/-! ### Matrix cells `u * N + v` -/

theorem cell_div {N u v : ℕ} (hv : v < N) : (u * N + v) / N = u := by
  rw [add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hv, zero_add]

theorem cell_mod {N u v : ℕ} (hv : v < N) : (u * N + v) % N = v := by
  rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]

/-- A cell of an `N × N` matrix is below `N * N`. -/
theorem cell_lt {N u v : ℕ} (hu : u < N) (hv : v < N) : u * N + v < N * N := by
  have : (u + 1) * N ≤ N * N := Nat.mul_le_mul_right _ hu
  rw [Nat.succ_mul] at this; omega

/-- Different cells of an `N × N` matrix are different. -/
theorem cell_inj {N u v u' v' : ℕ} (hv : v < N) (hv' : v' < N) (h : u * N + v = u' * N + v') :
    u = u' ∧ v = v' := by
  have h1 := cell_div (u := u) hv
  have h2 := cell_mod (u := u) hv
  rw [h, cell_div hv'] at h1
  rw [h, cell_mod hv'] at h2
  exact ⟨h1.symm, h2.symm⟩

/-! ### The initial configuration -/

@[simp] theorem initial_reg (l : List ℕ) (r : ℕ) : (initial l).reg r = 0 := rfl
@[simp] theorem initial_out (l : List ℕ) : (initial l).out = [] := rfl
theorem initial_mem (l : List ℕ) (a : ℕ) : (initial l).mem a = l.getD a 0 := rfl

theorem arr_initial (l : List ℕ) : Arr (initial l).mem 0 l := fun i hi => by
  simp [initial_mem, List.getElem?_eq_getElem hi]

theorem zeroFrom_initial (l : List ℕ) : ZeroFrom (initial l).mem l.length := fun a ha => by
  simp [initial_mem, List.getElem?_eq_none ha]

/-- The input of the machine on the graph `g`: the number of input entries, then their ends. -/
def graphInput (g : Graph) : List ℕ := g.length :: g.flatMap fun e => [e.1, e.2]

/-- **The label bound** of the input `g`: one more than its largest label (`1` for the empty
input), the size of a table indexed by labels. Linear-time statements bound time and space by
`C * (labelBound g + g.length + 1)`; for the usual labels `0, …, n - 1` it is `n`
(`R0.labelBound_eq`: `labelBound g = maxLab g + 1`). -/
def labelBound (g : Graph) : ℕ := (g.flatMap fun e => [e.1, e.2]).foldl max 0 + 1

@[simp] theorem length_flatMap_pair (g : Graph) : (g.flatMap fun e => [e.1, e.2]).length = 2 * g.length := by
  induction g with
  | nil => rfl
  | cons e g ih => simp [List.flatMap_cons, ih]; omega

@[simp] theorem length_graphInput (g : Graph) : (graphInput g).length = 2 * g.length + 1 := by
  simp [graphInput]; omega

/-- The entries of the input, as `getD`. -/
theorem getD_flatMap_pair (g : Graph) (j : ℕ) (hj : j < g.length) :
    (g.flatMap fun e => [e.1, e.2]).getD (2 * j) 0 = g[j].1 ∧
      (g.flatMap fun e => [e.1, e.2]).getD (2 * j + 1) 0 = g[j].2 := by
  induction g generalizing j with
  | nil => simp at hj
  | cons e g ih =>
    cases j with
    | zero => simp
    | succ j =>
      have := ih j (by simpa using hj)
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, show 2 * j + 1 + 1 + 1 = 2 * j + 1 + 1 + 1 from rfl]
      simpa only [List.flatMap_cons, List.cons_append, List.nil_append, List.getD_cons_succ,
        List.getElem_cons_succ] using this

/-- The entries of the input: `mem[2j + 1] = g[j].1`, `mem[2j + 2] = g[j].2`. -/
theorem initial_graphInput_entry (g : Graph) (j : ℕ) (hj : j < g.length) :
    (initial (graphInput g)).mem (2 * j + 1) = g[j].1 ∧
      (initial (graphInput g)).mem (2 * j + 2) = g[j].2 := by
  have h := getD_flatMap_pair g j hj
  simp only [initial_mem, graphInput, List.getD_cons_succ]
  exact h

end STACS2027.RAM
