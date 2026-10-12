module

public import Outerplanar.RAM.SortSpec
import Mathlib.Tactic

/-!
# Phase P1 of the polygon solver: growth frames and the gather loop

* `Grow W c₀ c`: `c` arises from `c₀` by a run writing only the registers of `W`, storing
  only at or above the free pointer of `c₀`, never lowering the free pointer, and writing no
  output. Arrays below the free pointer at registers outside `W` survive (`Grow.arr`,
  `Grow.tab`, `Grow.le`); `Grow.trans`, `Grow.mono`.
* `HT.grow`: a triple with the memory frame `SameOn (· < F₀) m₀` in its postcondition gives
  `Grow`;
* growth triples `HG s W P Q b` (`HG.ofGhost`), the form of `csort_spec`; the stages of P1 and
  P2 are composed as their bounded twins `HGB S`, `HGMB S` (`Poly1Grow.lean`);
* `ArrAt r l`, `TabAt r k f`: data at the address in a register, below the free pointer;
  `Stable W F`: `F` survives every `Grow W` (`Stable.arrAt`, `Stable.tabAt`, `Stable.regEq`,
  `Stable.and`, `Stable.sameOn`).
* `arr_flatMap`, `arr_flatMap_get`: a concatenation `(List.range K).flatMap f` stored as its
  parts at the running offsets.
* `gather`: `OUT[j] := F[IDX[j]]` (specified in bounded space in `Poly1Grow.lean`,
  `gather_spec`), with its arguments in fixed registers (`rGI`, `rGF`, `rGL`) and its result
  at `rGO`.
-/

@[expose] public section

namespace STACS2027.RAM.P1

/-! ### Growth -/

/-- `c` arises from `c₀` by writing the registers of `W`, storing at or above the free
pointer, allocating, and no output. -/
structure Grow (W : List ℕ) (c₀ c : Config) : Prop where
  reg : ∀ r, r ∉ W → c.reg r = c₀.reg r
  mem : SameOn (· < c₀.reg rFREE) c₀.mem c.mem
  free : c₀.reg rFREE ≤ c.reg rFREE
  out : c.out = c₀.out

namespace Grow

variable {W W' : List ℕ} {c₀ c c₁ : Config}

theorem refl (W : List ℕ) (c : Config) : Grow W c c :=
  ⟨fun _ _ => rfl, SameOn.refl _ _, le_rfl, rfl⟩

theorem mono (h : Grow W c₀ c) (hW : ∀ r ∈ W, r ∈ W') : Grow W' c₀ c :=
  ⟨fun r hr => h.reg r fun h' => hr (hW r h'), h.mem, h.free, h.out⟩

theorem trans (h₁ : Grow W c₀ c₁) (h₂ : Grow W c₁ c) : Grow W c₀ c where
  reg r hr := (h₂.reg r hr).trans (h₁.reg r hr)
  mem := h₁.mem.trans (h₂.mem.mono fun _ (ha : _ < _) => show _ < _ by have := h₁.free; omega)
  free := h₁.free.trans h₂.free
  out := h₂.out.trans h₁.out

theorem sameOn {F : ℕ} {m : ℕ → ℕ} (h : Grow W c₀ c) (hs : SameOn (· < F) m c₀.mem)
    (hF : F ≤ c₀.reg rFREE) : SameOn (· < F) m c.mem :=
  hs.trans (h.mem.mono fun _ (ha : _ < _) => show _ < _ by omega)

theorem le {r k : ℕ} (h : Grow W c₀ c) (hr : r ∉ W) (hb : c₀.reg r + k ≤ c₀.reg rFREE) :
    c.reg r + k ≤ c.reg rFREE := by
  rw [h.reg r hr]; have := h.free; omega

theorem arr {r : ℕ} {l : List ℕ} (h : Grow W c₀ c) (hr : r ∉ W) (ha : Arr c₀.mem (c₀.reg r) l)
    (hb : c₀.reg r + l.length ≤ c₀.reg rFREE) : Arr c.mem (c.reg r) l := by
  rw [h.reg r hr]; exact ha.of_below h.mem hb

theorem tab {r k : ℕ} {f : ℕ → ℕ} (h : Grow W c₀ c) (hr : r ∉ W)
    (ha : Tab c₀.mem (c₀.reg r) k f) (hb : c₀.reg r + k ≤ c₀.reg rFREE) :
    Tab c.mem (c.reg r) k f := by
  rw [h.reg r hr]; exact ha.of_below h.mem hb

theorem arr' {b : ℕ} {l : List ℕ} (h : Grow W c₀ c) (ha : Arr c₀.mem b l)
    (hb : b + l.length ≤ c₀.reg rFREE) : Arr c.mem b l := ha.of_below h.mem hb

end Grow

/-- A triple with the memory frame of its run gives `Grow` (for a program without output). -/
theorem HT.grow {s : Stmt} {P Q : Config → Prop} {b : ℕ} (hw : writes s = false)
    (h : ∀ (F₀ : ℕ) (m₀ : ℕ → ℕ), HT s (fun c => P c ∧ c.reg rFREE = F₀ ∧ c.mem = m₀)
      (fun c => Q c ∧ SameOn (· < F₀) m₀ c.mem ∧ F₀ ≤ c.reg rFREE) b) (c₀ : Config) :
    HT s (fun c => P c ∧ c = c₀) (fun c => Q c ∧ Grow (wregs s) c₀ c) b := by
  have := (h (c₀.reg rFREE) c₀.mem).withFrame c₀
  refine this.mono (fun c ⟨hp, hc⟩ => ⟨⟨hp, hc ▸ rfl, hc ▸ rfl⟩, hc⟩) ?_ le_rfl
  rintro c ⟨⟨hq, hs, hF⟩, hfr⟩
  exact ⟨hq, hfr.reg, hs, hF, hfr.out hw⟩

/-- A loop-free block that neither stores nor writes is a `Grow`. -/
theorem grow_run {s : Stmt} (hs : LoopFree s) (hst : stores s = false) (hw : writes s = false)
    (hF : rFREE ∉ wregs s) (c : Config) : Grow (wregs s) c (RAM.run s c) where
  reg r hr := run_reg_of_not_mem hs hr c
  mem := by rw [run_mem_of_stores hs hst]; exact SameOn.refl _ _
  free := (run_reg_of_not_mem hs hF c).ge
  out := run_out_of_writes hs hw c

/-! ### Growth triples -/

/-- A growth triple: from `P`, the program `s` reaches `Q` within `b` steps, and the run is a
`Grow W`. -/
def HG (s : Stmt) (W : List ℕ) (P Q : Config → Prop) (b : ℕ) : Prop :=
  ∀ c₀, HT s (fun c => P c ∧ c = c₀) (fun c => Q c ∧ Grow W c₀ c) b

namespace HG

variable {s : Stmt} {W : List ℕ} {P Q : Config → Prop} {b : ℕ}

/-- From a triple with the memory frame in its postcondition. -/
theorem ofGhost (hw : writes s = false) (hW : ∀ r ∈ wregs s, r ∈ W)
    (h : ∀ (F₀ : ℕ) (m₀ : ℕ → ℕ), HT s (fun c => P c ∧ c.reg rFREE = F₀ ∧ c.mem = m₀)
      (fun c => Q c ∧ SameOn (· < F₀) m₀ c.mem ∧ F₀ ≤ c.reg rFREE) b) : HG s W P Q b :=
  fun c₀ => (HT.grow hw h c₀).post fun _ ⟨hq, hg⟩ => ⟨hq, hg.mono hW⟩

end HG

/-! ### Assertions surviving growth -/

/-- The list `l` stored at the address in register `r`, below the free pointer. -/
def ArrAt (r : ℕ) (l : List ℕ) (c : Config) : Prop :=
  Arr c.mem (c.reg r) l ∧ c.reg r + l.length ≤ c.reg rFREE

/-- The function `f` stored on `k` cells at the address in register `r`, below the free
pointer. -/
def TabAt (r k : ℕ) (f : ℕ → ℕ) (c : Config) : Prop :=
  Tab c.mem (c.reg r) k f ∧ c.reg r + k ≤ c.reg rFREE

/-- `F` survives every run that is a `Grow W`. -/
def Stable (W : List ℕ) (F : Config → Prop) : Prop := ∀ c c', F c → Grow W c c' → F c'

namespace Stable

variable {W : List ℕ} {F G : Config → Prop}

theorem and (h₁ : Stable W F) (h₂ : Stable W G) : Stable W (fun c => F c ∧ G c) :=
  fun c c' h hg => ⟨h₁ c c' h.1 hg, h₂ c c' h.2 hg⟩

theorem of_iff (h : ∀ c, F c ↔ G c) (hG : Stable W G) : Stable W F :=
  fun c c' hf hg => (h c').mpr (hG c c' ((h c).mp hf) hg)

theorem const (p : Prop) : Stable W (fun _ => p) := fun _ _ h _ => h

theorem reg {r : ℕ} (hr : r ∉ W) (p : ℕ → Prop) : Stable W (fun c => p (c.reg r)) :=
  fun c c' h hg => show p (c'.reg r) by rw [hg.reg r hr]; exact h

theorem regEq {r : ℕ} (hr : r ∉ W) (v : ℕ) : Stable W (fun c => c.reg r = v) := reg hr (· = v)

theorem arrAt {r : ℕ} (hr : r ∉ W) (l : List ℕ) : Stable W (ArrAt r l) :=
  fun _ _ h hg => ⟨hg.arr hr h.1 h.2, hg.le hr h.2⟩

theorem tabAt {r k : ℕ} (hr : r ∉ W) (f : ℕ → ℕ) : Stable W (TabAt r k f) :=
  fun _ _ h hg => ⟨hg.tab hr h.1 h.2, hg.le hr h.2⟩

/-- The memory frame of a run from `F₀`, `m₀`. -/
theorem sameOn (F₀ : ℕ) (m₀ : ℕ → ℕ) :
    Stable W (fun c => SameOn (· < F₀) m₀ c.mem ∧ F₀ ≤ c.reg rFREE) :=
  fun _ _ h hg => ⟨hg.sameOn h.1 h.2, h.2.trans hg.free⟩

end Stable

theorem ArrAt.of_reg {r r' : ℕ} {l : List ℕ} {c c' : Config} (h : ArrAt r l c)
    (hr : c'.reg r' = c.reg r) (hm : c'.mem = c.mem) (hf : c'.reg rFREE = c.reg rFREE) :
    ArrAt r' l c' := by
  unfold ArrAt; rw [hr, hm, hf]; exact h

theorem TabAt.of_reg {r r' k : ℕ} {f : ℕ → ℕ} {c c' : Config} (h : TabAt r k f c)
    (hr : c'.reg r' = c.reg r) (hm : c'.mem = c.mem) (hf : c'.reg rFREE = c.reg rFREE) :
    TabAt r' k f c' := by
  unfold TabAt; rw [hr, hm, hf]; exact h

/-! ### Concatenations stored by parts -/

/-- The start of the part `k` of `(List.range K).flatMap f`. -/
def partOff (f : ℕ → List ℕ) (k : ℕ) : ℕ := ((List.range k).map fun j => (f j).length).sum

theorem partOff_succ (f : ℕ → List ℕ) (k : ℕ) : partOff f (k + 1) = partOff f k + (f k).length := by
  simp only [partOff, List.sum_range_succ]

theorem length_flatMap_range (f : ℕ → List ℕ) (K : ℕ) :
    ((List.range K).flatMap f).length = partOff f K := by
  rw [List.length_flatMap]; rfl

/-- A concatenation stored by parts. -/
theorem arr_flatMap {m : ℕ → ℕ} {b : ℕ} (f : ℕ → List ℕ) :
    ∀ K, (∀ k, k < K → Arr m (b + partOff f k) (f k)) → Arr m b ((List.range K).flatMap f)
  | 0, _ => by simp
  | K + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, arr_append,
      length_flatMap_range]
    exact ⟨arr_flatMap f K fun k hk => h k (by omega), h K (by omega)⟩

/-- The parts of a stored concatenation. -/
theorem arr_flatMap_get {m : ℕ → ℕ} {b : ℕ} (f : ℕ → List ℕ) :
    ∀ K, Arr m b ((List.range K).flatMap f) → ∀ k, k < K → Arr m (b + partOff f k) (f k)
  | 0, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | K + 1, h, k, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, arr_append,
      length_flatMap_range] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact arr_flatMap_get f K h.1 k hk
    · exact h.2

/-! ### Gathering: `OUT[j] := F[IDX[j]]` -/

/-- Argument: base of the index array. -/
abbrev rGI : ℕ := 110
/-- Argument: base of the field array. -/
abbrev rGF : ℕ := 111
/-- Argument: the number of indices. -/
abbrev rGL : ℕ := 112
/-- Result: base of the gathered array. -/
abbrev rGO : ℕ := 113
/-- Loop counter. -/
abbrev rGJ : ℕ := 114
/-- Temporary. -/
abbrev rGX : ℕ := 115

/-- One entry: `OUT[j] := F[IDX[j]]`. -/
def gaBody : Stmt := .seq (ld rGX rGI rGJ) (.seq (ld rGX rGF rGX) (st rGO rGJ rGX))

/-- **Gathering**: allocate `OUT` (`reg rGL` cells) and fill it. -/
def gather : Stmt := .seq (alloc rGO rGL) (forUp rGJ rGL gaBody)

/-- The arguments of `gather`. -/
structure GaIn (idx F : List ℕ) (c : Config) : Prop where
  ln : c.reg rGL = idx.length
  ai : ArrAt rGI idx c
  af : ArrAt rGF F c
  free : ZeroFrom c.mem (c.reg rFREE)

/-- The invariant of the gather loop after `j` entries. -/
def GaInv (idx F : List ℕ) (F₀ : ℕ) (m₀ : ℕ → ℕ) (j : ℕ) (c : Config) : Prop :=
  c.reg rGL = idx.length ∧ Arr c.mem (c.reg rGI) idx ∧ Arr c.mem (c.reg rGF) F ∧
    c.reg rGI + idx.length ≤ F₀ ∧ c.reg rGF + F.length ≤ F₀ ∧ c.reg rGO = F₀ ∧
    c.reg rFREE = F₀ + idx.length ∧ Arr c.mem F₀ ((idx.take j).map fun i => F.getD i 0) ∧
    ZeroFrom c.mem (F₀ + idx.length) ∧ SameOn (· < F₀) m₀ c.mem

end STACS2027.RAM.P1
