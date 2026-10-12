module

public import Runtimes.C4.Iface
public import Runtimes.C4.Paths
public import Runtimes.C4.Bounds
public import Outerplanar.RAM.BoundedLib
import Mathlib.Tactic

/-!
# Four-cycle listing on the RAM: common tools of the phases

Shared by the phases PEEL, ORIENT, SIZE, ENUM, EMIT:

* **Scratch registers** `xI … xO3` (`100`–`131`): every phase may clobber them. The phases
  write only `rT`, `rFREE`, the block `30–49` and these scratch registers.
* **Linked lists** `LL m lo hi a l`: from the node `a`, whose value is `m a`
  and whose successor is `m (a + 1)`, one reads the list `l`; all nodes lie in `[lo, hi)`,
  and `0` ends the list (so `lo ≥ 1` makes every node nonzero). `LL.congr`, `LL.mono`,
  `LL.upd`, `LL.push`.
* **Reading the base configuration** `c₀` (a `C4Base`) in a later memory that agrees with
  `c₀.mem` below `c₀.reg rFREE`: the CSR offsets (`C4Base.offR`: `OFF[v] = R1.ps E v`), the
  neighbour entries (`C4Base.adjR`: `ADJ[ps v + i] = (nb g v)[i]`), the labels
  (`C4Base.labR`).
* **Transfer** of the interfaces through a phase that writes only registers `≥ 30` (besides
  `rT`, `rFREE`), stores only at or above the initial `rFREE` and keeps free memory zero:
  `C4Base.transfer`, `PeelPost.transfer`, `OrientPost.transfer`.
* **Telescoping loops**: `HTB.forUpTele`, `HTB.forRangeTele` — if iteration `j`
  costs at most `f (j + 1) - f j - 4` (with `f j + 4 ≤ f (j + 1)`), the loop costs at most
  `f N - f A` plus a constant. Used with `f` = a weighted count of the 2-paths inserted and
  the cycles reported so far, so that state-dependent insertion costs telescope.
-/

@[expose] public section

namespace STACS2027.Runtimes.C4

open STACS2027 STACS2027.Algo STACS2027.RAM

/-! ### Scratch registers -/

/-- Scratch: a loop counter. -/
abbrev xI : ℕ := 100
/-- Scratch: a loop counter. -/
abbrev xJ : ℕ := 101
/-- Scratch: a loop bound or offset. -/
abbrev xA : ℕ := 102
/-- Scratch: a loop bound or offset. -/
abbrev xB : ℕ := 103
/-- Scratch: a vertex. -/
abbrev xV : ℕ := 104
/-- Scratch: a vertex. -/
abbrev xW : ℕ := 105
/-- Scratch: a value read from memory (insertion: the first endpoint). -/
abbrev xX : ℕ := 106
/-- Scratch: a value read from memory (insertion: the second endpoint). -/
abbrev xY : ℕ := 107
/-- Scratch: insertion: the centre. -/
abbrev xZ : ℕ := 108
/-- Scratch: a list head. -/
abbrev xH : ℕ := 109
/-- Scratch: an address / list walker. -/
abbrev xQ : ℕ := 110
/-- Scratch: a bucket index / degree. -/
abbrev xD : ℕ := 111
/-- Scratch: a counter. -/
abbrev xS : ℕ := 112
/-- Scratch: a pointer. -/
abbrev xP : ℕ := 113
/-- Scratch: a vertex. -/
abbrev xK : ℕ := 114
/-- Scratch: an offset. -/
abbrev xOv : ℕ := 115
/-- Scratch: a degree. -/
abbrev xDv : ℕ := 116
/-- Scratch: an offset. -/
abbrev xOj : ℕ := 117
/-- Scratch: a degree. -/
abbrev xDj : ℕ := 118
/-- Scratch: a bucket cell address. -/
abbrev xC : ℕ := 119
/-- Scratch: a loop start. -/
abbrev xA1 : ℕ := 120
/-- Scratch: a label. -/
abbrev xLa : ℕ := 121
/-- Scratch: a label. -/
abbrev xLb : ℕ := 122
/-- Scratch: a label. -/
abbrev xLc : ℕ := 123
/-- Scratch: a label. -/
abbrev xLd : ℕ := 124
/-- Scratch: an entry of a canonical cycle. -/
abbrev xO0 : ℕ := 125
/-- Scratch: an entry of a canonical cycle. -/
abbrev xO1 : ℕ := 126
/-- Scratch: an entry of a canonical cycle. -/
abbrev xO2 : ℕ := 127
/-- Scratch: an entry of a canonical cycle. -/
abbrev xO3 : ℕ := 128
/-- Scratch: a counter. -/
abbrev xT4 : ℕ := 129

/-! ### Linked lists -/

/-- `LL m lo hi a l`: from the node `a` (value `m a`, successor `m (a + 1)`) one reads the list
`l`; all nodes lie in `[lo, hi)` (both of their cells), `0` ends the list. -/
def LL (m : ℕ → ℕ) (lo hi : ℕ) : ℕ → List ℕ → Prop
  | a, [] => a = 0
  | a, x :: l => lo ≤ a ∧ a + 1 < hi ∧ m a = x ∧ LL m lo hi (m (a + 1)) l

@[simp] theorem LL_nil {m : ℕ → ℕ} {lo hi a : ℕ} : LL m lo hi a [] ↔ a = 0 := Iff.rfl

theorem LL_cons {m : ℕ → ℕ} {lo hi a x : ℕ} {l : List ℕ} :
    LL m lo hi a (x :: l) ↔ lo ≤ a ∧ a + 1 < hi ∧ m a = x ∧ LL m lo hi (m (a + 1)) l := Iff.rfl

/-- A list survives memory changes outside `[lo, hi)`. -/
theorem LL.congr {m m' : ℕ → ℕ} {lo hi : ℕ} (hm : ∀ q, lo ≤ q → q < hi → m' q = m q) :
    ∀ {a : ℕ} {l : List ℕ}, LL m lo hi a l → LL m' lo hi a l
  | _, [], h => h
  | a, _ :: _, ⟨h0, h1, h2, h3⟩ =>
    ⟨h0, h1, (hm a h0 (by omega)).trans h2, by rw [hm (a + 1) (by omega) h1]; exact LL.congr hm h3⟩

theorem LL.mono {m : ℕ → ℕ} {lo hi hi' : ℕ} (hh : hi ≤ hi') :
    ∀ {a : ℕ} {l : List ℕ}, LL m lo hi a l → LL m lo hi' a l
  | _, [], h => h
  | _, _ :: _, ⟨h0, h1, h2, h3⟩ => ⟨h0, by omega, h2, LL.mono hh h3⟩

/-- A store outside the nodes keeps a list. -/
theorem LL.upd {m : ℕ → ℕ} {lo hi a b v : ℕ} {l : List ℕ} (h : LL m lo hi a l)
    (hb : b < lo ∨ hi ≤ b) : LL (RAM.upd m b v) lo hi a l :=
  h.congr fun q h1 h2 => upd_ne m v (by omega)

/-- A nonempty list does not start at `0` (when `1 ≤ lo`). -/
theorem LL.ne_zero {m : ℕ → ℕ} {lo hi a x : ℕ} {l : List ℕ} (h : LL m lo hi a (x :: l))
    (hlo : 1 ≤ lo) : a ≠ 0 := by
  have := h.1; omega

/-- **Push**: a new node at `hi` (value `x`, successor the old head `h`) heads `x :: l`. -/
theorem LL.push {m m' : ℕ → ℕ} {lo hi h x : ℕ} {l : List ℕ} (hl : LL m lo hi h l)
    (hlo : lo ≤ hi) (hm : ∀ q, lo ≤ q → q < hi → m' q = m q) (hx : m' hi = x)
    (hh : m' (hi + 1) = h) : LL m' lo (hi + 2) hi (x :: l) :=
  ⟨hlo, by omega, hx, by rw [hh]; exact (hl.congr hm).mono (by omega)⟩

/-! ### The CSR segments -/

theorem csrAdj_prefix (E : List Edge) {v N : ℕ} (h : v ≤ N) :
    csrAdj E v <+: csrAdj E N := by
  induction N, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ N _ ih => rw [R1.csrAdj_succ]; exact ih.trans (List.prefix_append _ _)

/-- The segment of `v` in a stored CSR array. -/
theorem arr_seg {m : ℕ → ℕ} {b : ℕ} {E : List Edge} {N v : ℕ} (h : Arr m b (csrAdj E N))
    (hv : v < N) : Arr m (b + R1.ps E v) (nbOf E v) := by
  obtain ⟨t, ht⟩ := csrAdj_prefix E (show v + 1 ≤ N by omega)
  rw [← ht, R1.csrAdj_succ, List.append_assoc, arr_append, arr_append] at h
  rw [← R1.length_csrAdj]
  exact h.2.1

/-! ### Reading the base configuration -/

section read

variable {g : Graph} {c₀ : Config} {m : ℕ → ℕ}

theorem C4Base.free_pos (h : C4Base g c₀) : 0 < c₀.reg rFREE := by
  have := h.r1.below.1; omega

/-- The arrays read by the phases lie below the free address (for the address bounds). -/
theorem C4Base.bounds (h : C4Base g c₀) :
    c₀.reg gOFF + (numV g + 1) ≤ c₀.reg rFREE ∧
      c₀.reg gADJ + 2 * (idEdges g).length ≤ c₀.reg rFREE ∧
      c₀.reg gLB + numV g ≤ c₀.reg rFREE := by
  have h1 := h.r1.below
  have h2 := h.r1.base.below
  rw [R1.length_csrAdj, R1.idEdges_ps] at h1
  exact ⟨h1.1, h1.2.1, h2.1⟩

theorem C4Base.offR (h : C4Base g c₀) (hS : SameOn (· < c₀.reg rFREE) c₀.mem m) {v : ℕ}
    (hv : v ≤ numV g) : m (c₀.reg gOFF + v) = R1.ps (idEdges g) v := by
  have h1 := (h.r1.off.of_below hS (by simpa [R1.csrOff_eq] using h.r1.below.1)).get
    (i := v) (by simp [R1.csrOff_eq]; omega)
  simpa [R1.csrOff_eq] using h1

theorem C4Base.adjR (h : C4Base g c₀) (hS : SameOn (· < c₀.reg rFREE) c₀.mem m) {v i : ℕ}
    (hv : v < numV g) (hi : i < (nb g v).length) :
    m (c₀.reg gADJ + (R1.ps (idEdges g) v + i)) = (nb g v).getD i 0 := by
  have hA := h.r1.adj.of_below hS h.r1.below.2.1
  rw [← Nat.add_assoc]
  exact (arr_seg hA hv).getD hi

theorem C4Base.labR (h : C4Base g c₀) (hS : SameOn (· < c₀.reg rFREE) c₀.mem m) {x : ℕ}
    (hx : x < numV g) : m (c₀.reg gLB + x) = labelOf g x :=
  (h.r1.base.lb.of_below hS h.r1.base.below.1).getD hx

end read

/-! ### Transfer of the interfaces through a phase -/

/-- `C4Base` survives a phase that writes no register below `30` (besides `rT`, `rFREE`),
stores only at or above the initial `rFREE` and keeps free memory zero. -/
theorem C4Base.transfer {g : Graph} {c₀ c : Config} (h : C4Base g c₀)
    (hreg : ∀ r, r < 30 → r ≠ rT → r ≠ rFREE → c.reg r = c₀.reg r)
    (hS : SameOn (· < c₀.reg rFREE) c₀.mem c.mem) (hF : c₀.reg rFREE ≤ c.reg rFREE)
    (hZ : ZeroFrom c.mem (c.reg rFREE)) : C4Base g c := by
  have hB := h.r1.base
  have hb := hB.below
  have h1 := h.r1.below
  have hr : ∀ r, r < 30 → r ≠ rT → r ≠ rFREE → c.reg r = c₀.reg r := hreg
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hZ, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hr 0 (by decide) (by decide) (by decide)]; exact hB.zero
  · rw [hr 1 (by decide) (by decide) (by decide)]; exact hB.one
  · rw [hr gM (by decide) (by decide) (by decide)]; exact hB.m
  · rw [hr gN (by decide) (by decide) (by decide)]; exact hB.n
  · rw [hr gNE (by decide) (by decide) (by decide)]; exact hB.ne
  · rw [hr gLB (by decide) (by decide) (by decide)]; exact hB.lb.of_below hS hb.1
  · rw [hr gEU (by decide) (by decide) (by decide)]
    exact hB.eu.of_below hS (by simpa using hb.2.1)
  · rw [hr gEV (by decide) (by decide) (by decide)]
    exact hB.ev.of_below hS (by simpa using hb.2.2)
  · rw [hr gLB (by decide) (by decide) (by decide), hr gEU (by decide) (by decide) (by decide),
      hr gEV (by decide) (by decide) (by decide)]
    omega
  · rw [hr gOFF (by decide) (by decide) (by decide)]
    exact h.r1.off.of_below hS (by simpa [R1.csrOff_eq] using h1.1)
  · rw [hr gADJ (by decide) (by decide) (by decide)]; exact h.r1.adj.of_below hS h1.2.1
  · rw [hr gPRE (by decide) (by decide) (by decide)]; exact h.r1.pre.of_below hS h1.2.2.1
  · rw [hr gPAR (by decide) (by decide) (by decide)]; exact h.r1.par.of_below hS h1.2.2.2.1
  · rw [hr gORD (by decide) (by decide) (by decide)]; exact h.r1.ord.of_below hS h1.2.2.2.2
  · rw [hr gOFF (by decide) (by decide) (by decide), hr gADJ (by decide) (by decide) (by decide),
      hr gPRE (by decide) (by decide) (by decide), hr gPAR (by decide) (by decide) (by decide),
      hr gORD (by decide) (by decide) (by decide)]
    omega

/-- `PeelPost` survives a phase that writes no register below `34` (besides `rT`, `rFREE`). -/
theorem PeelPost.transfer {g : Graph} {c₀ c : Config} (h : PeelPost g c₀)
    (hreg : ∀ r, r < 34 → r ≠ rT → r ≠ rFREE → c.reg r = c₀.reg r)
    (hS : SameOn (· < c₀.reg rFREE) c₀.mem c.mem) (hF : c₀.reg rFREE ≤ c.reg rFREE)
    (hZ : ZeroFrom c.mem (c.reg rFREE)) : PeelPost g c := by
  refine ⟨h.base.transfer (fun r hr => hreg r (by omega)) hS hF hZ, ?_, ?_⟩
  · rw [hreg gPOS (by decide) (by decide) (by decide)]; exact h.pos.of_below hS h.below
  · rw [hreg gPOS (by decide) (by decide) (by decide)]; have := h.below; omega

/-- `OrientPost` survives a phase that writes no register below `36` (besides `rT`, `rFREE`). -/
theorem OrientPost.transfer {g : Graph} {c₀ c : Config} (h : OrientPost g c₀)
    (hreg : ∀ r, r < 36 → r ≠ rT → r ≠ rFREE → c.reg r = c₀.reg r)
    (hS : SameOn (· < c₀.reg rFREE) c₀.mem c.mem) (hF : c₀.reg rFREE ≤ c.reg rFREE)
    (hZ : ZeroFrom c.mem (c.reg rFREE)) : OrientPost g c := by
  have hb := h.below
  have hps : ∀ v < numV g, R1.ps (idEdges g) v + (outL g (peelPos g) v).length ≤
      2 * (idEdges g).length := by
    intro v hv
    have h1 := R1.ps_add_le (idEdges g) (show v < numV g from hv)
    have h2 : (outL g (peelPos g) v).length ≤ (nbOf (idEdges g) v).length :=
      length_outL_le g (peelPos g) v
    rw [R1.idEdges_ps] at h1
    omega
  refine ⟨h.peel.transfer (fun r hr => hreg r (by omega)) hS hF hZ, ?_, ?_, ?_⟩
  · rw [hreg gODEG (by decide) (by decide) (by decide)]; exact h.odeg.of_below hS hb.1
  · intro v hv
    rw [hreg gOADJ (by decide) (by decide) (by decide)]
    exact (h.oadj v hv).of_below hS (by have := hps v hv; omega)
  · rw [hreg gODEG (by decide) (by decide) (by decide),
      hreg gOADJ (by decide) (by decide) (by decide)]
    omega

/-! ### Telescoping loops -/

theorem le_of_steps {A : ℕ} (f : ℕ → ℕ) {N : ℕ} (hf : ∀ j, A ≤ j → j < N → f j + 4 ≤ f (j + 1))
    {j : ℕ} (hAj : A ≤ j) (hjN : j ≤ N) : f A + 4 * (j - A) ≤ f j := by
  induction j, hAj using Nat.le_induction with
  | base => simp
  | succ j hAj ih =>
    have := hf j hAj (by omega)
    have := ih (by omega)
    rw [show j + 1 - A = (j - A) + 1 by omega]
    omega

theorem sum_affine (n a b : ℕ) (f : ℕ → ℕ) :
    ∑ v ∈ Finset.range n, (a + b * f v) = a * n + b * ∑ v ∈ Finset.range n, f v := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, Finset.mul_sum]
  ring

/-- The telescoping sum. -/
theorem sum_tele {A N : ℕ} (f : ℕ → ℕ) (hf : ∀ j, A ≤ j → j < N → f j + 4 ≤ f (j + 1))
    (hAN : A ≤ N) : ∑ j ∈ Finset.Ico A N, (f (j + 1) - f j - 4 + 4) = f N - f A := by
  induction N, hAN using Nat.le_induction with
  | base => simp
  | succ N hAN ih =>
    rw [Finset.sum_Ico_succ_top hAN, ih (fun j h1 h2 => hf j h1 (by omega))]
    have h1 := hf N hAN (by omega)
    have h2 := le_of_steps f (N := N + 1) hf (j := N) hAN (by omega)
    omega

/-- **Counted loop with telescoping costs**: iteration `j` costs at most
`f (j + 1) - f j - 4`; the loop costs at most `f N - f 0 + 3`. -/
theorem HTB.forUpTele {S : ℕ} {i n N : ℕ} {body : Stmt} (Inv : ℕ → Config → Prop) (f : ℕ → ℕ)
    (hi : i ≠ rT) (hn : n ≠ rT) (hin : n ≠ i) (hInv : ∀ j, Indep [i, rT] (Inv j))
    (hf : ∀ j < N, f j + 4 ≤ f (j + 1))
    (hbody : ∀ j < N, HTB S body (fun c => Inv j c ∧ c.reg i = j ∧ c.reg n = N)
      (fun c => Inv (j + 1) c ∧ c.reg i = j ∧ c.reg n = N) (f (j + 1) - f j - 4)) :
    HTB S (RAM.forUp i n body) (fun c => Inv 0 c ∧ c.reg n = N)
      (fun c => Inv N c ∧ c.reg i = N ∧ c.reg n = N) (f N - f 0 + 3) := by
  have h := HTB.forUp Inv (fun j => f (j + 1) - f j - 4) hi hn hin hInv hbody
  refine h.weaken (le_of_eq ?_)
  rw [Finset.range_eq_Ico, sum_tele f (fun j _ hj => hf j hj) (Nat.zero_le _)]

/-- **Range loop with telescoping costs** over `[A, N)`: the loop costs at most
`f N - f A + 4`. -/
theorem HTB.forRangeTele {S : ℕ} {i a n A N : ℕ} {body : Stmt} (Inv : ℕ → Config → Prop)
    (f : ℕ → ℕ)
    (hi : i ≠ rT) (hn : n ≠ rT) (ha : a ≠ rT) (hin : n ≠ i) (hInv : ∀ j, Indep [i, rT] (Inv j))
    (hf : ∀ j, A ≤ j → j < N → f j + 4 ≤ f (j + 1))
    (hbody : ∀ j, A ≤ j → j < N → HTB S body (fun c => Inv j c ∧ c.reg i = j ∧ c.reg n = N)
      (fun c => Inv (j + 1) c ∧ c.reg i = j ∧ c.reg n = N) (f (j + 1) - f j - 4)) :
    HTB S (RAM.forRange i a n body) (fun c => Inv A c ∧ c.reg a = A ∧ c.reg n = N ∧ A ≤ N)
      (fun c => Inv N c ∧ c.reg i = N ∧ c.reg n = N) (f N - f A + 4) := by
  have h := HTB.forRange (A := A) Inv (fun j => f (j + 1) - f j - 4) hi hn ha hin hInv hbody
  refine HTB.prop_pre (P := fun c => Inv A c ∧ c.reg a = A ∧ c.reg n = N) (fun hAN => ?_) |>.pre
    (fun c ⟨hI, ha', hn', hAN⟩ => ⟨hAN, hI, ha', hn'⟩)
  refine (h.pre fun c ⟨hI, ha', hn'⟩ => ⟨hI, ha', hn', hAN⟩).weaken (le_of_eq ?_)
  rw [sum_tele f hf hAN]

end STACS2027.Runtimes.C4
