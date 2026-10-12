module

public import Outerplanar.RAM.Poly1Sort
import Mathlib.Tactic

/-!
# The polygon solver: growth triples in bounded space

The phases P1 and P2 of the polygon solver are composed as growth triples (`Grow`, `Stable`,
`Poly1Lib.lean`). Here their bounded-space forms:

* `HGB S s W P Q b`: from `P`, the program `s` reaches `Q` within `b` steps by an `ExecB S` run
  (every load and store below `S`), and the run is a `Grow W` (`HGB.seq`, `HGB.frame`,
  `HGB.mono`, `HGB.run`, `HGB.ofGhost`, `HGB.forUp`, …);
* `HGMB S s W P Q b m`: moreover the run moves the free pointer up by at most `m`, and the
  bound is only required to leave room for these `m` cells (`F₀ + m ≤ S`, `F₀` the initial
  free pointer). The sequence of two such triples needs room for the sum (`HGMB.seq`);
  everything a phase touches lies below its final free pointer, so the bound of a phase is its
  initial free pointer plus its fresh memory (`HGMB.bound`).
* the counting sort (`csort_specMB`, from `csort_specB`) and the gather loop (`gather_spec`)
  as such triples.
-/

@[expose] public section

namespace STACS2027.RAM.P1

/-! ### Growth triples in bounded space -/

/-- A bounded triple with the memory frame of its run gives `Grow` (for a program without
output). -/
theorem HTB.grow {S : ℕ} {s : Stmt} {P Q : Config → Prop} {b : ℕ} (hw : writes s = false)
    (h : ∀ (F₀ : ℕ) (m₀ : ℕ → ℕ), HTB S s (fun c => P c ∧ c.reg rFREE = F₀ ∧ c.mem = m₀)
      (fun c => Q c ∧ SameOn (· < F₀) m₀ c.mem ∧ F₀ ≤ c.reg rFREE) b) (c₀ : Config) :
    HTB S s (fun c => P c ∧ c = c₀) (fun c => Q c ∧ Grow (wregs s) c₀ c) b := by
  have := (h (c₀.reg rFREE) c₀.mem).withFrame c₀
  refine this.mono (fun c ⟨hp, hc⟩ => ⟨⟨hp, hc ▸ rfl, hc ▸ rfl⟩, hc⟩) ?_ le_rfl
  rintro c ⟨⟨hq, hs, hF⟩, hfr⟩
  exact ⟨hq, hfr.reg, hs, hF, hfr.out hw⟩

/-- A growth followed by an agreement on the other registers. -/
theorem Grow.agree {W V : List ℕ} {c₀ c c' : Config} (h : Grow W c₀ c) (hA : Agree V c c')
    (hV : ∀ r ∈ V, r ∈ W) (hF : rFREE ∉ V) : Grow W c₀ c' where
  reg r hr := by rw [hA.reg r fun h' => hr (hV r h')]; exact h.reg r hr
  mem := by rw [hA.mem]; exact h.mem
  free := by rw [hA.reg rFREE hF]; exact h.free
  out := by rw [hA.out]; exact h.out

/-- A growth triple in bounded space: from `P`, the program `s` reaches `Q` within `b` steps by
a run touching only addresses below `S`, and the run is a `Grow W`. -/
def HGB (S : ℕ) (s : Stmt) (W : List ℕ) (P Q : Config → Prop) (b : ℕ) : Prop :=
  ∀ c₀, HTB S s (fun c => P c ∧ c = c₀) (fun c => Q c ∧ Grow W c₀ c) b

namespace HGB

variable {S : ℕ} {s u body : Stmt} {W W' : List ℕ} {P P' Q Q' R F : Config → Prop}
  {b b' b₁ b₂ : ℕ}

theorem toHTB (h : HGB S s W P Q b) : HTB S s P Q b :=
  HTB.of_forall fun c₀ hp => (h c₀).mono (fun _ hc => ⟨hc ▸ hp, hc⟩) (fun _ h => h.1) le_rfl

theorem seq (h₁ : HGB S s W P R b₁) (h₂ : HGB S u W R Q b₂) : HGB S (.seq s u) W P Q (b₁ + b₂) := by
  intro c₀ c ⟨hp, hc⟩
  obtain ⟨c₁, t₁, he₁, ⟨hr, hg₁⟩, ht₁⟩ := h₁ c₀ c ⟨hp, hc⟩
  obtain ⟨c₂, t₂, he₂, ⟨hq, hg₂⟩, ht₂⟩ := h₂ c₁ c₁ ⟨hr, rfl⟩
  exact ⟨c₂, t₁ + t₂, ExecB.seq he₁ he₂, ⟨hq, hg₁.trans hg₂⟩, by omega⟩

theorem mono (h : HGB S s W P Q b) (hW : ∀ r ∈ W, r ∈ W') (hP : ∀ c, P' c → P c)
    (hQ : ∀ c, Q c → Q' c) (hb : b ≤ b') : HGB S s W' P' Q' b' := fun c₀ =>
  (h c₀).mono (fun c ⟨hp, hc⟩ => ⟨hP c hp, hc⟩) (fun c ⟨hq, hg⟩ => ⟨hQ c hq, hg.mono hW⟩) hb

theorem weaken (h : HGB S s W P Q b) (hb : b ≤ b') : HGB S s W P Q b' :=
  h.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) hb

theorem post (h : HGB S s W P Q b) (hQ : ∀ c, Q c → Q' c) : HGB S s W P Q' b :=
  h.mono (fun _ h => h) (fun _ h => h) hQ le_rfl

theorem pre (h : HGB S s W P Q b) (hP : ∀ c, P' c → P c) : HGB S s W P' Q b :=
  h.mono (fun _ h => h) hP (fun _ h => h) le_rfl

/-- The frame rule for assertions surviving `Grow`. -/
theorem frame (h : HGB S s W P Q b) (hF : Stable W F) :
    HGB S s W (fun c => P c ∧ F c) (fun c => Q c ∧ F c) b := by
  intro c₀ c ⟨⟨hp, hf⟩, hc⟩
  obtain ⟨c', t, he, ⟨hq, hg⟩, ht⟩ := h c₀ c ⟨hp, hc⟩
  subst hc
  exact ⟨c', t, he, ⟨⟨hq, hF _ _ hf hg⟩, hg⟩, ht⟩

/-- Loop-free code. -/
theorem run (hs : LoopFree s) (hb : size s ≤ b)
    (h : ∀ c, P c → AddrOK S s c ∧ Q (RAM.run s c) ∧ Grow W c (RAM.run s c)) :
    HGB S s W P Q b := fun c₀ =>
  HTB.run_le hs hb fun c ⟨hp, hc⟩ => by subst hc; exact ⟨(h c hp).1, (h c hp).2⟩

/-- Loop-free code storing at or above the free pointer. -/
theorem runG (hs : LoopFree s) (hw : writes s = false) (hb : size s ≤ b)
    (h : ∀ c, P c → AddrOK S s c ∧ Q (RAM.run s c) ∧
      SameOn (· < c.reg rFREE) c.mem (RAM.run s c).mem ∧ c.reg rFREE ≤ (RAM.run s c).reg rFREE) :
    HGB S s (wregs s) P Q b :=
  HGB.run hs hb fun c hc => ⟨(h c hc).1, (h c hc).2.1,
    { reg := fun _ hr => run_reg_of_not_mem hs hr c, mem := (h c hc).2.2.1,
      free := (h c hc).2.2.2, out := run_out_of_writes hs hw c }⟩

/-- Loop-free code writing registers only. -/
theorem runR (hs : LoopFree s) (hst : stores s = false) (hw : writes s = false)
    (hF : rFREE ∉ wregs s) (hb : size s ≤ b) (h : ∀ c, P c → AddrOK S s c ∧ Q (RAM.run s c)) :
    HGB S s (wregs s) P Q b :=
  HGB.run hs hb fun c hc => ⟨(h c hc).1, (h c hc).2, grow_run hs hst hw hF c⟩

/-- Loop-free code writing registers only, without memory access. -/
theorem runM (hs : LoopFree s) (hm : memFree s = true) (hst : stores s = false)
    (hw : writes s = false) (hF : rFREE ∉ wregs s) (hb : size s ≤ b)
    (h : ∀ c, P c → Q (RAM.run s c)) : HGB S s (wregs s) P Q b :=
  HGB.runR hs hst hw hF hb fun c hc => ⟨AddrOK.of_memFree hm, h c hc⟩

/-- From a bounded triple with the memory frame in its postcondition. -/
theorem ofGhost (hw : writes s = false) (hW : ∀ r ∈ wregs s, r ∈ W)
    (h : ∀ (F₀ : ℕ) (m₀ : ℕ → ℕ), HTB S s (fun c => P c ∧ c.reg rFREE = F₀ ∧ c.mem = m₀)
      (fun c => Q c ∧ SameOn (· < F₀) m₀ c.mem ∧ F₀ ≤ c.reg rFREE) b) : HGB S s W P Q b :=
  fun c₀ => (HTB.grow hw h c₀).post fun _ ⟨hq, hg⟩ => ⟨hq, hg.mono hW⟩

/-- A pure consequence of the precondition. -/
theorem of_pre {p : Prop} (hp : ∀ c, P c → p) (h : p → HGB S s W P Q b) : HGB S s W P Q b :=
  fun c₀ c hc => h (hp c hc.1) c₀ c hc

/-- A ghost value read off the initial configuration. -/
theorem ghost {α : Sort*} (f : Config → α) (h : ∀ v, HGB S s W (fun c => P c ∧ f c = v) Q b) :
    HGB S s W P Q b :=
  fun c₀ c hc => h (f c) c₀ c ⟨⟨hc.1, rfl⟩, hc.2⟩

/-- An existential precondition. -/
theorem exists_pre {α : Sort*} {P : α → Config → Prop} (h : ∀ x, HGB S s W (P x) Q b) :
    HGB S s W (fun c => ∃ x, P x c) Q b :=
  fun c₀ c ⟨⟨x, hx⟩, hc⟩ => h x c₀ c ⟨hx, hc⟩

/-- Branching on a register. -/
theorem ifz {a : ℕ} (h₁ : HGB S s W (fun c => P c ∧ c.reg a = 0) Q b)
    (h₂ : HGB S u W (fun c => P c ∧ c.reg a ≠ 0) Q b) : HGB S (.ifz a s u) W P Q (b + 1) :=
  fun c₀ => HTB.ifz ((h₁ c₀).pre fun _ ⟨⟨hp, hc⟩, ha⟩ => ⟨⟨hp, ha⟩, hc⟩)
    ((h₂ c₀).pre fun _ ⟨⟨hp, hc⟩, ha⟩ => ⟨⟨hp, ha⟩, hc⟩)

/-- `skip`. -/
theorem skip' : HGB S .skip W P P 1 :=
  HGB.run (by decide) le_rfl fun c hc => ⟨trivial, hc, Grow.refl W c⟩

/-- **Counted loop** as a bounded growth triple: the body grows within `W` (which contains the
counter and `rT`). -/
theorem forUp {i n N : ℕ} (Inv : ℕ → Config → Prop) (T : ℕ → ℕ) (hi : i ≠ rT) (hn : n ≠ rT)
    (hin : n ≠ i) (hiF : i ≠ rFREE) (hiW : i ∈ W) (hTW : rT ∈ W)
    (hInv : ∀ j, Indep [i, rT] (Inv j))
    (hbody : ∀ j, j < N → HGB S body W (fun c => Inv j c ∧ c.reg i = j ∧ c.reg n = N)
      (fun c => Inv (j + 1) c ∧ c.reg i = j ∧ c.reg n = N) (T j)) :
    HGB S (RAM.forUp i n body) W (fun c => Inv 0 c ∧ c.reg n = N)
      (fun c => Inv N c ∧ c.reg i = N ∧ c.reg n = N) (∑ j ∈ Finset.range N, (T j + 4) + 3) := by
  intro c₀
  have hV : ∀ r ∈ [i, rT], r ∈ W := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
  have hF : rFREE ∉ [i, rT] := by simp [Ne.symm hiF]
  have h := HTB.forUp (S := S) (i := i) (n := n) (N := N) (body := body)
    (fun j c => Inv j c ∧ Grow W c₀ c) T hi hn hin
    (fun j c c' hA ⟨hI, hg⟩ => ⟨hInv j c c' hA hI, hg.agree hA hV hF⟩) (fun j hj => ?_)
  · refine h.mono ?_ ?_ le_rfl
    · rintro c ⟨⟨hI, hn'⟩, rfl⟩
      exact ⟨⟨hI, Grow.refl W c⟩, hn'⟩
    · rintro c ⟨⟨hI, hg⟩, hi', hn'⟩
      exact ⟨⟨hI, hi', hn'⟩, hg⟩
  · refine HTB.of_forall fun c₁ ⟨⟨hI, hg⟩, hi', hn'⟩ => ?_
    refine (hbody j hj c₁).mono (fun c hc => ?_) ?_ le_rfl
    · subst hc; exact ⟨⟨hI, hi', hn'⟩, rfl⟩
    · rintro c ⟨⟨hI', hi'', hn''⟩, hg'⟩
      exact ⟨⟨hI', hg.trans hg'⟩, hi'', hn''⟩

/-- Counted loop with a constant bound per iteration. -/
theorem forUpC {i n N : ℕ} (Inv : ℕ → Config → Prop) (T : ℕ) (hi : i ≠ rT) (hn : n ≠ rT)
    (hin : n ≠ i) (hiF : i ≠ rFREE) (hiW : i ∈ W) (hTW : rT ∈ W)
    (hInv : ∀ j, Indep [i, rT] (Inv j))
    (hbody : ∀ j, j < N → HGB S body W (fun c => Inv j c ∧ c.reg i = j ∧ c.reg n = N)
      (fun c => Inv (j + 1) c ∧ c.reg i = j ∧ c.reg n = N) T) :
    HGB S (RAM.forUp i n body) W (fun c => Inv 0 c ∧ c.reg n = N)
      (fun c => Inv N c ∧ c.reg i = N ∧ c.reg n = N) (N * (T + 4) + 3) := by
  have := HGB.forUp Inv (fun _ => T) hi hn hin hiF hiW hTW hInv hbody
  simpa [Finset.sum_const, Finset.card_range, smul_eq_mul] using this

/-- Counted loop with a bound `N * (T + 4) + 3 ≤ b`, for `N ≤ M`. -/
theorem forUpCle {i n N : ℕ} (Inv : ℕ → Config → Prop) (T M : ℕ) (hNM : N ≤ M) (hi : i ≠ rT)
    (hn : n ≠ rT) (hin : n ≠ i) (hiF : i ≠ rFREE) (hiW : i ∈ W) (hTW : rT ∈ W)
    (hInv : ∀ j, Indep [i, rT] (Inv j))
    (hbody : ∀ j, j < N → HGB S body W (fun c => Inv j c ∧ c.reg i = j ∧ c.reg n = N)
      (fun c => Inv (j + 1) c ∧ c.reg i = j ∧ c.reg n = N) T) :
    HGB S (RAM.forUp i n body) W (fun c => Inv 0 c ∧ c.reg n = N)
      (fun c => Inv N c ∧ c.reg i = N ∧ c.reg n = N) (M * (T + 4) + 3) :=
  (HGB.forUpC Inv T hi hn hin hiF hiW hTW hInv hbody).weaken
    (by have := Nat.mul_le_mul_right (T + 4) hNM; omega)

end HGB

/-! ### Growth triples bounding the free pointer -/

/-- A bounded growth triple whose run moves the free pointer up by at most `m`, for every bound
`S` leaving room for these `m` cells above the initial free pointer. -/
def HGMB (S : ℕ) (s : Stmt) (W : List ℕ) (P Q : Config → Prop) (b m : ℕ) : Prop :=
  ∀ F₀, F₀ + m ≤ S →
    HGB S s W (fun c => P c ∧ c.reg rFREE = F₀) (fun c => Q c ∧ c.reg rFREE ≤ F₀ + m) b

namespace HGMB

variable {S : ℕ} {s u : Stmt} {W W' : List ℕ} {P P' Q Q' R F : Config → Prop}
  {b b' b₁ b₂ m m' m₁ m₂ : ℕ}

/-- The bounded triple with the bound of the free pointer in its postcondition. -/
theorem bound (h : HGMB S s W P Q b m) (c₀ : Config) (hS : c₀.reg rFREE + m ≤ S) :
    HTB S s (fun c => P c ∧ c = c₀)
      (fun c => Q c ∧ Grow W c₀ c ∧ c.reg rFREE ≤ c₀.reg rFREE + m) b := fun c ⟨hp, hc⟩ => by
  obtain ⟨c', t, he, ⟨⟨hq, hf⟩, hg⟩, ht⟩ := h (c₀.reg rFREE) hS c₀ c ⟨⟨hp, hc ▸ rfl⟩, hc⟩
  exact ⟨c', t, he, ⟨hq, hg, hf⟩, ht⟩

theorem seq (h₁ : HGMB S s W P R b₁ m₁) (h₂ : HGMB S u W R Q b₂ m₂) :
    HGMB S (.seq s u) W P Q (b₁ + b₂) (m₁ + m₂) := by
  intro F₀ hS c₀ c hc
  obtain ⟨c₁, t₁, he₁, ⟨⟨hr, hle⟩, hg₁⟩, ht₁⟩ := h₁ F₀ (by omega) c₀ c hc
  obtain ⟨c₂, t₂, he₂, ⟨⟨hq, hle₂⟩, hg₂⟩, ht₂⟩ :=
    h₂ (c₁.reg rFREE) (by omega) c₁ c₁ ⟨⟨hr, rfl⟩, rfl⟩
  exact ⟨c₂, t₁ + t₂, ExecB.seq he₁ he₂, ⟨⟨hq, by omega⟩, hg₁.trans hg₂⟩, by omega⟩

theorem mono (h : HGMB S s W P Q b m) (hW : ∀ r ∈ W, r ∈ W') (hP : ∀ c, P' c → P c)
    (hQ : ∀ c, Q c → Q' c) (hb : b ≤ b') (hm : m ≤ m') : HGMB S s W' P' Q' b' m' :=
  fun F₀ hS => (h F₀ (by omega)).mono hW (fun c ⟨hp, hf⟩ => ⟨hP c hp, hf⟩)
    (fun c ⟨hq, hf⟩ => ⟨hQ c hq, by omega⟩) hb

theorem weaken (h : HGMB S s W P Q b m) (hb : b ≤ b') (hm : m ≤ m') : HGMB S s W P Q b' m' :=
  h.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) hb hm

theorem pre (h : HGMB S s W P Q b m) (hP : ∀ c, P' c → P c) : HGMB S s W P' Q b m :=
  h.mono (fun _ h => h) hP (fun _ h => h) le_rfl le_rfl

theorem post (h : HGMB S s W P Q b m) (hQ : ∀ c, Q c → Q' c) : HGMB S s W P Q' b m :=
  h.mono (fun _ h => h) (fun _ h => h) hQ le_rfl le_rfl

/-- The frame rule for assertions surviving `Grow`. -/
theorem frame (h : HGMB S s W P Q b m) (hF : Stable W F) :
    HGMB S s W (fun c => P c ∧ F c) (fun c => Q c ∧ F c) b m := fun F₀ hS =>
  ((h F₀ hS).frame (F := F) hF).mono (fun _ h => h) (fun _ ⟨⟨hp, hf⟩, hF⟩ => ⟨⟨hp, hF⟩, hf⟩)
    (fun _ ⟨⟨hq, hf⟩, hF⟩ => ⟨⟨hq, hF⟩, hf⟩) le_rfl

/-- A program not writing the free pointer (its accesses may use `rFREE ≤ S`). -/
theorem zero (h : HGB S s W (fun c => P c ∧ c.reg rFREE ≤ S) Q b) (hF : rFREE ∉ wregs s) :
    HGMB S s W P Q b 0 := by
  intro F₀ hS c₀ c ⟨⟨hp, hf⟩, hc⟩
  obtain ⟨c', t, he, ⟨hq, hg⟩, ht⟩ := h c₀ c ⟨⟨hp, by omega⟩, hc⟩
  exact ⟨c', t, he, ⟨⟨hq, by rw [he.frame.reg rFREE hF]; omega⟩, hg⟩, ht⟩

/-- Loop-free code without memory access, not writing the free pointer. -/
theorem zeroRun (hs : LoopFree s) (hm : memFree s = true) (hb : size s ≤ b)
    (h : ∀ c, P c → Q (RAM.run s c) ∧ Grow W c (RAM.run s c)) (hF : rFREE ∉ wregs s) :
    HGMB S s W P Q b 0 :=
  HGMB.zero (HGB.run hs hb fun c hc => ⟨AddrOK.of_memFree hm, h c hc.1⟩) hF

/-- From a bounded triple with the memory frame and the bound of the free pointer in its
postcondition. -/
theorem ofGhost (hw : writes s = false) (hW : ∀ r ∈ wregs s, r ∈ W)
    (h : ∀ (F₀ : ℕ) (m₀ : ℕ → ℕ), F₀ + m ≤ S →
      HTB S s (fun c => P c ∧ c.reg rFREE = F₀ ∧ c.mem = m₀)
        (fun c => Q c ∧ SameOn (· < F₀) m₀ c.mem ∧ F₀ ≤ c.reg rFREE ∧ c.reg rFREE ≤ F₀ + m) b) :
    HGMB S s W P Q b m := fun F₀ hS =>
  HGB.ofGhost hw hW fun F₁ m₀ => HTB.of_forall fun c ⟨⟨hp, hf⟩, h1, h2⟩ => by
    have e : F₁ = F₀ := h1.symm.trans hf
    exact (h F₁ m₀ (by omega)).mono (fun c' hc' => by subst hc'; exact ⟨hp, h1, h2⟩)
      (fun _ ⟨hq, hs, hF, hle⟩ => ⟨⟨hq, by omega⟩, hs, hF⟩) le_rfl

/-- A bounded growth triple whose pre- and postcondition bound the growth of the free
pointer (its accesses may use `rFREE + m ≤ S`). -/
theorem ofHG (m : ℕ) (h : HGB S s W (fun c => P c ∧ c.reg rFREE + m ≤ S) Q b)
    (hm : ∀ c c', P c → Q c' → c'.reg rFREE ≤ c.reg rFREE + m) : HGMB S s W P Q b m := by
  intro F₀ hS c₀ c ⟨⟨hp, hf⟩, hc⟩
  obtain ⟨c', t, he, ⟨hq, hg⟩, ht⟩ := h c₀ c ⟨⟨hp, by omega⟩, hc⟩
  exact ⟨c', t, he, ⟨⟨hq, by have := hm c c' hp hq; omega⟩, hg⟩, ht⟩

/-- A ghost value read off the initial configuration. -/
theorem ghost {α : Sort*} (f : Config → α) (h : ∀ v, HGMB S s W (fun c => P c ∧ f c = v) Q b m) :
    HGMB S s W P Q b m :=
  fun F₀ hS c₀ c hc => h (f c) F₀ hS c₀ c ⟨⟨⟨hc.1.1, rfl⟩, hc.1.2⟩, hc.2⟩

/-- A pure consequence of the precondition. -/
theorem of_pre {p : Prop} (hp : ∀ c, P c → p) (h : p → HGMB S s W P Q b m) : HGMB S s W P Q b m :=
  fun F₀ hS c₀ c hc => h (hp c hc.1.1) F₀ hS c₀ c hc

end HGMB

/-! ### The counting sort -/

/-- **The stable counting sort** as a bounded growth triple (`2 K + 1 + |keys|` fresh cells, from
`csort_specB`). -/
theorem csort_specMB {S : ℕ} (keys : List ℕ) (K : ℕ) (hK : ∀ x ∈ keys, x < K) :
    HGMB S csort (wregs csort) (CsIn keys K)
      (fun c => CsOut keys K c ∧ ZeroFrom c.mem (c.reg rFREE))
      (28 * keys.length + 15 * K + 20) (2 * K + 1 + keys.length) :=
  HGMB.ofGhost (by decide) (fun _ h => h) fun F₀ m₀ hS =>
    (csort_specB keys K hK F₀ m₀ (S := S) (by omega)).post
      fun _ ⟨h, hs, hF, _⟩ => ⟨h, hs, by omega, by omega⟩

/-! ### Gathering -/

theorem gaBody_spec {S : ℕ} (idx F : List ℕ) (hidx : ∀ i ∈ idx, i < F.length) (F₀ : ℕ)
    (m₀ : ℕ → ℕ) (hS : F₀ + idx.length ≤ S) (j : ℕ) (hj : j < idx.length) :
    HTB S gaBody (fun c => GaInv idx F F₀ m₀ j c ∧ c.reg rGJ = j ∧ c.reg rGL = idx.length)
      (fun c => GaInv idx F F₀ m₀ (j + 1) c ∧ c.reg rGJ = j ∧ c.reg rGL = idx.length) 6 := by
  refine HTB.run_le (by decide) (by decide) fun c hc => ?_
  obtain ⟨⟨hl, hi, hf, hbi, hbf, ho, hfr, hout, hz, hs⟩, hj', -⟩ := hc
  have h1 : c.mem (c.reg rGI + j) = idx[j] := hi.get hj
  have hlt := hidx _ (List.getElem_mem hj)
  have h2 : c.mem (c.reg rGF + idx[j]) = F.getD idx[j] 0 := hf.getD hlt
  have htake : (idx.take (j + 1)).map (fun i => F.getD i 0) =
      (idx.take j).map (fun i => F.getD i 0) ++ [F.getD idx[j] 0] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.map_append,
      List.map_singleton]
  refine ⟨by addr_ok [gaBody, hj', h1, ho], ?_⟩
  simp only [gaBody, run_seq', run_ld, run_st (show rGX ≠ rT by decide)]
  simp +decide only [setReg_reg, ↓reduceIte, setReg_mem, hj', h1, h2, ho]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simpa +decide using hl
  · simpa +decide using hi.upd_of_disjoint (by omega)
  · simpa +decide using hf.upd_of_disjoint (by omega)
  · simpa +decide using hbi
  · simpa +decide using hbf
  · simpa +decide using ho
  · simpa +decide using hfr
  · rw [htake]; exact hout.upd_snoc (by simp; omega)
  · exact hz.upd (by omega)
  · exact hs.upd_of_ge (by omega) _
  · simpa +decide using hj'
  · simpa +decide using hl

/-- **Gathering** `idx.map (F.getD · 0)` into a fresh array (`|idx|` fresh cells). -/
theorem gather_spec {S : ℕ} (idx F : List ℕ) (hidx : ∀ i ∈ idx, i < F.length) :
    HGMB S gather (wregs gather) (GaIn idx F)
      (fun c => ArrAt rGO (idx.map fun i => F.getD i 0) c ∧ ZeroFrom c.mem (c.reg rFREE))
      (idx.length * 10 + 6) idx.length := by
  refine HGMB.ofGhost (by decide) (fun _ h => h) (fun F₀ m₀ hS => ?_)
  have h₀ : HTB S (alloc rGO rGL) (fun c => GaIn idx F c ∧ c.reg rFREE = F₀ ∧ c.mem = m₀)
      (fun c => GaInv idx F F₀ m₀ 0 c ∧ c.reg rGL = idx.length) 3 := by
    refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hc, hF, hm⟩ => ?_
    rw [run_alloc (by decide) (by decide)]
    have := hc.ai.2
    have := hc.af.2
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals simp +decide only [setReg_reg, ↓reduceIte, setReg_mem, hF, hm, hc.ln, List.take_zero,
      List.map_nil, arr_nil]
    · exact hm ▸ hc.ai.1
    · exact hm ▸ hc.af.1
    · omega
    · omega
    · exact hm ▸ hc.free.mono (by omega)
    · exact SameOn.refl _ _
  have hl := HTB.forUpC (i := rGJ) (n := rGL) (N := idx.length) (body := gaBody)
    (GaInv idx F F₀ m₀) 6 (by decide) (by decide) (by decide) (fun j => by indep [GaInv])
    (fun j hj => gaBody_spec idx F hidx F₀ m₀ hS j hj)
  refine (h₀.seq hl).mono (fun _ h => h) ?_ (by omega)
  rintro c ⟨⟨-, -, -, -, -, ho, hfr, hout, hz, hs⟩, -, -⟩
  rw [List.take_length] at hout
  refine ⟨⟨⟨by rw [ho]; exact hout, by simp; omega⟩, by rw [hfr]; exact hz⟩, hs, by omega, by omega⟩

end STACS2027.RAM.P1
