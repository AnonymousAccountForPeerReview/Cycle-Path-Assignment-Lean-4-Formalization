module

public import Outerplanar.RAM.Poly2Spec
public import Outerplanar.RAM.Poly1Grow
import Mathlib.Tactic

/-!
# Phase P2 of the polygon solver: streams, growth-triple rules and copying

Phase P2 builds its data by pushing values at the free pointer. This file provides:

* `Strm q out c`: the list `out` stored at `q` and ending at the free pointer (zeros above);
  `Bel b l c`: the list `l` stored at `b` below the free pointer (it survives every growth,
  `stable_bel`);
* `run_push`, `push_strm`: pushing a register onto the stream;
* (the bounded growth triples `P1.HGB` of `Poly1Grow.lean` compose the stages);
* `copy`: push the `reg rCL` entries starting at `reg rCS` (`copy_spec`, for a bound `S` above
  the end of the stream).
-/

@[expose] public section

namespace STACS2027.RAM.P2

open P1

/-! ### Streams -/

/-- The stream at `q`: the list `out` at `q`, ending at the free pointer, zeros above. -/
def Strm (q : ℕ) (out : List ℕ) (c : Config) : Prop :=
  Arr c.mem q out ∧ c.reg rFREE = q + out.length ∧ ZeroFrom c.mem (c.reg rFREE)

/-- The list `l` at `b`, below the free pointer. -/
def Bel (b : ℕ) (l : List ℕ) (c : Config) : Prop := Arr c.mem b l ∧ b + l.length ≤ c.reg rFREE

theorem stable_bel (W : List ℕ) (b : ℕ) (l : List ℕ) : Stable W (Bel b l) :=
  fun _ _ h hg => ⟨hg.arr' h.1 h.2, by have := hg.free; have := h.2; omega⟩

theorem Strm.bel {q : ℕ} {out : List ℕ} {c : Config} (h : Strm q out c) : Bel q out c :=
  ⟨h.1, by rw [h.2.1]⟩

theorem Bel.mono {b : ℕ} {l : List ℕ} {c c' : Config} (h : Bel b l c) (hm : c'.mem = c.mem)
    (hf : c.reg rFREE ≤ c'.reg rFREE) : Bel b l c' :=
  ⟨by rw [hm]; exact h.1, by have := h.2; omega⟩

theorem Bel.sub {b : ℕ} {l₁ l₂ l₃ : List ℕ} {c : Config} (h : Bel b (l₁ ++ l₂ ++ l₃) c) :
    Bel (b + l₁.length) l₂ c := by
  obtain ⟨h1, h2⟩ := h
  rw [arr_append, arr_append] at h1
  exact ⟨h1.1.2, by simp only [List.length_append] at h2; omega⟩

theorem Bel.get {b : ℕ} {l : List ℕ} {c : Config} (h : Bel b l c) {i : ℕ} (hi : i < l.length) :
    c.mem (b + i) = l[i] := h.1.get hi

theorem Bel.cons {b x : ℕ} {l : List ℕ} {c : Config} (h : Bel b (x :: l) c) :
    c.mem b = x ∧ Bel (b + 1) l c := by
  obtain ⟨h1, h2⟩ := h
  rw [arr_cons] at h1
  exact ⟨h1.1, h1.2, by simp only [List.length_cons] at h2; omega⟩

theorem take_succ_eq {α : Type*} {l : List α} {j : ℕ} (hj : j < l.length) :
    l.take (j + 1) = l.take j ++ [l[j]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]

/-! ### Pushing -/

theorem run_push (v : ℕ) (c : Config) :
    RAM.run (push v) c =
      ((c.setMem (c.reg rFREE) (c.reg v)).setReg rT 1).setReg rFREE (c.reg rFREE + 1) := by
  simp [push, run_inc]

theorem push_strm {q : ℕ} {out : List ℕ} {c : Config} (h : Strm q out c) (v : ℕ) :
    Strm q (out ++ [c.reg v]) (RAM.run (push v) c) := by
  rw [run_push]
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simpa only [setReg_mem, setMem_mem_upd] using h1.upd_snoc (by omega)
  · simp +decide only [setReg_reg, ↓reduceIte, List.length_append, List.length_singleton]
    omega
  · simp +decide only [setReg_reg, ↓reduceIte, setReg_mem, setMem_mem_upd]
    exact (h3.mono (by omega)).upd (by omega)

/-! ### Growth -/

theorem grow_agree {W V : List ℕ} {c₀ c c' : Config} (h : Grow W c₀ c) (hA : Agree V c c')
    (hV : ∀ r ∈ V, r ∈ W) (hF : rFREE ∉ V) : Grow W c₀ c' where
  reg r hr := by rw [hA.reg r fun h' => hr (hV r h')]; exact h.reg r hr
  mem := by rw [hA.mem]; exact h.mem
  free := by rw [hA.reg rFREE hF]; exact h.free
  out := by rw [hA.out]; exact h.out

/-- A loop-free run storing only at or above the free pointer and not lowering it. -/
theorem grow_run_of {s : Stmt} (hs : LoopFree s) (hw : writes s = false) {c : Config}
    (hm : SameOn (· < c.reg rFREE) c.mem (RAM.run s c).mem)
    (hf : c.reg rFREE ≤ (RAM.run s c).reg rFREE) : Grow (wregs s) c (RAM.run s c) where
  reg _ hr := run_reg_of_not_mem hs hr c
  mem := hm
  free := hf
  out := run_out_of_writes hs hw c

/-- A growth from an agreement. -/
theorem grow_of_agree {W V : List ℕ} {c c' : Config} (hA : Agree V c c') (hV : ∀ r ∈ V, r ∈ W)
    (hF : rFREE ∉ V) : Grow W c c' :=
  grow_agree (Grow.refl W c) hA hV hF

/-- The stream does not depend on registers other than the free pointer. -/
theorem strm_agree {W : List ℕ} {q : ℕ} {out : List ℕ} {c c' : Config} (hA : Agree W c c')
    (hF : rFREE ∉ W) (h : Strm q out c) : Strm q out c' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [hA.mem]; exact h1
  · rw [hA.reg _ hF]; exact h2
  · rw [hA.mem, hA.reg _ hF]; exact h3

theorem push_grow (v : ℕ) (c : Config) : Grow [rT, rFREE] c (RAM.run (push v) c) where
  reg r hr := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [run_push]; simp [hr.1, hr.2]
  mem := by
    rw [run_push]
    simp only [setReg_mem, setMem_mem_upd]
    exact SameOn.upd_of_ge (SameOn.refl _ _) le_rfl _
  free := by rw [run_push]; simp
  out := by rw [run_push]; simp

theorem push_reg (v : ℕ) (c : Config) {r : ℕ} (h1 : r ≠ rT) (h2 : r ≠ rFREE) :
    (RAM.run (push v) c).reg r = c.reg r :=
  (push_grow v c).reg r (by simp [h1, h2])

/-- `stab` proves `Stable W F` for conjunctions of register equations (registers outside `W`,
checked by `decide`) and `Bel` facts. -/
macro "stab" : tactic => `(tactic| (repeat' (first | apply stable_bel | apply Stable.regEq |
  apply Stable.and)) <;> decide)


/-! ### Copying -/

/-- Argument: the source address. -/
abbrev rCS : ℕ := 116
/-- Argument: the number of entries. -/
abbrev rCL : ℕ := 117
/-- Counter. -/
abbrev rCJ : ℕ := 118
/-- Temporary. -/
abbrev rCX : ℕ := 119

/-- One entry: push `mem[reg rCS + reg rCJ]`. -/
def cpBody : Stmt := .seq (ld rCX rCS rCJ) (push rCX)
/-- **Copy** the `reg rCL` entries at `reg rCS` onto the stream. -/
def copy : Stmt := forUp rCJ rCL cpBody

/-- The invariant of the copy loop. -/
def CpInv (q src : ℕ) (out l : List ℕ) (j : ℕ) (c : Config) : Prop :=
  Strm q (out ++ l.take j) c ∧ Bel src l c ∧ c.reg rCS = src

theorem cpBody_spec {S : ℕ} (q src : ℕ) (out l : List ℕ) (hS : q + (out ++ l).length ≤ S) (j : ℕ)
    (hj : j < l.length) :
    HGB S cpBody (wregs copy)
      (fun c => CpInv q src out l j c ∧ c.reg rCJ = j ∧ c.reg rCL = l.length)
      (fun c => CpInv q src out l (j + 1) c ∧ c.reg rCJ = j ∧ c.reg rCL = l.length) 5 := by
  refine (HGB.runG (s := cpBody) (by decide) (by decide) (by decide) fun c hc => ?_).mono
    (by decide) (fun _ h => h) (fun _ h => h) le_rfl
  obtain ⟨⟨hS', hB, hcs⟩, hj', hl⟩ := hc
  have hfr0 := hS'.2.1
  have hb2 := hB.2
  simp only [List.length_append, List.length_take] at hS hfr0 hb2
  refine ⟨by addr_ok [cpBody, push, hcs, hj'], ?_⟩
  have hS := hS'
  set c₁ := c.setReg rCX (c.mem (c.reg rCS + c.reg rCJ)) with hc₁
  have hx : c₁.reg rCX = l[j] := by simp [hc₁, hcs, hj', hB.get hj]
  have hS₁ : Strm q (out ++ l.take j) c₁ := by
    obtain ⟨h1, h2, h3⟩ := hS
    exact ⟨by simpa [hc₁] using h1, by simpa [hc₁] using h2, by simpa [hc₁] using h3⟩
  have hrun : RAM.run cpBody c = RAM.run (push rCX) c₁ := by simp [cpBody, hc₁]
  have hS₂ := push_strm hS₁ rCX
  rw [hx, List.append_assoc, ← take_succ_eq hj] at hS₂
  rw [hrun]
  have hfr : c₁.reg rFREE = c.reg rFREE := by simp [hc₁]
  have hmem : c₁.mem = c.mem := by simp [hc₁]
  refine ⟨⟨⟨hS₂, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [run_push]
      simpa only [setReg_mem, setMem_mem_upd, hmem] using
        hB.1.upd_of_disjoint (a := c₁.reg rFREE) (v := c₁.reg rCX) (by have := hB.2; omega)
    · rw [run_push]
      simp +decide only [setReg_reg, ↓reduceIte, hfr]
      have := hB.2; omega
  all_goals rw [run_push]; simp +decide [hc₁, hcs, hj', hl]
  · exact SameOn.upd_of_ge (SameOn.refl _ _) le_rfl _

/-- **Copying** `l` from `src` onto the stream. -/
theorem copy_spec {S : ℕ} (q src : ℕ) (out l : List ℕ) (hS : q + (out ++ l).length ≤ S) :
    HGB S copy (wregs copy)
      (fun c => Strm q out c ∧ Bel src l c ∧ c.reg rCS = src ∧ c.reg rCL = l.length)
      (fun c => Strm q (out ++ l) c) (l.length * 9 + 3) := by
  have h := HGB.forUpC (W := wregs copy) (i := rCJ) (n := rCL) (N := l.length) (body := cpBody)
    (CpInv q src out l) 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun j => by indep [CpInv, Strm, Bel]) (fun j hj => cpBody_spec q src out l hS j hj)
  exact h.mono (fun _ h => h) (fun c ⟨hS, hB, hcs, hcl⟩ => ⟨⟨by simpa using hS, hB, hcs⟩, hcl⟩)
    (fun c ⟨⟨hS, _, _⟩, _, _⟩ => by simpa using hS) le_rfl

end STACS2027.RAM.P2
