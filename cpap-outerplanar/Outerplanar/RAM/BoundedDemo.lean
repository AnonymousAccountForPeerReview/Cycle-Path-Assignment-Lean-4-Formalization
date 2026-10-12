module

public import Outerplanar.RAM.BoundedLib
import Mathlib.Tactic

/-!
# Demonstration: a complete program within linear space

A complete program (`EchoDemo.echo`) with its `ComputesIn` theorem: time and space are stated
together, the space being the length of the input.

The port of phase R1 that was first done here (validating the workflow of `GUIDE-SPACE.md`) now
lives in place in `R1Prog.lean`, `R1Dfs.lean` and `R1.lean` (`R1.r1_spec`): there the
memory-free blocks are lifted by `HTB.of_HT rfl`, the loop-free blocks with memory access by
`HTB.of_HT_addrOK` (or inline in `HTB.run_le`), the address proofs of the depth-first search
are split into one lemma `foo_addrOK` per sub-block `foo` (`dfsBody_addrOK`), and the layout
enters `omega` through `fits` (one inequality per region).
-/

@[expose] public section

/-! ### End to end: a complete program with `ComputesIn` -/

namespace STACS2027.RAM.EchoDemo

/-- Loop counter. -/
abbrev rI : ℕ := 100
/-- Address of the current entry. -/
abbrev rP : ℕ := 101
/-- The current entry. -/
abbrev rX : ℕ := 102
/-- The number of entries. -/
abbrev rN : ℕ := 103

/-- Output entry `rI + 1` of the input. -/
def body : Stmt := .seq (addc rP rI 1) (.seq (.load rX rP) (.write rX))

/-- On the input `n :: xs` (`n = |xs|`), output `xs`. -/
def echo : Stmt := .seq (.load rN rZERO) (forUp rI rN body)

/-- After `j` iterations: the memory is the initial one, the output is `xs.take j`. -/
def Inv (xs : List ℕ) (j : ℕ) (c : Config) : Prop :=
  c.mem = (initial (xs.length :: xs)).mem ∧ c.out = xs.take j

theorem body_spec (xs : List ℕ) (j : ℕ) (hj : j < xs.length) :
    HTB (xs.length + 1) body (fun c => Inv xs j c ∧ c.reg rI = j ∧ c.reg rN = xs.length)
      (fun c => Inv xs (j + 1) c ∧ c.reg rI = j ∧ c.reg rN = xs.length) 4 :=
  HTB.run_le (by decide) (by decide) fun c ⟨⟨hm, ho⟩, hi, hn⟩ => by
    refine ⟨by addr_ok [body, hi], ?_⟩
    have hx : c.mem (j + 1) = xs[j] := by
      rw [hm, initial_mem, List.getD_cons_succ, getD_eq_getElem' hj]
    refine ⟨⟨(run_mem_of_stores (by decide) rfl c).trans hm, ?_⟩, ?_, ?_⟩
    · simp only [body, run_seq', run_addc (show rI ≠ rT by decide), run_load, run_write, emit_out,
        setReg_out, setReg_reg, setReg_mem, ↓reduceIte]
      rw [hi, hx, ho, List.take_add_one, List.getElem?_eq_getElem hj]
      rfl
    · simp +decide [body, run_addc, hi]
    · simp +decide [body, run_addc, hn]

/-- **`echo` within linear time and the space of its input**: on `|xs| :: xs` it outputs `xs`
within `8 |xs| + 4` steps, accessing only the input cells `0, …, |xs|`. -/
theorem echo_computesIn (xs : List ℕ) :
    ∃ t, t ≤ 8 * xs.length + 4 ∧ ComputesIn echo (xs.length :: xs) xs t (xs.length + 1) := by
  apply HTB.computesIn
  have h0 : HTB (xs.length + 1) (.load rN rZERO) (fun c => c = initial (xs.length :: xs))
      (fun c => Inv xs 0 c ∧ c.reg rN = xs.length) 1 :=
    HTB.run_le (by decide) (by decide) fun c hc => by
      subst hc
      exact ⟨by addr_ok [initial_reg], ⟨rfl, by simp⟩, by simp [initial_mem]⟩
  have hl := HTB.forUpC (i := rI) (n := rN) (N := xs.length) (body := body) (Inv xs) 4
    (by decide) (by decide) (by decide) (fun j => by indep [Inv]) (fun j hj => body_spec xs j hj)
  exact (h0.seq hl).mono (fun _ h => h) (fun c ⟨⟨_, ho⟩, _⟩ => by rw [ho, List.take_length])
    (by omega)

end STACS2027.RAM.EchoDemo
