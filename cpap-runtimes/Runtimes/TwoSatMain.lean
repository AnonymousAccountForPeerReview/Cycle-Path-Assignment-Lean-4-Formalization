module

public import Runtimes.TwoSatPhase
import Mathlib.Tactic

/-!
# Linear-time 2-SAT on the RAM: the standalone machine

**Input encoding** (`twoSatInput n f`): the list `n :: m :: codes f`, where `m = |f|` is the
number of clauses and `codes f` lists, clause after clause, the codes
`code l = 2 · var + (if positive then 0 else 1)` of the two literals of each clause.

**Output**: `[0]` if `f` is unsatisfiable; otherwise `1` followed by the `n` bits (`0`/`1`)
of a satisfying assignment of the variables `0, …, n - 1`.

`twoSatMain` reads `n`, `m` into `tN`, `tM`, points `tCL` at the codes (cell `2`), sets
`rFREE := 2m + 2` (the end of the input), runs the 2-SAT phase `twoSat` and writes the flag and,
if it is `1`, the assignment. `twoSatMain_spec`: the output is exactly
`if okB n (codes f) then 1 :: asgBits n (codes f) else [0]`, within `CM · (n + m + 1)` steps
(`CM = 720`), accessing only the addresses below any `S ≥ spaceM n f` (the input and the arrays
of the 2-SAT phase, `spaceM_le`: at most `21 (n + m + 1)` cells). `twoSat_computes` restates it
with `RAM.ComputesIn` (time and space `CM · (n + m + 1)`) and the semantics.
-/

@[expose] public section

namespace STACS2027.Runtimes.TwoSat

open STACS2027.RAM Complexity.SAT

variable {S : ℕ}

/-- The input of the machine: `n`, the number of clauses, and the literal codes. -/
def twoSatInput (n : ℕ) (f : CNF) : List ℕ := n :: f.length :: codes f

/-- Reading the input: `tN := mem[0]`, `tM := mem[1]`, `tCL := 2`, `rFREE := 2m + 2`. -/
def mainInit : Stmt :=
  .seq (.load tN rZERO) (.seq (.const sX 1) (.seq (.load tM sX) (.seq (.const tCL 2)
    (.seq (.add rFREE tM tM) (addc rFREE rFREE 2)))))

/-- Writing one bit of the assignment. -/
def outLoopBody : Stmt := .seq (ld sX tAS sI) (.write sX)

/-- Writing the answer: the flag, then the bits if the flag is `1`. -/
def mainOut : Stmt := .seq (.write tOK) (.ifz tOK .skip (forUp sI tN outLoopBody))

/-- **The standalone 2-SAT machine.** -/
def twoSatMain : Stmt := .seq mainInit (.seq twoSat mainOut)

/-- The constant of its running time. -/
def CM : ℕ := 720

/-- The memory of the machine: the input (`2m + 2` cells) and the arrays of the 2-SAT phase. -/
def spaceM (n : ℕ) (f : CNF) : ℕ := endL n f.length (2 * f.length + 2)

/-- The memory of the machine is linear. -/
theorem spaceM_le (n : ℕ) (f : CNF) : spaceM n f ≤ 21 * (n + f.length + 1) := by
  have := endL_le n f.length (2 * f.length + 2); unfold spaceM; omega

section main

variable {n : ℕ} {f : CNF}

theorem mainInit_spec (hf : IsTwoCNF n f) (hSp : 2 ≤ S) :
    HTB S mainInit (fun c => c = initial (twoSatInput n f))
      (fun c => TwoSatIn n f.length (codes f) c ∧ c.out = [] ∧ c.reg rFREE = 2 * f.length + 2) 9 :=
    HTB.of_HT_addrOK (by decide) (fun c hc => by subst hc; addr_ok [mainInit, initial_reg]) <| by
  refine HT.run_le (by decide) (by decide) fun c hc => ?_
  subst hc
  have hlen := length_codes hf
  have hA : Arr (initial (twoSatInput n f)).mem 0 (n :: f.length :: codes f) := arr_initial _
  have hZ := zeroFrom_initial (twoSatInput n f)
  rw [arr_cons, arr_cons] at hA
  have h0 : (initial (twoSatInput n f)).mem 0 = n := hA.1
  have h1 : (initial (twoSatInput n f)).mem 1 = f.length := hA.2.1
  have hlenI : (twoSatInput n f).length = 2 * f.length + 2 := by
    simp [twoSatInput, hlen]
  rw [hlenI] at hZ
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp +decide [mainInit, run_addc, h0]
  · simp +decide [mainInit, run_addc, h1]
  · have hm : (run mainInit (initial (twoSatInput n f))).mem = (initial (twoSatInput n f)).mem :=
      run_mem_of_stores (by decide) rfl _
    rw [hm]
    simpa +decide [mainInit, run_addc] using hA.2.2
  · have hm : (run mainInit (initial (twoSatInput n f))).mem = (initial (twoSatInput n f)).mem :=
      run_mem_of_stores (by decide) rfl _
    rw [hm]
    have : (run mainInit (initial (twoSatInput n f))).reg rFREE = 2 * f.length + 2 := by
      simp +decide [mainInit, run_addc, h1]; ring
    rw [this]; exact hZ
  · simp +decide [mainInit, run_addc, h1, hlen]; omega
  · exact run_out_of_writes (by decide) rfl _
  · simp +decide [mainInit, run_addc, h1]; ring

/-- The invariant of the bit-writing loop after `j` bits. -/
def BitInv (bits : List ℕ) (A : ℕ) (j : ℕ) (c : Config) : Prop :=
  c.reg tAS = A ∧ Arr c.mem A bits ∧ c.out = 1 :: bits.take j

theorem mainOut_spec (bits : List ℕ) (hbl : bits.length = n) (A : ℕ) (b : Bool) (hA : A + n ≤ S) :
    HTB S mainOut (fun c => c.reg tOK = (if b then 1 else 0) ∧ c.reg tN = n ∧ c.reg tAS = A ∧
        Arr c.mem A bits ∧ c.out = [])
      (fun c => c.out = if b then 1 :: bits else [0]) (2 + (n * 7 + 3) + 1) := by
  have hw : HTB S (.write tOK) (fun c => c.reg tOK = (if b then 1 else 0) ∧ c.reg tN = n ∧
      c.reg tAS = A ∧ Arr c.mem A bits ∧ c.out = [])
      (fun c => c.reg tOK = (if b then 1 else 0) ∧ c.reg tN = n ∧ c.reg tAS = A ∧
        Arr c.mem A bits ∧ c.out = [if b then 1 else 0]) 1 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨h1, h2, h3, h4, h5⟩ => by
      simp [h1, h2, h3, h4, h5]
  have hbody : ∀ j < n, HTB S outLoopBody (fun c => BitInv bits A j c ∧ c.reg sI = j ∧ c.reg tN = n)
      (fun c => BitInv bits A (j + 1) c ∧ c.reg sI = j ∧ c.reg tN = n) 3 := by
    intro j hj
    refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hA', hM, ho⟩, hi, hn⟩ => ?_
    have hx := hM.get (i := j) (by omega)
    refine ⟨by addr_ok [outLoopBody, hA', hi], ⟨by simp +decide [outLoopBody, hA'],
      by simpa [outLoopBody] using hM, ?_⟩,
      by simp +decide [outLoopBody, hi], by simp +decide [outLoopBody, hn]⟩
    simp only [outLoopBody, run_seq', run_ld, run_write, emit_out, setReg_out, ho,
      List.cons_append, setReg_reg]
    simp +decide only [↓reduceIte, hA', hi, hx, List.take_add_one, List.getElem?_eq_getElem
      (show j < bits.length by omega), Option.toList_some]
  refine (hw.seq (HTB.ifz (b := n * 7 + 3) ?_ ?_)).weaken (by omega)
  · refine (HTB.run_le (s := .skip) (by decide) (by decide : size Stmt.skip ≤ 1)
      fun c ⟨⟨h1, _, _, _, h5⟩, h0⟩ => ⟨trivial, ?_⟩).weaken (by omega)
    cases b
    · simpa using h5
    · simp at h1; omega
  · cases b
    · exact HTB.of_false fun c ⟨⟨h1, _⟩, h0⟩ => h0 (by simpa using h1)
    · have hl := HTB.forUpC (i := sI) (n := tN) (N := n) (body := outLoopBody) (BitInv bits A) 3
        (by decide) (by decide) (by decide) (fun j => by indep [BitInv]) hbody
      refine (hl.pre fun c ⟨⟨_, hn, hA, hM, ho⟩, _⟩ => ⟨⟨hA, hM, by simpa using ho⟩, hn⟩).post
        fun c ⟨⟨_, _, ho⟩, _, _⟩ => ?_
      rw [ho, ← hbl, List.take_length]; rfl

/-- **The standalone 2-SAT machine**: on the input `twoSatInput n f` of a 2-CNF `f` over the
variables `0, …, n - 1`, `twoSatMain` halts within `CM · (n + |f| + 1)` steps with output
`1 :: asgBits n (codes f)` if `okB n (codes f)`, and `[0]` otherwise. -/
theorem twoSatMain_spec (hf : IsTwoCNF n f) (hSp : spaceM n f ≤ S) :
    HTB S twoSatMain (fun c => c = initial (twoSatInput n f))
      (fun c => c.out = if okB n (codes f) then 1 :: asgBits n (codes f) else [0])
      (CM * (n + f.length + 1)) := by
  intro c hc
  have hL := layout_eqs n f.length (2 * f.length + 2)
  obtain ⟨c₁, t₁, e₁, ⟨hB, ho₁, hF₁⟩, ht₁⟩ :=
    mainInit_spec (S := S) hf (by unfold spaceM at hSp; omega) c hc
  obtain ⟨c₂, t₂, e₂, hO, ht₂⟩ := twoSat_spec (S := S) n f.length (codes f) c₁ (length_codes hf)
    (codes_ok hf) (by rw [hF₁]; exact hSp) c₁ ⟨hB, rfl⟩
  have hA : c₂.reg tAS + n ≤ S := by
    have := hO.fresh.2; have := hO.rfree; rw [hF₁] at this; unfold spaceM at hSp; omega
  obtain ⟨c₃, t₃, e₃, ho₃, ht₃⟩ := mainOut_spec (n := n) (asgBits n (codes f)) (by simp [asgBits])
    (c₂.reg tAS) (okB n (codes f)) hA c₂ ⟨hO.ok, hO.rn, rfl, hO.asg, by rw [hO.out, ho₁]⟩
  refine ⟨c₃, t₁ + (t₂ + t₃), ExecB.seq e₁ (ExecB.seq e₂ e₃), ho₃, ?_⟩
  simp only [CT, CM] at ht₂ ⊢
  omega

/-- **Linear-time 2-SAT, with `ComputesIn`**: for every 2-CNF `f` over the variables
`0, …, n - 1`, on the input `n :: |f| :: codes f` the machine `twoSatMain` halts within
`CM · (n + |f| + 1)` steps, accessing only the addresses below `CM · (n + |f| + 1)` (input
included), and its output is `[0]` if `f` is unsatisfiable, and otherwise `1` followed by the
`n` bits (`0`/`1`) of an assignment satisfying `f`. -/
theorem twoSat_computes (hf : IsTwoCNF n f) :
    ∃ t ≤ CM * (n + f.length + 1), ∃ out,
      ComputesIn twoSatMain (n :: f.length :: codes f) out t (CM * (n + f.length + 1)) ∧
      ((¬ Satisfiable f ∧ out = [0]) ∨
        (∃ a : List Bool, a.length = n ∧ out = 1 :: a.map (fun b => if b then 1 else 0) ∧
          evalCNF (fun x => a.getD x false) f = true)) := by
  obtain ⟨c, t, he, ho, ht⟩ := twoSatMain_spec (S := CM * (n + f.length + 1)) hf
    ((spaceM_le n f).trans (Nat.mul_le_mul_right _ (by simp [CM]))) _ rfl
  refine ⟨t, ht, c.out, ⟨c, he, rfl⟩, ?_⟩
  have hc := twoSat_correct hf
  cases hok : okB n (codes f)
  · left
    rw [hok] at ho
    exact ⟨fun hs => by have := hc.1.mpr hs; rw [hok] at this; exact absurd this (by simp), by
      simpa using ho⟩
  · right
    rw [hok] at ho
    refine ⟨(List.range n).map (asg n (codes f)), by simp, ?_, ?_⟩
    · rw [ho]; simp [asgBits]
    · rw [evalCNF_congr hf (σ' := asg n (codes f)) fun x hx => ?_]
      · exact hc.2 hok
      · simp [List.getD_eq_getElem?_getD, hx]

end main

/-- **Linear-time 2-SAT on the unit-cost RAM** (ANONYMIZED–ANONYMIZED–ANONYMIZED 1979): one program and one
constant `C` serve every 2-CNF over `n` variables; time and space at most `C (n + m + 1)`. -/
theorem exists_linear_twoSat : ∃ (prog : Stmt) (C : ℕ), ∀ (n : ℕ) (f : CNF), IsTwoCNF n f →
    ∃ t ≤ C * (n + f.length + 1), ∃ out,
      ComputesIn prog (n :: f.length :: codes f) out t (C * (n + f.length + 1)) ∧
      ((¬ Satisfiable f ∧ out = [0]) ∨
        (∃ a : List Bool, a.length = n ∧ out = 1 :: a.map (fun b => if b then 1 else 0) ∧
          evalCNF (fun x => a.getD x false) f = true)) :=
  ⟨twoSatMain, CM, fun _ _ hf => twoSat_computes hf⟩

end STACS2027.Runtimes.TwoSat
