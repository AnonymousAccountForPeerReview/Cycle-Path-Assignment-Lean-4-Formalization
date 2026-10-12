module

public import Runtimes.Flow.Edges
public import Runtimes.Flow.Tri
import Mathlib.Tactic

/-!
# The extraction of an assignment on the RAM

The extraction machines receive the input of the construction followed by the answer of the
solver, `flowInput g cs k ++ 1 :: bits`, and write one position per cycle, read off the bits
of the arcs of the cycle (`O(t)` steps; the bits are found by address arithmetic, as the
position of every arc in the network is known):

* `extract4_spec` (`k = 4`): position `optionIndex (bit₁ ≠ 0) (bit₃ ≠ 0)` for cycle `i`, where
  `bit₁, bit₃` are the bits at positions `2t + 4i + 1`, `2t + 4i + 3` (`readOff4_select`);
* `extract3_spec` (`k = 3`): position `2`, `0` or `1` from the bits at positions `t + 3i`,
  `t + 3i + 1` (`readOff3_select`).

The machines do not store: they read the input and the answer only, so they run within any
space bound `S` above the last bit they read (`bD + 6t + 1` and `bD + 4t`; the input followed by
the answer has `bD + 1 + 10t`, respectively `bD + 1 + 7t`, cells).
-/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027 STACS2027.RAM

section ex

variable {g : Graph} {cs : List Cycle} {k : ℕ} {S : ℕ}

/-- The answer of the solver in the memory of the extraction machine. -/
theorem mem_answer (hcs : ∀ c ∈ cs, IsCycle g k c) (bits : List ℕ) (j : ℕ) :
    (initial (flowInput g cs k ++ 1 :: bits)).mem (bD g cs k + 1 + j) = bits.getD j 0 := by
  rw [initial_mem, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [length_flowInput hcs]; omega), length_flowInput hcs,
    show bD g cs k + 1 + j - bD g cs k = j + 1 by omega, List.getElem?_cons_succ]

/-- The positions read off a `0/1` vector of the four-cycle network. -/
def pos4 (t : ℕ) (bits : List ℕ) (i : ℕ) : ℕ :=
  optionIndex (decide (bits.getD (2 * t + (i * 4 + 1)) 0 ≠ 0))
    (decide (bits.getD (2 * t + (i * 4 + 3)) 0 ≠ 0))

/-- The state of the extraction after `i` cycles. -/
def ExInv4 (g : Graph) (cs : List Cycle) (bits : List ℕ) (i : ℕ) (c : Config) : Prop :=
  c.reg sB = bD g cs 4 + 1 + 2 * cs.length + i * 4 ∧ c.reg sOne = 1 ∧ c.reg sThree = 3 ∧
    c.mem = (initial (flowInput g cs 4 ++ 1 :: bits)).mem ∧
    c.out = (List.range i).map (pos4 cs.length bits)

theorem exInit4_spec (hcs : ∀ c ∈ cs, IsCycle g 4 c) (bits : List ℕ) (hS : bD g cs 4 ≤ S) :
    HTB S exInit4 (fun c => c = initial (flowInput g cs 4 ++ 1 :: bits))
      (fun c => ExInv4 g cs bits 0 c ∧ c.reg gT = cs.length) 16 :=
    HTB.of_HT_addrOK (by decide) (fun c hc => by
      subst hc
      obtain ⟨h0, -, -, -, -⟩ := input_facts hcs (1 :: bits)
      have hb : bD g cs 4 = 2 * g.length + 3 + 4 * cs.length := rfl
      addr_ok [exInit4, initial_reg, h0]) <| by
  refine HT.run_le (by decide) (by decide) fun c hc => ?_
  subst hc
  obtain ⟨h0, -, ht, -, -⟩ := input_facts hcs (1 :: bits)
  have hL := layout_eqs g cs 4
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals simp +decide only [exInit4, run_seq', run_load, run_add, run_addc, run_subc, run_inc,
    run_const, setReg_reg, setReg_mem, setReg_out, ↓reduceIte, initial_reg, h0, initial_out]
  · rw [show List.length g + List.length g + 3 - 1 = 2 * List.length g + 2 by omega, ht]
    simp only [hL.2.1, hL.1]; ring
  · simp
  · rw [show List.length g + List.length g + 3 - 1 = 2 * List.length g + 2 by omega, ht]

theorem exBody4_spec (hcs : ∀ c ∈ cs, IsCycle g 4 c) (bits : List ℕ)
    (hS : bD g cs 4 + 6 * cs.length + 1 ≤ S) (i : ℕ) (hi : i < cs.length) :
    HTB S exBody4 (fun c => ExInv4 g cs bits i c ∧ c.reg sI = i ∧ c.reg gT = cs.length)
      (fun c => ExInv4 g cs bits (i + 1) c ∧ c.reg sI = i ∧ c.reg gT = cs.length) 14 :=
    HTB.of_HT_addrOK (by decide) (fun c ⟨⟨hB, h1, h3, _, _⟩, _, _⟩ => by
      addr_ok [exBody4, hB, h1, h3]) <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨hB, h1, h3, hm, ho⟩, hI, hT⟩ => ?_
  have m1 : (initial (flowInput g cs 4 ++ 1 :: bits)).mem (bD g cs 4 + 1 + 2 * cs.length + i * 4 + 1) =
      bits.getD (2 * cs.length + (i * 4 + 1)) 0 := by
    rw [show bD g cs 4 + 1 + 2 * cs.length + i * 4 + 1 =
      bD g cs 4 + 1 + (2 * cs.length + (i * 4 + 1)) by ring]
    exact mem_answer hcs bits _
  have m3 : (initial (flowInput g cs 4 ++ 1 :: bits)).mem (bD g cs 4 + 1 + 2 * cs.length + i * 4 + 3) =
      bits.getD (2 * cs.length + (i * 4 + 3)) 0 := by
    rw [show bD g cs 4 + 1 + 2 * cs.length + i * 4 + 3 =
      bD g cs 4 + 1 + (2 * cs.length + (i * 4 + 3)) by ring]
    exact mem_answer hcs bits _
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals simp +decide only [exBody4, run_seq', run_ld, run_ifz', run_const, run_write,
    run_addc (show sB ≠ rT by decide), setReg_reg, setReg_mem, setReg_out, emit_reg, emit_mem,
    emit_out, config_ite_reg, config_ite_mem, config_ite_out, ↓reduceIte, hB, h1, h3, hm, hI, hT,
    m1, m3, ite_self]
  · ring
  · rw [ho, List.range_succ, List.map_append, List.map_singleton, pos4]
    split_ifs <;> simp_all [optionIndex]

/-- **The extraction machine of Theorem 2**: on the input followed by `1 :: bits`, it writes the
positions read off `bits`, within `18t + 20` steps. -/
theorem extract4_spec (hcs : ∀ c ∈ cs, IsCycle g 4 c) (bits : List ℕ)
    (hS : bD g cs 4 + 6 * cs.length + 1 ≤ S) :
    HTB S extract4 (fun c => c = initial (flowInput g cs 4 ++ 1 :: bits))
      (fun c => c.out = (List.range cs.length).map (pos4 cs.length bits)) (18 * cs.length + 20) := by
  have hl := HTB.forUpC (S := S) (i := sI) (n := gT) (N := cs.length) (body := exBody4)
    (ExInv4 g cs bits) 14 (by decide) (by decide) (by decide)
    (fun j => by indep [ExInv4]) (fun i hi => exBody4_spec hcs bits hS i hi)
  exact ((exInit4_spec hcs bits (by omega)).seq hl).mono (fun _ h => h) (fun _ h => h.1.2.2.2.2) (by omega)

/-- The positions read off a `0/1` vector of the triangle network. -/
def pos3b (t : ℕ) (bits : List ℕ) (i : ℕ) : ℕ :=
  if bits.getD (t + (i * 3 + 0)) 0 ≠ 0 then 2 else if bits.getD (t + (i * 3 + 1)) 0 ≠ 0 then 0 else 1

/-- The state of the triangle extraction after `i` triangles. -/
def ExInv3 (g : Graph) (cs : List Cycle) (bits : List ℕ) (i : ℕ) (c : Config) : Prop :=
  c.reg sB = bD g cs 3 + 1 + cs.length + i * 3 ∧ c.reg sOne = 1 ∧
    c.mem = (initial (flowInput g cs 3 ++ 1 :: bits)).mem ∧
    c.out = (List.range i).map (pos3b cs.length bits)

theorem exInit3_spec (hcs : ∀ c ∈ cs, IsCycle g 3 c) (bits : List ℕ) (hS : bD g cs 3 ≤ S) :
    HTB S exInit3 (fun c => c = initial (flowInput g cs 3 ++ 1 :: bits))
      (fun c => ExInv3 g cs bits 0 c ∧ c.reg gT = cs.length) 15 :=
    HTB.of_HT_addrOK (by decide) (fun c hc => by
      subst hc
      obtain ⟨h0, -, -, -, -⟩ := input_facts hcs (1 :: bits)
      have hb : bD g cs 3 = 2 * g.length + 3 + 3 * cs.length := rfl
      addr_ok [exInit3, initial_reg, h0]) <| by
  refine HT.run_le (by decide) (by decide) fun c hc => ?_
  subst hc
  obtain ⟨h0, -, ht, -, -⟩ := input_facts hcs (1 :: bits)
  have hL := layout_eqs g cs 3
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals simp +decide only [exInit3, run_seq', run_load, run_add, run_addc, run_subc, run_inc,
    run_const, setReg_reg, setReg_mem, setReg_out, ↓reduceIte, initial_reg, h0, initial_out]
  · rw [show List.length g + List.length g + 3 - 1 = 2 * List.length g + 2 by omega, ht]
    simp only [hL.2.1, hL.1]; ring
  · simp
  · rw [show List.length g + List.length g + 3 - 1 = 2 * List.length g + 2 by omega, ht]

theorem exBody3_spec (hcs : ∀ c ∈ cs, IsCycle g 3 c) (bits : List ℕ)
    (hS : bD g cs 3 + 4 * cs.length ≤ S) (i : ℕ) (hi : i < cs.length) :
    HTB S exBody3 (fun c => ExInv3 g cs bits i c ∧ c.reg sI = i ∧ c.reg gT = cs.length)
      (fun c => ExInv3 g cs bits (i + 1) c ∧ c.reg sI = i ∧ c.reg gT = cs.length) 11 :=
    HTB.of_HT_addrOK (by decide) (fun c ⟨⟨hB, h1, _, _⟩, _, _⟩ => by
      addr_ok [exBody3, hB, h1]) <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨hB, h1, hm, ho⟩, hI, hT⟩ => ?_
  have m0 : (initial (flowInput g cs 3 ++ 1 :: bits)).mem (bD g cs 3 + 1 + cs.length + i * 3) =
      bits.getD (cs.length + (i * 3 + 0)) 0 := by
    rw [show bD g cs 3 + 1 + cs.length + i * 3 = bD g cs 3 + 1 + (cs.length + (i * 3 + 0)) by ring]
    exact mem_answer hcs bits _
  have m1 : (initial (flowInput g cs 3 ++ 1 :: bits)).mem (bD g cs 3 + 1 + cs.length + i * 3 + 1) =
      bits.getD (cs.length + (i * 3 + 1)) 0 := by
    rw [show bD g cs 3 + 1 + cs.length + i * 3 + 1 =
      bD g cs 3 + 1 + (cs.length + (i * 3 + 1)) by ring]
    exact mem_answer hcs bits _
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals simp +decide only [exBody3, run_seq', run_ld, run_load, run_ifz', run_const, run_write,
    run_addc (show sB ≠ rT by decide), setReg_reg, setReg_mem, setReg_out, emit_reg, emit_mem,
    emit_out, config_ite_reg, config_ite_mem, config_ite_out, ↓reduceIte, hB, h1, hm, hI, hT,
    m0, m1, ite_self]
  · ring
  · rw [ho, List.range_succ, List.map_append, List.map_singleton, pos3b]
    split_ifs <;> simp_all

/-- **The extraction machine of the triangle corollary.** -/
theorem extract3_spec (hcs : ∀ c ∈ cs, IsCycle g 3 c) (bits : List ℕ)
    (hS : bD g cs 3 + 4 * cs.length ≤ S) :
    HTB S extract3 (fun c => c = initial (flowInput g cs 3 ++ 1 :: bits))
      (fun c => c.out = (List.range cs.length).map (pos3b cs.length bits)) (15 * cs.length + 20) := by
  have hl := HTB.forUpC (S := S) (i := sI) (n := gT) (N := cs.length) (body := exBody3)
    (ExInv3 g cs bits) 11 (by decide) (by decide) (by decide)
    (fun j => by indep [ExInv3]) (fun i hi => exBody3_spec hcs bits hS i hi)
  exact ((exInit3_spec hcs bits (by omega)).seq hl).mono (fun _ h => h) (fun _ h => h.1.2.2.2) (by omega)

end ex

end STACS2027.Runtimes.Flow
