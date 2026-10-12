module

public import Runtimes.GeneralCycles.Fold
import Mathlib.Tactic

/-! Fixed-length output blocks and input-cell correspondence. Artifact date: 2026-10-12. -/

@[expose] public section

namespace STACS2027.Runtimes.GeneralCycles

open STACS2027 STACS2027.RAM

def valuesList (c : Config) (values n : ℕ) : List ℕ :=
  (List.range n).map fun j => c.reg (values + j)

def emitValues (values : ℕ) : ℕ → Stmt
  | 0 => .skip
  | n + 1 => .seq (.write values) (emitValues (values + 1) n)

@[simp] theorem emitValues_loopFree (values n : ℕ) : LoopFree (emitValues values n) := by
  induction n generalizing values <;> simp [emitValues, LoopFree, *]

@[simp] theorem emitValues_size (values n : ℕ) : size (emitValues values n) = n + 1 := by
  induction n generalizing values <;> simp [emitValues, size, *]; omega

@[simp] theorem emitValues_addrOK (values n : ℕ) (S : ℕ) (c : Config) :
    AddrOK S (emitValues values n) c := by
  induction n generalizing values c <;> simp [emitValues, *]

@[simp] theorem emitValues_wregs (values n : ℕ) : wregs (emitValues values n) = [] := by
  induction n generalizing values <;> simp [emitValues, wregs, *]

@[simp] theorem emitValues_stores (values n : ℕ) : stores (emitValues values n) = false := by
  induction n generalizing values <;> simp [emitValues, stores, *]

theorem valuesList_succ (c : Config) (values n : ℕ) :
    valuesList c values (n + 1) = c.reg values :: valuesList c (values + 1) n := by
  simp only [valuesList, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro j hj
  simp [Nat.add_comm, Nat.add_left_comm]

theorem emitValues_out (values n : ℕ) (c : Config) :
    (run (emitValues values n) c).out = c.out ++ valuesList c values n := by
  induction n generalizing values c with
  | zero => simp [emitValues, valuesList]
  | succ n ih =>
    rw [emitValues, run_seq', run_write, ih, valuesList_succ]
    simp [valuesList, List.append_assoc]

theorem emitValues_spec {values n S : ℕ} (c₀ : Config) :
    HTB S (emitValues values n) (fun c => c = c₀)
      (fun c => c.reg = c₀.reg ∧ c.mem = c₀.mem ∧
        c.out = c₀.out ++ valuesList c₀ values n) (n + 1) := by
  refine HTB.run_le (emitValues_loopFree _ _) (by simp) ?_
  intro c hc
  subst c
  refine ⟨emitValues_addrOK _ _ _ _, ?_, ?_, emitValues_out _ _ _⟩
  · funext r
    exact run_reg_of_not_mem (emitValues_loopFree _ _) (by simp) c₀
  · exact run_mem_of_stores (emitValues_loopFree _ _) (by simp) c₀

theorem initial_endpoint (g : Graph) (i : ℕ) :
    (initial (graphInput g)).mem (1 + i) = (endpoints g).getD i 0 := by
  simp [initial_mem, graphInput, endpoints, Nat.add_comm]

theorem Placed.emission_labels {g : Graph} {indices values k : ℕ} {is : List ℕ} {c : Config}
    (hl : is.length = k) (h : Placed indices values (initial (graphInput g)).mem is c) :
    valuesList c values k = tupleLabels g is := by
  apply List.ext_getElem
  · simp [valuesList, tupleLabels, hl]
  · intro j hj hj'
    simp only [valuesList, List.getElem_map, List.getElem_range]
    have hlt : j < is.length := by simpa [valuesList, hl] using hj
    have hv := (h j hlt).2
    rw [hv, initial_endpoint]
    simp [tupleLabels, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]

end STACS2027.Runtimes.GeneralCycles
