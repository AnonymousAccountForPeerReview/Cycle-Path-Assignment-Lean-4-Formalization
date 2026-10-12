module

public import Outerplanar.Algo.Ear
import Mathlib.Tactic

/-!
# Ear elimination: the effect of one step, and termination

For the ear elimination of `Outerplanar/Algo/Ear.lean`:

* the fields of the states produced by `pushIf2`, `decDeg`, `elim` and `step`;
* **termination**: the potential `pot s = 3 * cnt + |stack|` drops with every iteration
  (`pot_step`: a skip pops one entry; an elimination lowers `cnt` by one and pushes at
  most two), it is at most `4 N` initially (`pot_init_le`), so after `4 N + 1` iterations
  the loop has stopped (`loop_stopped`).
-/

@[expose] public section

namespace STACS2027.Ear

/-! ### Field lemmas -/

section Fields

variable (s : State) (v : ℕ)

theorem pushIf2_adj : (pushIf2 s v).adj = s.adj := by unfold pushIf2; split <;> rfl
theorem pushIf2_mat : (pushIf2 s v).mat = s.mat := by unfold pushIf2; split <;> rfl
theorem pushIf2_deg : (pushIf2 s v).deg = s.deg := by unfold pushIf2; split <;> rfl
theorem pushIf2_dead : (pushIf2 s v).dead = s.dead := by unfold pushIf2; split <;> rfl
theorem pushIf2_log : (pushIf2 s v).log = s.log := by unfold pushIf2; split <;> rfl
theorem pushIf2_cnt : (pushIf2 s v).cnt = s.cnt := by unfold pushIf2; split <;> rfl
theorem pushIf2_stack :
    (pushIf2 s v).stack = if s.deg v = 2 then v :: s.stack else s.stack := by
  unfold pushIf2; split <;> rfl

theorem decDeg_adj : (decDeg s v).adj = s.adj := pushIf2_adj _ _
theorem decDeg_mat : (decDeg s v).mat = s.mat := pushIf2_mat _ _
theorem decDeg_dead : (decDeg s v).dead = s.dead := pushIf2_dead _ _
theorem decDeg_log : (decDeg s v).log = s.log := pushIf2_log _ _
theorem decDeg_cnt : (decDeg s v).cnt = s.cnt := pushIf2_cnt _ _
theorem decDeg_deg : (decDeg s v).deg = Function.update s.deg v (s.deg v - 1) :=
  pushIf2_deg _ _
theorem decDeg_stack :
    (decDeg s v).stack = if s.deg v - 1 = 2 then v :: s.stack else s.stack := by
  simp only [decDeg, pushIf2_stack, Function.update_self]

end Fields

section Elim

variable (s : State) (v u w : ℕ)

theorem elim_dead : (elim s v u w).dead = Function.update s.dead v true := by
  cases h : s.mat u w <;> simp only [elim, h, Bool.false_eq_true, ite_false, ite_true, decDeg_dead]

theorem elim_cnt : (elim s v u w).cnt = s.cnt - 1 := by
  cases h : s.mat u w <;> simp only [elim, h, Bool.false_eq_true, ite_false, ite_true, decDeg_cnt]

theorem elim_log : (elim s v u w).log = (v, u, w) :: s.log := by
  cases h : s.mat u w <;> simp only [elim, h, Bool.false_eq_true, ite_false, ite_true, decDeg_log]

variable {s u w}

theorem elim_mat_true (h : s.mat u w = true) : (elim s v u w).mat = s.mat := by
  simp only [elim, h, ite_true, decDeg_mat]

theorem elim_adj_true (h : s.mat u w = true) : (elim s v u w).adj = s.adj := by
  simp only [elim, h, ite_true, decDeg_adj]

theorem elim_deg_true (h : s.mat u w = true) (huw : u ≠ w) :
    (elim s v u w).deg = Function.update (Function.update s.deg u (s.deg u - 1)) w
      (s.deg w - 1) := by
  simp only [elim, h, ite_true, decDeg_deg, Function.update_of_ne huw.symm]

theorem elim_mat_false (h : s.mat u w = false) :
    (elim s v u w).mat = update2 (update2 s.mat u w true) w u true := by
  simp only [elim, h, Bool.false_eq_true, ite_false]

theorem elim_adj_false (h : s.mat u w = false) (huw : u ≠ w) :
    (elim s v u w).adj =
      Function.update (Function.update s.adj u (w :: s.adj u)) w (u :: s.adj w) := by
  simp only [elim, h, Bool.false_eq_true, ite_false, Function.update_of_ne huw.symm]

theorem elim_deg_false (h : s.mat u w = false) : (elim s v u w).deg = s.deg := by
  simp only [elim, h, Bool.false_eq_true, ite_false]

theorem elim_stack_false (h : s.mat u w = false) : (elim s v u w).stack = s.stack := by
  simp only [elim, h, Bool.false_eq_true, ite_false]

theorem elim_stack_true (h : s.mat u w = true) (huw : u ≠ w) :
    (elim s v u w).stack =
      if s.deg w - 1 = 2 then
        w :: (if s.deg u - 1 = 2 then u :: s.stack else s.stack)
      else (if s.deg u - 1 = 2 then u :: s.stack else s.stack) := by
  simp only [elim, h, ite_true, decDeg_stack, decDeg_deg, Function.update_of_ne huw.symm]

theorem mem_elim_stack (huw : u ≠ w) {x : ℕ} (hx : x ∈ s.stack) : x ∈ (elim s v u w).stack := by
  cases h : s.mat u w
  · rw [elim_stack_false v h]; exact hx
  · rw [elim_stack_true v h huw]; split_ifs <;> simp [hx]

theorem elim_stack_u (huw : u ≠ w) (h : s.mat u w = true) (hu : s.deg u - 1 = 2) :
    u ∈ (elim s v u w).stack := by
  rw [elim_stack_true v h huw]; split_ifs <;> simp

theorem elim_stack_w (huw : u ≠ w) (h : s.mat u w = true) (hw : s.deg w - 1 = 2) :
    w ∈ (elim s v u w).stack := by
  rw [elim_stack_true v h huw]; split_ifs <;> simp

theorem elim_stack_sub (huw : u ≠ w) {x : ℕ} (hx : x ∈ (elim s v u w).stack) :
    x ∈ s.stack ∨ x = u ∨ x = w := by
  cases h : s.mat u w
  · rw [elim_stack_false v h] at hx; exact Or.inl hx
  · rw [elim_stack_true v h huw] at hx
    split_ifs at hx <;> (try simp only [List.mem_cons] at hx) <;> tauto

end Elim

theorem elim_stack_length (s : State) (v u w : ℕ) :
    (elim s v u w).stack.length ≤ s.stack.length + 2 := by
  cases h : s.mat u w
  · simp only [elim, h, Bool.false_eq_true, ite_false]
    omega
  · simp only [elim, h, ite_true, decDeg_stack, decDeg_deg]
    split_ifs <;> simp

/-! ### One step -/

theorem step_skip {s : State} {v : ℕ} {rest : List ℕ} (hs : s.stack = v :: rest)
    (h : ¬ (s.dead v = false ∧ s.deg v = 2)) : step s = { s with stack := rest } := by
  unfold step
  rw [hs]
  simp only
  rw [ite_eq_right h]

theorem step_elim {s : State} {v : ℕ} {rest : List ℕ} (hs : s.stack = v :: rest)
    (h : s.dead v = false ∧ s.deg v = 2) :
    step s = elim { s with stack := rest } v
      (((s.adj v).filter fun x => s.dead x = false).getD 0 0)
      (((s.adj v).filter fun x => s.dead x = false).getD 1 0) := by
  unfold step
  rw [hs]
  simp only
  rw [ite_eq_left h]

/-! ### Termination -/

/-- The potential of a state. -/
def pot (s : State) : ℕ := 3 * s.cnt + s.stack.length

/-- Every iteration lowers the potential. -/
theorem pot_step (s : State) (h : s.stack ≠ [] ∧ 3 < s.cnt) : pot (step s) < pot s := by
  obtain ⟨hs, hc⟩ := h
  obtain ⟨v, rest, hsv⟩ := List.exists_cons_of_ne_nil hs
  by_cases hv : s.dead v = false ∧ s.deg v = 2
  · rw [step_elim hsv hv]
    have h1 := elim_stack_length { s with stack := rest } v
      (((s.adj v).filter fun x => s.dead x = false).getD 0 0)
      (((s.adj v).filter fun x => s.dead x = false).getD 1 0)
    simp only [pot, elim_cnt]
    simp only at h1
    rw [hsv, List.length_cons]
    omega
  · rw [step_skip hsv hv]
    simp only [pot, hsv, List.length_cons]
    omega

theorem pot_init_le (N : ℕ) (L : List Edge) : pot (init N L) ≤ 4 * N := by
  simp only [pot, init, List.length_reverse]
  have := List.length_filter_le (fun v => decide ((initAdj L v).length = 2)) (List.range N)
  simp only [List.length_range] at this
  omega

theorem loop_stopped_of_pot : ∀ (f : ℕ) (s : State), pot s < f →
    ¬ ((loop f s).stack ≠ [] ∧ 3 < (loop f s).cnt)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, s, h => by
    unfold loop
    split
    · next hc => exact loop_stopped_of_pot f (step s) (by have := pot_step s hc; omega)
    · next hc => exact hc

/-- **Termination**: after `4 N + 1` iterations the loop has stopped. -/
theorem loop_stopped (N : ℕ) (L : List Edge) :
    ¬ ((loop (4 * N + 1) (init N L)).stack ≠ [] ∧ 3 < (loop (4 * N + 1) (init N L)).cnt) :=
  loop_stopped_of_pot _ _ (by have := pot_init_le N L; omega)

end STACS2027.Ear
