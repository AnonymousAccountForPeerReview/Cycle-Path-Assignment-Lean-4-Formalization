module

public import ApproximationHardness.RAM.Model
import Lean.Elab.Tactic.Omega

/-!
# Reasoning about RAM programs

* `run`, `cost`: the final configuration and the exact step count of a loop-free
  program (`exec_run`), with `cost s c ≤ size s`;
* `Sat s P m b`: from every configuration satisfying `P`, `s` halts in `m c` within
  `b` steps; composition rules for sequencing and counted loops.
-/

@[expose] public section

namespace STACS2027.RAM

@[simp] theorem setReg_reg (c : Config) (d v i : Nat) : (c.setReg d v).reg i = if i = d then v else c.reg i := rfl
@[simp] theorem setReg_mem (c : Config) (d v : Nat) : (c.setReg d v).mem = c.mem := rfl
@[simp] theorem setReg_out (c : Config) (d v : Nat) : (c.setReg d v).out = c.out := rfl
@[simp] theorem setMem_reg (c : Config) (a v : Nat) : (c.setMem a v).reg = c.reg := rfl
@[simp] theorem setMem_mem (c : Config) (a v i : Nat) : (c.setMem a v).mem i = if i = a then v else c.mem i := rfl
@[simp] theorem setMem_out (c : Config) (a v : Nat) : (c.setMem a v).out = c.out := rfl
@[simp] theorem emit_reg (c : Config) (v : Nat) : (c.emit v).reg = c.reg := rfl
@[simp] theorem emit_mem (c : Config) (v : Nat) : (c.emit v).mem = c.mem := rfl
@[simp] theorem emit_out (c : Config) (v : Nat) : (c.emit v).out = c.out ++ [v] := rfl

/-- Loop-free programs. -/
def LoopFree : Stmt → Prop
  | .seq s t => LoopFree s ∧ LoopFree t
  | .ifz _ s t => LoopFree s ∧ LoopFree t
  | .loop _ _ => False
  | _ => True

/-- The final configuration of a loop-free program. -/
def run : Stmt → Config → Config
  | .skip, c => c
  | .const d v, c => c.setReg d v
  | .add d a b, c => c.setReg d (c.reg a + c.reg b)
  | .sub d a b, c => c.setReg d (c.reg a - c.reg b)
  | .load d a, c => c.setReg d (c.mem (c.reg a))
  | .store a b, c => c.setMem (c.reg a) (c.reg b)
  | .write a, c => c.emit (c.reg a)
  | .seq s t, c => run t (run s c)
  | .ifz a s t, c => if c.reg a = 0 then run s c else run t c
  | .loop _ _, c => c

/-- The step count of a loop-free program. -/
def cost : Stmt → Config → Nat
  | .seq s t, c => cost s c + cost t (run s c)
  | .ifz a s t, c => (if c.reg a = 0 then cost s c else cost t c) + 1
  | _, _ => 1

/-- The number of instructions of a program (a bound on the cost of a loop-free program). -/
def size : Stmt → Nat
  | .seq s t => size s + size t
  | .ifz _ s t => size s + size t + 1
  | .loop _ b => size b + 1
  | _ => 1

theorem exec_run : ∀ (s : Stmt), LoopFree s → ∀ c, Exec s c (cost s c) (run s c)
  | .skip, _, c => Exec.skip c
  | .const d v, _, c => Exec.const d v c
  | .add d a b, _, c => Exec.add d a b c
  | .sub d a b, _, c => Exec.sub d a b c
  | .load d a, _, c => Exec.load d a c
  | .store a b, _, c => Exec.store a b c
  | .write a, _, c => Exec.write a c
  | .seq s t, h, c => Exec.seq (exec_run s h.1 c) (exec_run t h.2 _)
  | .ifz a s t, h, c => by
    by_cases ha : c.reg a = 0
    · simp only [run, cost, ha, ↓reduceIte]
      exact Exec.ifzTrue ha (exec_run s h.1 c)
    · simp only [run, cost, ha, ↓reduceIte]
      exact Exec.ifzFalse ha (exec_run t h.2 c)
  | .loop _ _, h, _ => absurd h id

theorem cost_le_size : ∀ (s : Stmt) (c : Config), cost s c ≤ size s
  | .skip, _ | .const .., _ | .add .., _ | .sub .., _ | .load .., _ | .store .., _ | .write .., _ =>
    Nat.le_refl _
  | .loop .., _ => by simp [cost, size]
  | .seq s t, c => by
    have := cost_le_size s c
    have := cost_le_size t (run s c)
    simp only [cost, size]; omega
  | .ifz a s t, c => by
    have := cost_le_size s c
    have := cost_le_size t c
    simp only [cost, size]; split <;> omega

/-- From every configuration satisfying `P`, `s` halts in `m c` within `b` steps. -/
def Sat (s : Stmt) (P : Config → Prop) (m : Config → Config) (b : Nat) : Prop :=
  ∀ c, P c → ∃ t, Exec s c t (m c) ∧ t ≤ b

theorem Sat.ofLoopFree {s : Stmt} (h : LoopFree s) (P : Config → Prop) : Sat s P (run s) (size s) :=
  fun c _ => ⟨_, exec_run s h c, cost_le_size s c⟩

theorem Sat.mono {s : Stmt} {P P' : Config → Prop} {m : Config → Config} {b b' : Nat} (h : Sat s P m b)
    (hP : ∀ c, P' c → P c) (hb : b ≤ b') : Sat s P' m b' := by
  intro c hc
  obtain ⟨t, he, ht⟩ := h c (hP c hc)
  exact ⟨t, he, Nat.le_trans ht hb⟩

theorem Sat.congr {s : Stmt} {P : Config → Prop} {m m' : Config → Config} {b : Nat} (h : Sat s P m b)
    (hm : ∀ c, P c → m c = m' c) : Sat s P m' b := by
  intro c hc
  obtain ⟨t, he, ht⟩ := h c hc
  exact ⟨t, hm c hc ▸ he, ht⟩

theorem Sat.seq {s u : Stmt} {P Q : Config → Prop} {m₁ m₂ : Config → Config} {b₁ b₂ : Nat}
    (h₁ : Sat s P m₁ b₁) (hQ : ∀ c, P c → Q (m₁ c)) (h₂ : Sat u Q m₂ b₂) :
    Sat (.seq s u) P (fun c => m₂ (m₁ c)) (b₁ + b₂) := by
  intro c hc
  obtain ⟨t, he, ht⟩ := h₁ c hc
  obtain ⟨t', he', ht'⟩ := h₂ _ (hQ c hc)
  exact ⟨t + t', Exec.seq he he', by omega⟩

/-- `iterate m k c`: `k` applications of `m`. -/
def iterate (m : Config → Config) : Nat → Config → Config
  | 0, c => c
  | k + 1, c => iterate m k (m c)

/-- A counted loop: every body run decrements the counter `a` by one and preserves `P`;
`a` is at most `L` under `P`. -/
theorem Sat.loop {a : Nat} {body : Stmt} {P : Config → Prop} {m : Config → Config} {b L : Nat}
    (hb : Sat body (fun c => P c ∧ c.reg a ≠ 0) m b)
    (hP : ∀ c, P c → c.reg a ≠ 0 → P (m c))
    (hdec : ∀ c, P c → c.reg a ≠ 0 → (m c).reg a + 1 = c.reg a)
    (hL : ∀ c, P c → c.reg a ≤ L) :
    Sat (.loop a body) P (fun c => iterate m (c.reg a) c) (L * (b + 1) + 1) := by
  have key : ∀ k c, P c → c.reg a = k → ∃ t, Exec (.loop a body) c t (iterate m k c) ∧ t ≤ k * (b + 1) + 1 := by
    intro k
    induction k with
    | zero =>
      intro c _ hk
      exact ⟨1, Exec.loopDone hk, by simp⟩
    | succ k ih =>
      intro c hc hk
      have ha : c.reg a ≠ 0 := by omega
      obtain ⟨t, he, ht⟩ := hb c ⟨hc, ha⟩
      obtain ⟨t', he', ht'⟩ := ih (m c) (hP c hc ha) (by have := hdec c hc ha; omega)
      refine ⟨t + t' + 1, Exec.loopNext ha he he', ?_⟩
      rw [Nat.succ_mul]; omega
  intro c hc
  obtain ⟨t, he, ht⟩ := key (c.reg a) c hc rfl
  refine ⟨t, he, ?_⟩
  have := Nat.mul_le_mul_right (b + 1) (hL c hc)
  omega

/-- The invariant of a counted loop holds after it. -/
theorem iterate_invariant {a : Nat} {P : Config → Prop} {m : Config → Config}
    (hP : ∀ c, P c → c.reg a ≠ 0 → P (m c))
    (hdec : ∀ c, P c → c.reg a ≠ 0 → (m c).reg a + 1 = c.reg a) :
    ∀ k c, P c → c.reg a = k → P (iterate m k c) ∧ (iterate m k c).reg a = 0 := by
  intro k
  induction k with
  | zero => intro c hc hk; exact ⟨hc, hk⟩
  | succ k ih =>
    intro c hc hk
    have ha : c.reg a ≠ 0 := by omega
    exact ih (m c) (hP c hc ha) (by have := hdec c hc ha; omega)

/-- A sequence of statements. -/
def seqs : List Stmt → Stmt
  | [] => .skip
  | s :: ss => .seq s (seqs ss)

theorem loopFree_seqs : ∀ (ss : List Stmt), (∀ s ∈ ss, LoopFree s) → LoopFree (seqs ss)
  | [], _ => trivial
  | s :: ss, h => ⟨h s (by simp), loopFree_seqs ss (fun t ht => h t (by simp [ht]))⟩

@[simp] theorem run_seqs_nil (c : Config) : run (seqs []) c = c := rfl
@[simp] theorem run_seqs_cons (s : Stmt) (ss : List Stmt) (c : Config) :
    run (seqs (s :: ss)) c = run (seqs ss) (run s c) := rfl

theorem size_seqs : ∀ (ss : List Stmt), size (seqs ss) = (ss.map size).sum + 1
  | [] => rfl
  | s :: ss => by simp [seqs, size, size_seqs ss]; omega

end STACS2027.RAM
