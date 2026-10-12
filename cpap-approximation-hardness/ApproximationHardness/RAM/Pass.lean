module

public import ApproximationHardness.RAM.PassA
import Lean.Elab.Tactic.Omega

/-!
# Generic tools for RAM programs

* frame lemmas: the registers a loop-free program may write (`regsW`), and whether it
  stores (`hasStore`) or writes output (`hasWrite`);
* `sat_clausePass`: a loop over the clauses of the input, one loop-free body run per
  clause, with an invariant indexed by the clauses already read;
* `sat_countLoop`: a loop run a given number of times with an invariant indexed by the
  number of runs;
* their relational forms `exec_listPass`, `exec_countLoop`, and `exec_loopFree`.

All of them give runs within a space bound `S` (`SatB S`, `ExecB S`); a loop-free body must be
address-safe (`AddrOK S body c`) on the configurations it runs from.
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT

/-! ### Frames -/

/-- The registers a program may write. -/
def regsW : Stmt → List Nat
  | .const d _ | .add d _ _ | .sub d _ _ | .load d _ => [d]
  | .seq s t | .ifz _ s t => regsW s ++ regsW t
  | .loop _ b => regsW b
  | _ => []

/-- Whether a program contains a `store`. -/
def hasStore : Stmt → Bool
  | .store _ _ => true
  | .seq s t | .ifz _ s t => hasStore s || hasStore t
  | .loop _ b => hasStore b
  | _ => false

/-- Whether a program contains a `write`. -/
def hasWrite : Stmt → Bool
  | .write _ => true
  | .seq s t | .ifz _ s t => hasWrite s || hasWrite t
  | .loop _ b => hasWrite b
  | _ => false

theorem run_reg_frame : ∀ (s : Stmt) (c : Config) (r : Nat), r ∉ regsW s → (run s c).reg r = c.reg r
  | .skip, _, _, _ => rfl
  | .const d v, c, r, h => by simp [regsW] at h; simp [run, h]
  | .add d a b, c, r, h => by simp [regsW] at h; simp [run, h]
  | .sub d a b, c, r, h => by simp [regsW] at h; simp [run, h]
  | .load d a, c, r, h => by simp [regsW] at h; simp [run, h]
  | .store a b, c, r, _ => by simp [run]
  | .write a, c, r, _ => by simp [run]
  | .seq s t, c, r, h => by
    simp only [regsW, List.mem_append, not_or] at h
    simp only [run]; rw [run_reg_frame t _ r h.2, run_reg_frame s c r h.1]
  | .ifz a s t, c, r, h => by
    simp only [regsW, List.mem_append, not_or] at h
    simp only [run]; split
    · exact run_reg_frame s c r h.1
    · exact run_reg_frame t c r h.2
  | .loop _ _, _, _, _ => rfl

theorem run_mem_frame : ∀ (s : Stmt) (c : Config), hasStore s = false → (run s c).mem = c.mem
  | .skip, _, _ | .const .., _, _ | .add .., _, _ | .sub .., _, _ | .load .., _, _ | .write .., _, _ => rfl
  | .store .., _, h => by simp [hasStore] at h
  | .seq s t, c, h => by
    simp only [hasStore, Bool.or_eq_false_iff] at h
    simp only [run]; rw [run_mem_frame t _ h.2, run_mem_frame s c h.1]
  | .ifz a s t, c, h => by
    simp only [hasStore, Bool.or_eq_false_iff] at h
    simp only [run]; split
    · exact run_mem_frame s c h.1
    · exact run_mem_frame t c h.2
  | .loop _ _, _, _ => rfl

theorem run_out_frame : ∀ (s : Stmt) (c : Config), hasWrite s = false → (run s c).out = c.out
  | .skip, _, _ | .const .., _, _ | .add .., _, _ | .sub .., _, _ | .load .., _, _ | .store .., _, _ => rfl
  | .write .., _, h => by simp [hasWrite] at h
  | .seq s t, c, h => by
    simp only [hasWrite, Bool.or_eq_false_iff] at h
    simp only [run]; rw [run_out_frame t _ h.2, run_out_frame s c h.1]
  | .ifz a s t, c, h => by
    simp only [hasWrite, Bool.or_eq_false_iff] at h
    simp only [run]; split
    · exact run_out_frame s c h.1
    · exact run_out_frame t c h.2
  | .loop _ _, _, _ => rfl

@[simp] theorem regsW_seqs_cons (s : Stmt) (ss : List Stmt) : regsW (seqs (s :: ss)) = regsW s ++ regsW (seqs ss) := rfl
@[simp] theorem regsW_seqs_nil : regsW (seqs []) = [] := rfl
@[simp] theorem hasStore_seqs_cons (s : Stmt) (ss : List Stmt) :
    hasStore (seqs (s :: ss)) = (hasStore s || hasStore (seqs ss)) := rfl
@[simp] theorem hasStore_seqs_nil : hasStore (seqs []) = false := rfl
@[simp] theorem hasWrite_seqs_cons (s : Stmt) (ss : List Stmt) :
    hasWrite (seqs (s :: ss)) = (hasWrite s || hasWrite (seqs ss)) := rfl
@[simp] theorem hasWrite_seqs_nil : hasWrite (seqs []) = false := rfl
@[simp] theorem loopFree_seqs_cons (s : Stmt) (ss : List Stmt) :
    LoopFree (seqs (s :: ss)) ↔ LoopFree s ∧ LoopFree (seqs ss) := Iff.rfl
@[simp] theorem loopFree_seqs_nil : LoopFree (seqs []) := trivial

theorem run_seqs_app (A B : List Stmt) (c : Config) : run (seqs (A ++ B)) c = run (seqs B) (run (seqs A) c) := by
  induction A generalizing c with
  | nil => rfl
  | cons s A ih => simp [ih]

/-- `run` of a sequence `seq s t`. -/
@[simp] theorem run_seq (s t : Stmt) (c : Config) : run (.seq s t) c = run t (run s c) := rfl
@[simp] theorem run_ifz (a : Nat) (s t : Stmt) (c : Config) :
    run (.ifz a s t) c = if c.reg a = 0 then run s c else run t c := rfl


/-! ### Passes over the clauses -/

/-- The invariant of a clause pass with clause invariant `I`. -/
def PassInv (f : CNF) (I : CNF → Config → Prop) (c : Config) : Prop :=
  ∃ pre suf : CNF, pre ++ suf = f ∧ c.reg Reg.m = suf.length ∧ At c (suf.flatMap clauseCode) ∧ I pre c

/-- A loop over the clauses, `Reg.m` counting the clauses left and `Reg.p` pointing at the next
one: if one run of the loop-free `body` is address-safe, reads one clause and extends the
invariant `I` by it, the loop ends in a configuration satisfying `I f`, within
`|f| (size body + 1) + 1` steps and the space `S`. -/
theorem sat_clausePass {S : Nat} (f : CNF) {body : Stmt} (hlf : LoopFree body) (I : CNF → Config → Prop)
    (hstep : ∀ pre cl suf c, pre ++ cl :: suf = f → I pre c → c.reg Reg.m = suf.length + 1 →
      At c (clauseCode cl ++ suf.flatMap clauseCode) →
      AddrOK S body c ∧ I (pre ++ [cl]) (run body c) ∧ (run body c).reg Reg.m = suf.length ∧
        At (run body c) (suf.flatMap clauseCode)) :
    SatB S (.loop Reg.m body) (PassInv f I) (fun c => iterate (run body) (c.reg Reg.m) c)
        (f.length * (size body + 1) + 1) ∧
      ∀ c, PassInv f I c → I f (iterate (run body) (c.reg Reg.m) c) := by
  have hP : ∀ c, PassInv f I c → c.reg Reg.m ≠ 0 → AddrOK S body c ∧ PassInv f I (run body c) ∧
      (run body c).reg Reg.m + 1 = c.reg Reg.m := by
    intro c ⟨pre, suf, hf, hm, hAt, hI⟩ hm0
    cases suf with
    | nil => simp at hm; exact absurd hm hm0
    | cons cl suf =>
      simp only [List.flatMap_cons] at hAt
      obtain ⟨h0, h1, h2, h3⟩ := hstep pre cl suf c hf hI (by simpa using hm) hAt
      refine ⟨h0, ⟨pre ++ [cl], suf, by simp [← hf], h2, h3, h1⟩, ?_⟩
      rw [h2, hm]; simp
  refine ⟨?_, ?_⟩
  · refine SatB.loop (SatB.ofLoopFree hlf (fun c hc => (hP c hc.1 hc.2).1)) (fun c hc hm => (hP c hc hm).2.1)
      (fun c hc hm => (hP c hc hm).2.2) ?_
    intro c ⟨pre, suf, hf, hm, _⟩
    rw [hm, ← hf]; simp
  · intro c hc
    obtain ⟨⟨pre, suf, hf, hm, _, hI⟩, h0⟩ := iterate_invariant (a := Reg.m) (P := PassInv f I)
      (fun c hc hm => (hP c hc hm).2.1) (fun c hc hm => (hP c hc hm).2.2) _ c hc rfl
    rw [h0] at hm
    have : suf = [] := List.eq_nil_of_length_eq_zero hm.symm
    subst this
    simp only [List.append_nil] at hf
    subst hf
    exact hI

/-- A counted loop with an invariant indexed by the number of runs done. -/
theorem sat_countLoop {S : Nat} {a : Nat} {body : Stmt} (hlf : LoopFree body) (T : Nat) (I : Nat → Config → Prop)
    (hstep : ∀ j c, j < T → I j c → c.reg a = T - j →
      AddrOK S body c ∧ I (j + 1) (run body c) ∧ (run body c).reg a + 1 = c.reg a) :
    SatB S (.loop a body) (fun c => I 0 c ∧ c.reg a = T) (fun c => iterate (run body) (c.reg a) c)
        (T * (size body + 1) + 1) ∧
      ∀ c, I 0 c → c.reg a = T → I T (iterate (run body) T c) := by
  let P : Config → Prop := fun c => ∃ j, j ≤ T ∧ c.reg a = T - j ∧ I j c
  have hP : ∀ c, P c → c.reg a ≠ 0 → AddrOK S body c ∧ P (run body c) ∧ (run body c).reg a + 1 = c.reg a := by
    intro c ⟨j, hj, ha, hI⟩ ha0
    have hjT : j < T := by omega
    obtain ⟨h0, h1, h2⟩ := hstep j c hjT hI ha
    exact ⟨h0, ⟨j + 1, by omega, by omega, h1⟩, h2⟩
  refine ⟨?_, ?_⟩
  · have := SatB.loop (P := P) (L := T) (SatB.ofLoopFree hlf (fun c hc => (hP c hc.1 hc.2).1))
      (fun c hc hm => (hP c hc hm).2.1) (fun c hc hm => (hP c hc hm).2.2) (fun c ⟨j, _, ha, _⟩ => by omega)
    exact this.mono (fun c ⟨h0, ha⟩ => ⟨0, Nat.zero_le _, by omega, h0⟩) (Nat.le_refl _)
  · intro c h0 ha
    obtain ⟨⟨j, hj, ha', hI⟩, hz⟩ := iterate_invariant (a := a) (P := P)
      (fun c hc hm => (hP c hc hm).2.1) (fun c hc hm => (hP c hc hm).2.2) T c ⟨0, Nat.zero_le _, by omega, h0⟩ ha
    have : j = T := by omega
    subst this
    exact hI

/-! ### Relational loop rules -/

/-- A loop over a list `xs` of items written as `code x`: `cnt` counts the items left, and one run of
`body` reads one item, within `b x` steps and the space `S`. -/
theorem exec_listPass {S : Nat} {α : Type} (code : α → List Nat) (xs : List α) {cnt : Nat} {body : Stmt}
    (I : List α → Config → Prop) (b : α → Nat)
    (hstep : ∀ pre x suf c, pre ++ x :: suf = xs → I pre c → c.reg cnt = suf.length + 1 →
      At c (code x ++ suf.flatMap code) →
      ∃ t c', ExecB S body c t c' ∧ t ≤ b x ∧ I (pre ++ [x]) c' ∧ c'.reg cnt = suf.length ∧
        At c' (suf.flatMap code)) :
    ∀ c, I [] c → c.reg cnt = xs.length → At c (xs.flatMap code) →
      ∃ t c', ExecB S (.loop cnt body) c t c' ∧ t ≤ (xs.map fun x => b x + 1).sum + 1 ∧ I xs c' := by
  have key : ∀ suf pre c, pre ++ suf = xs → I pre c → c.reg cnt = suf.length → At c (suf.flatMap code) →
      ∃ t c', ExecB S (.loop cnt body) c t c' ∧ t ≤ (suf.map fun x => b x + 1).sum + 1 ∧ I xs c' := by
    intro suf
    induction suf with
    | nil =>
      intro pre c hpre hI hc _
      simp only [List.append_nil] at hpre
      subst hpre
      exact ⟨1, c, ExecB.loopDone (by simpa using hc), by simp, hI⟩
    | cons x suf ih =>
      intro pre c hpre hI hc hAt
      simp only [List.flatMap_cons] at hAt
      obtain ⟨t, c', he, ht, hI', hc', hAt'⟩ := hstep pre x suf c hpre hI (by simpa using hc) hAt
      obtain ⟨t', c'', he', ht', hI''⟩ := ih (pre ++ [x]) c' (by simp [← hpre]) hI' hc' hAt'
      refine ⟨t + t' + 1, c'', ExecB.loopNext (by simp at hc; omega) he he', ?_, hI''⟩
      simp only [List.map_cons, List.sum_cons]; omega
  intro c hI hc hAt
  exact key xs [] c rfl hI hc hAt

/-- A loop run `T` times, with an invariant indexed by the number of runs done. -/
theorem exec_countLoop {S : Nat} {a : Nat} {body : Stmt} (T : Nat) (I : Nat → Config → Prop) (b : Nat)
    (hstep : ∀ j c, j < T → I j c → c.reg a = T - j →
      ∃ t c', ExecB S body c t c' ∧ t ≤ b ∧ I (j + 1) c' ∧ c'.reg a + 1 = c.reg a) :
    ∀ c, I 0 c → c.reg a = T → ∃ t c', ExecB S (.loop a body) c t c' ∧ t ≤ T * (b + 1) + 1 ∧ I T c' := by
  have key : ∀ r j c, j + r = T → I j c → c.reg a = r →
      ∃ t c', ExecB S (.loop a body) c t c' ∧ t ≤ r * (b + 1) + 1 ∧ I T c' := by
    intro r
    induction r with
    | zero =>
      intro j c hj hI hc
      simp only [Nat.add_zero] at hj
      subst hj
      exact ⟨1, c, ExecB.loopDone hc, by simp, hI⟩
    | succ r ih =>
      intro j c hj hI hc
      obtain ⟨t, c', he, ht, hI', hc'⟩ := hstep j c (by omega) hI (by omega)
      obtain ⟨t', c'', he', ht', hI''⟩ := ih (j + 1) c' (by omega) hI' (by omega)
      refine ⟨t + t' + 1, c'', ExecB.loopNext (by omega) he he', ?_, hI''⟩
      rw [Nat.succ_mul]; omega
  intro c hI hc
  exact key T 0 c (by omega) hI hc

/-- Running an address-safe loop-free block, relationally. -/
theorem exec_loopFree {S : Nat} {s : Stmt} (h : LoopFree s) (c : Config) (hA : AddrOK S s c) :
    ∃ t, ExecB S s c t (run s c) ∧ t ≤ size s :=
  ⟨_, execB_run s h c hA, cost_le_size s c⟩

end STACS2027.RAM
