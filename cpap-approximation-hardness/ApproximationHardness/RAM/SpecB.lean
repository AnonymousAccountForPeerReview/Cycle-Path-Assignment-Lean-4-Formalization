module

public import ApproximationHardness.RAM.Spec
public import ApproximationHardness.RAM.Bounded
import Lean.Elab.Tactic.Omega

/-!
# Reasoning about space-bounded runs

The bounded-address twin of `Spec.lean`, for the runs `ExecB S` of `Bounded.lean`:

* `AddrOK S s c` (loop-free `s`): every `load`/`store` address along `run s c` is below `S`.
  The simp lemmas `addrOK_load`, `addrOK_store`, `addrOK_seq`, `addrOK_ifz`, `addrOK_seqs_cons`
  reduce it to arithmetic on the intermediate configurations; `addrOK_seqs_append` splits a
  sequence; code without `load`/`store` is address-safe (`AddrOK.of_memFree`);
* `execB_run`: the bounded run of an address-safe loop-free program;
* `SatB S s P m b`: from every configuration satisfying `P`, `s` halts in `m c` within `b`
  steps, by a run accessing only the addresses below `S`. Every rule of `Sat` has a twin with
  the same name: `SatB.ofLoopFree` (with the address condition `∀ c, P c → AddrOK S s c`),
  `SatB.mono`, `SatB.congr`, `SatB.seq`, `SatB.loop`; the bridges are `SatB.toSat` (forget the
  bound), **`SatB.of_Sat`** (lifting: for memory-free code, `memFree s = true`, a `Sat` proof is
  a `SatB` proof for every `S`), `SatB.mono_S`, and `SatB.computesIn` (a triple from the initial
  configuration is a bounded computation).
-/

@[expose] public section

namespace STACS2027.RAM

@[simp] theorem reg_ite {p : Prop} [Decidable p] (a b : Config) (i : Nat) :
    (if p then a else b).reg i = if p then a.reg i else b.reg i := by split <;> rfl
@[simp] theorem mem_ite {p : Prop} [Decidable p] (a b : Config) :
    (if p then a else b).mem = if p then a.mem else b.mem := by split <;> rfl
@[simp] theorem out_ite {p : Prop} [Decidable p] (a b : Config) :
    (if p then a else b).out = if p then a.out else b.out := by split <;> rfl

/-! ### Address safety of loop-free code -/

/-- Every `load`/`store` address along the run of the loop-free program `s` from `c` is below
`S` (`True` for a loop, which `run` does not execute). -/
def AddrOK (S : Nat) : Stmt → Config → Prop
  | .load _ a, c => c.reg a < S
  | .store a _, c => c.reg a < S
  | .seq s t, c => AddrOK S s c ∧ AddrOK S t (run s c)
  | .ifz a s t, c => (c.reg a = 0 → AddrOK S s c) ∧ (c.reg a ≠ 0 → AddrOK S t c)
  | _, _ => True

section addrOK

variable {S : Nat} {c : Config}

@[simp] theorem addrOK_skip : AddrOK S .skip c ↔ True := Iff.rfl
@[simp] theorem addrOK_const (d v : Nat) : AddrOK S (.const d v) c ↔ True := Iff.rfl
@[simp] theorem addrOK_add (d a b : Nat) : AddrOK S (.add d a b) c ↔ True := Iff.rfl
@[simp] theorem addrOK_sub (d a b : Nat) : AddrOK S (.sub d a b) c ↔ True := Iff.rfl
@[simp] theorem addrOK_write (a : Nat) : AddrOK S (.write a) c ↔ True := Iff.rfl
@[simp] theorem addrOK_loop (a : Nat) (b : Stmt) : AddrOK S (.loop a b) c ↔ True := Iff.rfl
@[simp] theorem addrOK_load (d a : Nat) : AddrOK S (.load d a) c ↔ c.reg a < S := Iff.rfl
@[simp] theorem addrOK_store (a b : Nat) : AddrOK S (.store a b) c ↔ c.reg a < S := Iff.rfl
@[simp] theorem addrOK_seq (s t : Stmt) :
    AddrOK S (.seq s t) c ↔ AddrOK S s c ∧ AddrOK S t (run s c) := Iff.rfl
@[simp] theorem addrOK_ifz (a : Nat) (s t : Stmt) :
    AddrOK S (.ifz a s t) c ↔ (c.reg a = 0 → AddrOK S s c) ∧ (c.reg a ≠ 0 → AddrOK S t c) := Iff.rfl
@[simp] theorem addrOK_seqs_cons (s : Stmt) (ss : List Stmt) :
    AddrOK S (seqs (s :: ss)) c ↔ AddrOK S s c ∧ AddrOK S (seqs ss) (run s c) := Iff.rfl
@[simp] theorem addrOK_seqs_nil : AddrOK S (seqs []) c ↔ True := Iff.rfl

theorem addrOK_seqs_append (A B : List Stmt) (c : Config) :
    AddrOK S (seqs (A ++ B)) c ↔ AddrOK S (seqs A) c ∧ AddrOK S (seqs B) (run (seqs A) c) := by
  induction A generalizing c with
  | nil => simp [seqs, run]
  | cons s A ih => simp only [List.cons_append, addrOK_seqs_cons, ih, run_seqs_cons, and_assoc]

/-- Code without memory access is address-safe. -/
theorem addrOK_of_memFree : ∀ {s : Stmt}, memFree s = true → ∀ c, AddrOK S s c
  | .skip, _, _ | .const .., _, _ | .add .., _, _ | .sub .., _, _ | .write .., _, _
  | .loop .., _, _ => trivial
  | .load .., h, _ | .store .., h, _ => absurd h (by simp [memFree])
  | .seq _ _, h, c => by
    simp only [memFree_seq, Bool.and_eq_true] at h
    exact ⟨addrOK_of_memFree h.1 c, addrOK_of_memFree h.2 _⟩
  | .ifz _ _ _, h, c => by
    simp only [memFree_ifz, Bool.and_eq_true] at h
    exact ⟨fun _ => addrOK_of_memFree h.1 c, fun _ => addrOK_of_memFree h.2 c⟩

/-- Code without memory access (`AddrOK.of_memFree rfl`). -/
theorem AddrOK.of_memFree {s : Stmt} (hm : memFree s = true) : AddrOK S s c := addrOK_of_memFree hm c

/-- Monotone in the bound. -/
theorem AddrOK.mono {S' : Nat} (hS : S ≤ S') : ∀ {s : Stmt} {c : Config}, AddrOK S s c → AddrOK S' s c
  | .load .., _, h | .store .., _, h => Nat.lt_of_lt_of_le h hS
  | .seq _ _, _, h => ⟨AddrOK.mono hS h.1, AddrOK.mono hS h.2⟩
  | .ifz _ _ _, _, h => ⟨fun ha => AddrOK.mono hS (h.1 ha), fun ha => AddrOK.mono hS (h.2 ha)⟩
  | .skip, _, _ | .const .., _, _ | .add .., _, _ | .sub .., _, _ | .write .., _, _
  | .loop .., _, _ => trivial

/-- The two halves of a sequence. -/
theorem AddrOK.seq {s t : Stmt} (h₁ : AddrOK S s c) (h₂ : AddrOK S t (run s c)) : AddrOK S (.seq s t) c :=
  ⟨h₁, h₂⟩

/-- The two branches of a test. -/
theorem AddrOK.ifz {a : Nat} {s t : Stmt} (h₁ : c.reg a = 0 → AddrOK S s c) (h₂ : c.reg a ≠ 0 → AddrOK S t c) :
    AddrOK S (.ifz a s t) c := ⟨h₁, h₂⟩

/-- A sequence `A ++ B` whose second part has no memory access. -/
theorem AddrOK.append_memFree {A B : List Stmt} (hA : AddrOK S (seqs A) c) (hB : memFree (seqs B) = true) :
    AddrOK S (seqs (A ++ B)) c :=
  (addrOK_seqs_append A B c).mpr ⟨hA, AddrOK.of_memFree hB⟩

end addrOK

/-! ### Memory-free sequences -/

@[simp] theorem memFree_seqs_cons (s : Stmt) (ss : List Stmt) :
    memFree (seqs (s :: ss)) = (memFree s && memFree (seqs ss)) := rfl
@[simp] theorem memFree_seqs_nil : memFree (seqs []) = true := rfl

theorem memFree_seqs_append {A B : List Stmt} (hA : memFree (seqs A) = true) (hB : memFree (seqs B) = true) :
    memFree (seqs (A ++ B)) = true := by
  induction A with
  | nil => exact hB
  | cons s A ih =>
    simp only [memFree_seqs_cons, Bool.and_eq_true] at hA
    simp only [List.cons_append, memFree_seqs_cons, hA.1, ih hA.2, Bool.and_self]

theorem memFree_flatMap {α : Type} (es : List α) (F : α → List Stmt) (h : ∀ e, memFree (seqs (F e)) = true) :
    memFree (seqs (es.flatMap F)) = true := by
  induction es with
  | nil => rfl
  | cons e es ih => exact memFree_seqs_append (h e) ih

/-! ### Bounded runs of loop-free code -/

/-- The bounded run of an address-safe loop-free program. -/
theorem execB_run {S : Nat} : ∀ (s : Stmt), LoopFree s → ∀ c, AddrOK S s c →
    ExecB S s c (cost s c) (run s c)
  | .skip, _, c, _ => ExecB.skip c
  | .const d v, _, c, _ => ExecB.const d v c
  | .add d a b, _, c, _ => ExecB.add d a b c
  | .sub d a b, _, c, _ => ExecB.sub d a b c
  | .load d a, _, c, h => ExecB.load d a c h
  | .store a b, _, c, h => ExecB.store a b c h
  | .write a, _, c, _ => ExecB.write a c
  | .seq s t, h, c, hA => ExecB.seq (execB_run s h.1 c hA.1) (execB_run t h.2 _ hA.2)
  | .ifz a s t, h, c, hA => by
    by_cases ha : c.reg a = 0
    · simp only [run, cost, ha, ↓reduceIte]
      exact ExecB.ifzTrue ha (execB_run s h.1 c (hA.1 ha))
    · simp only [run, cost, ha, ↓reduceIte]
      exact ExecB.ifzFalse ha (execB_run t h.2 c (hA.2 ha))
  | .loop _ _, h, _, _ => absurd h id

/-! ### Triples -/

/-- From every configuration satisfying `P`, `s` halts in `m c` within `b` steps, by a run
accessing only the memory addresses below `S`. -/
def SatB (S : Nat) (s : Stmt) (P : Config → Prop) (m : Config → Config) (b : Nat) : Prop :=
  ∀ c, P c → ∃ t, ExecB S s c t (m c) ∧ t ≤ b

namespace SatB

variable {S S' : Nat} {s u : Stmt} {P P' Q : Config → Prop} {m m' : Config → Config} {b b' : Nat}

/-- Forget the space bound. -/
theorem toSat (h : SatB S s P m b) : Sat s P m b := fun c hc =>
  let ⟨t, he, ht⟩ := h c hc
  ⟨t, he.exec, ht⟩

/-- **Lifting** for code without `load`/`store`: a `Sat` proof is a `SatB` proof for every `S`. -/
theorem of_Sat (hm : memFree s = true) (h : Sat s P m b) : SatB S s P m b := fun c hc =>
  let ⟨t, he, ht⟩ := h c hc
  ⟨t, Exec.toExecB_of_memFree hm he, ht⟩

/-- Monotone in the space bound. -/
theorem mono_S (hS : S ≤ S') (h : SatB S s P m b) : SatB S' s P m b := fun c hc =>
  let ⟨t, he, ht⟩ := h c hc
  ⟨t, he.mono hS, ht⟩

/-- A loop-free program, address-safe on the configurations satisfying `P`. -/
theorem ofLoopFree (h : LoopFree s) (hA : ∀ c, P c → AddrOK S s c) : SatB S s P (run s) (size s) :=
  fun c hc => ⟨_, execB_run s h c (hA c hc), cost_le_size s c⟩

theorem mono (h : SatB S s P m b) (hP : ∀ c, P' c → P c) (hb : b ≤ b') : SatB S s P' m b' := by
  intro c hc
  obtain ⟨t, he, ht⟩ := h c (hP c hc)
  exact ⟨t, he, Nat.le_trans ht hb⟩

theorem congr (h : SatB S s P m b) (hm : ∀ c, P c → m c = m' c) : SatB S s P m' b := by
  intro c hc
  obtain ⟨t, he, ht⟩ := h c hc
  exact ⟨t, hm c hc ▸ he, ht⟩

theorem seq {m₁ m₂ : Config → Config} {b₁ b₂ : Nat} (h₁ : SatB S s P m₁ b₁) (hQ : ∀ c, P c → Q (m₁ c))
    (h₂ : SatB S u Q m₂ b₂) : SatB S (.seq s u) P (fun c => m₂ (m₁ c)) (b₁ + b₂) := by
  intro c hc
  obtain ⟨t, he, ht⟩ := h₁ c hc
  obtain ⟨t', he', ht'⟩ := h₂ _ (hQ c hc)
  exact ⟨t + t', ExecB.seq he he', by omega⟩

/-- A counted loop: every body run decrements the counter `a` by one and preserves `P`;
`a` is at most `L` under `P`. -/
theorem loop {a : Nat} {body : Stmt} {L : Nat} (hb : SatB S body (fun c => P c ∧ c.reg a ≠ 0) m b)
    (hP : ∀ c, P c → c.reg a ≠ 0 → P (m c))
    (hdec : ∀ c, P c → c.reg a ≠ 0 → (m c).reg a + 1 = c.reg a)
    (hL : ∀ c, P c → c.reg a ≤ L) :
    SatB S (.loop a body) P (fun c => iterate m (c.reg a) c) (L * (b + 1) + 1) := by
  have key : ∀ k c, P c → c.reg a = k →
      ∃ t, ExecB S (.loop a body) c t (iterate m k c) ∧ t ≤ k * (b + 1) + 1 := by
    intro k
    induction k with
    | zero =>
      intro c _ hk
      exact ⟨1, ExecB.loopDone hk, by simp⟩
    | succ k ih =>
      intro c hc hk
      have ha : c.reg a ≠ 0 := by omega
      obtain ⟨t, he, ht⟩ := hb c ⟨hc, ha⟩
      obtain ⟨t', he', ht'⟩ := ih (m c) (hP c hc ha) (by have := hdec c hc ha; omega)
      refine ⟨t + t' + 1, ExecB.loopNext ha he he', ?_⟩
      rw [Nat.succ_mul]; omega
  intro c hc
  obtain ⟨t, he, ht⟩ := key (c.reg a) c hc rfl
  refine ⟨t, he, ?_⟩
  have := Nat.mul_le_mul_right (b + 1) (hL c hc)
  omega

/-- A triple from the initial configuration on `input` is a computation within the space `S`. -/
theorem computesIn {input output : List Nat} (h : SatB S s (fun c => c = initial input) m b)
    (hout : (m (initial input)).out = output) : ∃ t, ComputesIn s input output t S ∧ t ≤ b := by
  obtain ⟨t, he, ht⟩ := h _ rfl
  exact ⟨t, ⟨_, he, hout⟩, ht⟩

end SatB

end STACS2027.RAM
