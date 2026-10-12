module

public import Outerplanar.RAM.Bounded
public import Outerplanar.RAM.Frame
import Mathlib.Tactic

/-!
# A Hoare logic with step and space bounds

`HTB S s P Q b`: from every configuration satisfying `P`, the program `s` halts in a
configuration satisfying `Q` within `b` steps, by a run that accesses only the memory
addresses below `S` (`ExecB S`). `HTBt S s P Q`: the same with a postcondition that may mention
the step count. This file is the space-bounded twin of `HT.lean` and of the structural rules of
`Frame.lean`: every rule `HT.foo` has a twin `HTB.foo` with the same hypotheses (the bound `S` is
implicit), so porting a proof is mostly replacing `HT` by `HTB S`.

The only rules with new hypotheses are those for loop-free code: `AddrOK S s c` says that every
`load`/`store` address along the run of the loop-free program `s` from `c` is below `S`
(simp lemmas `addrOK_seq`, `addrOK_ifz`, `addrOK_load`, … reduce it to arithmetic;
constructors `AddrOK.seq`, `AddrOK.ifz`, `AddrOK.of_memFree`), and
* `HTB.run (hs : LoopFree s) (h : ∀ c, P c → AddrOK S s c ∧ Q (run s c)) : HTB S s P Q (size s)`,
* `HTB.run_le (hs) (hb : size s ≤ b) (h : ∀ c, P c → AddrOK S s c ∧ Q (run s c))`,
* `HTB.run_le' (hs) (hb) (hA : ∀ c, P c → AddrOK S s c) (h : ∀ c, P c → Q (run s c))`.

Bridges:
* `HTB.toHT : HTB S s P Q b → HT s P Q b` (forget the space bound);
* `HTB.of_HT (hm : memFree s = true) : HT s P Q b → HTB S s P Q b`: code without `load`/`store`
  (register arithmetic, control, allocation, output) reuses its `HT` proofs unchanged;
* `HTB.of_HT_addrOK (hs : LoopFree s) (hA : ∀ c, P c → AddrOK S s c) : HT s P Q b → HTB S s P Q b`:
  loop-free code reuses its `HT` proof, only the address obligation is new;
* `HTB.mono_S : S ≤ S' → HTB S s P Q b → HTB S' s P Q b`;
* `HTB.computesIn`: a triple from the initial configuration gives `ComputesIn`.

Further generic rules (twins of rules used in the client packages): `HTB.of_false`,
`HTB.assoc`, `HTB.reassoc`, `HTB.pre_fact`, `HTB.memRestore`.
-/

@[expose] public section

namespace STACS2027.RAM

/-! ### Frames of bounded runs -/

theorem ExecB.frame {S : ℕ} {s : Stmt} {c c' : Config} {t : ℕ} (h : ExecB S s c t c') :
    Frame s c c' := h.exec.frame

theorem ExecB.reg_frame {S : ℕ} {s : Stmt} {c c' : Config} {t r : ℕ} (h : ExecB S s c t c')
    (hr : r ∉ wregs s) : c'.reg r = c.reg r := h.exec.reg_frame hr

theorem ExecB.mem_frame {S : ℕ} {s : Stmt} {c c' : Config} {t : ℕ} (h : ExecB S s c t c')
    (hs : stores s = false) : c'.mem = c.mem := h.exec.mem_frame hs

theorem ExecB.out_frame {S : ℕ} {s : Stmt} {c c' : Config} {t : ℕ} (h : ExecB S s c t c')
    (hw : writes s = false) : c'.out = c.out := h.exec.out_frame hw

/-- Register-only assertions survive bounded runs. -/
theorem RegIndep.execB {P : Config → Prop} {S : ℕ} {s : Stmt} (h : RegIndep (wregs s) P)
    {c c' : Config} {t : ℕ} (he : ExecB S s c t c') (hc : P c) : P c' := h.exec he.exec hc

/-! ### Address safety of loop-free code -/

/-- Every `load`/`store` address along the run of the loop-free program `s` from `c` is below
`S` (`True` for a loop, which `run` does not execute). -/
def AddrOK (S : ℕ) : Stmt → Config → Prop
  | .load _ a, c => c.reg a < S
  | .store a _, c => c.reg a < S
  | .seq s t, c => AddrOK S s c ∧ AddrOK S t (run s c)
  | .ifz a s t, c => (c.reg a = 0 → AddrOK S s c) ∧ (c.reg a ≠ 0 → AddrOK S t c)
  | _, _ => True

section addrOK

variable {S : ℕ} {c : Config}

@[simp] theorem addrOK_skip : AddrOK S .skip c ↔ True := Iff.rfl
@[simp] theorem addrOK_const (d v : ℕ) : AddrOK S (.const d v) c ↔ True := Iff.rfl
@[simp] theorem addrOK_add (d a b : ℕ) : AddrOK S (.add d a b) c ↔ True := Iff.rfl
@[simp] theorem addrOK_sub (d a b : ℕ) : AddrOK S (.sub d a b) c ↔ True := Iff.rfl
@[simp] theorem addrOK_write (a : ℕ) : AddrOK S (.write a) c ↔ True := Iff.rfl
@[simp] theorem addrOK_load (d a : ℕ) : AddrOK S (.load d a) c ↔ c.reg a < S := Iff.rfl
@[simp] theorem addrOK_store (a b : ℕ) : AddrOK S (.store a b) c ↔ c.reg a < S := Iff.rfl
@[simp] theorem addrOK_seq (s t : Stmt) :
    AddrOK S (.seq s t) c ↔ AddrOK S s c ∧ AddrOK S t (run s c) := Iff.rfl
@[simp] theorem addrOK_ifz (a : ℕ) (s t : Stmt) :
    AddrOK S (.ifz a s t) c ↔ (c.reg a = 0 → AddrOK S s c) ∧ (c.reg a ≠ 0 → AddrOK S t c) := Iff.rfl

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

/-- Monotone in the bound. -/
theorem AddrOK.mono {S' : ℕ} (hS : S ≤ S') : ∀ {s : Stmt} {c : Config}, AddrOK S s c → AddrOK S' s c
  | .load .., _, h | .store .., _, h => Nat.lt_of_lt_of_le h hS
  | .seq _ _, _, h => ⟨AddrOK.mono hS h.1, AddrOK.mono hS h.2⟩
  | .ifz _ _ _, _, h => ⟨fun ha => AddrOK.mono hS (h.1 ha), fun ha => AddrOK.mono hS (h.2 ha)⟩
  | .skip, _, _ | .const .., _, _ | .add .., _, _ | .sub .., _, _ | .write .., _, _
  | .loop .., _, _ => trivial

/-- The two halves of a sequence. -/
theorem AddrOK.seq {s t : Stmt} (h₁ : AddrOK S s c) (h₂ : AddrOK S t (run s c)) :
    AddrOK S (.seq s t) c := ⟨h₁, h₂⟩

/-- The two branches of a test. -/
theorem AddrOK.ifz {a : ℕ} {s t : Stmt} (h₁ : c.reg a = 0 → AddrOK S s c)
    (h₂ : c.reg a ≠ 0 → AddrOK S t c) : AddrOK S (.ifz a s t) c := ⟨h₁, h₂⟩

/-- Code without memory access (`AddrOK.of_memFree rfl`). -/
theorem AddrOK.of_memFree {s : Stmt} (hm : memFree s = true) : AddrOK S s c :=
  addrOK_of_memFree hm c

end addrOK

/-- The bounded run of an address-safe loop-free program. -/
theorem execB_run {S : ℕ} : ∀ (s : Stmt), LoopFree s → ∀ c, AddrOK S s c →
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

/-- A bounded run of a loop-free program is address-safe. -/
theorem ExecB.addrOK {S : ℕ} : ∀ {s : Stmt} {c c' : Config} {t : ℕ}, LoopFree s →
    ExecB S s c t c' → AddrOK S s c
  | .skip, _, _, _, _, _ | .const .., _, _, _, _, _ | .add .., _, _, _, _, _
  | .sub .., _, _, _, _, _ | .write .., _, _, _, _, _ => trivial
  | .load .., _, _, _, _, h => by cases h; assumption
  | .store .., _, _, _, _, h => by cases h; assumption
  | .seq s u, _, _, _, hs, h => by
    cases h with
    | seq h₁ h₂ =>
      refine ⟨ExecB.addrOK hs.1 h₁, ?_⟩
      obtain ⟨_, rfl⟩ := h₁.det_exec (exec_run s hs.1 _)
      exact ExecB.addrOK hs.2 h₂
  | .ifz _ _ _, _, _, _, hs, h => by
    cases h with
    | ifzTrue ha h' => exact ⟨fun _ => ExecB.addrOK hs.1 h', fun h0 => absurd ha h0⟩
    | ifzFalse ha h' => exact ⟨fun h0 => absurd h0 ha, fun _ => ExecB.addrOK hs.2 h'⟩
  | .loop .., _, _, _, hs, _ => absurd hs id

/-! ### Triples -/

/-- From every configuration satisfying `P`, `s` halts, by a run accessing only the addresses
below `S`, in one satisfying `Q c' t`, where `t` is the number of steps. -/
def HTBt (S : ℕ) (s : Stmt) (P : Config → Prop) (Q : Config → ℕ → Prop) : Prop :=
  ∀ c, P c → ∃ c' t, ExecB S s c t c' ∧ Q c' t

/-- From every configuration satisfying `P`, `s` halts within `b` steps in one satisfying `Q`,
by a run accessing only the addresses below `S`. -/
def HTB (S : ℕ) (s : Stmt) (P Q : Config → Prop) (b : ℕ) : Prop :=
  HTBt S s P (fun c' t => Q c' ∧ t ≤ b)

namespace HTBt

variable {S S' : ℕ} {s : Stmt} {P : Config → Prop} {Q : Config → ℕ → Prop}

theorem toHTt (h : HTBt S s P Q) : HTt s P Q := fun c hc =>
  let ⟨c', t, he, hq⟩ := h c hc
  ⟨c', t, he.exec, hq⟩

theorem of_HTt (hm : memFree s = true) (h : HTt s P Q) : HTBt S s P Q := fun c hc =>
  let ⟨c', t, he, hq⟩ := h c hc
  ⟨c', t, Exec.toExecB_of_memFree hm he, hq⟩

theorem mono_S (hS : S ≤ S') (h : HTBt S s P Q) : HTBt S' s P Q := fun c hc =>
  let ⟨c', t, he, hq⟩ := h c hc
  ⟨c', t, he.mono hS, hq⟩

end HTBt

namespace HTB

variable {S S' : ℕ} {s u : Stmt} {P P' Q Q' R F : Config → Prop} {b b' : ℕ}

/-! #### Bridges -/

/-- Forget the space bound. -/
theorem toHT (h : HTB S s P Q b) : HT s P Q b := HTBt.toHTt h

/-- **Lifting** for code without `load`/`store`: an `HT` proof is an `HTB` proof for every `S`. -/
theorem of_HT (hm : memFree s = true) (h : HT s P Q b) : HTB S s P Q b := HTBt.of_HTt hm h

/-- **Lifting for loop-free code**: an `HT` triple of a loop-free program whose runs are
address-safe from the precondition is an `HTB` triple. (The `HT` proof is reused unchanged;
only `AddrOK` is new.) -/
theorem of_HT_addrOK (hs : LoopFree s) (hA : ∀ c, P c → AddrOK S s c) (h : HT s P Q b) :
    HTB S s P Q b := by
  intro c hc
  obtain ⟨c', t, he, hq, ht⟩ := h c hc
  obtain ⟨rfl, rfl⟩ := Exec.det (exec_run s hs c) he
  exact ⟨_, _, execB_run s hs c (hA c hc), hq, ht⟩

/-- Monotone in the space bound. -/
theorem mono_S (hS : S ≤ S') (h : HTB S s P Q b) : HTB S' s P Q b := HTBt.mono_S hS h

/-- A triple from the initial configuration on `input` gives a bounded computation. -/
theorem computesIn {input output : List ℕ} (h : HTB S s (fun c => c = initial input)
    (fun c => c.out = output) b) : ∃ t, t ≤ b ∧ ComputesIn s input output t S := by
  obtain ⟨c', t, he, hout, ht⟩ := h _ rfl
  exact ⟨t, ht, c', he, hout⟩

/-- A triple with any postcondition from the initial configuration: a bounded computation of
an output satisfying the postcondition. -/
theorem computesIn_post {input : List ℕ} {O : List ℕ → Prop}
    (h : HTB S s (fun c => c = initial input) (fun c => O c.out) b) :
    ∃ out t, t ≤ b ∧ O out ∧ ComputesIn s input out t S := by
  obtain ⟨c', t, he, hout, ht⟩ := h _ rfl
  exact ⟨c'.out, t, ht, hout, c', he, rfl⟩

/-! #### The rules of `HT.lean` -/

theorem mono (h : HTB S s P Q b) (hP : ∀ c, P' c → P c) (hQ : ∀ c, Q c → Q' c) (hb : b ≤ b') :
    HTB S s P' Q' b' := by
  intro c hc
  obtain ⟨c', t, he, hq, ht⟩ := h c (hP c hc)
  exact ⟨c', t, he, hQ c' hq, le_trans ht hb⟩

theorem pre {P' : Config → Prop} (h : HTB S s P Q b) (hP : ∀ c, P' c → P c) : HTB S s P' Q b :=
  h.mono hP (fun _ h => h) le_rfl

theorem post {Q' : Config → Prop} (h : HTB S s P Q b) (hQ : ∀ c, Q c → Q' c) : HTB S s P Q' b :=
  h.mono (fun _ h => h) hQ le_rfl

theorem weaken (h : HTB S s P Q b) (hb : b ≤ b') : HTB S s P Q b' :=
  h.mono (fun _ h => h) (fun _ h => h) hb

/-- Sequencing. -/
theorem seq (h₁ : HTB S s P R b) (h₂ : HTB S u R Q b') : HTB S (.seq s u) P Q (b + b') := by
  intro c hc
  obtain ⟨c₁, t₁, he₁, hr, ht₁⟩ := h₁ c hc
  obtain ⟨c₂, t₂, he₂, hq, ht₂⟩ := h₂ c₁ hr
  exact ⟨c₂, t₁ + t₂, ExecB.seq he₁ he₂, hq, by omega⟩

/-- Branching on a register. -/
theorem ifz {a : ℕ} (h₁ : HTB S s (fun c => P c ∧ c.reg a = 0) Q b)
    (h₂ : HTB S u (fun c => P c ∧ c.reg a ≠ 0) Q b) : HTB S (.ifz a s u) P Q (b + 1) := by
  intro c hc
  by_cases ha : c.reg a = 0
  · obtain ⟨c', t, he, hq, ht⟩ := h₁ c ⟨hc, ha⟩
    exact ⟨c', t + 1, ExecB.ifzTrue ha he, hq, by omega⟩
  · obtain ⟨c', t, he, hq, ht⟩ := h₂ c ⟨hc, ha⟩
    exact ⟨c', t + 1, ExecB.ifzFalse ha he, hq, by omega⟩

/-- **Loop-free code**: the final configuration is `run s c`; every address must be below `S`. -/
theorem run (hs : LoopFree s) (h : ∀ c, P c → AddrOK S s c ∧ Q (RAM.run s c)) :
    HTB S s P Q (size s) := by
  intro c hc
  exact ⟨_, _, execB_run s hs c (h c hc).1, (h c hc).2, cost_le_size s c⟩

/-- A loop with a potential (see `HT.loopPot`). -/
theorem loopPot {a : ℕ} {body : Stmt} {Inv : Config → Prop} (Φ : Config → ℕ)
    (hbody : ∀ v, HTBt S body (fun c => Inv c ∧ c.reg a ≠ 0 ∧ Φ c = v)
      (fun c' t => Inv c' ∧ Φ c' + t + 1 ≤ v)) :
    ∀ c, Inv c → ∃ c' t, ExecB S (.loop a body) c t c' ∧ Inv c' ∧ c'.reg a = 0 ∧
      t + Φ c' ≤ Φ c + 1 := by
  intro c
  induction hv : Φ c using Nat.strong_induction_on generalizing c with
  | _ v ih =>
  intro hc
  by_cases ha : c.reg a = 0
  · exact ⟨c, 1, ExecB.loopDone ha, hc, ha, by omega⟩
  · obtain ⟨c₁, t₁, he₁, hi₁, hΦ₁⟩ := hbody v c ⟨hc, ha, hv⟩
    obtain ⟨c', t₂, he₂, hi', ha', hΦ'⟩ := ih (Φ c₁) (by omega) c₁ rfl hi₁
    exact ⟨c', t₁ + t₂ + 1, ExecB.loopNext ha he₁ he₂, hi', ha', by omega⟩

/-- A loop with a potential bounded by `K` under the invariant. -/
theorem loop {a : ℕ} {body : Stmt} {Inv : Config → Prop} (Φ : Config → ℕ) {K : ℕ}
    (hbody : ∀ v, HTBt S body (fun c => Inv c ∧ c.reg a ≠ 0 ∧ Φ c = v)
      (fun c' t => Inv c' ∧ Φ c' + t + 1 ≤ v))
    (hK : ∀ c, Inv c → Φ c ≤ K) :
    HTB S (.loop a body) Inv (fun c => Inv c ∧ c.reg a = 0) (K + 1) := by
  intro c hc
  obtain ⟨c', t, he, hi, ha, ht⟩ := loopPot Φ hbody c hc
  exact ⟨c', t, he, ⟨hi, ha⟩, by have := hK c hc; omega⟩

/-- A body with a fixed bound `T` lowering the potential by at least `T + 1`. -/
theorem body_of_HT {body : Stmt} {Inv : Config → Prop} {a : ℕ} {Φ : Config → ℕ} {T : ℕ}
    (h : ∀ v, HTB S body (fun c => Inv c ∧ c.reg a ≠ 0 ∧ Φ c = v)
      (fun c' => Inv c' ∧ Φ c' + T + 1 ≤ v) T) :
    ∀ v, HTBt S body (fun c => Inv c ∧ c.reg a ≠ 0 ∧ Φ c = v)
      (fun c' t => Inv c' ∧ Φ c' + t + 1 ≤ v) := by
  intro v c hc
  obtain ⟨c', t, he, ⟨hi, hΦ⟩, ht⟩ := h v c hc
  exact ⟨c', t, he, hi, by omega⟩

/-! #### The rules of `Frame.lean` -/

theorem skip : HTB S .skip P P 1 := fun c hc => ⟨c, 1, ExecB.skip c, hc, le_rfl⟩

/-- Loop-free code with an explicit bound; every address must be below `S`. -/
theorem run_le (hs : LoopFree s) (hb : size s ≤ b) (h : ∀ c, P c → AddrOK S s c ∧ Q (RAM.run s c)) :
    HTB S s P Q b :=
  (HTB.run hs h).weaken hb

/-- `HTB.run_le` with the address obligation as a separate argument. -/
theorem run_le' (hs : LoopFree s) (hb : size s ≤ b) (hA : ∀ c, P c → AddrOK S s c)
    (h : ∀ c, P c → Q (RAM.run s c)) : HTB S s P Q b :=
  HTB.run_le hs hb fun c hc => ⟨hA c hc, h c hc⟩

/-- **Frame rule**: an assertion preserved by every change allowed by the footprint of `s`. -/
theorem frame (h : HTB S s P Q b) (hF : ∀ c c', Frame s c c' → F c → F c') :
    HTB S s (fun c => P c ∧ F c) (fun c => Q c ∧ F c) b := by
  intro c ⟨hp, hf⟩
  obtain ⟨c', t, he, hq, ht⟩ := h c hp
  exact ⟨c', t, he, ⟨hq, hF c c' he.frame hf⟩, ht⟩

/-- Frame rule for register-only assertions, for every program. -/
theorem frameReg (h : HTB S s P Q b) (hF : RegIndep (wregs s) F) :
    HTB S s (fun c => P c ∧ F c) (fun c => Q c ∧ F c) b :=
  h.frame fun _ _ hfr hf => hF _ _ hfr.reg hf

/-- Frame rule for a program that neither stores nor writes. -/
theorem frameIndep (h : HTB S s P Q b) (hs : stores s = false) (hw : writes s = false)
    (hF : Indep (wregs s) F) : HTB S s (fun c => P c ∧ F c) (fun c => Q c ∧ F c) b :=
  h.frame fun c c' hfr hf => hF c c' (hfr.agree hs hw) hf

/-- Relational frame information, through a ghost initial configuration `c₀`. -/
theorem withFrame (h : HTB S s P Q b) (c₀ : Config) :
    HTB S s (fun c => P c ∧ c = c₀) (fun c => Q c ∧ Frame s c₀ c) b := by
  intro c ⟨hp, hc⟩
  subst hc
  obtain ⟨c', t, he, hq, ht⟩ := h c hp
  exact ⟨c', t, he, ⟨hq, he.frame⟩, ht⟩

/-- Two triples for the same program combine (the machine is deterministic). -/
theorem and {Q₁ Q₂ : Config → Prop} {b₁ b₂ : ℕ} (h₁ : HTB S s P Q₁ b₁) (h₂ : HTB S s P Q₂ b₂) :
    HTB S s P (fun c => Q₁ c ∧ Q₂ c) (min b₁ b₂) := by
  intro c hc
  obtain ⟨c₁, t₁, he₁, hq₁, ht₁⟩ := h₁ c hc
  obtain ⟨c₂, t₂, he₂, hq₂, ht₂⟩ := h₂ c hc
  obtain ⟨rfl, rfl⟩ := he₁.det he₂
  exact ⟨c₁, t₁, he₁, ⟨hq₁, hq₂⟩, le_min ht₁ ht₂⟩

/-- A bounded triple combines with an unbounded one for the same program. -/
theorem and_HT {Q₁ Q₂ : Config → Prop} {b₁ b₂ : ℕ} (h₁ : HTB S s P Q₁ b₁) (h₂ : HT s P Q₂ b₂) :
    HTB S s P (fun c => Q₁ c ∧ Q₂ c) (min b₁ b₂) := by
  intro c hc
  obtain ⟨c₁, t₁, he₁, hq₁, ht₁⟩ := h₁ c hc
  obtain ⟨c₂, t₂, he₂, hq₂, ht₂⟩ := h₂ c hc
  obtain ⟨rfl, rfl⟩ := he₁.det_exec he₂
  exact ⟨c₁, t₁, he₁, ⟨hq₁, hq₂⟩, le_min ht₁ ht₂⟩

/-- Ghost variables: an existential precondition. -/
theorem exists_pre {α : Sort*} {P : α → Config → Prop} (h : ∀ x, HTB S s (P x) Q b) :
    HTB S s (fun c => ∃ x, P x c) Q b := fun c ⟨x, hx⟩ => h x c hx

/-- A pure proposition in the precondition. -/
theorem prop_pre {p : Prop} (h : p → HTB S s P Q b) : HTB S s (fun c => p ∧ P c) Q b :=
  fun c ⟨hp, hc⟩ => h hp c hc

/-- Case split on a proposition. -/
theorem cases (p : Prop) (h₁ : HTB S s (fun c => P c ∧ p) Q b) (h₂ : HTB S s (fun c => P c ∧ ¬ p) Q b) :
    HTB S s P Q b := by
  intro c hc
  by_cases hp : p
  · exact h₁ c ⟨hc, hp⟩
  · exact h₂ c ⟨hc, hp⟩

/-- Case split on a property of the initial configuration. -/
theorem casesOn (p : Config → Prop) (h₁ : HTB S s (fun c => P c ∧ p c) Q b)
    (h₂ : HTB S s (fun c => P c ∧ ¬ p c) Q b) : HTB S s P Q b := by
  intro c hc
  by_cases hp : p c
  · exact h₁ c ⟨hc, hp⟩
  · exact h₂ c ⟨hc, hp⟩

/-- An unconditional triple from a family of triples indexed by the initial configuration. -/
theorem of_forall (h : ∀ c₀, P c₀ → HTB S s (fun c => c = c₀) Q b) : HTB S s P Q b :=
  fun c hc => h c hc c rfl

/-- Sequencing three programs. -/
theorem seq3 {s₁ s₂ s₃ : Stmt} {R₁ R₂ : Config → Prop} {b₁ b₂ b₃ : ℕ} (h₁ : HTB S s₁ P R₁ b₁)
    (h₂ : HTB S s₂ R₁ R₂ b₂) (h₃ : HTB S s₃ R₂ Q b₃) :
    HTB S (.seq s₁ (.seq s₂ s₃)) P Q (b₁ + (b₂ + b₃)) :=
  h₁.seq (h₂.seq h₃)

/-- Sequencing with a bound given up to `≤`. -/
theorem seq_le {b₁ b₂ : ℕ} (h₁ : HTB S s P R b₁) (h₂ : HTB S u R Q b₂) (hb : b₁ + b₂ ≤ b) :
    HTB S (.seq s u) P Q b := (h₁.seq h₂).weaken hb

/-- **Loop with a decreasing measure** (see `HT.loopT`). -/
theorem loopT {a : ℕ} {body : Stmt} {Inv : Config → Prop} (μ : Config → ℕ) {T : ℕ}
    (hbody : ∀ v, HTB S body (fun c => Inv c ∧ c.reg a ≠ 0 ∧ μ c = v) (fun c => Inv c ∧ μ c < v) T)
    (K : ℕ) : HTB S (.loop a body) (fun c => Inv c ∧ μ c ≤ K) (fun c => Inv c ∧ c.reg a = 0)
      (K * (T + 1) + 1) := by
  suffices key : ∀ k c, Inv c → μ c ≤ k →
      ∃ c' t, ExecB S (.loop a body) c t c' ∧ (Inv c' ∧ c'.reg a = 0) ∧ t ≤ k * (T + 1) + 1 from
    fun c ⟨hi, hk⟩ => key K c hi hk
  intro k
  induction k with
  | zero =>
    intro c hi hk
    by_cases ha : c.reg a = 0
    · exact ⟨c, 1, ExecB.loopDone ha, ⟨hi, ha⟩, by omega⟩
    · obtain ⟨_, _, _, ⟨_, hlt⟩, _⟩ := hbody (μ c) c ⟨hi, ha, rfl⟩
      omega
  | succ k ih =>
    intro c hi hk
    by_cases ha : c.reg a = 0
    · exact ⟨c, 1, ExecB.loopDone ha, ⟨hi, ha⟩, by omega⟩
    · obtain ⟨c₁, t₁, he₁, ⟨hi₁, hlt⟩, ht₁⟩ := hbody (μ c) c ⟨hi, ha, rfl⟩
      obtain ⟨c₂, t₂, he₂, hq, ht₂⟩ := ih c₁ hi₁ (by omega)
      refine ⟨c₂, t₁ + t₂ + 1, ExecB.loopNext ha he₁ he₂, hq, ?_⟩
      rw [Nat.succ_mul]; omega

/-! #### Further generic rules -/

/-- An unsatisfiable precondition. -/
theorem of_false (h : ∀ c, P c → False) : HTB S s P Q b := fun c hc => absurd hc (h c)

/-- A pure fact read off the precondition. -/
theorem pre_fact {p : Prop} (hp : ∀ c, P c → p) (h : p → HTB S s P Q b) : HTB S s P Q b :=
  fun c hc => h (hp c hc) c hc

/-- Reassociating a sequence (left to right). -/
theorem assoc {a₁ a₂ a₃ : Stmt} (h : HTB S (.seq (.seq a₁ a₂) a₃) P Q b) :
    HTB S (.seq a₁ (.seq a₂ a₃)) P Q b := by
  intro c hc
  obtain ⟨c', t, he, hq, ht⟩ := h c hc
  cases he with
  | seq h₁ h₂ =>
    cases h₁ with
    | seq h₁₁ h₁₂ => exact ⟨c', _, ExecB.seq h₁₁ (ExecB.seq h₁₂ h₂), hq, by omega⟩

/-- Reassociating a sequence (right to left). -/
theorem reassoc {a₁ a₂ a₃ : Stmt} (h : HTB S (.seq a₁ (.seq a₂ a₃)) P Q b) :
    HTB S (.seq (.seq a₁ a₂) a₃) P Q b := by
  intro c hc
  obtain ⟨c', t, he, hq, ht⟩ := h c hc
  cases he with
  | seq h₁ h₂ =>
    cases h₂ with
    | seq h₂₁ h₂₂ => exact ⟨c', _, ExecB.seq (ExecB.seq h₁ h₂₁) h₂₂, hq, by omega⟩

/-- **Frame rule for memory-restoring programs**: if every run of `s` from a configuration
satisfying `Pre` leaves the memory as it was, every assertion `P` independent of the registers
`W ⊇ wregs s` survives `s`. -/
theorem memRestore {W : List ℕ} {Pre : Config → Prop}
    (h : ∀ c₀, P c₀ → Pre c₀ → HTB S s (fun c => c = c₀) (fun c => Q c ∧ c.mem = c₀.mem) b)
    (hw : writes s = false) (hW : ∀ r ∈ wregs s, r ∈ W) (hP : Indep W P) :
    HTB S s (fun c => P c ∧ Pre c) (fun c => P c ∧ Q c) b := by
  intro c ⟨hp, hpre⟩
  obtain ⟨c', t, he, ⟨hq, hm⟩, ht⟩ := h c hp hpre c rfl
  refine ⟨c', t, he, ⟨hP c c' ⟨fun r hr => he.reg_frame fun h => hr (hW r h), hm,
    he.out_frame hw⟩ hp, hq⟩, ht⟩

end HTB

end STACS2027.RAM
