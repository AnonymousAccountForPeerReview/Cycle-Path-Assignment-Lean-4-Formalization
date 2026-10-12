module

public import ApproximationHardness.RAM.Polarize.Correct
import Lean.Elab.Tactic.Omega

/-!
# The first pass of the decoding program, without output

`passAq` is the first pass of the Theorem 8 program (`passA`) without its output instruction:
it leaves `n = variableBound f` in `Reg.n`, the length of `ramInput f` in `Reg.N` (and in `Reg.p`)
and `N + 2n` in `Reg.B`. It reads `ramInput f` from the start of any memory holding it.
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT
open Stmt

def passAqPre : Stmt :=
  seqs [const Reg.one 1, const Reg.p 0, Stmt.load Reg.m Reg.p, add Reg.p Reg.p Reg.one]

def passAq : Stmt := Stmt.seq passAqPre (Stmt.seq (Stmt.loop Reg.m clauseA) passApost)

/-- The invariant of the clause loop of `passAq`, for a memory `M` holding `ramInput f` first. -/
def InvAq (f : CNF) (M : Nat → Nat) (c : Config) : Prop :=
  ∃ pre suf : CNF, pre ++ suf = f ∧ c.reg Reg.m = suf.length ∧ At c (suf.flatMap clauseCode) ∧
    c.mem = M ∧ c.reg Reg.one = 1 ∧ c.reg Reg.zero = 0 ∧
    c.reg Reg.n = variableBound pre ∧ c.reg Reg.p = 1 + (pre.flatMap clauseCode).length ∧ c.out = []

theorem InvAq.step {f : CNF} {M : Nat → Nat} {c : Config} (h : InvAq f M c) (hm : c.reg Reg.m ≠ 0) :
    InvAq f M (clauseAModel c) ∧ (clauseAModel c).reg Reg.m + 1 = c.reg Reg.m := by
  obtain ⟨pre, suf, hf, hmc, hAt, hmem, hone, hzero, hn, hp, hout⟩ := h
  cases suf with
  | nil => simp at hmc; exact absurd hmc hm
  | cons cl suf =>
    simp only [List.flatMap_cons] at hAt
    obtain ⟨m2, o2, mm2, n2, p2, a2, r2⟩ := clauseA_run c cl _ hAt hone hzero
    refine ⟨⟨pre ++ [cl], suf, by simp [← hf], ?_, a2, by rw [m2, hmem], ?_, ?_, ?_, ?_, by rw [o2, hout]⟩, ?_⟩
    · rw [mm2, hmc]; simp
    · rw [r2 _ (by decide), hone]
    · rw [r2 _ (by decide), hzero]
    · rw [n2, hn, variableBound_append]; simp [variableBound]
    · rw [p2, hp]; simp only [List.flatMap_append, List.length_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, clauseCode_length]; omega
    · rw [mm2, hmc]; simp

theorem InvAq.len_le {f : CNF} (hf : ∀ c ∈ f, c.length ≤ 3) {M : Nat → Nat} {c : Config} (h : InvAq f M c)
    (hm : c.reg Reg.m ≠ 0) : c.mem (c.reg Reg.p) ≤ 3 := by
  obtain ⟨pre, suf, hfe, hmc, hAt, -, -, -, -, -, -⟩ := h
  cases suf with
  | nil => simp at hmc; exact absurd hmc hm
  | cons cl suf =>
    simp only [List.flatMap_cons, clauseCode, List.cons_append] at hAt
    rw [hAt.head]
    exact hf cl (by rw [← hfe]; simp)

theorem InvAq.m_le {f : CNF} {M : Nat → Nat} {c : Config} (h : InvAq f M c) : c.reg Reg.m ≤ f.length := by
  obtain ⟨pre, suf, hfe, hmc, -⟩ := h
  rw [hmc, ← hfe]; simp

theorem InvAq.p_le {f : CNF} {M : Nat → Nat} {c : Config} (h : InvAq f M c) (hm : c.reg Reg.m ≠ 0) :
    c.reg Reg.p + 1 + 2 * c.mem (c.reg Reg.p) ≤ (ramInput f).length := by
  obtain ⟨pre, suf, hfe, hmc, hAt, -, -, -, -, hp, -⟩ := h
  cases suf with
  | nil => simp at hmc; exact absurd hmc hm
  | cons cl suf =>
    simp only [List.flatMap_cons, clauseCode, List.cons_append] at hAt
    rw [hAt.head, hp]
    exact ramInput_clause_le hfe

/-- A memory holding `ramInput f` from cell `0`. -/
def HoldsInput (f : CNF) (c : Config) : Prop := ∀ i, i < (ramInput f).length → c.mem i = (ramInput f).getD i 0

theorem InvAq.start (f : CNF) (c : Config) (hc : HoldsInput f c) (hout : c.out = []) (hzero : c.reg Reg.zero = 0)
    (hn0 : c.reg Reg.n = 0) :
    InvAq f c.mem (run passAqPre c) := by
  have h0 := hc 0 (by simp [ramInput])
  refine ⟨[], f, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp +decide [passAqPre, run, h0, ramInput]
  · intro i hi
    simp +decide [passAqPre, run]
    have := hc (1 + i) (by simp only [ramInput, List.length_cons]; omega)
    rw [this]; simp [ramInput, Nat.add_comm 1 i]
  · simp [passAqPre, run]
  · simp +decide [passAqPre, run]
  · simp +decide [passAqPre, run, hzero]
  · simp +decide [passAqPre, run, variableBound, hn0]
  · simp +decide [passAqPre, run]
  · simp +decide [passAqPre, run, hout]

theorem passAq_eq : passAq = Stmt.seq passAqPre (Stmt.seq (Stmt.loop Reg.m clauseA) passApost) := rfl

def passAqModel (c : Config) : Config :=
  run passApost (iterate clauseAModel ((run passAqPre c).reg Reg.m) (run passAqPre c))

/-- The first pass reads only `ramInput f`: it runs within every space bound `S ≥ |ramInput f|`. -/
theorem sat_passAq (f : CNF) (hf : ∀ c ∈ f, c.length ≤ 3) {S : Nat} (hS : (ramInput f).length ≤ S) :
    SatB S passAq (fun c => HoldsInput f c ∧ c.out = [] ∧ c.reg Reg.zero = 0 ∧ c.reg Reg.n = 0) passAqModel
      (passACost f) := by
  have hN : 1 ≤ (ramInput f).length := by simp [ramInput]
  have h₁ := SatB.ofLoopFree (S := S) (s := passAqPre) (by simp [passAqPre, seqs, LoopFree])
    (P := fun c => HoldsInput f c ∧ c.out = [] ∧ c.reg Reg.zero = 0 ∧ c.reg Reg.n = 0)
    (fun c _ => by simp +decide [passAqPre, run]; omega)
  have h₂ := SatB.loop (a := Reg.m) (body := clauseA) (P := fun c => ∃ M, InvAq f M c) (m := clauseAModel)
    (L := f.length)
    (sat_clauseA.mono (fun c hc => by
        obtain ⟨⟨M, hM⟩, hm⟩ := hc
        exact ⟨hM.len_le hf hm, by obtain ⟨_, _, _, _, _, _, h, _⟩ := hM; exact h,
          Nat.le_trans (hM.p_le hm) hS⟩) (Nat.le_refl _))
    (fun c ⟨M, hM⟩ hm => ⟨M, (hM.step hm).1⟩) (fun c ⟨M, hM⟩ hm => (hM.step hm).2)
    (fun c ⟨M, hM⟩ => hM.m_le)
  have h₃ := SatB.ofLoopFree (S := S) (s := passApost) (by simp [passApost, seqs, LoopFree]) (P := fun _ => True)
    (fun _ _ => AddrOK.of_memFree rfl)
  have h := h₁.seq (Q := fun c => ∃ M, InvAq f M c) (fun c ⟨hc, ho, hz, hn⟩ => ⟨_, InvAq.start f c hc ho hz hn⟩)
    (h₂.seq (fun _ _ => trivial) h₃)
  have hpre : size passAqPre ≤ size passApre := by simp [passAqPre, passApre, size, seqs]
  rw [passAq_eq]
  exact (h.mono (fun c hc => hc) (by simp only [passACost]; omega)).congr (fun c _ => rfl)

theorem passAqModel_spec (f : CNF) (c : Config) (hc : HoldsInput f c) (hout : c.out = []) (hzero : c.reg Reg.zero = 0)
    (hn0 : c.reg Reg.n = 0) :
    let c' := passAqModel c
    c'.mem = c.mem ∧ c'.out = [] ∧ c'.reg Reg.one = 1 ∧ c'.reg Reg.zero = 0 ∧
      c'.reg Reg.n = variableBound f ∧ c'.reg Reg.N = (ramInput f).length ∧
      c'.reg Reg.B = (ramInput f).length + variableBound f + variableBound f ∧
      c'.reg Reg.p = (ramInput f).length := by
  have hstart := InvAq.start f c hc hout hzero hn0
  obtain ⟨⟨pre, suf, hfe, hmc, -, hmem, hone, hzero', hn, hp, hout'⟩, hm0⟩ :=
    iterate_invariant (a := Reg.m) (P := InvAq f c.mem) (m := clauseAModel) (fun c hc hm => (hc.step hm).1)
      (fun c hc hm => (hc.step hm).2) _ _ hstart rfl
  have hsuf : suf = [] := by
    rw [hm0] at hmc; exact List.eq_nil_of_length_eq_zero hmc.symm
  subst hsuf
  simp only [List.append_nil] at hfe
  subst hfe
  intro c'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [c', passAqModel, passApost, run_seqs_cons, run_seqs_nil, run, setReg_mem]; exact hmem
  · simp only [c', passAqModel, passApost, run_seqs_cons, run_seqs_nil, run, setReg_out]; exact hout'
  · simp +decide only [c', passAqModel, passApost, run_seqs_cons, run_seqs_nil, run, setReg_reg, ↓reduceIte]
    exact hone
  · simp +decide only [c', passAqModel, passApost, run_seqs_cons, run_seqs_nil, run, setReg_reg, ↓reduceIte]
    exact hzero'
  · simp +decide only [c', passAqModel, passApost, run_seqs_cons, run_seqs_nil, run, setReg_reg, ↓reduceIte]
    exact hn
  · simp +decide only [c', passAqModel, passApost, run_seqs_cons, run_seqs_nil, run, setReg_reg, ↓reduceIte]
    rw [hp, hzero']; simp [ramInput]; omega
  · simp +decide only [c', passAqModel, passApost, run_seqs_cons, run_seqs_nil, run, setReg_reg, ↓reduceIte]
    rw [hp, hzero', hn]; simp [ramInput]; omega
  · simp +decide only [c', passAqModel, passApost, run_seqs_cons, run_seqs_nil, run, setReg_reg, ↓reduceIte]
    rw [hp]; simp [ramInput]; omega

end STACS2027.RAM
