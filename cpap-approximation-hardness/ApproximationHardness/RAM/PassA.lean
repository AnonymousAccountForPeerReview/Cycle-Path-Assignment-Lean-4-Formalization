module

public import ApproximationHardness.RAM.Program
public import NPHardness.GlobalSize
import Lean.Elab.Tactic.Omega

/-!
# The first pass of the RAM program

`passA` writes the budget `m`, and leaves `n = variableBound f` in `Reg.n`, the input
length in `Reg.N` and `N + 2n` in `Reg.B`, within `O(m)` steps.
-/

@[expose] public section

namespace STACS2027.RAM

open Complexity.SAT

/-- The cells from `reg p` on hold `w`. -/
def At (c : Config) (w : List Nat) : Prop := ∀ i, i < w.length → c.mem (c.reg Reg.p + i) = w.getD i 0

theorem At.head {c : Config} {x : Nat} {w : List Nat} (h : At c (x :: w)) : c.mem (c.reg Reg.p) = x := by
  have := h 0 (by simp)
  simpa using this

theorem At.tail {c c' : Config} {x : Nat} {w : List Nat} (h : At c (x :: w)) (hm : c'.mem = c.mem)
    (hp : c'.reg Reg.p = c.reg Reg.p + 1) : At c' w := by
  intro i hi
  rw [hm, hp, Nat.add_assoc, Nat.add_comm 1 i]
  have := h (i + 1) (by simp; omega)
  simpa using this

theorem At.append_left {c : Config} {w u : List Nat} (h : At c (w ++ u)) : At c w := by
  intro i hi
  have := h i (by simp; omega)
  rw [this, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem At.drop {c c' : Config} {w u : List Nat} (h : At c (w ++ u)) (hm : c'.mem = c.mem)
    (hp : c'.reg Reg.p = c.reg Reg.p + w.length) : At c' u := by
  intro i hi
  rw [hm, hp, Nat.add_assoc]
  have := h (w.length + i) (by simp; omega)
  rw [this, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp

/-- The memory `mem` is unchanged at the cells `[reg p, reg p + |w|)` relevant to `At`. -/
theorem At.of_mem {c c' : Config} {w : List Nat} (h : At c w) (hp : c'.reg Reg.p = c.reg Reg.p)
    (hm : ∀ i, i < w.length → c'.mem (c.reg Reg.p + i) = c.mem (c.reg Reg.p + i)) : At c' w := by
  intro i hi
  rw [hp, hm i hi]
  exact h i hi

/-! ### One literal -/

/-- The registers `litA` writes. -/
def litARegs : List Nat := [Reg.len, Reg.v, Reg.p, Reg.t, Reg.n]

theorem litA_run (c : Config) (l : Literal) (w : List Nat) (hAt : At c (litCode l ++ w))
    (hone : c.reg Reg.one = 1) (hzero : c.reg Reg.zero = 0) :
    (run litA c).mem = c.mem ∧ (run litA c).out = c.out ∧
      (run litA c).reg Reg.len = c.reg Reg.len - 1 ∧
      (run litA c).reg Reg.n = max (c.reg Reg.n) (l.var + 1) ∧
      (run litA c).reg Reg.p = c.reg Reg.p + 2 ∧ At (run litA c) w ∧
      ∀ r, r ∉ litARegs → (run litA c).reg r = c.reg r := by
  have hv : c.mem (c.reg Reg.p) = l.var := hAt.head
  have hmem : (run litA c).mem = c.mem := by
    simp only [litA, run_seqs_cons, run_seqs_nil, run]; split <;> simp
  have hp : (run litA c).reg Reg.p = c.reg Reg.p + 2 := by
    simp only [litA, run_seqs_cons, run_seqs_nil, run]; split <;> simp +decide [hone] <;> omega
  refine ⟨hmem, ?_, ?_, ?_, hp, ?_, ?_⟩
  · simp only [litA, run_seqs_cons, run_seqs_nil, run]; split <;> simp
  · simp only [litA, run_seqs_cons, run_seqs_nil, run]; split <;> simp +decide [hone]
  · simp only [litA, run_seqs_cons, run_seqs_nil, run]
    split
    · rename_i h
      simp +decide [hone, hv] at h ⊢
      omega
    · rename_i h
      simp +decide [hone, hv, hzero] at h ⊢
      omega
  · exact hAt.drop hmem (by rw [hp]; rfl)
  · intro r hr
    simp only [litARegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5⟩ := hr
    simp only [litA, run_seqs_cons, run_seqs_nil, run]
    split <;> simp [h1, h2, h3, h4, h5]

theorem litA_iter (ls : List Literal) : ∀ (c : Config) (w : List Nat),
    At c (ls.flatMap litCode ++ w) → c.reg Reg.len = ls.length → c.reg Reg.one = 1 → c.reg Reg.zero = 0 →
    let c' := iterate (run litA) ls.length c
    c'.mem = c.mem ∧ c'.out = c.out ∧ c'.reg Reg.len = 0 ∧
      c'.reg Reg.n = max (c.reg Reg.n) (clauseBound ls) ∧
      c'.reg Reg.p = c.reg Reg.p + 2 * ls.length ∧ At c' w ∧
      ∀ r, r ∉ litARegs → c'.reg r = c.reg r := by
  induction ls with
  | nil =>
    intro c w hAt hl _ _
    exact ⟨rfl, rfl, by simpa [iterate] using hl, by simp [clauseBound, iterate], by simp [iterate],
      by simpa [iterate] using hAt, fun _ _ => rfl⟩
  | cons l ls ih =>
    intro c w hAt hl hone hzero
    simp only [List.flatMap_cons, List.append_assoc] at hAt
    obtain ⟨m1, o1, l1, n1, p1, a1, r1⟩ := litA_run c l _ hAt hone hzero
    obtain ⟨m2, o2, l2, n2, p2, a2, r2⟩ := ih (run litA c) w a1 (by rw [l1, hl]; simp)
      (by rw [r1 _ (by decide), hone]) (by rw [r1 _ (by decide), hzero])
    refine ⟨?_, ?_, l2, ?_, ?_, a2, ?_⟩
    · show (iterate (run litA) ls.length (run litA c)).mem = _
      rw [m2, m1]
    · show (iterate (run litA) ls.length (run litA c)).out = _
      rw [o2, o1]
    · show (iterate (run litA) ls.length (run litA c)).reg Reg.n = _
      rw [n2, n1]; simp only [clauseBound, Nat.max_assoc]
    · show (iterate (run litA) ls.length (run litA c)).reg Reg.p = _
      rw [p2, p1]; simp; omega
    · intro r hr
      show (iterate (run litA) ls.length (run litA c)).reg r = _
      rw [r2 r hr, r1 r hr]

/-! ### One clause -/

/-- The prefix of `clauseA`: decrement the clause counter and read the clause length. -/
def clauseApre : Stmt := seqs [Stmt.sub Reg.m Reg.m Reg.one, Stmt.load Reg.len Reg.p, Stmt.add Reg.p Reg.p Reg.one]

theorem clauseA_eq : clauseA = Stmt.seq clauseApre (Stmt.loop Reg.len litA) := rfl

/-- The model of `clauseA`. -/
def clauseAModel (c : Config) : Config :=
  iterate (run litA) ((run clauseApre c).reg Reg.len) (run clauseApre c)

theorem clauseA_run (c : Config) (cl : Clause) (w : List Nat) (hAt : At c (clauseCode cl ++ w))
    (hone : c.reg Reg.one = 1) (hzero : c.reg Reg.zero = 0) :
    (clauseAModel c).mem = c.mem ∧ (clauseAModel c).out = c.out ∧
      (clauseAModel c).reg Reg.m = c.reg Reg.m - 1 ∧
      (clauseAModel c).reg Reg.n = max (c.reg Reg.n) (clauseBound cl) ∧
      (clauseAModel c).reg Reg.p = c.reg Reg.p + 1 + 2 * cl.length ∧ At (clauseAModel c) w ∧
      ∀ r, r ∉ Reg.m :: litARegs → (clauseAModel c).reg r = c.reg r := by
  have hl : c.mem (c.reg Reg.p) = cl.length := hAt.head
  let c₁ := run clauseApre c
  have h₁mem : c₁.mem = c.mem := by simp [c₁, clauseApre, run]
  have h₁len : c₁.reg Reg.len = cl.length := by simp +decide [c₁, clauseApre, run, hl]
  have h₁p : c₁.reg Reg.p = c.reg Reg.p + 1 := by simp +decide [c₁, clauseApre, run, hone]
  have h₁ : ∀ r, r ≠ Reg.m → r ≠ Reg.len → r ≠ Reg.p → c₁.reg r = c.reg r := by
    intro r a1 a2 a3; simp [c₁, clauseApre, run, a1, a2, a3]
  have hAt₁ : At c₁ (cl.flatMap litCode ++ w) := by
    simp only [clauseCode, List.cons_append] at hAt
    exact hAt.tail h₁mem h₁p
  obtain ⟨m2, o2, l2, n2, p2, a2, r2⟩ := litA_iter cl c₁ w hAt₁ h₁len
    (by rw [h₁ _ (by decide) (by decide) (by decide), hone]) (by rw [h₁ _ (by decide) (by decide) (by decide), hzero])
  have hm : clauseAModel c = iterate (run litA) cl.length c₁ := by
    simp only [clauseAModel]; rw [show (run clauseApre c).reg Reg.len = cl.length from h₁len]
  rw [hm]
  refine ⟨by rw [m2, h₁mem], by rw [o2]; simp [c₁, clauseApre, run], ?_, ?_, ?_, a2, ?_⟩
  · rw [r2 _ (by decide)]; simp +decide [c₁, clauseApre, run, hone]
  · rw [n2, h₁ _ (by decide) (by decide) (by decide)]
  · rw [p2, h₁p]
  · intro r hr
    simp only [litARegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hr
    rw [r2 r (by simp [litARegs, a1, a2, a3, a4, a5]), h₁ r a0 a1 a3]

theorem litCodes_length (ls : List Literal) : (ls.flatMap litCode).length = 2 * ls.length := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [litCode, ih]; omega

theorem clauseCode_length (cl : Clause) : (clauseCode cl).length = 1 + 2 * cl.length := by
  simp only [clauseCode, List.length_cons, litCodes_length]; omega

theorem clauseCodes_length_le (f : CNF) (hf : ∀ c ∈ f, c.length ≤ 3) :
    (f.flatMap clauseCode).length ≤ 7 * f.length := by
  induction f with
  | nil => simp
  | cons c f ih =>
    have h1 := hf c (by simp)
    have h2 := ih (fun c' hc' => hf c' (by simp [hc']))
    simp only [List.flatMap_cons, List.length_append, clauseCode_length, List.length_cons]; omega

/-- The cost of one clause of the first pass (clauses of at most three literals). -/
def clauseACost : Nat := size clauseApre + (3 * (size litA + 1) + 1)

/-- One clause of the first pass, reading the cells `p, …, p + 2 · len` below `S`. -/
theorem sat_clauseA {S : Nat} :
    SatB S clauseA (fun c => c.mem (c.reg Reg.p) ≤ 3 ∧ c.reg Reg.one = 1 ∧
      c.reg Reg.p + 1 + 2 * c.mem (c.reg Reg.p) ≤ S) clauseAModel clauseACost := by
  have h₁ := SatB.ofLoopFree (S := S) (s := clauseApre) (by simp [clauseApre, seqs, LoopFree])
    (P := fun c => c.mem (c.reg Reg.p) ≤ 3 ∧ c.reg Reg.one = 1 ∧ c.reg Reg.p + 1 + 2 * c.mem (c.reg Reg.p) ≤ S)
    (fun c hc => by simp +decide [clauseApre, run]; omega)
  have h₂ := SatB.loop (S := S) (a := Reg.len) (body := litA)
    (P := fun c => c.reg Reg.len ≤ 3 ∧ c.reg Reg.one = 1 ∧ c.reg Reg.p + 2 * c.reg Reg.len ≤ S)
    (m := run litA) (L := 3)
    (SatB.ofLoopFree (by simp [litA, seqs, LoopFree]) (fun c hc => by simp +decide [litA, run]; omega))
    (by
      intro c hc _
      obtain ⟨h1, h2, h3⟩ := hc
      simp only [litA, run_seqs_cons, run_seqs_nil, run]; split <;> simp +decide [h2] <;> omega)
    (by
      intro c hc ha
      obtain ⟨h1, h2, -⟩ := hc
      simp only [litA, run_seqs_cons, run_seqs_nil, run]; split <;> simp +decide [h2] <;> omega)
    (fun c hc => hc.1)
  have h := h₁.seq (Q := fun c => c.reg Reg.len ≤ 3 ∧ c.reg Reg.one = 1 ∧ c.reg Reg.p + 2 * c.reg Reg.len ≤ S)
    (by intro c hc; simp +decide [clauseApre, run]; omega) h₂
  rw [clauseA_eq]
  exact h.congr (fun c _ => rfl)

/-! ### The first pass -/

def passApre : Stmt :=
  seqs [Stmt.const Reg.one 1, Stmt.const Reg.p 0, Stmt.load Reg.m Reg.p, Stmt.add Reg.p Reg.p Reg.one, Stmt.write Reg.m]

def passApost : Stmt := seqs [Stmt.add Reg.N Reg.p Reg.zero, Stmt.add Reg.B Reg.N Reg.n, Stmt.add Reg.B Reg.B Reg.n]

theorem passA_eq : passA = Stmt.seq passApre (Stmt.seq (Stmt.loop Reg.m clauseA) passApost) := rfl

/-- The invariant of the clause loop of the first pass for the formula `f`. -/
def InvA (f : CNF) (c : Config) : Prop :=
  ∃ pre suf : CNF, pre ++ suf = f ∧ c.reg Reg.m = suf.length ∧ At c (suf.flatMap clauseCode) ∧
    c.mem = (initial (ramInput f)).mem ∧ c.reg Reg.one = 1 ∧ c.reg Reg.zero = 0 ∧
    c.reg Reg.n = variableBound pre ∧ c.reg Reg.p = 1 + (pre.flatMap clauseCode).length ∧
    c.out = [f.length]

theorem InvA.step {f : CNF} {c : Config} (h : InvA f c) (hm : c.reg Reg.m ≠ 0) :
    InvA f (clauseAModel c) ∧ (clauseAModel c).reg Reg.m + 1 = c.reg Reg.m := by
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

theorem InvA.len_le {f : CNF} (hf : ∀ c ∈ f, c.length ≤ 3) {c : Config} (h : InvA f c) (hm : c.reg Reg.m ≠ 0) :
    c.mem (c.reg Reg.p) ≤ 3 := by
  obtain ⟨pre, suf, hfe, hmc, hAt, -, -, -, -, -, -⟩ := h
  cases suf with
  | nil => simp at hmc; exact absurd hmc hm
  | cons cl suf =>
    simp only [List.flatMap_cons, clauseCode, List.cons_append] at hAt
    rw [hAt.head]
    exact hf cl (by rw [← hfe]; simp)

theorem InvA.m_le {f : CNF} {c : Config} (h : InvA f c) : c.reg Reg.m ≤ f.length := by
  obtain ⟨pre, suf, hfe, hmc, -⟩ := h
  rw [hmc, ← hfe]; simp

/-- The clause at `p` lies inside the input. -/
theorem ramInput_clause_le {f pre suf : CNF} {cl : Clause} (hfe : pre ++ cl :: suf = f) :
    1 + (pre.flatMap clauseCode).length + 1 + 2 * cl.length ≤ (ramInput f).length := by
  subst hfe
  simp only [ramInput, List.flatMap_append, List.flatMap_cons, List.length_cons, List.length_append,
    clauseCode_length]
  omega

theorem InvA.p_le {f : CNF} {c : Config} (h : InvA f c) (hm : c.reg Reg.m ≠ 0) :
    c.reg Reg.p + 1 + 2 * c.mem (c.reg Reg.p) ≤ (ramInput f).length := by
  obtain ⟨pre, suf, hfe, hmc, hAt, -, -, -, -, hp, -⟩ := h
  cases suf with
  | nil => simp at hmc; exact absurd hmc hm
  | cons cl suf =>
    simp only [List.flatMap_cons, clauseCode, List.cons_append] at hAt
    rw [hAt.head, hp]
    exact ramInput_clause_le hfe

/-- The model of the first pass. -/
def passAModel (c : Config) : Config :=
  run passApost (iterate clauseAModel ((run passApre c).reg Reg.m) (run passApre c))

def passACost (f : CNF) : Nat := size passApre + (f.length * (clauseACost + 1) + 1 + size passApost)

theorem InvA.start (f : CNF) : InvA f (run passApre (initial (ramInput f))) := by
  refine ⟨[], f, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp +decide [passApre, run, initial, ramInput]
  · intro i hi
    simp +decide [passApre, run, initial, ramInput]
    rw [Nat.add_comm 1 i]
    simp
  · simp [passApre, run]
  · simp +decide [passApre, run]
  · simp +decide [passApre, run, initial]
  · simp +decide [passApre, run, initial, variableBound]
  · simp +decide [passApre, run]
  · simp +decide [passApre, run, initial, ramInput]

/-- The first pass reads only the input: it runs within every space bound `S ≥ |ramInput f|`. -/
theorem sat_passA (f : CNF) (hf : ∀ c ∈ f, c.length ≤ 3) {S : Nat} (hS : (ramInput f).length ≤ S) :
    SatB S passA (fun c => c = initial (ramInput f)) passAModel (passACost f) := by
  have hN : 1 ≤ (ramInput f).length := by simp [ramInput]
  have h₁ := SatB.ofLoopFree (S := S) (s := passApre) (by simp [passApre, seqs, LoopFree])
    (P := fun c => c = initial (ramInput f)) (fun c _ => by simp +decide [passApre, run]; omega)
  have h₂ := SatB.loop (a := Reg.m) (body := clauseA) (P := InvA f) (m := clauseAModel) (L := f.length)
    (sat_clauseA.mono (fun c hc => ⟨hc.1.len_le hf hc.2, by obtain ⟨_, _, _, _, _, _, h, _⟩ := hc.1; exact h,
      Nat.le_trans (hc.1.p_le hc.2) hS⟩) (Nat.le_refl _))
    (fun c hc hm => (hc.step hm).1) (fun c hc hm => (hc.step hm).2) (fun c hc => hc.m_le)
  have h₃ := SatB.ofLoopFree (S := S) (s := passApost) (by simp [passApost, seqs, LoopFree]) (P := fun _ => True)
    (fun _ _ => AddrOK.of_memFree rfl)
  have h := h₁.seq (Q := InvA f) (by rintro c rfl; exact InvA.start f) (h₂.seq (fun _ _ => trivial) h₃)
  rw [passA_eq]
  exact (h.mono (fun c hc => hc) (by simp only [passACost]; omega)).congr (fun c _ => rfl)

/-- The first pass computes the budget, the number of variables, and the input length. -/
theorem passAModel_initial (f : CNF) :
    let c := passAModel (initial (ramInput f))
    c.mem = (initial (ramInput f)).mem ∧ c.out = [f.length] ∧ c.reg Reg.one = 1 ∧ c.reg Reg.zero = 0 ∧
      c.reg Reg.n = variableBound f ∧ c.reg Reg.N = (ramInput f).length ∧
      c.reg Reg.B = (ramInput f).length + variableBound f + variableBound f := by
  have hstart := InvA.start f
  obtain ⟨⟨pre, suf, hfe, hmc, -, hmem, hone, hzero, hn, hp, hout⟩, hm0⟩ :=
    iterate_invariant (a := Reg.m) (P := InvA f) (m := clauseAModel) (fun c hc hm => (hc.step hm).1)
      (fun c hc hm => (hc.step hm).2) _ _ hstart rfl
  have hsuf : suf = [] := by
    rw [hm0] at hmc; exact List.eq_nil_of_length_eq_zero hmc.symm
  subst hsuf
  simp only [List.append_nil] at hfe
  subst hfe
  intro c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [c, passAModel, passApost, run_seqs_cons, run_seqs_nil, run, setReg_mem]; exact hmem
  · simp only [c, passAModel, passApost, run_seqs_cons, run_seqs_nil, run, setReg_out]; exact hout
  · simp +decide only [c, passAModel, passApost, run_seqs_cons, run_seqs_nil, run, setReg_reg, ↓reduceIte]
    exact hone
  · simp +decide only [c, passAModel, passApost, run_seqs_cons, run_seqs_nil, run, setReg_reg, ↓reduceIte]
    exact hzero
  · simp +decide only [c, passAModel, passApost, run_seqs_cons, run_seqs_nil, run, setReg_reg, ↓reduceIte]
    exact hn
  · simp +decide only [c, passAModel, passApost, run_seqs_cons, run_seqs_nil, run, setReg_reg, ↓reduceIte]
    rw [hp, hzero]; simp [ramInput]; omega
  · simp +decide only [c, passAModel, passApost, run_seqs_cons, run_seqs_nil, run, setReg_reg, ↓reduceIte]
    rw [hp, hzero, hn]; simp [ramInput]; omega

end STACS2027.RAM
