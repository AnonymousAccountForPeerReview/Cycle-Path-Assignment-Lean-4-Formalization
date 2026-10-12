module

public import Runtimes.GeneralCycles.Definitions
public import Outerplanar.RAM.BoundedLib
public import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Read-only tuple scans on the RAM

The tuple length is a program parameter. Every counter is an endpoint index;
labels loaded from the input are held only in registers. Artifact date: 2026-10-12.
-/

@[expose] public section

namespace STACS2027.Runtimes.GeneralCycles

open STACS2027 STACS2027.RAM

abbrev choiceAddr : ℕ := 9
abbrev endpointCount : ℕ := 10

def controlRegs (indices values k : ℕ) : List ℕ :=
  rT :: choiceAddr :: (List.range' indices k ++ List.range' values k)

def Placed (indices values : ℕ) (memory : ℕ → ℕ) (stem : List ℕ)
    (c : Config) : Prop :=
  ∀ j, j < stem.length → c.reg (indices + j) = stem.getD j 0 ∧
    c.reg (values + j) = memory (1 + stem.getD j 0)

def readChoice (indices values depth : ℕ) : Stmt :=
  .seq (addc choiceAddr (indices + depth) 1) (.load (values + depth) choiceAddr)

def scanTuples (indices values depth : ℕ) : ℕ → Stmt → Stmt
  | 0, body => body
  | n + 1, body => forUp (indices + depth) endpointCount
      (.seq (readChoice indices values depth) (scanTuples indices values (depth + 1) n body))

def foldTuples {α : Type*} (N : ℕ) (F : α → List ℕ → α) :
    ℕ → List ℕ → α → α
  | 0, stem, a => F a stem
  | n + 1, stem, a => (List.range N).foldl
      (fun a i => foldTuples N F n (stem ++ [i]) a) a

def tupleTime (N B : ℕ) : ℕ → ℕ
  | 0 => B
  | n + 1 => N * (tupleTime N B n + 7) + 3

theorem placed_nil (indices values : ℕ) (memory : ℕ → ℕ) (c : Config) :
    Placed indices values memory [] c := by
  simp [Placed]

theorem Placed.append {indices values : ℕ} {memory : ℕ → ℕ} {stem : List ℕ}
    {c : Config} (h : Placed indices values memory stem c) (i : ℕ)
    (hi : c.reg (indices + stem.length) = i)
    (hv : c.reg (values + stem.length) = memory (1 + i)) :
    Placed indices values memory (stem ++ [i]) c := by
  intro j hj
  by_cases hlt : j < stem.length
  · rw [List.getD_append _ _ _ _ hlt]
    exact h j hlt
  · have he : j = stem.length := by simp only [List.length_append, List.length_singleton] at hj; omega
    subst j
    rw [List.getD_append_right _ _ _ _ le_rfl]
    simpa using And.intro hi hv

theorem Placed.stem {indices values : ℕ} {memory : ℕ → ℕ} {stem : List ℕ}
    {c : Config} {i : ℕ} (h : Placed indices values memory (stem ++ [i]) c) :
    Placed indices values memory stem c := by
  intro j hj
  have hh := h j (by simp only [List.length_append, List.length_singleton]; omega)
  rw [List.getD_append _ _ _ _ hj] at hh
  exact hh

theorem Placed.last {indices values : ℕ} {memory : ℕ → ℕ} {stem : List ℕ}
    {c : Config} {i : ℕ} (h : Placed indices values memory (stem ++ [i]) c) :
    c.reg (indices + stem.length) = i := by
  have hh := (h stem.length (by simp)).1
  simpa [List.getD_append_right _ _ _ _ le_rfl] using hh

theorem placed_indep {indices values depth k : ℕ} {memory : ℕ → ℕ}
    {stem : List ℕ} (hi : 20 ≤ indices) (hv : indices + k ≤ values)
    (hd : stem.length = depth) (hdk : depth < k) :
    Indep [rT, choiceAddr, indices + depth, values + depth]
      (Placed indices values memory stem) := by
  intro c c' ha hp j hj
  have hneqI : indices + j ∉ [rT, choiceAddr, indices + depth, values + depth] := by
    simp [rT, choiceAddr]
    omega
  have hneqV : values + j ∉ [rT, choiceAddr, indices + depth, values + depth] := by
    simp [rT, choiceAddr]
    omega
  exact ⟨(ha.reg _ hneqI).trans (hp j hj).1,
    (ha.reg _ hneqV).trans (hp j hj).2⟩

theorem readChoice_spec {indices values depth k N S j : ℕ}
    {memory : ℕ → ℕ} {stem : List ℕ} {P : Config → Prop}
    (hi : 20 ≤ indices) (hv : indices + k ≤ values)
    (hd : stem.length = depth) (hdk : depth < k)
    (hj : j < N) (hS : N + 1 ≤ S)
    (hP : Indep (controlRegs indices values k) P) :
    HTB S (readChoice indices values depth)
      (fun c => P c ∧ c.reg endpointCount = N ∧ c.mem = memory ∧
        Placed indices values memory stem c ∧ c.reg (indices + depth) = j)
      (fun c => P c ∧ c.reg endpointCount = N ∧ c.mem = memory ∧
        Placed indices values memory (stem ++ [j]) c) 3 := by
  have hne : indices + depth ≠ rT := by simp [rT]; omega
  have hia : indices + depth ≠ choiceAddr := by simp [choiceAddr]; omega
  have hmI : indices + depth ∈ controlRegs indices values k := by
    simp [controlRegs, List.mem_range']; omega
  have hmV : values + depth ∈ controlRegs indices values k := by
    simp [controlRegs, List.mem_range']; omega
  refine HTB.run_le (by simp [readChoice, addc, LoopFree]) (by simp [readChoice, addc, size]) ?_
  intro c ⟨hp, hN, hm, hs, hidx⟩
  have hc : run (readChoice indices values depth) c =
      ((c.setReg rT 1).setReg choiceAddr (j + 1)).setReg (values + depth) (memory (1 + j)) := by
    simp [readChoice, run_addc hne, run_load, hidx, hm, choiceAddr,
      Nat.add_comm]
  refine ⟨?_, ?_⟩
  · simp [readChoice, addrOK_seq, addrOK_addc, addrOK_load, run_addc hne, hidx,
      choiceAddr]
    omega
  · have hpc : P (run (readChoice indices values depth) c) := by
      rw [hc]
      exact hP.setReg hmV _ (hP.setReg (by simp [controlRegs]) _
        (hP.setReg (by simp [controlRegs]) _ hp))
    have ha : Agree [rT, choiceAddr, indices + depth, values + depth] c
        (run (readChoice indices values depth) c) := by
      rw [hc]
      exact (agree_setReg (by simp) c 1).trans
        ((agree_setReg (by simp) _ (j + 1)).trans (agree_setReg (by simp) _ _))
    have hstem := placed_indep hi hv hd hdk c _ ha hs
    refine ⟨hpc, ?_, ?_, ?_⟩
    · rw [hc]
      simp [setReg_reg, endpointCount, rT, choiceAddr, hN]
      omega
    · rw [hc]
      simpa using hm
    · apply hstem.append j
      · rw [hd, hc]
        simp [setReg_reg, hne, hia, hidx]
        omega
      · rw [hd, hc]
        simp

/-- A tuple scan folds the callback over every index tuple. Its ghost assertion
may describe an accumulated Boolean or an accumulated output list. -/
theorem scanTuples_spec {α : Type*} {indices values k N S B : ℕ}
    {memory : ℕ → ℕ} {body : Stmt} (P : α → Config → Prop)
    (F : α → List ℕ → α) (hi : 20 ≤ indices) (hv : indices + k ≤ values)
    (hS : N + 1 ≤ S) (hP : ∀ a, Indep (controlRegs indices values k) (P a))
    (hbody : ∀ full : List ℕ, full.length = k → (∀ i ∈ full, i < N) → ∀ a,
      HTB S body
        (fun c => P a c ∧ c.reg endpointCount = N ∧ c.mem = memory ∧
          Placed indices values memory full c)
        (fun c => P (F a full) c ∧ c.reg endpointCount = N ∧ c.mem = memory ∧
          Placed indices values memory full c) B) :
    ∀ n depth stem a, stem.length = depth → depth + n = k → (∀ i ∈ stem, i < N) →
      HTB S (scanTuples indices values depth n body)
        (fun c => P a c ∧ c.reg endpointCount = N ∧ c.mem = memory ∧
          Placed indices values memory stem c)
        (fun c => P (foldTuples N F n stem a) c ∧ c.reg endpointCount = N ∧
          c.mem = memory ∧ Placed indices values memory stem c)
        (tupleTime N B n) := by
  intro n
  induction n with
  | zero =>
    intro depth stem a hd hsum hb
    have hl : stem.length = k := by omega
    simpa [scanTuples, foldTuples, tupleTime] using hbody stem hl hb a
  | succ n ih =>
    intro depth stem a hd hsum hb
    have hdk : depth < k := by omega
    have hctr : indices + depth ≠ rT := by simp [rT]; omega
    have hbound : endpointCount ≠ rT := by decide
    have hdistinct : endpointCount ≠ indices + depth := by simp [endpointCount]; omega
    have hmI : indices + depth ∈ controlRegs indices values k := by
      simp [controlRegs, List.mem_range']; omega
    let step := fun a i => foldTuples N F n (stem ++ [i]) a
    let accum := fun j => (List.range j).foldl step a
    let Inv := fun j c => P (accum j) c ∧ c.reg endpointCount = N ∧ c.mem = memory ∧
      Placed indices values memory stem c
    have hacc : ∀ j, accum (j + 1) = foldTuples N F n (stem ++ [j]) (accum j) := by
      intro j
      simp [accum, step, List.range_succ, List.foldl_append]
    have hInv : ∀ j, Indep [indices + depth, rT] (Inv j) := by
      intro j c c' hag ⟨hp, hn, hm, ht⟩
      have hwide : Agree (controlRegs indices values k) c c' := hag.mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hmI
        · simp [controlRegs]
      have hnreg : endpointCount ∉ [indices + depth, rT] := by
        simp [endpointCount, rT]; omega
      have hplaced : Indep [indices + depth, rT] (Placed indices values memory stem) :=
        (placed_indep hi hv hd hdk).mono fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> simp
      exact ⟨hP _ c c' hwide hp, (hag.reg _ hnreg).trans hn, hag.mem.trans hm,
        hplaced c c' hag ht⟩
    have hstep : ∀ j, j < N →
        HTB S (.seq (readChoice indices values depth)
          (scanTuples indices values (depth + 1) n body))
          (fun c => Inv j c ∧ c.reg (indices + depth) = j ∧ c.reg endpointCount = N)
          (fun c => Inv (j + 1) c ∧ c.reg (indices + depth) = j ∧
            c.reg endpointCount = N) (tupleTime N B n + 3) := by
      intro j hj
      have hread := readChoice_spec (memory := memory) hi hv hd hdk hj hS (hP (accum j))
      have hlen : (stem ++ [j]).length = depth + 1 := by simp [hd]
      have hsum' : depth + 1 + n = k := by omega
      have hb' : ∀ i ∈ stem ++ [j], i < N := by
        intro i hi'
        rcases List.mem_append.mp hi' with hi' | hi'
        · exact hb i hi'
        · simpa using (show i = j from List.mem_singleton.mp hi') ▸ hj
      have hrec := ih (depth + 1) (stem ++ [j]) (accum j) hlen hsum' hb'
      refine (hread.seq hrec).mono ?_ ?_ (by omega)
      · rintro c ⟨⟨hp, hn, hm, ht⟩, hjreg, _⟩
        exact ⟨hp, hn, hm, ht, hjreg⟩
      · rintro c ⟨hp, hn, hm, ht⟩
        refine ⟨⟨?_, hn, hm, ht.stem⟩, ?_, hn⟩
        · rw [hacc]
          exact hp
        · rw [← hd]
          exact ht.last
    have hloop := HTB.forUpC Inv (tupleTime N B n + 3) hctr hbound hdistinct hInv hstep
    have hloop' := hloop.mono (P' := fun c => P a c ∧ c.reg endpointCount = N ∧
        c.mem = memory ∧ Placed indices values memory stem c)
      (Q' := fun c => P (foldTuples N F (n + 1) stem a) c ∧
        c.reg endpointCount = N ∧ c.mem = memory ∧ Placed indices values memory stem c)
      (fun c hc => ⟨by simpa [Inv, accum] using hc, hc.2.1⟩)
      (fun c hc => by simpa [Inv, accum, step, foldTuples] using hc.1) le_rfl
    simpa [scanTuples, tupleTime, Nat.add_assoc] using hloop'

theorem tupleTime_bound (N B n : ℕ) :
    tupleTime N B n ≤ (B + 10) * (N + 1) ^ (n + 1) := by
  induction n with
  | zero =>
    simp only [tupleTime, Nat.zero_add, pow_one]
    have : 1 ≤ N + 1 := by omega
    nlinarith
  | succ n ih =>
    rw [tupleTime, pow_succ]
    have hp : N + 1 ≤ (N + 1) ^ (n + 1) := by
      exact Nat.le_self_pow (by omega) _
    nlinarith

end STACS2027.Runtimes.GeneralCycles
