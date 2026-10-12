module

public import Runtimes.GeneralCycles.PairScan
public import Runtimes.GeneralCycles.Counter
import Mathlib.Tactic

/-! A complete bounded RAM test of cycle validity. Artifact date: 2026-10-12. -/

@[expose] public section

namespace STACS2027.Runtimes.GeneralCycles

open STACS2027 STACS2027.RAM

def registerValidTest (k : ℕ) (rs : List ℕ) : RegTest :=
  .both (.truth (decide (3 ≤ k ∧ rs.length = k))) (distinctTest rs)

def validRegisters (k : ℕ) (rs : List ℕ) (d : ℕ) : Stmt :=
  .seq ((registerValidTest k rs).flag d) (scanPairs (cyclicRegs rs) d)

def validCheck (values k d : ℕ) : Stmt := validRegisters k (registers values k) d

def validityConstant (values k d : ℕ) : ℕ :=
  size ((registerValidTest k (registers values k)).flag d) + 220 * (k + 1)

theorem held_values {rs : List ℕ} {values : ℕ → ℕ} {c : Config}
    (h : Held rs values c) : regValues c rs = rs.map values := List.map_congr_left h

theorem cyclicRegs_length_le (rs : List ℕ) : (cyclicRegs rs).length ≤ rs.length := by
  have h := congrArg List.length (cyclicRegs_map rs (initial []))
  simp only [List.length_map, cycleEdges, pathEdges_length, regValues, List.length_append,
    List.length_take, List.length_map] at h
  omega

theorem allPairs_cyclic (g : Graph) (rs : List ℕ) (c : Config) :
    allPairs g c.reg (cyclicRegs rs) ↔ ∀ e ∈ cycleEdges (regValues c rs), e ∈ g := by
  rw [← cyclicRegs_map]
  simp only [List.forall_mem_map]
  rfl

theorem registerValidTest_eval (k : ℕ) (rs : List ℕ) (c : Config) :
    (registerValidTest k rs).eval c =
      decide (3 ≤ k ∧ rs.length = k ∧ (regValues c rs).Nodup) := by
  simp [registerValidTest, RegTest.eval, Bool.and_assoc]

theorem registerValidTest_safe {k : ℕ} {rs : List ℕ} (h : rT ∉ rs) :
    rT ∉ (registerValidTest k rs).sources := by
  simpa [registerValidTest, RegTest.sources] using distinctTest_safe rs h

theorem validRegisters_frozen {g : Graph} {rs : List ℕ} {k d S : ℕ}
    (c₀ : Config) (hregs : ∀ r ∈ rs, 100 ≤ r) (hd : 40 ≤ d) (hd' : d < 50)
    (hS : 2 * g.length + 1 ≤ S) (hc : c₀.reg edgeCount = g.length)
    (hm : c₀.mem = (initial (graphInput g)).mem) :
    HTB S (validRegisters k rs d) (fun c => c = c₀)
      (fun c => c.reg d = bit (decide (IsCycle g k (regValues c₀ rs))) ∧
        Agree (d :: edgeScratch) c₀ c)
      (size ((registerValidTest k rs).flag d) +
        (cyclicRegs rs).length * (208 * (g.length + 1) + 3) + 1) := by
  let W := d :: edgeScratch
  let memory := (initial (graphInput g)).mem
  let Base := fun c => Agree W c₀ c ∧ c.reg edgeCount = g.length ∧
    c.mem = memory ∧ Held rs c₀.reg c
  let b := (registerValidTest k rs).eval c₀
  have hW : ∀ r ∈ rs, r ∉ W := by
    intro r hr
    have h := hregs r hr
    simp [W, edgeScratch, rT, edgeCounter, edgeAddr, edgeFirst, edgeSecond, edgeFound]
    omega
  have hbase : Indep W Base := by
    intro c c' hag ⟨ha, hn, hmemory, hh⟩
    have hnreg : edgeCount ∉ W := by
      simp [W, edgeCount, edgeScratch, rT, edgeCounter, edgeAddr,
        edgeFirst, edgeSecond, edgeFound]
      omega
    exact ⟨ha.trans hag, (hag.reg _ hnreg).trans hn, hag.mem.trans hmemory,
      held_indep hW _ _ hag hh⟩
  have hsafe : rT ∉ (registerValidTest k rs).sources := registerValidTest_safe (by
    intro hr
    have := hregs rT hr
    simp [rT] at this)
  have hinit : HTB S ((registerValidTest k rs).flag d) Base
      (fun c => Base c ∧ c.reg d = bit b) (size ((registerValidTest k rs).flag d)) := by
    have hlf := (registerValidTest k rs).branch_loopFree (s := .const d 1) (u := .const d 0)
      trivial trivial
    have hst := (registerValidTest k rs).branch_stores (s := .const d 1) (u := .const d 0) rfl rfl
    have hwr := (registerValidTest k rs).branch_writes (s := .const d 1) (u := .const d 0) rfl rfl
    have hmf := (registerValidTest k rs).branch_memFree (s := .const d 1) (u := .const d 0) rfl rfl
    refine HTB.run hlf ?_
    intro c hh
    have hag : Agree W c (run ((registerValidTest k rs).flag d) c) :=
      agree_run hlf hst hwr (by
        intro r hr
        rcases (registerValidTest k rs).branch_wregs hr with h | h | h
        · simp [W, edgeScratch, h]
        · exact List.mem_cons.mpr (Or.inl (by simpa [wregs] using h))
        · exact List.mem_cons.mpr (Or.inl (by simpa [wregs] using h))) c
    refine ⟨AddrOK.of_memFree hmf, hbase _ _ hag hh, ?_⟩
    rw [RegTest.run_flag _ hsafe]
    have he : (registerValidTest k rs).eval c = b := by
      dsimp only [b]
      rw [registerValidTest_eval, registerValidTest_eval, held_values hh.2.2.2]
      rfl
    simp [bit, he]
  have hagree : Indep W (fun c => Agree W c₀ c) := fun _ _ hag h => h.trans hag
  have hpairs := scanPairs_spec (P := fun c => Agree W c₀ c) (values := c₀.reg)
    (cyclicRegs rs) b hregs hd hd' (cyclicRegs_mem rs) hagree (graphMemory_initial g) hS
  have hall := hinit.seq (hpairs.pre (by
    rintro c ⟨⟨ha, hn, hm', hh⟩, hf⟩
    exact ⟨ha, hn, hm', hh, hf⟩))
  refine hall.mono ?_ ?_ (by omega)
  · intro c he
    subst c
    exact ⟨Agree.refl W c₀, hc, hm, fun _ _ => rfl⟩
  · rintro c ⟨ha, _, _, _, hf⟩
    refine ⟨?_, ha⟩
    have he : (b && decide (allPairs g c₀.reg (cyclicRegs rs))) =
        decide (IsCycle g k (regValues c₀ rs)) := by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      change ((registerValidTest k rs).eval c₀ = true ∧
        allPairs g c₀.reg (cyclicRegs rs)) ↔ IsCycle g k (regValues c₀ rs)
      rw [registerValidTest_eval, decide_eq_true_eq, allPairs_cyclic]
      unfold IsCycle
      have hlen : (regValues c₀ rs).length = rs.length := by simp [regValues]
      rw [hlen]
      tauto
    simpa [bit, he] using hf

theorem validCheck_bound (values k d m : ℕ) :
    size ((registerValidTest k (registers values k)).flag d) +
      (cyclicRegs (registers values k)).length * (208 * (m + 1) + 3) + 1 ≤
        validityConstant values k d * (2 * m + 1) := by
  have hl : (cyclicRegs (registers values k)).length ≤ k := by
    simpa [registers] using cyclicRegs_length_le (registers values k)
  have hm := Nat.mul_le_mul_right (208 * (m + 1) + 3) hl
  dsimp [validityConstant]
  nlinarith [Nat.zero_le (size ((registerValidTest k (registers values k)).flag d)),
    Nat.zero_le m, Nat.zero_le k]

end STACS2027.Runtimes.GeneralCycles
