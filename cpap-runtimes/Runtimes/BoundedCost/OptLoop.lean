module

public import Runtimes.BoundedCost.OptStep
public import Runtimes.BoundedCost.OptEmit
import Mathlib.Tactic

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.OptLoop

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost OptControl

set_option maxHeartbeats 1000000

/-- The exact remaining sum of per-budget bounds. -/
def remaining (work : ℕ → ℕ) (last start : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (last + 1 - start), (work (start + j) + 1)

theorem remaining_step (work : ℕ → ℕ) {last start : ℕ} (hs : start ≤ last) :
    remaining work last start = work start + 1 + remaining work last (start + 1) := by
  unfold remaining
  rw [show last + 1 - start = (last - start) + 1 by omega, Finset.sum_range_succ']
  rw [show last + 1 - (start + 1) = last - start by omega]
  simp only [Nat.add_zero]
  have he : (∑ j ∈ Finset.range (last - start), (work (start + (j + 1)) + 1)) =
      ∑ j ∈ Finset.range (last - start), (work (start + 1 + j) + 1) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    omega
  rw [he]
  omega

def Inv (component : Stmt) (C : ℕ) (g : Graph) (k P : ℕ) : Option ℕ → Config → Prop
  | none => OptStep.Done component C g k P
  | some p => fun c => OptCall.State component g k p c ∧ p ≤ P

def potential (component : Stmt) (C : ℕ) (g : Graph) (k P : ℕ) : Option ℕ → ℕ
  | none => 0
  | some p => remaining (OptStep.cost component C g k) P p

def program (component : Stmt) (C : ℕ) : Stmt :=
  .loop (callerRegister alive) (OptStep.program component C)

theorem program_spec {component : Stmt} {C : ℕ} (hcomponent : OptCall.BoundedProgram component C)
    {g : Graph} {k P S : ℕ} (hopt : IsOptimalCost g k P) (hk : 3 ≤ k)
    (ht : 0 < (cycles g k).length) (hspace : OptCall.callSpace C g k P ≤ S) :
    HTB S (program component C) (OptCall.State component g k 0)
      (OptStep.Done component C g k P)
      ((∑ p ∈ Finset.range (P + 1), (OptStep.cost component C g k p + 1)) + 1) := by
  have hbody : ∀ x, HTBt S (OptStep.program component C)
      (fun c => Inv component C g k P x c ∧ c.reg (callerRegister alive) ≠ 0)
      (fun c' time => ∃ y, Inv component C g k P y c' ∧
        potential component C g k P y + time + 1 ≤ potential component C g k P x) := by
    intro x c hx
    cases x with
    | none => exact False.elim (hx.2 hx.1.2.2.1)
    | some p =>
      obtain ⟨hc, hpP⟩ := hx.1
      obtain ⟨c', time, he, hpost, ht'⟩ := OptStep.step_spec hcomponent hopt hk ht S p hpP hspace c hc
      refine ⟨c', time, he, ?_⟩
      by_cases hp : p = P
      · refine ⟨none, ?_, ?_⟩
        · simpa only [hp, ite_true, Inv] using hpost
        · simp only [potential, zero_add]
          change time + 1 ≤ remaining (OptStep.cost component C g k) P p
          rw [remaining_step _ hpP]
          omega
      · refine ⟨some (p + 1), ⟨?_, by omega⟩, ?_⟩
        · simpa only [if_neg hp] using hpost
        · change remaining (OptStep.cost component C g k) P (p + 1) + time + 1 ≤
            remaining (OptStep.cost component C g k) P p
          rw [remaining_step _ hpP]
          omega
  have h := HTB.loopG (S := S) (a := callerRegister alive) (body := OptStep.program component C)
    (Inv component C g k P) (potential component C g k P) hbody (some 0)
  refine h.mono (fun c hc => ⟨hc, by omega⟩) ?_ ?_
  · rintro c ⟨x, hx, halive⟩
    cases x with
    | none => exact hx
    | some p => exact False.elim (by have := hx.1.2.2.1; omega)
  · simp [potential, remaining]

/-- After the first accepted budget the RAM emits that budget and its assignment. -/
def searchAndEmit (component : Stmt) (C : ℕ) : Stmt :=
  .seq (program component C) OptEmit.program

theorem searchAndEmit_spec {component : Stmt} {C : ℕ} (hcomponent : OptCall.BoundedProgram component C)
    {g : Graph} {k P S : ℕ} (hopt : IsOptimalCost g k P) (hk : 3 ≤ k)
    (ht : 0 < (cycles g k).length) (hspace : OptCall.callSpace C g k P ≤ S) :
    HTB S (searchAndEmit component C) (OptCall.State component g k 0)
      (fun c => OptEmit.OptimumAnswer g k c.out)
      ((∑ p ∈ Finset.range (P + 1), (OptStep.cost component C g k p + 1)) +
        12 * (OptCall.bound C g k P + 1) + 1) := by
  intro c₀ hc₀
  obtain ⟨c₁, time₁, he₁, h₁, ht₁⟩ := program_spec hcomponent hopt hk ht hspace c₀ hc₀
  obtain ⟨hg, hp, _, hb, _, _, ho, output, hl, hm, hans, hhead⟩ := h₁
  have hlength : output.length ≤ OptCall.bound C g k P := by
    rcases hans with hneg | ⟨pos, hpos, hlen, _⟩
    · rw [hneg.2] at hhead
      simp at hhead
    · have hinput := OptCall.bound_input C g k P
      rw [CoreRAM.coreInput_length] at hinput
      have htk : (cycles g k).length ≤ k * (cycles g k).length :=
        Nat.le_mul_of_pos_left _ (by omega)
      simp only [hpos, List.length_cons, hlen]
      omega
  have houtputSpace : 4 * (OptCall.bound C g k P + output.length) + 1 ≤ S := by
    unfold OptCall.callSpace at hspace
    omega
  obtain ⟨c₂, time₂, he₂, ho₂, ht₂⟩ := OptEmit.program_spec c₁ hp hb hl hm ho houtputSpace c₁ rfl
  refine ⟨c₂, time₁ + time₂, .seq he₁ he₂, ?_, ?_⟩
  · exact ⟨P, output, by simpa using ho₂, hopt, hans, hhead⟩
  · nlinarith only [ht₁, ht₂, hlength]

end STACS2027.Runtimes.BoundedCost.OptLoop
