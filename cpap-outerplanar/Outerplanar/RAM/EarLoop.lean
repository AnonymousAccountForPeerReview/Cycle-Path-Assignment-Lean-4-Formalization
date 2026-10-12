module

public import Outerplanar.RAM.EarElim
import Mathlib.Tactic

/-!
# The ear-elimination machine: the elimination loop

`mainLoop_spec`: from the initial state, the `while` loop `mainLoop` ends in the state
`Ear.loop (4 N + 1) (Ear.init N L)` of `Ear.earHam`, within `5 + (Φ N (init N L) + 1)` steps,
where the potential

  `Φ N s = 128 · pot s + 24 · asum N s + 48 · cnt`

(`pot s = 3 cnt + |stack|`, `asum N s` = the total length of the lists of the alive vertices)
pays for every round (`phi_round`): a skip lowers `pot`; an elimination of `v` lowers `pot`,
removes `adj v` from `asum` (which gains at most two entries) and lowers `cnt`, which pays for
the scan of `adj v`. Initially `Φ ≤ 560 N + 48 |L|` (`phi_init_le`).

The loop invariant (`MInv`) carries the abstract state `s` (ghost) with `Good N s`,
`fin s = fin (init N L)` and a ghost Hamiltonian cycle `H` with `Ear.Inv` and `Ear.Static` (kept
by `Ear.Inv.step_static`; they make the orientation answer every query, `round_spec`); when the
test fails, `s` is stopped, so `s = fin (init N L)`. The triple is an `HTB S` triple, for any
bound `S ≥ bEND F N |L|` of the layout.
-/

@[expose] public section

namespace STACS2027.RAM.EarR

open STACS2027 STACS2027.Ear

/-- The potential of the elimination loop. -/
def phi (N : ℕ) (s : State) : ℕ := 128 * pot s + 24 * asum N s + 48 * s.cnt

theorem phi_round {N : ℕ} {s : State} (hG : Good N s) (hRun : Running s) :
    phi N (step s) + roundCost s + 1 ≤ phi N s := by
  have hpot := pot_step s hRun
  obtain ⟨hne, hc3⟩ := hRun
  obtain ⟨v, rest, hs⟩ := List.exists_cons_of_ne_nil hne
  have hv : v < N := hG.stack_lt v (by simp [hs])
  rw [roundCost_cons hs]
  unfold phi
  by_cases h : s.dead v = false ∧ s.deg v = 2
  · simp only [h, and_self, ↓reduceIte]
    rw [step_elim hs h] at hpot ⊢
    have ha := asum_elim (N := N) { s with stack := rest }
      (((s.adj v).filter fun x => s.dead x = false).getD 0 0)
      (((s.adj v).filter fun x => s.dead x = false).getD 1 0) hv h.1
    have hasum : asum N { s with stack := rest } = asum N s := rfl
    rw [elim_cnt]
    simp only at ha ⊢
    omega
  · simp only [h, ↓reduceIte]
    rw [step_skip hs h] at hpot ⊢
    have hasum : asum N { s with stack := rest } = asum N s := rfl
    rw [hasum]
    simp only at hpot ⊢
    omega

theorem good_init {N : ℕ} {L : List Edge} (hL : ∀ e ∈ L, e.1 < N ∧ e.2 < N) : Good N (init N L) where
  stack_lt := fun v hv => by
    rw [init_stack, List.mem_reverse] at hv
    exact stackPre_lt L N v hv
  adj_lt := initAdj_lt hL
  log_lt := by simp [init_log]
  log_len := by simp [init_log, init_cnt]
  pot_le := pot_init_le N L

theorem phi_init_le {N : ℕ} {L : List Edge} (hL : ∀ e ∈ L, e.1 < N ∧ e.2 < N) :
    phi N (init N L) ≤ 560 * N + 48 * L.length := by
  have h1 := pot_init_le N L
  have h2 := asum_init_le hL
  unfold phi
  rw [init_cnt]
  omega

/-- The invariant of the elimination loop, after each test. -/
def MInv (N : ℕ) (L : List Edge) (F : ℕ) (m₀ : ℕ → ℕ) (ham0 : List ℕ) (s : State) (c : Config) :
    Prop :=
  LRep N L F m₀ s c ∧ Good N s ∧ fin s = fin (init N L) ∧ (c.reg rT = 0 ↔ ¬ Running s) ∧
    ∃ H, Inv N ham0 s H ∧ Static L s H

/-- **The elimination loop** ends in the state of `Ear.earHam`, given the ghost invariants of the
initial state and an orientation of `L` (`OutOK`). -/
theorem mainLoop_spec {S : ℕ} (N : ℕ) (L : List Edge) (F : ℕ) (m₀ : ℕ → ℕ) (hN : 3 ≤ N)
    (hL : ∀ e ∈ L, e.1 < e.2 ∧ e.2 < N) {ham0 : List ℕ}
    (hI0 : ∃ H, Inv N ham0 (init N L) H ∧ Static L (init N L) H) (hO : OutOK N L F m₀)
    (hS : bEND F N L.length ≤ S) :
    HTB S mainLoop (LRep N L F m₀ (init N L)) (LRep N L F m₀ (loop (4 * N + 1) (init N L)))
      (5 + (phi N (init N L) + 1)) := by
  have hL' : ∀ e ∈ L, e.1 < N ∧ e.2 < N := fun e he => ⟨by have := hL e he; omega, (hL e he).2⟩
  have hGi : Good N (init N L) := good_init hL'
  have hinit : HTB S mcond (LRep N L F m₀ (init N L)) (MInv N L F m₀ ham0 (init N L)) 5 :=
    HTB.of_HT rfl (HT.run_le (by decide) (by decide) fun c hR =>
      ⟨(mcond_run hR).1, hGi, rfl, (mcond_run hR).2, hI0⟩)
  have hl := HTB.whileG (cond := mcond) (body := mbody) (MInv N L F m₀ ham0) (phi N) (init N L) hinit
    fun s c ⟨⟨hR, hG, hfin, hT, H, hI, hSt⟩, hT0⟩ => by
      have hRun : Running s := by
        by_contra h
        exact hT0 (hT.mpr h)
      obtain ⟨H', hI', hSt'⟩ := hI.step_static hSt hRun
      exact HTB.toG (y := step s) ((round_spec (L := L) (F := F) (m₀ := m₀) hN hG hRun hI hSt hO
        hS).post fun c' ⟨hR', hT'⟩ =>
          ⟨hR', good_step hG (by omega) hRun, (fin_step hRun).trans hfin, hT', H', hI', hSt'⟩)
        (phi_round hG hRun) c hR
  refine hl.post fun c ⟨y, ⟨hR, _, hfin, hT, _⟩, hT0⟩ => ?_
  rw [loop_init, ← hfin, fin_stop (hT.mp hT0)]
  exact hR

end STACS2027.RAM.EarR
