module

public import Runtimes.BoundedCost.State
import Mathlib.Tactic

/-!
# Theorem 4 on the RAM: reading the input

* `stepInitZ_spec`: Corollary 5's `stepInit` on the input `boundedCostInput g k Ψ` followed by any
  list `z` (the extraction reads the input followed by the solver's answer): the registers `GA`,
  `rFREE = bD g k` (the address of `Ψ`), the memory untouched, within `5t + 16` steps and the
  addresses below any `S ≥ bD g k` (it reads the cells `0`, `2m + 1`, `2m + 2`);
* `stepInit5_spec`: phase 1 of the formula, `stepInit` then `readPsi`: `gPSI := Ψ`, the number of
  copies `gPS1 := nCopies g k Ψ` (`Ψ + 1`, or `0` without cycles), and the cell of `Ψ` is
  cleared, so that the state is Corollary 5's `InitPost g k` (the end of the input `bD g k` is
  the first free cell), within `5t + 23` steps and the addresses below any `S > bD g k`.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost

variable {S : ℕ}

/-- The number of copies of the path constraints: `Ψ + 1`, or `0` if there is no cycle (then
there is no path constraint). -/
def nCopies (g : Graph) (k Ψ : ℕ) : ℕ := if (cycles g k).length = 0 then 0 else Ψ + 1

/-- The registers holding `Ψ` and the number of copies `N`. -/
def PsiR (Ψ N : ℕ) (c : Config) : Prop := c.reg gPSI = Ψ ∧ c.reg gPS1 = N

theorem initReadZ_spec (g : Graph) (k Ψ : ℕ) (z : List ℕ) (hS : bD g k ≤ S) :
    HTB S initRead (fun c => c = initial (boundedCostInput g k Ψ ++ z))
      (fun c => c.reg gK = k ∧ c.reg gT = (cycles g k).length ∧ c.reg gV = bV g ∧
        c.reg rFREE = 0 ∧ c.mem = (initial (boundedCostInput g k Ψ ++ z)).mem ∧ c.out = []) 10 :=
    HTB.of_HT_addrOK (by decide) (fun c hc => by
      subst hc
      obtain ⟨h0, -, -, -, -⟩ := input5z_facts g k Ψ z
      have hb : bD g k = 2 * g.length + 3 + k * (cycles g k).length := rfl
      addr_ok [initRead, initial_reg, h0]) <| by
  refine HT.run_le (by decide) (by decide) fun c hc => ?_
  subst hc
  obtain ⟨h0, hk, ht, -, -⟩ := input5z_facts g k Ψ z
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp +decide only [initRead, run_seq', run_load, run_add, run_addc, run_subc, setReg_reg,
    setReg_mem, setReg_out, ↓reduceIte, initial_reg, h0, initial_out]
  · rw [show g.length + g.length + 3 - 2 = 2 * g.length + 1 by omega, hk]
  · rw [show g.length + g.length + 3 - 1 = 2 * g.length + 2 by omega, ht]
  · simp [bV]; omega

/-- Corollary 5's `stepInit` on the input of Theorem 4 followed by `z`. -/
theorem stepInitZ_spec (g : Graph) (k Ψ : ℕ) (z : List ℕ) (hS : bD g k ≤ S) :
    HTB S stepInit (fun c => c = initial (boundedCostInput g k Ψ ++ z))
      (fun c => GA g k c ∧ c.reg rFREE = bD g k ∧ c.mem = (initial (boundedCostInput g k Ψ ++ z)).mem ∧
        c.out = []) (5 * (cycles g k).length + 16) := by
  have h1 := initReadZ_spec g k Ψ z hS
  have h2 := HTB.mul (S := S) (d := gKT) (a := gK) (b := gT) (k := sQ) (x := k)
    (y := (cycles g k).length)
    (P := fun c => c.reg gK = k ∧ c.reg gT = (cycles g k).length ∧ c.reg gV = bV g ∧
        c.reg rFREE = 0 ∧ c.mem = (initial (boundedCostInput g k Ψ ++ z)).mem ∧ c.out = [])
    (by decide) (by indep) (fun c h => h.1) (fun c h => h.2.1)
  have h3 : HTB S initFin (fun c => (c.reg gK = k ∧ c.reg gT = (cycles g k).length ∧
        c.reg gV = bV g ∧ c.reg rFREE = 0 ∧ c.mem = (initial (boundedCostInput g k Ψ ++ z)).mem ∧
        c.out = []) ∧ c.reg gKT = k * (cycles g k).length)
      (fun c => GA g k c ∧ c.reg rFREE = bD g k ∧ c.mem = (initial (boundedCostInput g k Ψ ++ z)).mem ∧
        c.out = []) 2 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨hk, ht, hv, _, hm, ho⟩, hkt⟩ => ?_
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    all_goals simp +decide only [initFin, run_seq', run_add, setReg_reg, setReg_mem, setReg_out,
      ↓reduceIte, hk, ht, hv, hkt, hm, ho]
    · ring
    · simp [bD]
  exact (h1.seq (h2.seq h3)).weaken (by omega)

/-- `readPsi`: `Ψ`, the number of copies, and the cell of `Ψ` cleared. -/
theorem readPsi_spec (g : Graph) (k Ψ : ℕ) (hS : bD g k + 1 ≤ S) :
    HTB S readPsi
      (fun c => GA g k c ∧ c.reg rFREE = bD g k ∧ c.mem = (initial (boundedCostInput g k Ψ)).mem ∧
        c.out = []) (fun c => InitPost g k c ∧ PsiR Ψ (nCopies g k Ψ) c) 8 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨hga, hfr, hm, ho⟩ => ?_
  obtain ⟨-, -, -, hV, hP, hZ⟩ := input5_facts g k Ψ
  refine ⟨by addr_ok [readPsi, hfr], ?_⟩
  have hga' : GA g k (run readPsi c) :=
    (show RegIndep [gPSI, sX, gPS1, rT] (GA g k) by indep [gA_iff]).run_of_sub (by decide)
      (by decide) hga
  have hl := lay5 g k
  have hmem : (run readPsi c).mem = upd (initial (boundedCostInput g k Ψ)).mem (bD g k) 0 := by
    simp +decide only [readPsi, run_seq', run_load, run_const, run_store,
      run_addc (show gPSI ≠ rT by decide), run_ifz', setReg_reg, setMem_reg, ↓reduceIte, hfr, hm]
    split_ifs <;> simp only [run_skip, setReg_mem, setMem_mem_upd, hm]
  have hreg : (run readPsi c).reg rFREE = bD g k ∧ (run readPsi c).out = [] ∧
      (run readPsi c).reg gPSI = Ψ ∧ (run readPsi c).reg gPS1 = nCopies g k Ψ := by
    have hT := hga.rt
    unfold nCopies
    by_cases ht0 : (cycles g k).length = 0
    · have hz : c.reg gT = 0 := by rw [hT, ht0]
      simp +decide [readPsi, run_addc (show gPSI ≠ rT by decide), hfr, hm, ho, hP, hz, ht0]
    · have hz : c.reg gT ≠ 0 := by rw [hT]; exact ht0
      simp +decide [readPsi, run_addc (show gPSI ≠ rT by decide), hfr, hm, ho, hP, hz, ht0]
  refine ⟨⟨hga', hreg.1, ?_, ?_, hreg.2.1⟩, hreg.2.2⟩
  · rw [hmem]; exact hV.upd_of_disjoint (by rw [length_verts]; omega)
  · rw [hmem]
    intro a ha
    by_cases hab : a = bD g k
    · subst hab; simp
    · simp only [upd_apply, hab, ↓reduceIte]; exact hZ a (by omega)

/-- **Phase 1**: reading `m`, `k`, `t`, `Ψ`. -/
theorem stepInit5_spec (g : Graph) (k Ψ : ℕ) (hS : bD g k + 1 ≤ S) :
    HTB S stepInit5 (fun c => c = initial (boundedCostInput g k Ψ))
      (fun c => InitPost g k c ∧ PsiR Ψ (nCopies g k Ψ) c) (5 * (cycles g k).length + 24) := by
  have h1 := stepInitZ_spec (S := S) g k Ψ [] (by omega)
  simp only [List.append_nil] at h1
  exact (h1.seq (readPsi_spec g k Ψ hS)).weaken (by omega)

end STACS2027.Runtimes.BoundedCost
