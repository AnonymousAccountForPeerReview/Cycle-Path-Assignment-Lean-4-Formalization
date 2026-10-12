module

public import Runtimes.BoundedCost.Answer
import Mathlib.Tactic

/-!
# Theorem 4 on the RAM: `Ψ = 0` by linear 2-SAT

For `Ψ = 0` the formula `Γ' = Γ_∅ = permittedFormula g k []` (`almostFormula_zero`) is a plain
2-CNF over the `kt` variables `b_{C,e}`, satisfiable iff a cost-`0` assignment exists
(`permittedFormula_nil_satisfiable_iff`). The machine `zero5 = form5 ; callSat5 ; stepRec`
builds it in memory, runs the formalized linear-time 2-SAT phase (`TwoSat.twoSat_spec`) and
Corollary 5's recovery: `zero5_spec`, within `zeroCost g k` steps and the addresses below
`zeroSpace g k` (the 2-SAT phase's layout after the codes, `TwoSat.endL`). No Almost 2-SAT
solver is involved.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost Complexity.SAT

/-- The space of the machine for `Ψ = 0`. -/
def zeroSpace (g : Graph) (k : ℕ) : ℕ :=
  TwoSat.endL (k * (cycles g k).length) (almostFormula g k 0).length (formSpace g k 0)

/-- The cost of the machine for `Ψ = 0`. -/
def zeroCost (g : Graph) (k : ℕ) : ℕ :=
  formCost g k 0 + (6 + TwoSat.CT * (k * (cycles g k).length + (almostFormula g k 0).length + 1) +
    ((cycles g k).length * (k * (k * 40 + 18) + 11) + 7))

/-- **The machine for `Ψ = 0`**: the formula, linear 2-SAT, the recovery. -/
theorem zero5_spec (g : Graph) (k : ℕ) (hk : 4 ≤ k) :
    HTB (zeroSpace g k) zero5 (fun c => c = initial (boundedCostInput g k 0))
      (fun c => BoundedCostAnswer g k 0 c.out) (zeroCost g k) := by
  set n := k * (cycles g k).length
  set f := almostFormula g k 0
  have hf : TwoSat.IsTwoCNF n f := almost_two g k 0
  have hcl : (TwoSat.codes f).length = 2 * f.length := TwoSat.length_codes hf
  have hok : TwoSat.CodesOk n (TwoSat.codes f) := TwoSat.codes_ok hf
  have hl := lay5 g k
  have hE := TwoSat.endL_le n f.length (formSpace g k 0)
  have hFS : formSpace g k 0 = bC5 g k + 2 * f.length := rfl
  have hZS : zeroSpace g k = TwoSat.endL n f.length (formSpace g k 0) := rfl
  have hEL := TwoSat.layout_eqs n f.length (formSpace g k 0)
  -- the formula
  have h1 := form5_spec (S := zeroSpace g k) g k 0 (by rw [hcl]; omega)
  -- the moves
  have h2 : HTB (zeroSpace g k) satMoves
      (fun c => HS g k (fun _ => 0) f c ∧ c.reg gPSI = 0)
      (fun c => TwoSat.TwoSatIn n f.length (TwoSat.codes f) c ∧ GA g k c ∧
        Arr c.mem (bV g) (verts g k) ∧ c.out = [] ∧ c.reg rFREE = formSpace g k 0) 6 :=
      HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨hG, hfr, hn, hM, ho⟩, _⟩ => ?_
    have hag : Agree [rT, TwoSat.tN, TwoSat.tM, TwoSat.tCL] c (run satMoves c) :=
      agree_run (by decide) rfl rfl (by decide) c
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, (show RegIndep [rT, TwoSat.tN, TwoSat.tM, TwoSat.tCL] (GA g k) by
      indep [gA_iff]).indep c _ hag hG.ga, by rw [hag.mem]; exact hM.mverts, by rw [hag.out, ho],
      by rw [hag.reg rFREE (by decide), hfr, hcl]; rfl⟩
    · simp +decide [satMoves, run_mov (show gKT ≠ rT by decide), run_mov (show gNC ≠ rT by decide),
        run_mov (show gCL ≠ rT by decide), hG.ga.rkt, n]
    · simp +decide [satMoves, run_mov (show gKT ≠ rT by decide), run_mov (show gNC ≠ rT by decide),
        run_mov (show gCL ≠ rT by decide), hn]
    · rw [hag.mem]
      simpa +decide [satMoves, run_mov (show gKT ≠ rT by decide), run_mov (show gNC ≠ rT by decide),
        run_mov (show gCL ≠ rT by decide), hG.rcl] using hM.mcodes
    · rw [hag.mem, hag.reg rFREE (by decide), hfr]; exact hM.mzero
    · rw [hag.reg rFREE (by decide), hfr]
      simp +decide [satMoves, run_mov (show gKT ≠ rT by decide), run_mov (show gNC ≠ rT by decide),
        run_mov (show gCL ≠ rT by decide), hG.rcl]
  -- the 2-SAT phase and the recovery
  have h3 : HTB (zeroSpace g k) (.seq TwoSat.twoSat stepRec)
      (fun c => TwoSat.TwoSatIn n f.length (TwoSat.codes f) c ∧ GA g k c ∧
        Arr c.mem (bV g) (verts g k) ∧ c.out = [] ∧ c.reg rFREE = formSpace g k 0)
      (fun c => BoundedCostAnswer g k 0 c.out)
      (TwoSat.CT * (n + f.length + 1) + ((cycles g k).length * (k * (k * 40 + 18) + 11) + 7)) := by
    refine HTB.of_forall fun c₀ ⟨hB, hga, hV, ho, hfr⟩ => ?_
    have hT := TwoSat.twoSat_spec (S := zeroSpace g k) n f.length (TwoSat.codes f) c₀ hcl hok
      (by rw [hfr, hZS])
    refine HTB.seq (hT.pre fun c hc => ⟨hc ▸ hB, hc⟩) (HTB.of_forall fun c₁ hO => ?_)
    have hcor := TwoSat.twoSatOut_correct hf hO
    have hfr' : ∀ r, 250 ≤ r → c₁.reg r = c₀.reg r := fun r hr =>
      hO.frame r (fun h => absurd (h ▸ hr) (by decide)) (fun h => absurd (h ▸ hr) (by decide))
        (Or.inr hr)
    have hga₁ : GA g k c₁ := by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hga
      exact ⟨by rw [hfr' _ (by decide), h1], by rw [hfr' _ (by decide), h2],
        by rw [hfr' _ (by decide), h3], by rw [hfr' _ (by decide), h4], by rw [hfr' _ (by decide), h5]⟩
    have hV₁ : Arr c₁.mem (bV g) (verts g k) :=
      hV.of_below hO.same (by rw [hfr, length_verts, hFS]; omega)
    have hbits : ∀ x < n, c₁.mem (c₁.reg TwoSat.tAS + x) ≤ 1 := fun x hx => by
      have := hO.asg.get (i := x) (by simp [TwoSat.asgBits]; omega)
      rw [this]
      simp only [TwoSat.asgBits, List.getElem_map, List.getElem_range]
      split <;> omega
    have hfresh := hO.fresh
    have hrf := hO.rfree
    rw [hfr] at hrf
    refine (stepRec_spec g k c₁.mem (c₁.reg TwoSat.tAS) (c₁.reg TwoSat.tOK) hV₁ hbits
      (by rw [hZS]; omega) (by rw [hZS]; omega)).mono
      (fun c hc => by subst hc; exact ⟨⟨hga₁, rfl, rfl⟩, by rw [hO.out, ho], rfl⟩)
      (fun c hout => ?_) le_rfl
    by_cases h1 : c₁.reg TwoSat.tOK = 1
    · rw [hout, ite_eq_right (by omega)]
      have := hcor.2 h1
      exact answer_of_table hk _ (I := []) (by simp) (by rw [← almostFormula_zero]; exact this)
    · have h0 : c₁.reg TwoSat.tOK = 0 := by rw [hO.ok] at h1 ⊢; split at h1 <;> simp_all
      rw [hout, ite_eq_left h0]
      refine Or.inl ⟨fun hA => h1 (hcor.1.mpr ?_), rfl⟩
      show Satisfiable (almostFormula g k 0)
      rw [almostFormula_zero]; exact (permittedFormula_nil_satisfiable_iff hk g).mpr hA
  refine (h1.seq (h2.seq h3).reassoc).weaken (le_of_eq ?_)
  simp only [zeroCost, Nat.add_assoc]; rfl

end STACS2027.Runtimes.BoundedCost
