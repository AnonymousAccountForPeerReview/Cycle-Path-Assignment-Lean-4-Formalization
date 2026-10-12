module

public import Runtimes.ZeroCostRec
import Mathlib.Tactic

/-!
# Corollary 5 with its running time

The manuscript's Corollary 5 (`cor:Cost0Assignment`): *for every fixed `k ≥ 4`, a zero-cost
assignment for `CPAP(G, k)` can be found, or its nonexistence certified, in `O(k²t + Υ_k)`
time.* (`k = 3` goes through min-cost flow and is not treated here.)

`Υ_k` is the time to enumerate the simple `k`-cycles; as in the manuscript, the enumeration is
charged separately: the machine `zeroCostProg` receives the enumerated cycles as part of its input
`zeroCostInput g k = graphInput g ++ k :: t :: verts g k` (the graph, `k`, the number `t` of
cycles, and their vertices, cycle after cycle). Any enumeration that reads the graph takes at
least `m = |g|` steps, so `Υ_k ≥ m` and the bound `O(k²t + m)` proved here is `O(k²t + Υ_k)`.
(The machine itself does not read the edges of `g`: it reads `m` only to find the cycles.)

**The machine** (`ZeroCostProg.lean`): it maps the cycle edges to identifiers in linear time (a
label dictionary of size `max label + 1 ≤ labelBound g`, untouched cells being zero, then
outerplanar package's module `PairIds.pairIds` on the id pairs of the occurrences: a counting sort by
first id and a timestamped scan, no `N × N` table), builds in memory the literal codes of the
2-CNF `zcf g k` — the path
constraints `Γ₁` and the prefix clauses of Section 4 (the clauses of `zeroCostFormula g k`,
`mem_zcf`) — calls the linear-time 2-SAT phase `TwoSat.twoSat` (ANONYMIZED–ANONYMIZED–ANONYMIZED) on the
`2kt` variables, and, if the formula is satisfiable, recovers for every cycle `C_i` the omitted
position `omittedPosition g k σ i` of Algorithm 3 (`recoverAssignment g k σ`).

**Output**: `[0]` if `CPAP(G, k)` has no assignment of cost `0`; otherwise `1` followed by `t`
positions `pos` (each `< k`), and the paths `selected C_i pos_i` (`List.zipWith selected (cycles g k) pos`)
form a cycle-path assignment of cost `0`.

**Main theorem** `zeroCost_ram`: one program and one constant `C` serve every graph and every
`k ≥ 4`; the running time is at most `C · (k²t + m + 1)` steps, and the run accesses only the
addresses below `C · (labelBound g + k²t + m + 1)` (`RAM.ComputesIn`, input included;
`labelBound g = 1 + the largest label` is the size of the label dictionary, which costs space but
no time). The memory of the machine is `zeroCostSpace g k` (`zeroCostSpace_le`).
-/

@[expose] public section

namespace STACS2027.Runtimes.ZeroCost

open STACS2027 STACS2027.RAM STACS2027.RAM.R0 Complexity.SAT

variable {S : ℕ}

/-! ### The memory of the machine -/

/-- The memory of the machine: the input, the dictionary, the arrays of phases 4–5, the codes
of `zcf g k` and the arrays of the 2-SAT phase. -/
def zeroCostSpace (g : Graph) (k : ℕ) : ℕ :=
  TwoSat.endL (2 * (k * (cycles g k).length)) (zcf g k).length
    (bCL g k + (TwoSat.codes (zcf g k)).length)

theorem bCL_codes_le (g : Graph) (k : ℕ) :
    bCL g k + (TwoSat.codes (zcf g k)).length ≤ zeroCostSpace g k := by
  have := TwoSat.layout_eqs (2 * (k * (cycles g k).length)) (zcf g k).length
    (bCL g k + (TwoSat.codes (zcf g k)).length)
  unfold zeroCostSpace; omega

/-- The constant of the space bound. -/
def CS20 : ℕ := 140

/-- **The memory is linear** in `labelBound g + k²t + m + 1`. -/
theorem zeroCostSpace_le (g : Graph) {k : ℕ} (hk : 1 ≤ k) :
    zeroCostSpace g k ≤ CS20 * (labelBound g + k * k * (cycles g k).length + g.length + 1) := by
  have h1 := TwoSat.endL_le (2 * (k * (cycles g k).length)) (zcf g k).length
    (bCL g k + (TwoSat.codes (zcf g k)).length)
  have h2 := TwoSat.length_codes (zcf_two (g := g) (k := k))
  have h3 := length_zcf_le (g := g) (k := k)
  have h4 := layout_eqs g k
  have h5 := nV_le (g := g) (k := k)
  have h6 := nE_le g k
  have h7 := maxV_lt_labelBound (g := g) (k := k)
  have h8 : k * (cycles g k).length ≤ k * k * (cycles g k).length := by
    rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
  unfold zeroCostSpace CS20; omega

/-! ### Phase 8: the 2-SAT call -/

/-- The facts after the 2-SAT phase about the memory `m`, the address `A` of the assignment and
the answer `ok`. -/
def SatFacts (g : Graph) (k : ℕ) (m : ℕ → ℕ) (A ok : ℕ) : Prop :=
  Arr m (bV g) (verts g k) ∧ (∀ x < k * (cycles g k).length, m (A + x) ≤ 1) ∧ ok ≤ 1 ∧
    (ok = 1 ↔ Satisfiable (zcf g k)) ∧ (ok = 1 → evalCNF (memAsg m A) (zcf g k) = true) ∧
    A + k * (cycles g k).length ≤ zeroCostSpace g k

/-- The state after the 2-SAT phase. -/
def SatPost (g : Graph) (k : ℕ) (c : Config) : Prop :=
  ∃ m A ok, SatFacts g k m A ok ∧ (RG g k m A c ∧ c.out = [] ∧ c.reg TwoSat.tOK = ok)

/-- **Phase 8**: the 2-SAT phase on the codes of `zcf g k` over `2kt` variables. -/
theorem callSat_spec (g : Graph) (k : ℕ) (hSp : zeroCostSpace g k ≤ S) :
    HTB S callSat (fun c => GState g k (cntF g k (k * (cycles g k).length)) (zcf g k) c)
      (SatPost g k) (6 + TwoSat.CT * (2 * (k * (cycles g k).length) + (zcf g k).length + 1)) := by
  set n := 2 * (k * (cycles g k).length)
  set cl := TwoSat.codes (zcf g k)
  have hf := zcf_two (g := g) (k := k)
  have hcl : cl.length = 2 * (zcf g k).length := TwoSat.length_codes hf
  have hok : TwoSat.CodesOk n cl := TwoSat.codes_ok hf
  have hl := layout_eqs g k
  -- the moves
  have h0 : HTB S (.seq (.seq (mov TwoSat.tN gNV) (mov TwoSat.tM gNC)) (mov TwoSat.tCL gCL))
      (fun c => GState g k (cntF g k (k * (cycles g k).length)) (zcf g k) c)
      (fun c => TwoSat.TwoSatIn n (zcf g k).length cl c ∧ GA g k c ∧ Arr c.mem (bV g) (verts g k) ∧
        c.out = [] ∧ c.reg rFREE = bCL g k + cl.length) 6 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨hG, hfr, hn, hM, ho⟩ => ?_
    have hag : Agree [rT, TwoSat.tN, TwoSat.tM, TwoSat.tCL] c
        (run (.seq (.seq (mov TwoSat.tN gNV) (mov TwoSat.tM gNC)) (mov TwoSat.tCL gCL)) c) :=
      agree_run (by decide) rfl rfl (by decide) c
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, (show Indep [rT, TwoSat.tN, TwoSat.tM, TwoSat.tCL] (GA g k) by
      indep [gA_iff]) c _ hag hG.ga, by rw [hag.mem]; exact hM.mverts, by rw [hag.out, ho],
      by rw [hag.reg rFREE (by decide), hfr]⟩
    · simp +decide [run_mov (show gNV ≠ rT by decide), run_mov (show gNC ≠ rT by decide),
        run_mov (show gCL ≠ rT by decide), hG.ga.rnv, n]
    · simp +decide [run_mov (show gNV ≠ rT by decide), run_mov (show gNC ≠ rT by decide),
        run_mov (show gCL ≠ rT by decide), hn]
    · rw [hag.mem]
      simpa +decide [run_mov (show gNV ≠ rT by decide), run_mov (show gNC ≠ rT by decide),
        run_mov (show gCL ≠ rT by decide), hG.rcl] using hM.mcodes
    · rw [hag.mem, hag.reg rFREE (by decide), hfr]; exact hM.mzero
    · rw [hag.reg rFREE (by decide), hfr]
      simp +decide [run_mov (show gNV ≠ rT by decide), run_mov (show gNC ≠ rT by decide),
        run_mov (show gCL ≠ rT by decide), hG.rcl, cl]
  -- the 2-SAT phase
  have h1 : HTB S TwoSat.twoSat
      (fun c => TwoSat.TwoSatIn n (zcf g k).length cl c ∧ GA g k c ∧ Arr c.mem (bV g) (verts g k) ∧
        c.out = [] ∧ c.reg rFREE = bCL g k + cl.length) (SatPost g k)
      (TwoSat.CT * (n + (zcf g k).length + 1)) := by
    intro c ⟨hB, hga, hV, ho, hfr⟩
    obtain ⟨c', t, he, hO, ht⟩ := TwoSat.twoSat_spec (S := S) n (zcf g k).length cl c hcl hok
      (by rw [hfr]; exact hSp) c ⟨hB, rfl⟩
    refine ⟨c', t, he, ⟨c'.mem, c'.reg TwoSat.tAS, c'.reg TwoSat.tOK, ⟨?_, ?_, ?_,
      (TwoSat.twoSatOut_correct hf hO).1, (TwoSat.twoSatOut_correct hf hO).2, ?_⟩,
      ⟨?_, rfl, rfl⟩, by rw [hO.out, ho], rfl⟩, ht⟩
    · exact hV.of_below hO.same (by rw [hfr, length_verts]; omega)
    · intro x hx
      have := hO.asg.get (i := x) (by simp [TwoSat.asgBits, n]; omega)
      rw [this]
      simp only [TwoSat.asgBits, List.getElem_map, List.getElem_range]
      split <;> omega
    · rw [hO.ok]; split <;> omega
    · have h1 := hO.fresh.2
      have h2 := hO.rfree
      rw [hfr] at h2
      have hn : n = 2 * (k * (cycles g k).length) := rfl
      show c'.reg TwoSat.tAS + k * (cycles g k).length ≤
        TwoSat.endL n (zcf g k).length (bCL g k + cl.length)
      omega
    · have hfr' : ∀ r, 250 ≤ r → c'.reg r = c.reg r := fun r hr =>
        hO.frame r (fun h => absurd (h ▸ hr) (by decide)) (fun h => absurd (h ▸ hr) (by decide))
          (Or.inr hr)
      obtain ⟨h1, h2, h3, h4, h5⟩ := hga
      exact ⟨by rw [hfr' _ (by decide), h1], by rw [hfr' _ (by decide), h2],
        by rw [hfr' _ (by decide), h3], by rw [hfr' _ (by decide), h4], by rw [hfr' _ (by decide), h5]⟩
  exact HTB.assoc (HTB.assoc (h0.seq h1))

/-! ### The whole machine -/

/-- The answer of the machine. -/
def ZeroCostAnswer (g : Graph) (k : ℕ) (out : List ℕ) : Prop :=
  (¬ HasAssignment g k 0 ∧ out = [0]) ∨
    (∃ pos : List ℕ, out = 1 :: pos ∧ pos.length = (cycles g k).length ∧ (∀ p ∈ pos, p < k) ∧
      ValidChoices ((cycles g k).map selectedOptions) (List.zipWith selected (cycles g k) pos) ∧
      cost (List.zipWith selected (cycles g k) pos) = 0)

/-- The bound of the recovery and its correctness. -/
theorem stepRec_answer (g : Graph) (k : ℕ) (hk : 4 ≤ k) (hSp : zeroCostSpace g k ≤ S) :
    HTB S stepRec (SatPost g k) (fun c => ZeroCostAnswer g k c.out)
      ((cycles g k).length * (k * (k * 40 + 18) + 11) + 7) := by
  refine HTB.exists_pre fun m => HTB.exists_pre fun A => HTB.exists_pre fun ok =>
    HTB.prop_pre fun ⟨hV, hbits, hle, hsat, heval, hA⟩ => ?_
  have hD : bD g k ≤ S := by
    have := bCL_codes_le g k; have := layout_eqs g k; omega
  refine (stepRec_spec g k m A ok hV hbits hD (by omega)).post fun c ho => ?_
  by_cases h0 : ok = 0
  · left
    rw [ite_eq_left h0] at ho
    refine ⟨fun hA => ?_, ho⟩
    have : Satisfiable (zcf g k) := by
      obtain ⟨σ, hσ⟩ := (zeroCostFormula_satisfiable_iff hk g).mpr hA
      exact ⟨σ, by rw [evalCNF_zcf]; exact hσ⟩
    have := hsat.mpr this
    omega
  · right
    rw [ite_eq_right h0] at ho
    have h1 : ok = 1 := by omega
    set σ := memAsg m A
    have hσ : evalCNF σ (zeroCostFormula g k) = true := by rw [← evalCNF_zcf]; exact heval h1
    obtain ⟨hvalid, hcost⟩ := recoverAssignment_zeroCost hk g σ hσ
    have hpos : (List.range (cycles g k).length).map (recPos g k σ) =
        (List.range (cycles g k).length).map (omittedPosition g k σ) :=
      List.map_congr_left fun i hi => (omittedPosition_eq σ (List.mem_range.mp hi)).symm
    refine ⟨(List.range (cycles g k).length).map (omittedPosition g k σ), by rw [ho, hpos],
      by simp, ?_, ?_, ?_⟩
    · simp only [List.mem_map, List.mem_range]
      rintro p ⟨i, -, rfl⟩
      exact omittedPosition_lt g (by omega) σ i
    · rw [zipWith_recover]; exact hvalid
    · rw [zipWith_recover]; exact hcost

/-- The constant of the running time. -/
def CZeroCost : ℕ := 5000

/-- **The machine of Corollary 5**, as a Hoare triple: started on `zeroCostInput g k` (`k ≥ 4`), it
halts within `CZeroCost · (k²t + m + 1)` steps with a correct answer, accessing only the addresses
below any `S ≥ zeroCostSpace g k`. -/
theorem zeroCostProg_spec (g : Graph) (k : ℕ) (hk : 4 ≤ k) (hSp : zeroCostSpace g k ≤ S) :
    HTB S zeroCostProg (fun c => c = initial (zeroCostInput g k)) (fun c => ZeroCostAnswer g k c.out)
      (CZeroCost * (k * k * (cycles g k).length + g.length + 1)) := by
  have hL := layout_eqs g k
  have hC := bCL_codes_le g k
  have hPC : bCL g k + (TwoSat.codes (pathConstraints g k)).length ≤ S := by
    have hz : zcf g k = pathConstraints g k ++ occPre g k (k * (cycles g k).length) := rfl
    rw [hz, codes_append, List.length_append] at hC; omega
  have h := (stepInit_spec g k (by omega)).seq ((stepMax_spec g k (by omega)).seq
    ((stepDict_spec g k (by omega)).seq ((stepEdges_spec g k (by omega)).seq
    ((stepOff_spec g k (by omega)).seq ((stepPc_spec g k hPC).seq
    ((stepOcc_spec g k (by omega)).seq ((callSat_spec g k hSp).seq
    (stepRec_answer g k hk hSp))))))))
  refine h.weaken ?_
  have hN := nV_le (g := g) (k := k)
  have hE := nE_le g k
  have hZ := length_zcf_le (g := g) (k := k)
  set t := (cycles g k).length
  have e1 : t * (k * 36 + 8) = 36 * (k * t) + 8 * t := by ring
  have e2 : t * (k * (k * 65 + 7) + 8) = 65 * (k * k * t) + 7 * (k * t) + 8 * t := by ring
  have e3 : t * (k * (k * 40 + 18) + 11) = 40 * (k * k * t) + 18 * (k * t) + 11 * t := by ring
  have h1 : t ≤ k * t := Nat.le_mul_of_pos_left t (by omega)
  have h2 : k * t ≤ k * k * t := by
    rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
  simp only [TwoSat.CT, CZeroCost, PairIds.CI, PairIds.CL, PairIds.CR]
  omega

/-- **Corollary 5** (`k ≥ 4`): on `zeroCostInput g k`, within `C (k²t + m + 1)` steps (`O(k²t + Υ_k)`)
and the addresses below `C (labelBound g + k²t + m + 1)`, the program writes `[0]` if there is no
assignment of cost `0`, else `1` and one position `pos_i < k` per cycle forming one. -/
theorem zeroCost_ram :
    ∃ (prog : RAM.Stmt) (C : ℕ), ∀ (g : Graph) (k : ℕ), 4 ≤ k →
      ∃ (out : List ℕ) (T : ℕ),
        RAM.ComputesIn prog (zeroCostInput g k) out T
          (C * (labelBound g + k * k * (cycles g k).length + g.length + 1)) ∧
        T ≤ C * (k * k * (cycles g k).length + g.length + 1) ∧
        ((¬ HasAssignment g k 0 ∧ out = [0]) ∨
          (∃ pos : List ℕ, out = 1 :: pos ∧ pos.length = (cycles g k).length ∧
            (∀ p ∈ pos, p < k) ∧
            ValidChoices ((cycles g k).map selectedOptions) (List.zipWith selected (cycles g k) pos) ∧
            cost (List.zipWith selected (cycles g k) pos) = 0)) :=
  ⟨zeroCostProg, CZeroCost, fun g k hk => by
    obtain ⟨out, T, hT, ho, hc⟩ := HTB.computesIn_post (O := ZeroCostAnswer g k)
      (zeroCostProg_spec g k hk le_rfl)
    refine ⟨out, T, hc.mono ((zeroCostSpace_le g (by omega)).trans
      (Nat.mul_le_mul_right _ (by simp [CS20, CZeroCost]))), hT, ho⟩⟩

end STACS2027.Runtimes.ZeroCost
