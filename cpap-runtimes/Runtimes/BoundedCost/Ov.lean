module

public import Runtimes.BoundedCost.Pc
import Mathlib.Tactic

/-!
# Theorem 4 on the RAM: the overlap clauses

Phase 5 of the formula (`stepOv_spec`): after the clauses `F₀` (the copies of the path
constraints), it pushes the codes of the candidate-overlap clauses of Section 4, in Section 4's
order: for every cycle `C_i` and every later cycle `C_{i'}` (`i < i'`), the clauses
`b_{C_i,e} ∨ b_{C_{i'},e}` for the edges `e` of `C_i` (in the order of `C_i`) lying on `C_{i'}`
(`ovI g k t`, which is `(candidateOverlaps g k).map (overlapClause g k)` by `ovI_full`).

A pair costs `O(k)`: the table `SEEN` (one cell per distinct edge, zero, at `bS5 g k`) serves as
the mark table; the edges of `C_{i'}` are marked (`markBody_spec`, the table `markF g k i' j`),
the edges of `C_i` are scanned (`scanBody_spec`: the mark of an edge is its variable in `C_{i'}`
plus one, or `0` if it is not on `C_{i'}`, `ovCl_eq`), and the marks are cleared
(`clearBody_spec`, `clearF_full`). In total `t (t (44k + 16) + 9) + 4` steps, i.e.
`O(kt² + t)`, and the addresses below any `S ≥ bC5 g k + |codes (F₀ ++ ovI g k t)|`.
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost Complexity.SAT

variable {S : ℕ}

theorem length_codes_ovS_le (g : Graph) (k i i' : ℕ) {j j' : ℕ} (h : j ≤ j') :
    (TwoSat.codes (ovS g k i i' j)).length ≤ (TwoSat.codes (ovS g k i i' j')).length :=
  length_codes_flatMap_le _ h

theorem length_codes_ovJ_le (g : Graph) (k i : ℕ) {j j' : ℕ} (h : j ≤ j') :
    (TwoSat.codes (ovJ g k i j)).length ≤ (TwoSat.codes (ovJ g k i j')).length :=
  length_codes_flatMap_le _ h

theorem length_codes_ovI_le (g : Graph) (k : ℕ) {i i' : ℕ} (h : i ≤ i') :
    (TwoSat.codes (ovI g k i)).length ≤ (TwoSat.codes (ovI g k i')).length :=
  length_codes_flatMap_le _ h

/-! ### Marking -/

/-- The state after marking the first `j` edges of `C_{i'}`. -/
def MarkI (g : Graph) (k : ℕ) (F : CNF) (i i' j : ℕ) (c : Config) : Prop :=
  HS g k (markF g k i' j) F c ∧ c.reg sBase = i * k ∧ c.reg sW = i' * k

theorem markBody_spec (g : Graph) (k : ℕ) (F : CNF) (hSp : bC5 g k ≤ S) {i i' : ℕ}
    (hi' : i' < (cycles g k).length) (j : ℕ) (hj : j < k) :
    HTB S markBody (fun c => MarkI g k F i i' j c ∧ c.reg sJ = j ∧ c.reg gK = k)
      (fun c => MarkI g k F i i' (j + 1) c ∧ c.reg sJ = j ∧ c.reg gK = k) 7 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hS, hB, hW⟩, hJ, hK⟩ => ?_
  have hq : i' * k + j < k * (cycles g k).length := occ_lt hi' hj
  have he := eidOf_lt hq
  have hl := lay5 g k
  have h1 : c.mem (bE5 g k + (i' * k + j)) = eidOf g k (i' * k + j) := hS.2.2.2.1.meid _ hq
  have hfr := frame_of_wregs (s := markBody) (by decide) [sP, sE, sZ, rT] (by decide) c
  have hmem : (run markBody c).mem = upd c.mem (bS5 g k + eidOf g k (i' * k + j)) (i' * k + j + 1) := by
    simp +decide only [markBody, run_seq', run_add, run_ld, run_addc (show sP ≠ rT by decide),
      run_st (show sZ ≠ rT by decide), setReg_reg, setReg_mem, setMem_mem_upd, ↓reduceIte, hW, hJ,
      hS.1.reid, hS.1.rseen, h1]
  refine ⟨by addr_ok [markBody, hW, hJ, hS.1.reid, hS.1.rseen, h1], ⟨?_,
    by rw [hfr sBase (by decide), hB], by rw [hfr sW (by decide), hW]⟩,
    by rw [hfr sJ (by decide), hJ], by rw [hfr gK (by decide), hK]⟩
  rw [markF_succ]
  exact HS.seen hS he _ (fun r hr => hfr r (not_mem_of_sub hr (by decide))) (hfr rFREE (by decide))
    (hfr gNC (by decide)) hmem (run_out_of_writes (by decide) (by decide) c)

/-! ### Scanning -/

/-- The state after scanning the first `j` edges of `C_i` against the marks of `C_{i'}`. -/
def ScanI (g : Graph) (k : ℕ) (F : CNF) (i i' j : ℕ) (c : Config) : Prop :=
  HS g k (markF g k i' k) (F ++ ovS g k i i' j) c ∧ c.reg sBase = i * k ∧ c.reg sW = i' * k

/-- Emitting an overlap clause: `b_q ∨ b_{v-1}` with `q = sP`, `v = sZ`. -/
theorem emitOv_run {g : Graph} {k : ℕ} {s : ℕ → ℕ} {F : CNF} {c : Config} (h : HS g k s F c)
    {q v : ℕ} (hq : c.reg sP = q) (hv : c.reg sZ = v) :
    HS g k s (F ++ [[⟨q, true⟩, ⟨v - 1, true⟩]]) (run emitOv c) ∧
      ∀ r, r ∉ [sU, sV, rT, rFREE, gNC] → (run emitOv c).reg r = c.reg r := by
  have hfr := frame_of_wregs (s := emitOv) (by decide) [sU, sV, rT, rFREE, gNC] (by decide) c
  refine ⟨h.emit _ _ (HG.regIndepO g k) (fun r hr => hfr r (not_mem_of_sub hr (by decide)))
    ?_ ?_ ?_ ?_, hfr⟩
  · simp +decide [emitOv, run_push, run_inc, run_subc]
  · simp +decide [emitOv, run_push, run_inc, run_subc]
  · simp +decide only [emitOv, run_seq', run_add, run_subc (show sZ ≠ rT by decide),
      run_inc (show gNC ≠ rT by decide), run_push, setReg_reg, setReg_mem, setMem_reg,
      setMem_mem_upd, ↓reduceIte, hq, hv, code_pos]
  · simp [emitOv, run_push, run_inc, run_subc]

theorem scanBody_spec (g : Graph) (k : ℕ) (F : CNF) {i i' : ℕ} (hi : i < (cycles g k).length)
    (hi' : i' < (cycles g k).length) (j : ℕ) (hj : j < k)
    (hSp : bC5 g k + (TwoSat.codes (F ++ ovS g k i i' (j + 1))).length ≤ S) :
    HTB S scanBody (fun c => ScanI g k F i i' j c ∧ c.reg sJ = j ∧ c.reg gK = k)
      (fun c => ScanI g k F i i' (j + 1) c ∧ c.reg sJ = j ∧ c.reg gK = k) 19 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hS, hB, hW⟩, hJ, hK⟩ => ?_
  have hq : i * k + j < k * (cycles g k).length := occ_lt hi hj
  have he := eidOf_lt hq
  have hl := lay5 g k
  have h1 : c.mem (bE5 g k + (i * k + j)) = eidOf g k (i * k + j) := hS.2.2.2.1.meid _ hq
  have h2 : c.mem (bS5 g k + eidOf g k (i * k + j)) = markF g k i' k (eidOf g k (i * k + j)) :=
    hS.2.2.2.1.mseen _ he
  have hcl := ovCl_eq hi hi' hj
  have hfree := hS.2.1
  generalize markF g k i' k (eidOf g k (i * k + j)) = v at h2 hcl
  -- the reads
  set c1 := run (.seq (.add sP sBase sJ) (.seq (ld sE gEID sP) (ld sZ gSEEN sE))) c
  have hag : Agree [sP, sE, sZ] c c1 := agree_run (by decide) rfl rfl (by decide) c
  have hP : c1.reg sP = i * k + j := by simp +decide [c1, hB, hJ]
  have hZ : c1.reg sZ = v := by
    simp +decide only [c1, run_seq', run_add, run_ld, setReg_reg, setReg_mem, ↓reduceIte, hB, hJ,
      hS.1.reid, hS.1.rseen, h1, h2]
  have hS1 : ScanI g k F i i' j c1 :=
    (show Indep [sP, sE, sZ] (ScanI g k F i i' j) by indep [ScanI, HS, hG_iff, gA_iff]) c _ hag
      ⟨hS, hB, hW⟩
  have hJ1 : c1.reg sJ = j := by rw [hag.reg sJ (by decide), hJ]
  have hK1 : c1.reg gK = k := by rw [hag.reg gK (by decide), hK]
  have e : run scanBody c = run (.ifz sZ .skip emitOv) c1 := rfl
  have he' : c.mem (bE5 g k + (i * k + j)) < (edgesOnCycles g k).length := by rw [h1]; exact he
  have hSp' := hSp
  rw [length_codes_append] at hSp'
  rw [e, run_ifz', hZ]
  by_cases hv : v = 0
  · simp only [hv, ↓reduceIte, run_skip] at hcl ⊢
    refine ⟨by
      addr_simp [scanBody, emitOv, push, hB, hJ, hS.1.reid, hS.1.rseen, h1, h2, hv]
      exact ⟨by omega, by omega, False.elim⟩, ⟨?_, hS1.2⟩, hJ1, hK1⟩
    rw [ovS_succ, hcl, List.append_nil]; exact hS1.1
  · simp only [hv, ↓reduceIte] at hcl ⊢
    rw [ovS_succ, hcl, ← List.append_assoc] at hSp
    have hroom := hS1.1.room hSp
    have hfr1 : c1.reg rFREE = c.reg rFREE := hag.reg rFREE (by decide)
    obtain ⟨hE, hfr⟩ := emitOv_run hS1.1 hP hZ
    rw [hfr1] at hroom
    refine ⟨by addr_ok [scanBody, emitOv, push, hB, hJ, hS.1.reid, hS.1.rseen, h1, h2, hv],
      ⟨?_, by rw [hfr sBase (by decide), hS1.2.1],
      by rw [hfr sW (by decide), hS1.2.2]⟩, by rw [hfr sJ (by decide), hJ1],
      by rw [hfr gK (by decide), hK1]⟩
    rw [ovS_succ, hcl, ← List.append_assoc]; exact hE

/-! ### Clearing -/

/-- The state after clearing the marks of the first `j` edges of `C_{i'}`. -/
def ClearI (g : Graph) (k : ℕ) (F : CNF) (i i' j : ℕ) (c : Config) : Prop :=
  HS g k (clearF g k i' j) (F ++ ovPairCl g k i i') c ∧ c.reg sBase = i * k ∧ c.reg sW = i' * k

theorem clearBody_spec (g : Graph) (k : ℕ) (F : CNF) (hSp : bC5 g k ≤ S) {i i' : ℕ}
    (hi' : i' < (cycles g k).length) (j : ℕ) (hj : j < k) :
    HTB S clearBody (fun c => ClearI g k F i i' j c ∧ c.reg sJ = j ∧ c.reg gK = k)
      (fun c => ClearI g k F i i' (j + 1) c ∧ c.reg sJ = j ∧ c.reg gK = k) 6 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hS, hB, hW⟩, hJ, hK⟩ => ?_
  have hq : i' * k + j < k * (cycles g k).length := occ_lt hi' hj
  have he := eidOf_lt hq
  have hl := lay5 g k
  have h1 : c.mem (bE5 g k + (i' * k + j)) = eidOf g k (i' * k + j) := hS.2.2.2.1.meid _ hq
  have hfr := frame_of_wregs (s := clearBody) (by decide) [sP, sE, sZ, rT] (by decide) c
  have hmem : (run clearBody c).mem = upd c.mem (bS5 g k + eidOf g k (i' * k + j)) 0 := by
    simp +decide only [clearBody, run_seq', run_add, run_ld, run_const,
      run_st (show sZ ≠ rT by decide), setReg_reg, setReg_mem, setMem_mem_upd, ↓reduceIte, hW, hJ,
      hS.1.reid, hS.1.rseen, h1]
  refine ⟨by addr_ok [clearBody, hW, hJ, hS.1.reid, hS.1.rseen, h1], ⟨?_,
    by rw [hfr sBase (by decide), hB], by rw [hfr sW (by decide), hW]⟩,
    by rw [hfr sJ (by decide), hJ], by rw [hfr gK (by decide), hK]⟩
  rw [clearF_succ]
  exact HS.seen hS he _ (fun r hr => hfr r (not_mem_of_sub hr (by decide))) (hfr rFREE (by decide))
    (hfr gNC (by decide)) hmem (run_out_of_writes (by decide) (by decide) c)

/-! ### A pair, a row, the phase -/

/-- **The overlap clauses of a pair** `(C_i, C_{i'})`, in `O(k)` steps; the mark table is zero
before and after. -/
theorem ovPair_spec (g : Graph) (k : ℕ) (F : CNF) {i i' : ℕ} (hi : i < (cycles g k).length)
    (hi' : i' < (cycles g k).length)
    (hSp : bC5 g k + (TwoSat.codes (F ++ ovPairCl g k i i')).length ≤ S) :
    HTB S ovPair (fun c => (HS g k (fun _ => 0) F c ∧ c.reg sBase = i * k ∧ c.reg sW = i' * k) ∧
        c.reg gK = k)
      (fun c => (HS g k (fun _ => 0) (F ++ ovPairCl g k i i') c ∧ c.reg sBase = i * k ∧
        c.reg sW = i' * k) ∧ c.reg gK = k) (k * 44 + 9) := by
  have hC : bC5 g k ≤ S := by have := length_codes_append F (ovPairCl g k i i'); omega
  have hm := HTB.forUpC (i := sJ) (n := gK) (N := k) (body := markBody) (MarkI g k F i i') 7
    (by decide) (by decide) (by decide) (fun j => by indep [MarkI, HS, hG_iff, gA_iff])
    (fun j hj => markBody_spec g k F hC hi' j hj)
  have hs := HTB.forUpC (i := sJ) (n := gK) (N := k) (body := scanBody) (ScanI g k F i i') 19
    (by decide) (by decide) (by decide) (fun j => by indep [ScanI, HS, hG_iff, gA_iff])
    (fun j hj => scanBody_spec (S := S) g k F hi hi' j hj (by
      have h1 := length_codes_ovS_le g k i i' (show j + 1 ≤ k by omega)
      have h2 := length_codes_append F (ovS g k i i' (j + 1))
      have h3 := length_codes_append F (ovPairCl g k i i')
      have h4 : (TwoSat.codes (ovPairCl g k i i')).length = (TwoSat.codes (ovS g k i i' k)).length :=
        rfl
      omega))
  have hc := HTB.forUpC (i := sJ) (n := gK) (N := k) (body := clearBody) (ClearI g k F i i') 6
    (by decide) (by decide) (by decide) (fun j => by indep [ClearI, HS, hG_iff, gA_iff])
    (fun j hj => clearBody_spec g k F hC hi' j hj)
  refine (hm.seq ((hs.pre fun c ⟨⟨hS, hB, hW⟩, _, hK⟩ => ⟨⟨by simpa [ovS] using hS, hB, hW⟩, hK⟩).seq
    (hc.pre fun c ⟨⟨hS, hB, hW⟩, _, hK⟩ => ⟨⟨hS, hB, hW⟩, hK⟩))).mono
    (fun c ⟨⟨hS, hB, hW⟩, hK⟩ => ⟨⟨hS, hB, hW⟩, hK⟩)
    (fun c ⟨⟨hS, hB, hW⟩, _, hK⟩ => ⟨⟨?_, hB, hW⟩, hK⟩) (by omega)
  rw [← clearF_full hi']; exact hS

/-- The state before the pair `(i, i')` of row `i`, after the prefix `F₀`. -/
def PairI (g : Graph) (k : ℕ) (F₀ : CNF) (i i' : ℕ) (c : Config) : Prop :=
  HS g k (fun _ => 0) (F₀ ++ ovI g k i ++ ovJ g k i i') c ∧ c.reg sBase = i * k ∧ c.reg sI = i ∧
    c.reg sW = i' * k

theorem ovPairT_spec (g : Graph) (k : ℕ) (F₀ : CNF) {i i' : ℕ} (hi : i < (cycles g k).length)
    (hi' : i' < (cycles g k).length)
    (hSp : bC5 g k + (TwoSat.codes (F₀ ++ ovI g k i ++ ovJ g k i (i' + 1))).length ≤ S) :
    HTB S ovPairT (fun c => PairI g k F₀ i i' c ∧ c.reg sA = i' ∧ c.reg gT = (cycles g k).length)
      (fun c => PairI g k F₀ i (i' + 1) c ∧ c.reg sA = i' ∧ c.reg gT = (cycles g k).length)
      (k * 44 + 12) := by
  set F := F₀ ++ ovI g k i ++ ovJ g k i i'
  -- the test
  have h1 : HTB S (ifLt sI sA ovPair .skip)
      (fun c => PairI g k F₀ i i' c ∧ c.reg sA = i' ∧ c.reg gT = (cycles g k).length)
      (fun c => (HS g k (fun _ => 0) (F₀ ++ ovI g k i ++ ovJ g k i (i' + 1)) c ∧
        c.reg sBase = i * k ∧ c.reg sI = i ∧ c.reg sW = i' * k) ∧ c.reg sA = i' ∧
        c.reg gT = (cycles g k).length) (k * 44 + 11) := by
    refine HTB.ifLt (B := k * 44 + 9) (show sI ≠ rT by decide) (show sA ≠ rT by decide)
      (by indep [PairI, HS, hG_iff, gA_iff]) ?_ ?_
    · refine HTB.pre_fact (p := i < i') (fun c ⟨⟨⟨_, _, hI, _⟩, hA, _⟩, hlt⟩ => by
        rw [hI, hA] at hlt; exact hlt) fun hlt => ?_
      have hF : F₀ ++ ovI g k i ++ ovJ g k i (i' + 1) = F ++ ovPairCl g k i i' := by
        simp only [F, ovJ_succ, hlt, ↓reduceIte, List.append_assoc]
      refine ((ovPair_spec g k F hi hi' (by rw [← hF]; exact hSp)).frameReg
        (F := fun c => c.reg sI = i ∧ c.reg sA = i' ∧ c.reg gT = (cycles g k).length)
        (by indep)).mono
        (fun c ⟨⟨⟨hS, hB, hI, hW⟩, hA, hT⟩, _⟩ => ⟨⟨⟨hS, hB, hW⟩, hS.1.ga.rk⟩, hI, hA, hT⟩)
        (fun c ⟨⟨⟨hS, hB, hW⟩, _⟩, hI, hA, hT⟩ => ⟨⟨?_, hB, hI, hW⟩, hA, hT⟩) le_rfl
      rw [hF]; exact hS
    · refine HTB.pre_fact (p := ¬ i < i') (fun c ⟨⟨⟨_, _, hI, _⟩, hA, _⟩, hle⟩ => by
        rw [hI, hA] at hle; omega) fun hlt => ?_
      refine HTB.run_le (by decide) (by simp only [size]; omega)
        fun c ⟨⟨⟨hS, hB, hI, hW⟩, hA, hT⟩, _⟩ => ⟨trivial, ?_⟩
      refine ⟨⟨?_, hB, hI, hW⟩, hA, hT⟩
      simp only [run_skip, ovJ_succ, hlt, ↓reduceIte, List.append_nil]
      exact hS
  have h2 : HTB S (.add sW sW gK)
      (fun c => (HS g k (fun _ => 0) (F₀ ++ ovI g k i ++ ovJ g k i (i' + 1)) c ∧
        c.reg sBase = i * k ∧ c.reg sI = i ∧ c.reg sW = i' * k) ∧ c.reg sA = i' ∧
        c.reg gT = (cycles g k).length)
      (fun c => PairI g k F₀ i (i' + 1) c ∧ c.reg sA = i' ∧ c.reg gT = (cycles g k).length) 1 :=
      HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨hS, hB, hI, hW⟩, hA, hT⟩ => ?_
    refine ⟨⟨(show Indep [sW] (HS g k (fun _ => 0) (F₀ ++ ovI g k i ++ ovJ g k i (i' + 1))) by
      indep [HS, hG_iff, gA_iff]).setReg (by decide) _ hS, ?_, ?_, ?_⟩, ?_, ?_⟩
    all_goals simp +decide [hB, hI, hW, hA, hT, hS.1.ga.rk]
    ring
  exact h1.seq h2

/-- The state before row `i`, after the prefix `F₀`. -/
def RowI (g : Graph) (k : ℕ) (F₀ : CNF) (i : ℕ) (c : Config) : Prop :=
  HS g k (fun _ => 0) (F₀ ++ ovI g k i) c ∧ c.reg sBase = i * k

theorem ovRow_spec (g : Graph) (k : ℕ) (F₀ : CNF) {i : ℕ} (hi : i < (cycles g k).length)
    (hSp : bC5 g k + (TwoSat.codes (F₀ ++ ovI g k (i + 1))).length ≤ S) :
    HTB S ovRow (fun c => RowI g k F₀ i c ∧ c.reg sI = i ∧ c.reg gT = (cycles g k).length)
      (fun c => RowI g k F₀ (i + 1) c ∧ c.reg sI = i ∧ c.reg gT = (cycles g k).length)
      ((cycles g k).length * (k * 44 + 16) + 5) := by
  have h0 : HTB S (.const sW 0)
      (fun c => RowI g k F₀ i c ∧ c.reg sI = i ∧ c.reg gT = (cycles g k).length)
      (fun c => PairI g k F₀ i 0 c ∧ c.reg gT = (cycles g k).length) 1 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨hS, hB⟩, hI, hT⟩ => ?_
    have hS' : HS g k (fun _ => 0) (F₀ ++ ovI g k i ++ ovJ g k i 0) c := by
      rw [ovJ_start, List.append_nil]; exact hS
    refine ⟨⟨(show Indep [sW] (HS g k (fun _ => 0) (F₀ ++ ovI g k i ++ ovJ g k i 0)) by
      indep [HS, hG_iff, gA_iff]).setReg (by decide) _ hS', ?_, ?_, ?_⟩, ?_⟩
    all_goals simp +decide [hB, hI, hT]
  have hl := HTB.forUpC (i := sA) (n := gT) (N := (cycles g k).length) (body := ovPairT)
    (PairI g k F₀ i) (k * 44 + 12) (by decide) (by decide) (by decide)
    (fun j => by indep [PairI, HS, hG_iff, gA_iff]) (fun i' hi' => ovPairT_spec (S := S) g k F₀ hi hi' (by
      have := length_codes_ovJ_le g k i (show i' + 1 ≤ (cycles g k).length by omega)
      simp only [ovI_succ, length_codes_append] at hSp ⊢; omega))
  have h2 : HTB S (.add sBase sBase gK)
      (fun c => PairI g k F₀ i (cycles g k).length c ∧ c.reg sA = (cycles g k).length ∧
        c.reg gT = (cycles g k).length)
      (fun c => RowI g k F₀ (i + 1) c ∧ c.reg sI = i ∧ c.reg gT = (cycles g k).length) 1 :=
      HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨hS, hB, hI, _⟩, _, hT⟩ => ?_
    have hS' : HS g k (fun _ => 0) (F₀ ++ ovI g k (i + 1)) c := by
      rw [ovI_succ, ← List.append_assoc]; exact hS
    refine ⟨⟨(show Indep [sBase] (HS g k (fun _ => 0) (F₀ ++ ovI g k (i + 1))) by
      indep [HS, hG_iff, gA_iff]).setReg (by decide) _ hS', ?_⟩, ?_, ?_⟩
    all_goals simp +decide [hB, hI, hT, hS.1.ga.rk]
    ring
  exact (h0.seq (hl.seq h2)).weaken (by ring_nf; omega)

/-- **Phase 5**: the overlap clauses of Section 4, in Section 4's order, after the clauses `F₀`;
`O(kt² + t)` steps. -/
theorem stepOv_spec (g : Graph) (k : ℕ) (F₀ : CNF)
    (hSp : bC5 g k + (TwoSat.codes (F₀ ++ ovI g k (cycles g k).length)).length ≤ S) :
    HTB S stepOv (fun c => HS g k (fun _ => 0) F₀ c)
      (fun c => HS g k (fun _ => 0) (F₀ ++ ovI g k (cycles g k).length) c)
      ((cycles g k).length * ((cycles g k).length * (k * 44 + 16) + 9) + 4) := by
  have h0 : HTB S (.const sBase 0) (fun c => HS g k (fun _ => 0) F₀ c)
      (fun c => RowI g k F₀ 0 c ∧ c.reg gT = (cycles g k).length) 1 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c hS => ?_
    have hS' : HS g k (fun _ => 0) (F₀ ++ ovI g k 0) c := by simpa [ovI] using hS
    refine ⟨⟨(show Indep [sBase] (HS g k (fun _ => 0) (F₀ ++ ovI g k 0)) by
      indep [HS, hG_iff, gA_iff]).setReg (by decide) _ hS', by simp⟩, by simp +decide [hS.1.ga.rt]⟩
  have hl := HTB.forUpC (i := sI) (n := gT) (N := (cycles g k).length) (body := ovRow)
    (RowI g k F₀) ((cycles g k).length * (k * 44 + 16) + 5) (by decide) (by decide) (by decide)
    (fun j => by indep [RowI, HS, hG_iff, gA_iff]) (fun i hi => ovRow_spec (S := S) g k F₀ hi (by
      have := length_codes_ovI_le g k (show i + 1 ≤ (cycles g k).length by omega)
      simp only [length_codes_append] at hSp ⊢; omega))
  exact (h0.seq hl).mono (fun _ h => h) (fun c ⟨⟨hS, _⟩, _⟩ => hS) (by ring_nf; omega)

end STACS2027.Runtimes.BoundedCost
