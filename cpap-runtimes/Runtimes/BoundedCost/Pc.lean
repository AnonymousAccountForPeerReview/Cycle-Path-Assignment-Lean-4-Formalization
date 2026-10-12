module

public import Runtimes.BoundedCost.State
import Mathlib.Tactic

/-!
# Theorem 4 on the RAM: the copies of the path constraints

Corollary 5's generation of the path constraints (`pcRow`, `pcBody`, `pcEmit` of
`ZeroCostProg.lean`) is proved here in the layout of Theorem 4 (`HS`, after the sorting front end)
and after an arbitrary prefix `F₀` of clauses already in memory (`pcBody_spec5`,
`pcRowA_spec5`, `pcRow_spec5`, `pcCopy_spec`), and phase 4 of the formula repeats them `N`
times (`stepPcs_spec`, `N = gPS1`): afterwards the codes of `pcs g k N` are at `bC5 g k`,
within `N (t (k (65k + 7) + 8) + 8) + 7` steps and the addresses below any
`S ≥ bC5 g k + |codes (pcs g k N)|` (each push extends a prefix of the final code array:
`length_codes_pcB_le`, `length_codes_pcA_le`, `length_codes_pcI_le`, `length_codes_pcs`).
-/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost Complexity.SAT

variable {S : ℕ}

/-- Emitting a path constraint `¬b_{base+a} ∨ ¬b_{base+b}`. -/
theorem pcEmit_run5 {g : Graph} {k : ℕ} {s : ℕ → ℕ} {F : CNF} {c : Config} (h : HS g k s F c)
    {base a b : ℕ} (hB : c.reg sBase = base) (hA : c.reg sA = a) (hb : c.reg sB = b) :
    HS g k s (F ++ [[⟨base + a, false⟩, ⟨base + b, false⟩]]) (run pcEmit c) ∧
      ∀ r, r ∉ [sU, sV, rT, rFREE, gNC] → (run pcEmit c).reg r = c.reg r := by
  have hfr : ∀ r, r ∉ [sU, sV, rT, rFREE, gNC] → (run pcEmit c).reg r = c.reg r := fun r hr =>
    run_reg_of_not_mem (by decide) (fun h => hr (by
      have : ∀ x ∈ wregs pcEmit, x ∈ [sU, sV, rT, rFREE, gNC] := by decide
      exact this r h)) c
  refine ⟨h.emit _ _ (HG.regIndep g k) (fun r hr => hfr r fun h' => hr (by
      have : ∀ x ∈ [sU, sV, rT, rFREE, gNC], x ∈ WG := by decide
      exact this r h')) ?_ ?_ ?_ ?_, hfr⟩
  · simp +decide [pcEmit, run_push, run_inc]
  · simp +decide [pcEmit, run_push, run_inc]
  · simp +decide only [pcEmit, run_seq', run_add, run_inc (show sU ≠ rT by decide),
      run_inc (show sV ≠ rT by decide), run_inc (show gNC ≠ rT by decide), run_push, setReg_reg,
      setReg_mem, setMem_reg, setMem_mem_upd, ↓reduceIte, hB, hA, hb, code_neg]
  · simp [pcEmit, run_push, run_inc]

/-- The state at pair `(a, b)` of cycle `i`, after the prefix `F₀`. -/
def PcInv5 (g : Graph) (k : ℕ) (F₀ : CNF) (i a b : ℕ) (c : Config) : Prop :=
  HS g k (fun _ => 0) (F₀ ++ (pcI k i ++ pcA k i a ++ pcB k i a b)) c ∧ c.reg sBase = i * k ∧
    c.reg sI = i ∧ c.reg sA = a

theorem PcInv5.indep (g : Graph) (k : ℕ) (F₀ : CNF) (i a b : ℕ) :
    Indep [rT, sX, sY] (PcInv5 g k F₀ i a b) := by
  indep [PcInv5, HS, hG_iff, gA_iff]

theorem pcBody_spec5 (g : Graph) (k : ℕ) (F₀ : CNF) (i a b : ℕ)
    (hSp : bC5 g k + (TwoSat.codes (F₀ ++ (pcI k i ++ pcA k i a ++ pcB k i a (b + 1)))).length ≤ S) :
    HTB S pcBody (fun c => PcInv5 g k F₀ i a b c ∧ c.reg sB = b ∧ c.reg gK = k)
      (fun c => PcInv5 g k F₀ i a (b + 1) c ∧ c.reg sB = b ∧ c.reg gK = k) 61 := by
  -- the two outcomes
  have hemit : HTB S pcEmit (fun c => (PcInv5 g k F₀ i a b c ∧ c.reg sB = b ∧ c.reg gK = k) ∧
        (a + 1 < b ∧ ¬ (a = 0 ∧ b + 1 = k)))
      (fun c => PcInv5 g k F₀ i a (b + 1) c ∧ c.reg sB = b ∧ c.reg gK = k) 16 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨⟨⟨hS, hB, hI, hA⟩, hb, hK⟩, hc⟩ => ?_
    obtain ⟨hS', hfr⟩ := pcEmit_run5 hS hB hA hb
    have hl : F₀ ++ (pcI k i ++ pcA k i a ++ pcB k i a (b + 1)) =
        F₀ ++ (pcI k i ++ pcA k i a ++ pcB k i a b) ++ [[⟨i * k + a, false⟩, ⟨i * k + b, false⟩]] := by
      rw [pcB_succ, pcCl_pos hc]; simp only [List.append_assoc]
    rw [hl] at hSp
    exact ⟨pcEmit_addrOK (hS.room hSp), ⟨by rw [hl]; exact hS', by rw [hfr sBase (by decide), hB],
      by rw [hfr sI (by decide), hI], by rw [hfr sA (by decide), hA]⟩, by rw [hfr sB (by decide), hb],
      by rw [hfr gK (by decide), hK]⟩
  have hskip : HTB S .skip (fun c => (PcInv5 g k F₀ i a b c ∧ c.reg sB = b ∧ c.reg gK = k) ∧
        ¬ (a + 1 < b ∧ ¬ (a = 0 ∧ b + 1 = k)))
      (fun c => PcInv5 g k F₀ i a (b + 1) c ∧ c.reg sB = b ∧ c.reg gK = k) 1 := by
    refine HTB.run_le (by decide) le_rfl fun c ⟨h, hc⟩ => ⟨trivial, ?_⟩
    rw [run_skip, PcInv5, pcB_succ, pcCl_neg hc, List.append_nil]
    exact h
  have hP1 : Indep [rT, sX, sY] (fun c => PcInv5 g k F₀ i a b c ∧ c.reg sB = b ∧ c.reg gK = k) :=
    (PcInv5.indep g k F₀ i a b).and (by indep)
  have h1 := HTB.addc (S := S) (d := sX) (a := sA) (k := 1) (x := a) (show sA ≠ rT by decide)
    (hP1.mono (by decide)) (fun c h => h.1.2.2.2)
  -- the branch `a + 1 < b`
  have hS : HTB S (.seq (addc sY sB 1) (.ifz sA (ifEq sY gK .skip pcEmit) pcEmit))
      (fun c => ((PcInv5 g k F₀ i a b c ∧ c.reg sB = b ∧ c.reg gK = k) ∧ c.reg sX = a + 1) ∧
        c.reg sX < c.reg sB)
      (fun c => PcInv5 g k F₀ i a (b + 1) c ∧ c.reg sB = b ∧ c.reg gK = k) 23 := by
    have hY := HTB.addc (S := S) (d := sY) (a := sB) (k := 1) (x := b) (show sB ≠ rT by decide)
      (P := fun c => ((PcInv5 g k F₀ i a b c ∧ c.reg sB = b ∧ c.reg gK = k) ∧ c.reg sX = a + 1) ∧
        c.reg sX < c.reg sB) (by indep [PcInv5, HS, hG_iff, gA_iff]) (fun c h => h.1.1.2.1)
    refine (hY.seq (HTB.ifz (b := 20) ?_ ?_)).weaken (by omega)
    · refine HTB.ifEq (B := 16) (show sY ≠ rT by decide) (show gK ≠ rT by decide)
        (by indep [PcInv5, HS, hG_iff, gA_iff]) ?_ ?_
      · refine (hskip.pre fun c ⟨⟨⟨⟨⟨hP, _⟩, _⟩, hY⟩, h0⟩, heq⟩ => ⟨hP, ?_⟩).weaken (by omega)
        have ha : a = 0 := by rw [← hP.1.2.2.2, h0]
        have hk : b + 1 = k := by rw [← hY, heq, hP.2.2]
        exact fun ⟨_, hn⟩ => hn ⟨ha, hk⟩
      · refine hemit.pre fun c ⟨⟨⟨⟨⟨hP, hX⟩, hlt⟩, hY⟩, _⟩, hne⟩ => ⟨hP, ?_, ?_⟩
        · rw [hX, hP.2.1] at hlt; exact hlt
        · rintro ⟨_, hk⟩; apply hne; rw [hY, hP.2.2, hk]
    · refine (hemit.pre fun c ⟨⟨⟨⟨hP, hX⟩, hlt⟩, _⟩, h0⟩ => ⟨hP, ?_, ?_⟩).weaken (by omega)
      · rw [hX, hP.2.1] at hlt; exact hlt
      · rintro ⟨ha, _⟩; apply h0; rw [hP.1.2.2.2, ha]
  have hU : HTB S .skip (fun c => ((PcInv5 g k F₀ i a b c ∧ c.reg sB = b ∧ c.reg gK = k) ∧
        c.reg sX = a + 1) ∧ c.reg sB ≤ c.reg sX)
      (fun c => PcInv5 g k F₀ i a (b + 1) c ∧ c.reg sB = b ∧ c.reg gK = k) 23 :=
    (hskip.pre fun c ⟨⟨hP, hX⟩, hle⟩ => ⟨hP, fun ⟨hlt, _⟩ => by rw [hX, hP.2.1] at hle; omega⟩).weaken
      (by omega)
  exact (h1.seq (HTB.ifLt (show sX ≠ rT by decide) (show sB ≠ rT by decide)
    (by indep [PcInv5, HS, hG_iff, gA_iff]) hS hU)).weaken (by omega)

/-- The state before the pairs of cycle `i` with first position `a`, after the prefix `F₀`. -/
def MInv5 (g : Graph) (k : ℕ) (F₀ : CNF) (i a : ℕ) (c : Config) : Prop :=
  HS g k (fun _ => 0) (F₀ ++ (pcI k i ++ pcA k i a)) c ∧ c.reg sBase = i * k ∧ c.reg sI = i

/-- The state before cycle `i`, after the prefix `F₀`. -/
def OInv5 (g : Graph) (k : ℕ) (F₀ : CNF) (i : ℕ) (c : Config) : Prop :=
  HS g k (fun _ => 0) (F₀ ++ pcI k i) c ∧ c.reg sBase = i * k

theorem pcRowA_spec5 (g : Graph) (k : ℕ) (F₀ : CNF) (i a : ℕ)
    (hSp : bC5 g k + (TwoSat.codes (F₀ ++ (pcI k i ++ pcA k i (a + 1)))).length ≤ S) :
    HTB S pcRowA (fun c => MInv5 g k F₀ i a c ∧ c.reg sA = a ∧ c.reg gK = k)
      (fun c => MInv5 g k F₀ i (a + 1) c ∧ c.reg sA = a ∧ c.reg gK = k) (k * 65 + 3) := by
  have hl := HTB.forUpC (i := sB) (n := gK) (N := k) (body := pcBody) (PcInv5 g k F₀ i a) 61
    (by decide) (by decide) (by decide) (fun j => by indep [PcInv5, HS, hG_iff, gA_iff])
    (fun b hb => pcBody_spec5 (S := S) g k F₀ i a b (by
      have := length_codes_pcB_le k i a (show b + 1 ≤ k by omega)
      simp only [codes_append, List.length_append, pcA_succ] at hSp ⊢; omega))
  refine hl.mono (fun c ⟨⟨hS, hB, hI⟩, hA, hK⟩ => ⟨⟨by simpa [pcB] using hS, hB, hI, hA⟩, hK⟩)
    (fun c ⟨⟨hS, hB, hI, hA⟩, _, hK⟩ => ⟨⟨?_, hB, hI⟩, hA, hK⟩) (by omega)
  simp only [pcA_succ, List.append_assoc] at hS ⊢; exact hS

theorem pcRow_spec5 (g : Graph) (k : ℕ) (F₀ : CNF) (i : ℕ)
    (hSp : bC5 g k + (TwoSat.codes (F₀ ++ pcI k (i + 1))).length ≤ S) :
    HTB S pcRow (fun c => OInv5 g k F₀ i c ∧ c.reg sI = i ∧ c.reg gT = (cycles g k).length)
      (fun c => OInv5 g k F₀ (i + 1) c ∧ c.reg sI = i ∧ c.reg gT = (cycles g k).length)
      (k * (k * 65 + 7) + 4) := by
  have hl := HTB.forUpC (i := sA) (n := gK) (N := k) (body := pcRowA) (MInv5 g k F₀ i) (k * 65 + 3)
    (by decide) (by decide) (by decide) (fun j => by indep [MInv5, HS, hG_iff, gA_iff])
    (fun a ha => pcRowA_spec5 (S := S) g k F₀ i a (by
      have := length_codes_pcA_le k i (show a + 1 ≤ k by omega)
      simp only [codes_append, List.length_append, pcI_succ] at hSp ⊢; omega))
  have h2 : HTB S (.add sBase sBase gK) (fun c => MInv5 g k F₀ i k c ∧ c.reg sA = k ∧ c.reg gK = k)
      (fun c => OInv5 g k F₀ (i + 1) c ∧ c.reg sI = i ∧ c.reg gT = (cycles g k).length) 1 :=
      HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨hS, hB, hI⟩, _, hK⟩ => ?_
    have hS' : HS g k (fun _ => 0) (F₀ ++ pcI k (i + 1)) c := by rw [pcI_succ]; exact hS
    refine ⟨⟨(show Indep [sBase] (HS g k (fun _ => 0) (F₀ ++ pcI k (i + 1))) by
      indep [HS, hG_iff, gA_iff]).setReg (by decide) _ hS', ?_⟩, ?_, ?_⟩
    · simp +decide [hB, hK]; ring
    · simp +decide [hI]
    · simp +decide [hS.1.ga.rt]
  refine (hl.seq h2).mono (fun c ⟨⟨hS, hB⟩, hI, _⟩ => ⟨⟨by simpa [pcA] using hS, hB, hI⟩, hS.1.ga.rk⟩)
    (fun _ h => h) (by ring_nf; omega)

/-- **One copy of the path constraints** after the prefix `F₀`. -/
theorem pcCopy_spec (g : Graph) (k : ℕ) (F₀ : CNF)
    (hSp : bC5 g k + (TwoSat.codes (F₀ ++ pathConstraints g k)).length ≤ S) :
    HTB S pcCopy (fun c => HS g k (fun _ => 0) F₀ c)
      (fun c => HS g k (fun _ => 0) (F₀ ++ pathConstraints g k) c)
      ((cycles g k).length * (k * (k * 65 + 7) + 8) + 4) := by
  have h0 : HTB S (.const sBase 0) (fun c => HS g k (fun _ => 0) F₀ c)
      (fun c => OInv5 g k F₀ 0 c ∧ c.reg gT = (cycles g k).length) 1 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c hS => ?_
    refine ⟨⟨?_, by simp⟩, by simp +decide [hS.1.ga.rt]⟩
    have : F₀ ++ pcI k 0 = F₀ := by simp [pcI]
    rw [this]
    exact (show Indep [sBase] (HS g k (fun _ => 0) F₀) by
      indep [HS, hG_iff, gA_iff]).setReg (by decide) _ hS
  have hl := HTB.forUpC (i := sI) (n := gT) (N := (cycles g k).length) (body := pcRow)
    (OInv5 g k F₀) (k * (k * 65 + 7) + 4) (by decide) (by decide) (by decide)
    (fun j => by indep [OInv5, HS, hG_iff, gA_iff]) (fun i hi => pcRow_spec5 (S := S) g k F₀ i (by
      have := length_codes_pcI_le k (show i + 1 ≤ (cycles g k).length by omega)
      rw [pcI_full] at this
      simp only [codes_append, List.length_append] at hSp ⊢; omega))
  refine (h0.seq hl).mono (fun _ h => h) (fun c ⟨⟨hS, _⟩, _, _⟩ => ?_) (le_of_eq (by ring))
  rw [← pcI_full]; exact hS

theorem length_codes_pcs (g : Graph) (k r : ℕ) :
    (TwoSat.codes (pcs g k r)).length = r * (TwoSat.codes (pathConstraints g k)).length := by
  induction r with
  | zero => simp [pcs, TwoSat.codes]
  | succ r ih => rw [pcs_succ, codes_append, List.length_append, ih]; ring

/-- The state after the mark table: the front end's identifiers, a zero table `SEEN` at
`bS5 g k`, free memory from `bC5 g k` on. -/
@[mk_iff] structure SeenPost (g : Graph) (k : ℕ) (c : Config) : Prop where
  ga : GA g k c
  reid : c.reg gEID = bE5 g k
  rseen : c.reg gSEEN = bS5 g k
  rfree : c.reg rFREE = bC5 g k
  mverts : Arr c.mem (bV g) (verts g k)
  meid : Tab c.mem (bE5 g k) (k * (cycles g k).length) (eidOf g k)
  mzero : ZeroFrom c.mem (bS5 g k)
  rout : c.out = []

/-- **Phase 4**: `N` copies of the path constraints. -/
theorem stepPcs_spec (g : Graph) (k N : ℕ)
    (hSp : bC5 g k + (TwoSat.codes (pcs g k N)).length ≤ S) :
    HTB S stepPcs (fun c => SeenPost g k c ∧ c.reg gPS1 = N)
      (fun c => HS g k (fun _ => 0) (pcs g k N) c)
      (N * ((cycles g k).length * (k * (k * 65 + 7) + 8) + 8) + 7) := by
  have hl5 := lay5 g k
  have h0 : HTB S (.seq (mov gCL rFREE) (.const gNC 0)) (fun c => SeenPost g k c ∧ c.reg gPS1 = N)
      (fun c => HS g k (fun _ => 0) (pcs g k 0) c ∧ c.reg gPS1 = N) 3 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨hP, hps⟩ => ?_
    have hga : GA g k (run (.seq (mov gCL rFREE) (.const gNC 0)) c) :=
      (show RegIndep [rT, gCL, gNC] (GA g k) by indep [gA_iff]).run_of_sub
        (by decide) (by decide) hP.ga
    refine ⟨⟨⟨hga, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals simp +decide only [run_seq', run_mov (show rFREE ≠ rT by decide), run_const, setReg_reg,
      setReg_mem, setReg_out, ↓reduceIte, hP.reid, hP.rseen, hP.rfree, hP.rout, hps]
    · simp [pcs, TwoSat.codes]
    · simp [pcs]
    · refine ⟨hP.mverts, hP.meid, fun e he => hP.mzero _ (by omega), by simp [pcs, TwoSat.codes],
        ?_⟩
      simpa [pcs, TwoSat.codes] using hP.mzero.mono (show bS5 g k ≤ bC5 g k by omega)
  have hl := HTB.forUpC (S := S) (i := sR) (n := gPS1) (N := N) (body := pcCopy)
    (fun r c => HS g k (fun _ => 0) (pcs g k r) c)
    ((cycles g k).length * (k * (k * 65 + 7) + 8) + 4) (by decide) (by decide) (by decide)
    (fun j => by indep [HS, hG_iff, gA_iff]) (fun r hr => ?_)
  · exact HTB.assoc ((h0.seq hl).mono (fun _ h => h) (fun c h => h.1) (by ring_nf; omega))
  · have hcp := pcCopy_spec (S := S) g k (pcs g k r) (by
      rw [← pcs_succ]
      have h1 := length_codes_pcs g k (r + 1)
      have h2 := length_codes_pcs g k N
      have h3 : (r + 1) * (TwoSat.codes (pathConstraints g k)).length ≤
          N * (TwoSat.codes (pathConstraints g k)).length := Nat.mul_le_mul_right _ (by omega)
      omega)
    refine (hcp.frameReg (F := fun c => c.reg sR = r ∧ c.reg gPS1 = N)
      (by indep)).mono (fun _ h => h) (fun c ⟨h, h'⟩ => ⟨?_, h'⟩) le_rfl
    rw [pcs_succ]; exact h

end STACS2027.Runtimes.BoundedCost
