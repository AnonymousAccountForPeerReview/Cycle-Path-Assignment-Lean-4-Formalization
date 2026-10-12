module

public import Runtimes.Greedy.Prog
import Mathlib.Tactic

/-!
# Lemma 15 on the RAM: one cycle of Algorithm 1

The state at cycle `i` (`CS g k i L O`): the registers of Corollary 5's phase 1, `gEID`, `xLD`,
`xB = ik`, the identifier table `EID` (`eidOf g k`), a load table `L` on the `nE` identifiers and
the output `O`. From `L = ldF g k i` (the loads of the paths chosen for `C_0, …, C_{i−1}`) and
`O = pos 0, …, pos (i − 1)`, one cycle (`cycBody_spec`, `50k + 30` steps, within any
`S ≥ grSpace g k`) writes `pos g k i` and ends with `ldF g k (i + 1)`:
* `sumPhase_spec`: `xTot = tot g k i`;
* `choosePhase_spec`: `xBJ = pos g k i` (the scan `scanMin` over the load-sums `val g k i j`,
  computed as `tot − lp j − lp (prv j)`, `val_eq`);
* `updPhase_spec`: the table `uF g k i J p` after the positions `p' < p` (`uF_succ`), equal to
  `ldF g k (i + 1)` at the end (`uF_final`).
-/

@[expose] public section

namespace STACS2027.Runtimes.Greedy

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost

variable {S : ℕ} {g : Graph} {k : ℕ}

/-! ### The state -/

/-- The registers fixed during Algorithm 1. -/
@[mk_iff] structure GR (g : Graph) (k : ℕ) (c : Config) : Prop where
  ga : GA g k c
  reid : c.reg gEID = bEID g k
  rld : c.reg xLD = bOFF g k

/-- The memory during Algorithm 1: the identifiers and the load table `L`. -/
structure GM (g : Graph) (k : ℕ) (L : ℕ → ℕ) (m : ℕ → ℕ) : Prop where
  meid : Tab m (bEID g k) (k * (cycles g k).length) (eidOf g k)
  mld : Tab m (bOFF g k) (edgesOnCycles g k).length L

/-- The state at cycle `i`, with the load table `L` and the output `O`. -/
def CS (g : Graph) (k i : ℕ) (L : ℕ → ℕ) (O : List ℕ) (c : Config) : Prop :=
  GR g k c ∧ c.reg xB = i * k ∧ GM g k L c.mem ∧ c.out = O

/-! ### The total load -/

theorem sumBody_spec (hS : grSpace g k ≤ S) {i : ℕ} (hi : i < (cycles g k).length) (O : List ℕ)
    (p : ℕ) (hp : p < k) :
    HTB S sumBody
      (fun c => (CS g k i (ldF g k i) O c ∧ c.reg xTot = tsum g k i p) ∧ c.reg xP = p ∧
        c.reg gK = k)
      (fun c => (CS g k i (ldF g k i) O c ∧ c.reg xTot = tsum g k i (p + 1)) ∧ c.reg xP = p ∧
        c.reg gK = k) 6 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨⟨hG, hB, hM, ho⟩, hT⟩, hP, hK⟩ => ?_
  have hq := occIdx_lt hi hp
  have he := eidOf_lt hq
  have h1 := hM.meid.get hq
  have h2 := hM.mld.get he
  have := fitsG hS
  refine ⟨by addr_ok [sumBody, hB, hP, hG.reid, hG.rld, h1], ?_⟩
  have hag : Agree [xQ, xE, xX, xTot] c (run sumBody c) := agree_run (by decide) rfl rfl (by decide) c
  refine ⟨⟨(show Indep [xQ, xE, xX, xTot] (CS g k i (ldF g k i) O) by indep [CS, gR_iff, gA_iff])
    c _ hag ⟨hG, hB, hM, ho⟩, ?_⟩, by rw [hag.reg xP (by decide), hP],
    by rw [hag.reg gK (by decide), hK]⟩
  simp +decide only [sumBody, run_seq', run_add, run_ld, setReg_reg, setReg_mem, ↓reduceIte, hB,
    hP, hG.reid, hG.rld, h1, h2, hT]
  rw [tsum_succ, ldF_eidOf i hi hp]; rfl

/-- **The total load** of the edges of `C_i`. -/
theorem sumPhase_spec (hS : grSpace g k ≤ S) {i : ℕ} (hi : i < (cycles g k).length)
    (O : List ℕ) :
    HTB S sumPhase (CS g k i (ldF g k i) O)
      (fun c => CS g k i (ldF g k i) O c ∧ c.reg xTot = tot g k i) (k * 10 + 4) := by
  have h0 : HTB S (.const xTot 0) (CS g k i (ldF g k i) O)
      (fun c => (CS g k i (ldF g k i) O c ∧ c.reg xTot = tsum g k i 0) ∧ c.reg gK = k) 1 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hC =>
      ⟨⟨(show Indep [xTot] (CS g k i (ldF g k i) O) by indep [CS, gR_iff, gA_iff]).setReg
        (by decide) _ hC, by simp [tsum_zero]⟩, by simp +decide [hC.1.ga.rk]⟩
  have hl := HTB.forUpC (i := xP) (n := gK) (N := k) (body := sumBody)
    (fun p c => CS g k i (ldF g k i) O c ∧ c.reg xTot = tsum g k i p) 6 (by decide) (by decide)
    (by decide) (fun p => by indep [CS, gR_iff, gA_iff]) (fun p hp => sumBody_spec hS hi O p hp)
  exact (h0.seq hl).mono (fun _ h => h) (fun c ⟨⟨hC, hT⟩, _, _⟩ => ⟨hC, hT⟩) (by omega)

/-! ### The first option of minimum load-sum -/

/-- The state of the scan before option `j`. -/
def ChInv (g : Graph) (k i : ℕ) (O : List ℕ) (j : ℕ) (c : Config) : Prop :=
  CS g k i (ldF g k i) O c ∧ c.reg xTot = tot g k i ∧ c.reg xY = lp g k i (prv k j) ∧
    c.reg xBV = (scanMin (val g k i) (tot g k i + 1) j).1 ∧
    c.reg xBJ = (scanMin (val g k i) (tot g k i + 1) j).2

/-- The state of the scan after reading option `j`. -/
def ChMid (g : Graph) (k i : ℕ) (O : List ℕ) (j : ℕ) (c : Config) : Prop :=
  CS g k i (ldF g k i) O c ∧ c.reg xTot = tot g k i ∧ c.reg xY = lp g k i j ∧
    c.reg xBV = (scanMin (val g k i) (tot g k i + 1) j).1 ∧
    c.reg xBJ = (scanMin (val g k i) (tot g k i + 1) j).2 ∧ c.reg xV = val g k i j

theorem chooseInit_spec (hS : grSpace g k ≤ S) {i : ℕ} (hi : i < (cycles g k).length)
    (O : List ℕ) :
    HTB S chooseInit (fun c => CS g k i (ldF g k i) O c ∧ c.reg xTot = tot g k i)
      (fun c => ChInv g k i O 0 c ∧ c.reg gK = k) 10 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hG, hB, hM, ho⟩, hT⟩ => ?_
  have hk := k_ge_of_lt hi
  have hq := occIdx_lt hi (show k - 1 < k by omega)
  have he := eidOf_lt hq
  have e1 : i * k + k - 1 = i * k + (k - 1) := by omega
  have h1 : c.mem (bEID g k + (i * k + k - 1)) = eidOf g k (i * k + (k - 1)) := by
    rw [e1]; exact hM.meid.get hq
  have h2 := hM.mld.get he
  have := fitsG hS
  refine ⟨by addr_ok [chooseInit, hB, hG.ga.rk, hG.reid, hG.rld, h1], ?_⟩
  have hag : Agree [xQ, rT, xE, xY, xBV, xBJ] c (run chooseInit c) :=
    agree_run (by decide) rfl rfl (by decide) c
  refine ⟨⟨(show Indep [xQ, rT, xE, xY, xBV, xBJ] (CS g k i (ldF g k i) O) by
    indep [CS, gR_iff, gA_iff]) c _ hag ⟨hG, hB, hM, ho⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals simp +decide only [chooseInit, run_seq', run_add, run_dec, run_ld, run_addc,
    run_const, setReg_reg, setReg_mem, ↓reduceIte, hB, hG.ga.rk, hG.reid, hG.rld, h1, h2, hT]
  · rw [ldF_eidOf i hi (by omega)]
    simp [lp, prv]
  · rfl
  · rfl

theorem readV_spec (hS : grSpace g k ≤ S) {i : ℕ} (hi : i < (cycles g k).length) (O : List ℕ)
    (j : ℕ) (hj : j < k) :
    HTB S readV (fun c => ChInv g k i O j c ∧ c.reg xJ = j ∧ c.reg gK = k)
      (fun c => ChMid g k i O j c ∧ c.reg xJ = j ∧ c.reg gK = k) 9 := by
  refine HTB.run_le (by decide) (by decide)
    fun c ⟨⟨⟨hG, hB, hM, ho⟩, hT, hY, hBV, hBJ⟩, hJ, hK⟩ => ?_
  have hq := occIdx_lt hi hj
  have he := eidOf_lt hq
  have h1 := hM.meid.get hq
  have h2 := hM.mld.get he
  have := fitsG hS
  refine ⟨by addr_ok [readV, hB, hJ, hG.reid, hG.rld, h1], ?_⟩
  have hag : Agree [xQ, xE, xX, xV, rT, xY] c (run readV c) :=
    agree_run (by decide) rfl rfl (by decide) c
  have hl : ldF g k i (eidOf g k (i * k + j)) = lp g k i j := ldF_eidOf i hi hj
  refine ⟨⟨(show Indep [xQ, xE, xX, xV, rT, xY] (CS g k i (ldF g k i) O) by
    indep [CS, gR_iff, gA_iff]) c _ hag ⟨hG, hB, hM, ho⟩, ?_, ?_, ?_, ?_, ?_⟩,
    by rw [hag.reg xJ (by decide), hJ], by rw [hag.reg gK (by decide), hK]⟩
  all_goals simp +decide only [readV, run_seq', run_add, run_sub, run_ld, run_mov, setReg_reg,
    setReg_mem, ↓reduceIte, hB, hJ, hG.reid, hG.rld, h1, h2, hT, hY, hBV, hBJ, hl]
  rw [val_eq hi hj]

theorem better_spec {i : ℕ} (O : List ℕ) (j : ℕ) :
    HTB S better (fun c => (ChMid g k i O j c ∧ c.reg xJ = j ∧ c.reg gK = k) ∧
        c.reg xV < c.reg xBV)
      (fun c => ChInv g k i O (j + 1) c ∧ c.reg xJ = j ∧ c.reg gK = k) 4 :=
  HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
    fun c ⟨⟨⟨hC, hT, hY, hBV, hBJ, hV⟩, hJ, hK⟩, hlt⟩ => by
      have hag : Agree [rT, xBV, xBJ] c (run better c) :=
        agree_run (by decide) rfl rfl (by decide) c
      have hlt' : val g k i j < (scanMin (val g k i) (tot g k i + 1) j).1 := by omega
      refine ⟨⟨(show Indep [rT, xBV, xBJ] (CS g k i (ldF g k i) O) by
        indep [CS, gR_iff, gA_iff]) c _ hag hC, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      all_goals simp +decide only [better, run_seq', run_mov, setReg_reg, ↓reduceIte, hT, hY, hV,
        hJ, hK, scanMin_succ, hlt']
      · simp [prv]

theorem notBetter_spec {i : ℕ} (O : List ℕ) (j : ℕ) :
    HTB S .skip (fun c => (ChMid g k i O j c ∧ c.reg xJ = j ∧ c.reg gK = k) ∧
        c.reg xBV ≤ c.reg xV)
      (fun c => ChInv g k i O (j + 1) c ∧ c.reg xJ = j ∧ c.reg gK = k) 4 :=
  HTB.skip.mono (fun _ h => h) (fun c ⟨⟨⟨hC, hT, hY, hBV, hBJ, hV⟩, hJ, hK⟩, hle⟩ => by
    have hn : ¬ val g k i j < (scanMin (val g k i) (tot g k i + 1) j).1 := by omega
    refine ⟨⟨hC, hT, ?_, ?_, ?_⟩, hJ, hK⟩
    · rw [hY]; simp [prv]
    · rw [hBV, scanMin_succ]; simp only [hn, ↓reduceIte]
    · rw [hBJ, scanMin_succ]; simp only [hn, ↓reduceIte]) (by omega)

theorem chooseBody_spec (hS : grSpace g k ≤ S) {i : ℕ} (hi : i < (cycles g k).length)
    (O : List ℕ) (j : ℕ) (hj : j < k) :
    HTB S chooseBody (fun c => ChInv g k i O j c ∧ c.reg xJ = j ∧ c.reg gK = k)
      (fun c => ChInv g k i O (j + 1) c ∧ c.reg xJ = j ∧ c.reg gK = k) 15 :=
  (readV_spec hS hi O j hj).seq (HTB.ifLt (by decide) (by decide)
    (by indep [ChMid, CS, gR_iff, gA_iff]) (better_spec O j) (notBetter_spec O j))

/-- **The chosen option**: `xBJ = pos g k i`. -/
theorem choosePhase_spec (hS : grSpace g k ≤ S) {i : ℕ} (hi : i < (cycles g k).length)
    (O : List ℕ) :
    HTB S choosePhase (fun c => CS g k i (ldF g k i) O c ∧ c.reg xTot = tot g k i)
      (fun c => CS g k i (ldF g k i) O c ∧ c.reg xBJ = pos g k i) (k * 19 + 13) := by
  have hl := HTB.forUpC (i := xJ) (n := gK) (N := k) (body := chooseBody) (ChInv g k i O) 15
    (by decide) (by decide) (by decide) (fun j => by indep [ChInv, CS, gR_iff, gA_iff])
    (fun j hj => chooseBody_spec hS hi O j hj)
  exact ((chooseInit_spec hS hi O).seq hl).mono (fun _ h => h)
    (fun c ⟨⟨hC, _, _, _, hBJ⟩, _, _⟩ => ⟨hC, hBJ⟩) (by omega)

/-! ### Writing the option -/

theorem write_spec {i : ℕ} (L : ℕ → ℕ) (O : List ℕ) (J : ℕ) :
    HTB S (.write xBJ) (fun c => CS g k i L O c ∧ c.reg xBJ = J)
      (fun c => CS g k i L (O ++ [J]) c ∧ c.reg xBJ = J) 1 :=
  HTB.write fun c ⟨⟨hG, hB, hM, ho⟩, hJ⟩ =>
    ⟨⟨(show RegIndep [] (GR g k) by indep [gR_iff, gA_iff]).emit _ hG, by simp [hB],
      by simpa using hM, by simp [ho, hJ]⟩, by simp [hJ]⟩

/-! ### The update of the loads -/

/-- The state of the update before position `p`, for the chosen option `J`. -/
def UInv (g : Graph) (k i : ℕ) (O : List ℕ) (J p : ℕ) (c : Config) : Prop :=
  CS g k i (uF g k i J p) O c ∧ c.reg xBJ = J ∧ c.reg xBP = prv k J

theorem updInit_spec {i : ℕ} (O : List ℕ) (J : ℕ) :
    HTB S updInit (fun c => CS g k i (ldF g k i) O c ∧ c.reg xBJ = J)
      (fun c => UInv g k i O J 0 c ∧ c.reg gK = k) 8 := HTB.of_HT rfl <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨hC, hJ⟩ => ?_
  rw [← uF_zero (g := g) (k := k) i J] at hC
  have hag : Agree [rT, xBP] c (run updInit c) := agree_run (by decide) rfl rfl (by decide) c
  refine ⟨⟨(show Indep [rT, xBP] (CS g k i (uF g k i J 0) O) by
    indep [CS, gR_iff, gA_iff]) c _ hag hC, ?_, ?_⟩, ?_⟩
  · rw [hag.reg xBJ (by decide), hJ]
  · by_cases h0 : J = 0
    · simp +decide [updInit, run_mov, run_dec, hJ, h0, hC.1.ga.rk, prv]
    · simp +decide [updInit, run_mov, run_dec, hJ, h0, prv]
  · rw [hag.reg gK (by decide), hC.1.ga.rk]

theorem incLoad_spec (hS : grSpace g k ≤ S) {i : ℕ} (hi : i < (cycles g k).length)
    (O : List ℕ) (J p : ℕ) (hp : p < k) (hc : ¬ (J = p ∨ J = next k p)) :
    HTB S incLoad (fun c => UInv g k i O J p c ∧ c.reg xP = p ∧ c.reg gK = k)
      (fun c => UInv g k i O J (p + 1) c ∧ c.reg xP = p ∧ c.reg gK = k) 9 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨⟨hG, hB, hM, ho⟩, hJ, hBP⟩, hP, hK⟩ => ?_
  have hq := occIdx_lt hi hp
  have he := eidOf_lt hq
  have h1 := hM.meid.get hq
  have h2 := hM.mld.get he
  have := fitsG hS
  have hlay := bEID_kt_le g k
  refine ⟨by addr_ok [incLoad, hB, hP, hG.reid, hG.rld, h1], ?_⟩
  set e := eidOf g k (i * k + p)
  have hmem : (run incLoad c).mem = upd c.mem (bOFF g k + e) (uF g k i J p e + 1) := by
    simp +decide only [incLoad, run_seq', run_add, run_ld, run_inc, run_st, setReg_mem,
      setMem_mem_upd, setReg_reg, ↓reduceIte, hB, hP, hG.reid, hG.rld, h1, h2, e]
  have hreg : ∀ r, r ∉ [xQ, xE, xX, rT] → (run incLoad c).reg r = c.reg r := fun r hr =>
    run_reg_of_not_mem (s := incLoad) (by decide) (fun h => hr (by
      have : ∀ x ∈ wregs incLoad, x ∈ [xQ, xE, xX, rT] := by decide
      exact this r h)) c
  have hout : (run incLoad c).out = c.out := run_out_of_writes (s := incLoad) (by decide) rfl c
  refine ⟨⟨⟨((show RegIndep [xQ, xE, xX, rT] (GR g k) by indep [gR_iff, gA_iff])) _ _ hreg hG,
    by rw [hreg xB (by decide), hB], ⟨?_, ?_⟩, by rw [hout, ho]⟩,
    by rw [hreg xBJ (by decide), hJ], by rw [hreg xBP (by decide), hBP]⟩,
    by rw [hreg xP (by decide), hP], by rw [hreg gK (by decide), hK]⟩
  · rw [hmem]; exact hM.meid.upd_of_disjoint (Or.inr (by omega))
  · rw [hmem, uF_succ]
    simp only [hc, not_false_eq_true, ↓reduceIte]
    exact hM.mld.upd rfl

theorem updBody_spec (hS : grSpace g k ≤ S) {i : ℕ} (hi : i < (cycles g k).length)
    (O : List ℕ) (J : ℕ) (hJ : J < k) (p : ℕ) (hp : p < k) :
    HTB S updBody (fun c => UInv g k i O J p c ∧ c.reg xP = p ∧ c.reg gK = k)
      (fun c => UInv g k i O J (p + 1) c ∧ c.reg xP = p ∧ c.reg gK = k) 17 := by
  have hk := k_ge_of_lt hi
  have hsame : ∀ c, (J = p ∨ J = next k p) → UInv g k i O J p c ∧ c.reg xP = p ∧ c.reg gK = k →
      UInv g k i O J (p + 1) c ∧ c.reg xP = p ∧ c.reg gK = k := fun c hn ⟨⟨hC, h1, h2⟩, h3, h4⟩ => by
    rw [UInv, uF_succ]
    simp only [hn, not_true_eq_false, ↓reduceIte]
    exact ⟨⟨hC, h1, h2⟩, h3, h4⟩
  have hInd : Indep [rT] (fun c => UInv g k i O J p c ∧ c.reg xP = p ∧ c.reg gK = k) := by
    indep [UInv, CS, gR_iff, gA_iff]
  refine HTB.ifEq (by decide) (by decide) hInd
    (HTB.skip.mono (fun _ h => h) (fun c ⟨h, heq⟩ => hsame c (Or.inl (by
      rw [h.1.2.1, h.2.1] at heq; exact heq.symm)) h) (by omega))
    (HTB.ifEq (by decide) (by decide) (by indep [UInv, CS, gR_iff, gA_iff])
      (HTB.skip.mono (fun _ h => h) (fun c ⟨⟨h, _⟩, heq⟩ => hsame c (by
        rw [h.1.2.2, h.2.1] at heq
        exact (off_option_iff (by omega) hJ hp).mpr (Or.inr heq)) h) (by omega))
      ((HTB.pre_fact (p := ¬ (J = p ∨ J = next k p))
        (fun c ⟨⟨h, hne1⟩, hne2⟩ => by
          rw [h.1.2.1, h.2.1] at hne1
          rw [h.1.2.2, h.2.1] at hne2
          rw [off_option_iff (by omega) hJ hp]
          omega)
        (fun hc => (incLoad_spec hS hi O J p hp hc).pre (fun c h => h.1.1)))))

/-- **The update**: the loads of the edges of the chosen path, ending in `ldF g k (i + 1)`. -/
theorem updPhase_spec (hS : grSpace g k ≤ S) {i : ℕ} (hi : i < (cycles g k).length)
    (O : List ℕ) :
    HTB S updPhase (fun c => UInv g k i O (pos g k i) 0 c ∧ c.reg gK = k)
      (CS g k i (ldF g k (i + 1)) O) (k * 21 + 3) := by
  have hl := HTB.forUpC (i := xP) (n := gK) (N := k) (body := updBody) (UInv g k i O (pos g k i))
    17 (by decide) (by decide) (by decide) (fun p => by indep [UInv, CS, gR_iff, gA_iff])
    (fun p hp => updBody_spec hS hi O (pos g k i) (pos_lt hi) p hp)
  refine hl.mono (fun _ h => h) (fun c ⟨⟨⟨hG, hB, hM, ho⟩, _, _⟩, _, _⟩ =>
    ⟨hG, hB, ⟨hM.meid, hM.mld.congr_fun fun e he => uF_final hi he⟩, ho⟩) (by omega)

/-! ### One cycle -/

theorem nextBase_spec {i : ℕ} (L : ℕ → ℕ) (O : List ℕ) :
    HTB S (.add xB xB gK) (CS g k i L O) (CS g k (i + 1) L O) 1 :=
  HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hG, hB, hM, ho⟩ =>
    ⟨(show RegIndep [xB] (GR g k) by indep [gR_iff, gA_iff]).setReg (by decide) _ hG,
      by simp [hB, hG.ga.rk]; ring, hM, ho⟩

/-- **One cycle of Algorithm 1**: from the loads after `i` cycles and the options chosen so far,
the option `pos g k i` is written and the loads after `i + 1` cycles are stored. -/
theorem cycBody_spec (hS : grSpace g k ≤ S) {i : ℕ} (hi : i < (cycles g k).length) :
    HTB S cycBody (CS g k i (ldF g k i) ((List.range i).map (pos g k)))
      (CS g k (i + 1) (ldF g k (i + 1)) ((List.range (i + 1)).map (pos g k))) (k * 50 + 30) := by
  have hO : (List.range (i + 1)).map (pos g k) = (List.range i).map (pos g k) ++ [pos g k i] := by
    rw [List.range_succ, List.map_append, List.map_singleton]
  rw [hO]
  exact ((sumPhase_spec hS hi _).seq ((choosePhase_spec hS hi _).seq
    ((write_spec _ _ _).seq ((updInit_spec _ _).seq ((updPhase_spec hS hi _).seq
    (nextBase_spec _ _)))))).weaken (by omega)

end STACS2027.Runtimes.Greedy
