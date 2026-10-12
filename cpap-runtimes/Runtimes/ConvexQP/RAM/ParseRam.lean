module

public import Runtimes.ConvexQP.RAM.ParseHStep
public import Runtimes.ConvexQP.RAM.ParseConstsBound
import Mathlib.Tactic

/-!
# Lemma 16 on the RAM: the parser with the constants (`parse_ramB`)

`parseProg = stepInit ; ifz gT tZero (front ; stepH ; stepConsts)`: Corollary 5's phase 1
(`stepInit`), the **sorting front end** `Sort.front` (`Runtimes/Sort/Front.lean`: the edge
identifiers `EID[q] = eidOf g k q` by a stable merge sort of the labels and outerplanar package's
`PairIds` modules — **no memory indexed by a vertex label**, in place of Corollary 5's
dictionary phases), the matrix `H` (`ParseH*.lean`), the constants (`ParseKS.lean`,
`Consts.lean`, `ParseConsts*.lean`). If there is no cycle, the machine writes `1` and sets
`qT := 0`.

**`parse_ramB : ParseSpecRamB parseProg`**, with the bound `30000 · (|input| + 2)³` on the time
and on the addresses accessed: the front end is `O(kt log kt + 1)` time and `O(kt)` cells
(`front_spec`), `stepH` costs `O((kt)² k)` (`Th_le`) and `2 (kt)² + nE` cells, the constants
`O(((k+1)t + 2)³)` (`constCost_le`), their scratch at most their time (`HTF`), and `kt ≤ |input|`,
`k ≤ kt` when `t ≥ 1`.
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Parse

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ConvexQP STACS2027.Runtimes.ZeroCost

variable {S : ℕ}

/-! ### The program -/

/-- No cycle: `qT := 0`, output `1`. -/
def tZero : Stmt := .seq (.const qT 0) (.seq (.const hV 1) (.write hV))

/-- The parser after the header, when there is a cycle. -/
def parseRest : Stmt := .seq Sort.front (.seq stepH stepConsts)

/-! ### Correctness -/

/-- The post-condition of `ParseSpecRamB` (without the bound on the free address). -/
def ParsePost (g : Graph) (k : ℕ) (c : Config) : Prop :=
  ((cycles g k).length = 0 ∧ c.reg qT = 0 ∧ c.out = [1]) ∨
    (0 < (cycles g k).length ∧ QIn (instOf g k) c)

/-- The cost of the front end. -/
def frontCost (g : Graph) (k : ℕ) : ℕ :=
  Sort.CF * (Sort.fL g k * (Nat.clog 2 (Sort.fL g k) + 1) + 1)

/-- The cost of `parseRest`. -/
def restCost (g : Graph) (k : ℕ) : ℕ :=
  frontCost g k + (Th g k + constCost (cycles g k).length k)

theorem consts_spec {g : Graph} (hg : g.Nodup) {k : ℕ} (ht : 0 < (cycles g k).length)
    (hk : 3 ≤ k) (hSp : bEnd g k + constCost (cycles g k).length k ≤ S) :
    HTB S stepConsts (OInv g k (nN g k))
      (fun c => QIn (instOf g k) c ∧ c.reg rFREE = bEnd g k) (constCost (cycles g k).length k) := by
  intro c ⟨hG, hM, _, ho⟩
  have hn : 1 ≤ nDim (cycles g k).length k := by
    unfold nDim; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨c', T, he, ⟨hmem, hfree, hbh, hout, hregs⟩, hT⟩ :=
    stepConsts_spec (S := S) (m₀ := c.mem) (F := bEnd g k) (B := bH g k) hM.mzero _ k hn hSp c
      ⟨rfl, hG.rfree, hG.rbh, ho, hG.rt, hG.rk, hG.rkt⟩
  have hIt : (instOf g k).t = (cycles g k).length := List.length_map _
  have hL := hlayout g k
  refine ⟨c', T, he, ⟨⟨?_, ?_, ?_, ?_, hout⟩, hfree⟩, hT⟩
  · unfold QRegs; rw [hIt]; exact hregs
  · rw [hmem, hbh]; exact hMem_of_HM hg hM
  · have e : (instOf g k).t * (instOf g k).k = nN g k := by rw [hIt, Nat.mul_comm]
    rw [hbh, hfree, hL.2.2]
    unfold hCells; rw [e]
  · rw [hmem, hfree]; exact hM.mzero

/-- The front end from Corollary 5's phase 1. -/
theorem front_parse (g : Graph) (k : ℕ) (hSp : Sort.fEnd g k (bD g k) ≤ S) :
    HTB S Sort.front (InitPost g k) (FP g k) (frontCost g k) :=
  HTB.of_forall fun c₀ hI => (Sort.front_spec g k c₀ (Sort.frontIn_of_initPost hI)
    (by rw [hI.rfree]; exact hSp)).post fun c ⟨hP, _, ho⟩ => by
      rw [hI.rfree] at hP
      exact ⟨hP, by rw [ho, hI.rout]⟩

theorem rest_spec {g : Graph} (hg : g.Nodup) {k : ℕ} (ht : 0 < (cycles g k).length)
    (hSp : bEnd g k + constCost (cycles g k).length k ≤ S) :
    HTB S parseRest (InitPost g k) (fun c => ParsePost g k c ∧ c.reg rFREE = bEnd g k)
      (restCost g k) := by
  have hk : 3 ≤ k := cycles_k_ge (List.ne_nil_of_length_pos ht)
  have hL := hlayout g k
  have h := (front_parse g k (by
      have : Sort.fEnd g k (bD g k) = bMK g k := rfl
      omega)).seq ((stepH_spec g k (by omega)).seq (consts_spec hg ht hk hSp))
  exact h.post fun c hc => ⟨Or.inr ⟨ht, hc.1⟩, hc.2⟩

theorem tZero_spec (g : Graph) (k : ℕ) :
    HTB S tZero (fun c => InitPost g k c ∧ c.reg ZeroCost.gT = 0)
      (fun c => ParsePost g k c ∧ c.reg rFREE = bD g k) 3 :=
  HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hI, h0⟩ =>
    ⟨Or.inl ⟨by rw [← hI.ga.rt]; exact h0, by simp [tZero], by simp [tZero, Config.emit, hI.rout]⟩,
      by simp [tZero, hI.rfree]⟩

/-- The bound of the branch. -/
def branchCost (g : Graph) (k : ℕ) : ℕ := if (cycles g k).length = 0 then 3 else restCost g k

/-- The memory of the branch. -/
def branchEnd (g : Graph) (k : ℕ) : ℕ :=
  if (cycles g k).length = 0 then bD g k else bEnd g k

theorem parseProg_spec {g : Graph} (hg : g.Nodup) (k : ℕ)
    (hSp : bD g k ≤ S ∧ ((cycles g k).length ≠ 0 →
      bEnd g k + constCost (cycles g k).length k ≤ S)) :
    HTB S (.seq stepInit (.ifz ZeroCost.gT tZero parseRest)) (fun c => c = initial (zeroCostInput g k))
      (fun c => ParsePost g k c ∧ c.reg rFREE = branchEnd g k)
      ((5 * (cycles g k).length + 16) + (branchCost g k + 1)) := by
  refine (stepInit_spec g k hSp.1).seq (HTB.ifz ?_ ?_)
  · intro c ⟨hI, h0⟩
    have ht0 : (cycles g k).length = 0 := by rw [← hI.ga.rt]; exact h0
    simp only [branchCost, branchEnd, ht0, ↓reduceIte]
    exact tZero_spec g k c ⟨hI, h0⟩
  · intro c ⟨hI, hne⟩
    have ht0 : (cycles g k).length ≠ 0 := by rw [← hI.ga.rt]; exact hne
    simp only [branchCost, branchEnd, ht0, ↓reduceIte]
    exact rest_spec hg (Nat.pos_of_ne_zero ht0) (hSp.2 ht0) c hI

/-! ### The step bound -/

/-- `stepH` costs `O(N² k)`: at most `160 P³` for `N = kt ≤ P`, `k ≤ P`. -/
theorem Th_le {g : Graph} {k P : ℕ} (hN : nN g k ≤ P) (hk : k ≤ P) (hP : 1 ≤ P) :
    Th g k ≤ 160 * P ^ 3 := by
  unfold Th Tout
  have hTmw : Tmw k ≤ 11 + 15 * P := by unfold Tmw; omega
  have hTin : Tin k + 4 ≤ 29 + 16 * P := by unfold Tin Tcw; omega
  have h1 : nN g k * (Tin k + 4) ≤ 29 * P + 16 * (P * P) :=
    calc nN g k * (Tin k + 4) ≤ P * (29 + 16 * P) := Nat.mul_le_mul hN hTin
      _ = 29 * P + 16 * (P * P) := by ring
  have h2 : nN g k * (1 + (Tmw k + (4 + (nN g k * (Tin k + 4) + 3 + (1 + (Tmw k + 12))))) + 4) ≤
      47 * P + 59 * (P * P) + 16 * (P * P * P) :=
    calc _ ≤ P * (47 + 59 * P + 16 * (P * P)) := Nat.mul_le_mul hN (by omega)
      _ = 47 * P + 59 * (P * P) + 16 * (P * P * P) := by ring
  have h3 : P ≤ P * P := Nat.le_mul_of_pos_left _ hP
  have h4 : P * P ≤ P * P * P := Nat.le_mul_of_pos_right _ hP
  have h5 : P ^ 3 = P * P * P := by ring
  rw [h5]; omega

theorem input_len (g : Graph) (k : ℕ) :
    (zeroCostInput g k).length = 2 * g.length + 3 + k * (cycles g k).length := by
  rw [length_zeroCostInput, bD, bV]

end STACS2027.Runtimes.QPRam.Parse

namespace STACS2027.Runtimes.QPRam

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ConvexQP STACS2027.Runtimes.ZeroCost
  STACS2027.Runtimes.QPRam.Parse

/-- **The parser** with the constants. -/
def parseProg : Stmt := .seq stepInit (.ifz ZeroCost.gT tZero parseRest)

/-- **The parser** (with the constants) meets its bounded specification: within
`30000 · (|input| + 2)³` steps, accessing only the addresses below any
`S ≥ 30000 · (|input| + 2)³` (no memory indexed by a vertex label). -/
theorem parse_ramB : ParseSpecRamB parseProg := by
  refine ⟨30000, fun g k hg S hS => ?_⟩
  have hLen := input_len g k
  set P := (zeroCostInput g k).length + 2 with hPdef
  have hP3 : 8 ≤ P ^ 3 :=
    le_trans (by norm_num) (Nat.pow_le_pow_left (show 2 ≤ P by omega) 3)
  have hP1 : P ≤ P ^ 3 := by
    calc P = P ^ 1 := (pow_one P).symm
      _ ≤ P ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hP2 : P * P ≤ P ^ 3 := by
    calc P * P = P ^ 2 := (sq P).symm
      _ ≤ P ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  -- the memory of the branch
  have hbD : bD g k ≤ P := by rw [← length_zeroCostInput]; omega
  have hmem : ∀ ht : (cycles g k).length ≠ 0,
      bEnd g k + constCost (cycles g k).length k ≤ 30000 * P ^ 3 := by
    intro ht0
    have ht : 0 < (cycles g k).length := Nat.pos_of_ne_zero ht0
    have hk : 3 ≤ k := cycles_k_ge (List.ne_nil_of_length_pos ht)
    have hN : k * (cycles g k).length ≤ P := by omega
    have hnE : nE g k ≤ k * (cycles g k).length := nE_le g k
    have hfe := Sort.fEnd_le g k (bD g k)
    have hNN : nN g k * (2 * nN g k) ≤ 2 * (P * P) := by
      have : nN g k * (2 * nN g k) = 2 * (nN g k * nN g k) := by ring
      rw [this]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hN hN)
    have hC := constCost_le ht hk
    have hD : dimKKT (cycles g k).length k + 2 ≤ 2 * P := by
      have : dimKKT (cycles g k).length k = k * (cycles g k).length + (cycles g k).length := by
        unfold dimKKT; ring
      have htk : (cycles g k).length ≤ k * (cycles g k).length :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hD3 : (dimKKT (cycles g k).length k + 2) ^ 3 ≤ 8 * P ^ 3 :=
      (Nat.pow_le_pow_left hD 3).trans (le_of_eq (by ring))
    have e1 : bEnd g k = Sort.fEnd g k (bD g k) + nE g k + nN g k * (2 * nN g k) := rfl
    simp only [Sort.fL] at hfe
    omega
  have hSp : bD g k ≤ S ∧ ((cycles g k).length ≠ 0 →
      bEnd g k + constCost (cycles g k).length k ≤ S) :=
    ⟨by omega, fun ht => (hmem ht).trans hS⟩
  refine (parseProg_spec (S := S) hg k hSp).mono (fun _ h => h) (fun c ⟨hc, hF⟩ => ⟨hc, ?_⟩) ?_
  · rw [hF]
    unfold branchEnd
    split_ifs with ht0
    · omega
    · have := hmem ht0; omega
  · by_cases ht0 : (cycles g k).length = 0
    · simp only [branchCost, ht0, ↓reduceIte]; omega
    · simp only [branchCost, ht0, ↓reduceIte, restCost, frontCost]
      have ht : 0 < (cycles g k).length := Nat.pos_of_ne_zero ht0
      have hk : 3 ≤ k := cycles_k_ge (List.ne_nil_of_length_pos ht)
      set t := (cycles g k).length with htdef
      have hN : k * t ≤ P := by omega
      have hkt : k ≤ k * t := Nat.le_mul_of_pos_right _ ht
      have htk : t ≤ k * t := Nat.le_mul_of_pos_left _ (by omega)
      have hTh := Th_le (g := g) (k := k) (P := P) hN (by omega) (by omega)
      have hC := constCost_le ht hk
      have hD : dimKKT t k + 2 ≤ 2 * P := by
        have : dimKKT t k = k * t + t := by unfold dimKKT; ring
        omega
      have hD3 : (dimKKT t k + 2) ^ 3 ≤ 8 * P ^ 3 :=
        (Nat.pow_le_pow_left hD 3).trans (le_of_eq (by ring))
      -- the front end: `kt (⌈log₂ kt⌉ + 1) + 1 ≤ 3 P²`
      have hcl : Nat.clog 2 (Sort.fL g k) ≤ P :=
        (Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)).trans (by simp only [Sort.fL]; omega)
      have hfr : Sort.fL g k * (Nat.clog 2 (Sort.fL g k) + 1) + 1 ≤ 3 * P ^ 3 := by
        have : Sort.fL g k * (Nat.clog 2 (Sort.fL g k) + 1) ≤ P * (P + 1) :=
          Nat.mul_le_mul (by simp only [Sort.fL]; omega) (by omega)
        have e : P * (P + 1) = P * P + P := by ring
        omega
      have hCF : Sort.CF = 500 := rfl
      rw [hCF]
      omega

end STACS2027.Runtimes.QPRam
