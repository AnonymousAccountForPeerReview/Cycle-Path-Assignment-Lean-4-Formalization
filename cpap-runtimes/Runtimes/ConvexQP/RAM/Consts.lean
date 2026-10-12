module

public import Runtimes.ConvexQP.RAM.ParseKS
import Mathlib.Tactic

/-!
# Lemma 16 on the RAM, the constants: program and stages

From `gT = t`, `gK = k`, `gKT = kt`, the phase `stepConsts` writes the constants of `QRegs`
into `qT … qCD` (memory, `rFREE`, `qBH` and the output unchanged). Stages:

1. `cA`, `cND`: `t`, `k`, `kt`, `k − 1`, `k + 1`, `k − 2`, `M = 3kt + 2t`, `n = (k−1)t`,
   `d = (k+1)t`;
2. `cFact`, `cPow`, `cE`: `E = 2 (d² + 1) d! (k−2)^{d+1}` (`d` multiplications by `j ≤ d`, `d + 1`
   by `k − 2`);
3. `cRad`: `n / r_K = n · 4 C₀ E⁴ (k−2)² t² (k−1)` (`E·E`, `E²·E²`, then small factors);
4. `cIt`: `L = ⌈log₂(n/r_K)⌉` (`clogLoop`) and `N = 16 n (n+1) L + 1`;
5. `cPrec`: `p = 64 (n+1) L + 3 ⌈log₂(n+1)⌉ + 15` (`prec_eq`, `n ≥ 1`);
6. `cCN`: `cN = n² (32 n (n+1) + 1)³`, `cD = (n² − 1) (32 n (n+1))³`.

Every `mulN` has the small factor second, except `E·E` and `E²·E²`.
The values are `cv t k r`; the stage `i` ends in `KS m₀ F B rsᵢ (cv t k)`.
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Parse

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ConvexQP

/-! ### Registers and values -/

/-- Loop counter. -/
abbrev cI : ℕ := 540
/-- `j + 1`. -/
abbrev cJ : ℕ := 541
/-- `k − 2`. -/
abbrev cA0 : ℕ := 542
/-- `k − 1`. -/
abbrev cK1 : ℕ := 543
/-- Scratch (`k + 1`, `16n…`). -/
abbrev cX : ℕ := 544
/-- `n / r_K`. -/
abbrev cR : ℕ := 545
/-- `L = ⌈log₂(n/r_K)⌉`. -/
abbrev cL : ℕ := 546
/-- `n + 1`. -/
abbrev cY : ℕ := 547
/-- Doubling register of the first `clogLoop`. -/
abbrev cW : ℕ := 548
/-- `⌈log₂(n+1)⌉`. -/
abbrev cZ : ℕ := 549
/-- Scratch (`d² + 1`, `n²`). -/
abbrev cU : ℕ := 270
/-- Scratch (`3kt + t`, `64(n+1)L`, `32n(n+1)`). -/
abbrev cV : ℕ := 271
/-- Scratch (`3⌈log₂(n+1)⌉`, `32n(n+1) + 1`). -/
abbrev cB : ℕ := 272
/-- `d + 1`. -/
abbrev cD1 : ℕ := 273
/-- `C₀ = 2(k−2)t²`. -/
abbrev cC : ℕ := 274
/-- Doubling register of the second `clogLoop`. -/
abbrev cW2 : ℕ := 275

/-- The values of the constants phase. -/
def cv (t k : ℕ) (r : ℕ) : ℕ :=
  if r = ZeroCost.gT then t else if r = ZeroCost.gK then k else if r = ZeroCost.gKT then k * t else
  if r = qT then t else if r = qK then k else if r = qKT then k * t else
  if r = cK1 then k - 1 else if r = cA0 then k - 2 else if r = cX then k + 1 else
  if r = qM then nRows t k else if r = qN then nDim t k else if r = qD then dimKKT t k else
  if r = qE then bigE t k else if r = cR then radInv t k else if r = cL then logRad t k else
  if r = cY then nDim t k + 1 else if r = qIt then iters t k else if r = qP then prec t k else
  if r = qCN then cNum t k else if r = qCD then cDen t k else 0

/-- The registers known before the phase. -/
def rs0 : List ℕ := [ZeroCost.gT, ZeroCost.gK, ZeroCost.gKT]
/-- After stage 1. -/
def rs1 : List ℕ := [qD, qN, qM, cA0, cK1, qKT, qK, qT, ZeroCost.gT, ZeroCost.gK, ZeroCost.gKT]
/-- After stage 2. -/
def rs2 : List ℕ := qE :: rs1
/-- After stage 3. -/
def rs3 : List ℕ := cR :: rs2
/-- After stage 4. -/
def rs4 : List ℕ := qIt :: cY :: cL :: rs3
/-- After stage 5. -/
def rs5 : List ℕ := qP :: rs4
/-- After stage 6. -/
def rs6 : List ℕ := qCD :: qCN :: rs5

/-! ### The program -/

/-- Stage 1a: copies, `k ± 1`, `k − 2`, `M`. -/
def cA : Stmt :=
  .seq (mov qT ZeroCost.gT) (.seq (mov qK ZeroCost.gK) (.seq (mov qKT ZeroCost.gKT) (.seq (subc cK1 ZeroCost.gK 1)
    (.seq (addc cX ZeroCost.gK 1) (.seq (subc cA0 ZeroCost.gK 2) (.seq (.add cV qKT qKT)
    (.seq (.add cV cV qKT) (.seq (.add cV cV qT) (.add qM cV qT)))))))))

/-- Stage 1b: `n`, `d`. -/
def cND : Stmt := .seq (Arith.mulN qN cK1 qT) (Arith.mulN qD cX qT)

/-- One step of the factorial. -/
def factBody : Stmt := .seq (addc cJ cI 1) (Arith.mulN qE qE cJ)

/-- Stage 2a: `qE := d!`. -/
def cFact : Stmt := .seq (.const qE 1) (forUp cI qD factBody)

/-- Stage 2b: `qE := qE · (k−2)^{d+1}`. -/
def cPow : Stmt := .seq (addc cD1 qD 1) (forUp cI cD1 (Arith.mulN qE qE cA0))

/-- Stage 2c: `qE := 2 (d² + 1) qE`. -/
def cE : Stmt :=
  .seq (Arith.mulN cU qD qD) (.seq (addc cU cU 1) (.seq (Arith.mulN qE qE cU) (.add qE qE qE)))

/-- Stage 3: `n / r_K`. -/
def cRad : Stmt :=
  .seq (Arith.mulN cR qE qE) (.seq (Arith.mulN cR cR cR) (.seq (.add cR cR cR) (.seq (.add cR cR cR)
    (.seq (Arith.mulN cC cA0 qT) (.seq (Arith.mulN cC cC qT) (.seq (.add cC cC cC)
    (.seq (Arith.mulN cR cR cC) (.seq (Arith.mulN cR cR cA0) (.seq (Arith.mulN cR cR cA0)
    (.seq (Arith.mulN cR cR qT) (.seq (Arith.mulN cR cR qT) (.seq (Arith.mulN cR cR cK1)
    (Arith.mulN cR cR qN)))))))))))))

/-- Stage 4: `L` and `N`. -/
def cIt : Stmt :=
  .seq (clogLoop cL cR cW) (.seq (.add cX qN qN) (.seq (.add cX cX cX) (.seq (.add cX cX cX)
    (.seq (.add cX cX cX) (.seq (addc cY qN 1) (.seq (Arith.mulN cX cX cY)
    (.seq (Arith.mulN cX cX cL) (addc qIt cX 1))))))))

/-- Stage 5: `p`. -/
def cPrec : Stmt :=
  .seq (clogLoop cZ cY cW2) (.seq (Arith.mulN cV cY cL) (.seq (.add cV cV cV) (.seq (.add cV cV cV)
    (.seq (.add cV cV cV) (.seq (.add cV cV cV) (.seq (.add cV cV cV) (.seq (.add cV cV cV)
    (.seq (.add cB cZ cZ) (.seq (.add cB cB cZ) (.seq (.add qP cV cB) (addc qP qP 15)))))))))))

/-- Stage 6: `cN`, `cD`. -/
def cCN : Stmt :=
  .seq (Arith.mulN cV qN cY) (.seq (.add cV cV cV) (.seq (.add cV cV cV) (.seq (.add cV cV cV)
    (.seq (.add cV cV cV) (.seq (.add cV cV cV) (.seq (addc cB cV 1) (.seq (Arith.mulN cU qN qN)
    (.seq (Arith.mulN qCN cU cB) (.seq (Arith.mulN qCN qCN cB) (.seq (Arith.mulN qCN qCN cB)
    (.seq (subc cU cU 1) (.seq (Arith.mulN qCD cU cV) (.seq (Arith.mulN qCD qCD cV)
    (Arith.mulN qCD qCD cV))))))))))))))

/-- **The constants.** -/
def stepConsts : Stmt :=
  .seq (.seq cA cND) (.seq (.seq cFact (.seq cPow cE)) (.seq cRad (.seq cIt (.seq cPrec cCN))))

/-! ### The two loops of stage 2 -/

theorem mulCost_mono {a b : ℕ} (h : a ≤ b) : Arith.mulCost a ≤ Arith.mulCost b := by
  unfold Arith.mulCost; have := Nat.size_le_size h; omega

section loops

variable {m₀ : ℕ → ℕ} {F B S : ℕ}

theorem KS.cons {rs : List ℕ} {v : ℕ → ℕ} {c : Config} (h : KS m₀ F B rs v c) {r z : ℕ}
    (hr : c.reg r = z) : KS m₀ F B (r :: rs) (Function.update v r z) c := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun r' hr' => ?_⟩
  by_cases e : r' = r
  · subst e; simp [hr]
  · rw [Function.update_of_ne e]; exact h.get (by simpa [e] using hr')

/-- **The factorial**: `qE := d!` with `d = reg qD`. -/
theorem KS.fact (hZ0 : ZeroFrom m₀ F) {rs : List ℕ} {v : ℕ → ℕ} (hD : qD ∈ rs)
    (hrs : ∀ r ∈ rs, r ∉ Arith.arithW ∧ r ≠ cI ∧ r ≠ cJ ∧ r ≠ qE) :
    HTF S F cFact (KS m₀ F B rs v)
      (KS m₀ F B (qE :: rs) (Function.update v qE (v qD).factorial))
      (1 + (v qD * (2 + Arith.mulCost (v qD) + 4) + 3)) := by
  have hrT : rT ∉ rs := fun h => (hrs rT h).1 (by decide)
  have h0 := HTF.of_HT (S := S) (F := F) rfl (KS.const (m₀ := m₀) (F := F) (B := B) (rs := rs)
    (v := v) (d := qE) (z := 1) hrT (by decide))
  have hInv : ∀ j : ℕ, Indep [cI, rT] (KS m₀ F B (qE :: rs) (Function.update v qE j.factorial)) :=
    fun j => KS.indep (by decide) (by decide) fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · decide
      · have := hrs r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨this.2.1, fun e => this.1 (e ▸ by decide)⟩
  have hbody : ∀ j < v qD, HTF S F factBody
      (fun c => KS m₀ F B (qE :: rs) (Function.update v qE j.factorial) c ∧ c.reg cI = j ∧
        c.reg qD = v qD)
      (fun c => KS m₀ F B (qE :: rs) (Function.update v qE (j + 1).factorial) c ∧ c.reg cI = j ∧
        c.reg qD = v qD) (2 + Arith.mulCost (v qD)) := by
    intro j hj
    set v1 := Function.update (Function.update v qE j.factorial) cI j with hv1
    have h1 := HTF.of_HT (S := S) (F := F) rfl (KS.addc (m₀ := m₀) (F := F) (B := B)
      (rs := cI :: qE :: rs) (v := v1) (d := cJ) (a := cI) (k := 1) (by simp) (by decide)
      (by simp only [List.mem_cons, not_or]; exact ⟨by decide, by decide, hrT⟩) (by decide))
    have h2 := KS.mulN (S := S) (m₀ := m₀) (F := F) (B := B) hZ0 (rs := cJ :: cI :: qE :: rs)
      (v := Function.update v1 cJ (v1 cI + 1)) (d := qE) (x := qE) (y := cJ) (by decide)
      (by decide) (by simp) (by simp) (by decide) (fun r hr hne => by
        rcases List.mem_cons.mp hr with rfl | hr
        · decide
        rcases List.mem_cons.mp hr with rfl | hr
        · decide
        rcases List.mem_cons.mp hr with rfl | hr
        · exact absurd rfl hne
        · exact (hrs r hr).1)
    have e1 : v1 cI = j := by simp [hv1]
    have e2 : v1 qE = j.factorial := by simp [hv1]
    refine (h1.seq h2).mono (fun c ⟨hK, hi, _⟩ => hK.cons hi) (fun c h => ⟨h.sub ?_, ?_, ?_⟩) ?_
    · intro r hr
      refine ⟨by simp only [List.mem_cons] at hr ⊢; tauto, ?_⟩
      rcases List.mem_cons.mp hr with rfl | hr'
      · simp [e1, e2, Nat.factorial_succ, Nat.mul_comm]
      · obtain ⟨-, h1, h2, h3⟩ := hrs r hr'
        simp [h1, h2, h3, hv1]
    · rw [h.get (by simp)]; simp [hv1]
    · rw [h.get (by simp [hD])]
      have := hrs qD hD
      simp [hv1]
    · have : Function.update v1 cJ (v1 cI + 1) cJ = j + 1 := by simp [e1]
      rw [this]
      have := mulCost_mono (show j + 1 ≤ v qD by omega)
      omega
  have hl := HTF.forUpC (S := S) (F := F) (i := cI) (n := qD) (N := v qD) (body := factBody)
    (fun j : ℕ => KS m₀ F B (qE :: rs) (Function.update v qE j.factorial)) (2 + Arith.mulCost (v qD))
    (by decide) (by decide) (by decide) hInv hbody
  refine h0.seq (hl.mono (fun c h => ⟨?_, ?_⟩) (fun c h => h.1) le_rfl)
  · rw [Nat.factorial_zero]; exact h
  · rw [h.get (List.mem_cons_of_mem _ hD), Function.update_of_ne (by decide)]

/-- **The power**: `qE := qE · (k−2)^{d+1}` with `k − 2 = reg cA0`, `d = reg qD`. -/
theorem KS.pow (hZ0 : ZeroFrom m₀ F) {rs : List ℕ} {v : ℕ → ℕ} (hD : qD ∈ rs) (hA : cA0 ∈ rs)
    (hE : qE ∈ rs) (hrs : ∀ r ∈ rs, r ∉ Arith.arithW ∧ r ≠ cI ∧ r ≠ cD1) :
    HTF S F cPow (KS m₀ F B rs v)
      (KS m₀ F B (cD1 :: rs) (Function.update (Function.update v cD1 (v qD + 1)) qE
        (v qE * v cA0 ^ (v qD + 1))))
      (2 + ((v qD + 1) * (Arith.mulCost (v cA0) + 4) + 3)) := by
  have hrT : rT ∉ rs := fun h => (hrs rT h).1 (by decide)
  set vb := Function.update v cD1 (v qD + 1) with hvb
  have h0 := HTF.of_HT (S := S) (F := F) rfl (KS.addc (m₀ := m₀) (F := F) (B := B) (rs := rs)
    (v := v) (d := cD1) (a := qD) (k := 1) hD (by decide) hrT (by decide))
  have hInv : ∀ j, Indep [cI, rT]
      (KS m₀ F B (cD1 :: rs) (Function.update vb qE (v qE * v cA0 ^ j))) :=
    fun j => KS.indep (by decide) (by decide) fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · decide
      · have := hrs r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨this.2.1, fun e => this.1 (e ▸ by decide)⟩
  have hvA : vb cA0 = v cA0 := by simp [hvb]
  have hbody : ∀ j < v qD + 1, HTF S F (Arith.mulN qE qE cA0)
      (fun c => KS m₀ F B (cD1 :: rs) (Function.update vb qE (v qE * v cA0 ^ j)) c ∧
        c.reg cI = j ∧ c.reg cD1 = v qD + 1)
      (fun c => KS m₀ F B (cD1 :: rs) (Function.update vb qE (v qE * v cA0 ^ (j + 1))) c ∧
        c.reg cI = j ∧ c.reg cD1 = v qD + 1) (Arith.mulCost (v cA0)) := by
    intro j _
    have h2 := (KS.mulN (S := S) (m₀ := m₀) (F := F) (B := B) hZ0 (rs := cD1 :: rs)
      (v := Function.update vb qE (v qE * v cA0 ^ j)) (d := qE) (x := qE) (y := cA0) (by decide)
      (by decide) (by simp [hE]) (by simp [hA]) (by decide) (fun r hr hne => by
        rcases List.mem_cons.mp hr with rfl | hr
        · decide
        · exact (hrs r hr).1)).frameReg (Fr := fun c => c.reg cI = j) (by indep)
    refine h2.mono (fun c ⟨hK, hi, _⟩ => ⟨hK, hi⟩) (fun c ⟨h, hi⟩ => ⟨h.sub ?_, hi, ?_⟩) ?_
    · intro r hr
      refine ⟨List.mem_cons_of_mem _ hr, ?_⟩
      by_cases e : r = qE
      · subst e; simp [hvA, pow_succ, Nat.mul_assoc]
      · simp [e]
    · rw [h.get (by simp)]; simp [hvb]
    · simp [hvA]
  have hl := HTF.forUpC (S := S) (F := F) (i := cI) (n := cD1) (N := v qD + 1)
    (body := Arith.mulN qE qE cA0)
    (fun j => KS m₀ F B (cD1 :: rs) (Function.update vb qE (v qE * v cA0 ^ j)))
    (Arith.mulCost (v cA0)) (by decide) (by decide) (by decide) hInv hbody
  refine h0.seq (hl.mono (fun c h => ⟨h.sub ?_, ?_⟩) (fun c h => h.1) le_rfl)
  · intro r hr
    refine ⟨hr, ?_⟩
    by_cases e : r = qE
    · subst e; simp [hvb]
    · simp [Function.update_apply, e, hvb]
  · rw [h.get (by simp)]; simp

end loops

end STACS2027.Runtimes.QPRam.Parse
