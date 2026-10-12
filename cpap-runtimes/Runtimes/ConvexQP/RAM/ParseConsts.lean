module

public import Runtimes.ConvexQP.RAM.Consts
import Mathlib.Tactic

/-!
# Lemma 16 on the RAM, the constants: the six stages, `stepConsts_spec`

Each stage `i` goes from `KS m₀ F B rsᵢ₋₁ (cv t k)` to `KS m₀ F B rsᵢ (cv t k)` (`st1_spec` …
`st6_spec`), by the step lemmas of `ParseKS.lean` (the macros `ksmul`, `ksadd`, … supply the
decidable side conditions) and the loops `KS.fact`, `KS.pow`; the values are checked by `simp`
and `ring` against the definitions (`bigE`, `radInv`, `iters`, `prec_eq`, `cNum`, `cDen`).
`stepConsts_spec`: the constants `CRegs t k` in `qT … qCD`, within `constCost t k` steps, as
`HTF S F` triples: the space allowance above the free address `F` is the step bound (it covers
the multiplications' scratch tables).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Parse

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ConvexQP

set_option hygiene false in
/-- `KS.mulN` with its decidable side conditions (uses `hZ0` from the context). -/
macro "ksmul" d:term:max x:term:max y:term:max : term =>
  `(KS.mulN hZ0 (d := $d) (x := $x) (y := $y) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide))
/-- `KS.add` with its decidable side conditions. -/
macro "ksadd" d:term:max a:term:max b:term:max : term =>
  `(HTF.of_HT rfl (KS.add (d := $d) (a := $a) (b := $b) (by decide) (by decide) (by decide)
    (by decide)))
/-- `KS.addc` with its decidable side conditions. -/
macro "ksaddc" d:term:max a:term:max k:term:max : term =>
  `(HTF.of_HT rfl (KS.addc (d := $d) (a := $a) (k := $k) (by decide) (by decide) (by decide)
    (by decide)))
/-- `KS.subc` with its decidable side conditions. -/
macro "kssubc" d:term:max a:term:max k:term:max : term =>
  `(HTF.of_HT rfl (KS.subc (d := $d) (a := $a) (k := $k) (by decide) (by decide) (by decide)
    (by decide)))
/-- `KS.mov` with its decidable side conditions. -/
macro "ksmov" d:term:max a:term:max : term =>
  `(HTF.of_HT rfl (KS.mov (d := $d) (a := $a) (by decide) (by decide) (by decide) (by decide)))
/-- `KS.clog` with its decidable side conditions. -/
macro "ksclog" d:term:max s:term:max w:term:max : term =>
  `(HTF.of_HT rfl (KS.clog (dst := $d) (src := $s) (w := $w) (by decide) (by decide) (by decide)
    (by decide)))

variable {m₀ : ℕ → ℕ} {F B S : ℕ}

/-! ### Costs of the stages -/

/-- Stage 1. -/
def cost1 (t _k : ℕ) : ℕ := 16 + (Arith.mulCost t + Arith.mulCost t)
/-- Stage 2. -/
def cost2 (t k : ℕ) : ℕ :=
  (1 + (dimKKT t k * (2 + Arith.mulCost (dimKKT t k) + 4) + 3)) +
    ((2 + ((dimKKT t k + 1) * (Arith.mulCost (k - 2) + 4) + 3)) +
    (Arith.mulCost (dimKKT t k) + (2 + (Arith.mulCost (dimKKT t k * dimKKT t k + 1) + 1))))
/-- Stage 3. -/
def cost3 (t k : ℕ) : ℕ :=
  Arith.mulCost (bigE t k) + (Arith.mulCost (bigE t k * bigE t k) + (1 + (1 +
    (Arith.mulCost t + (Arith.mulCost t + (1 + (Arith.mulCost (curv t k) +
    (Arith.mulCost (k - 2) + (Arith.mulCost (k - 2) + (Arith.mulCost t + (Arith.mulCost t +
    (Arith.mulCost (k - 1) + Arith.mulCost (nDim t k)))))))))))))
/-- Stage 4. -/
def cost4 (t k : ℕ) : ℕ :=
  clogCost (radInv t k) + (1 + (1 + (1 + (1 + (2 + (Arith.mulCost (nDim t k + 1) +
    (Arith.mulCost (logRad t k) + 2)))))))
/-- Stage 5. -/
def cost5 (t k : ℕ) : ℕ := clogCost (nDim t k + 1) + (Arith.mulCost (logRad t k) + 13)
/-- Stage 6. -/
def cost6 (t k : ℕ) : ℕ :=
  Arith.mulCost (nDim t k + 1) + (Arith.mulCost (nDim t k) +
    3 * Arith.mulCost (32 * nDim t k * (nDim t k + 1) + 1) +
    3 * Arith.mulCost (32 * nDim t k * (nDim t k + 1)) + 9)

/-- Stage 1: copies, `M`, `n`, `d`. -/
theorem st1_spec (hZ0 : ZeroFrom m₀ F) (t k : ℕ) :
    HTF S F (.seq cA cND) (KS m₀ F B rs0 (cv t k)) (KS m₀ F B rs1 (cv t k)) (cost1 t k) := by
  unfold cA cND
  refine HTF.mono (P := KS m₀ F B rs0 (cv t k))
    ((ksmov qT ZeroCost.gT).seq ((ksmov qK ZeroCost.gK).seq ((ksmov qKT ZeroCost.gKT).seq
      ((kssubc cK1 ZeroCost.gK 1).seq ((ksaddc cX ZeroCost.gK 1).seq ((kssubc cA0 ZeroCost.gK 2).seq
      ((ksadd cV qKT qKT).seq ((ksadd cV cV qKT).seq ((ksadd cV cV qT).seq (ksadd qM cV qT)))))))))
      |>.seq ((ksmul qN cK1 qT).seq (ksmul qD cX qT)))
    (fun _ h => h) (fun c h => h.sub ?_) ?_
  · clear h c
    simp only [rs1, List.forall_mem_cons]
    simp +decide [Function.update_apply, cv, nRows, nDim, dimKKT]
    ring
  · simp +decide [cv, cost1]

/-- Stage 2: `E`. -/
theorem st2_spec (hZ0 : ZeroFrom m₀ F) (t k : ℕ) :
    HTF S F (.seq cFact (.seq cPow cE)) (KS m₀ F B rs1 (cv t k)) (KS m₀ F B rs2 (cv t k))
      (cost2 t k) := by
  unfold cE
  refine HTF.mono (P := KS m₀ F B rs1 (cv t k))
    ((KS.fact hZ0 (by decide) (by decide)).seq ((KS.pow hZ0 (by decide) (by decide) (by decide)
      (by decide)).seq ((ksmul cU qD qD).seq ((ksaddc cU cU 1).seq ((ksmul qE qE cU).seq
      (ksadd qE qE qE))))))
    (fun _ h => h) (fun c h => h.sub ?_) ?_
  · clear h c
    simp only [rs2, rs1, List.forall_mem_cons]
    simp +decide [Function.update_apply, cv, bigE, entryBound]
    ring
  · simp +decide [cv, cost2]

/-- Stage 3: `n / r_K`. -/
theorem st3_spec (hZ0 : ZeroFrom m₀ F) (t k : ℕ) :
    HTF S F cRad (KS m₀ F B rs2 (cv t k)) (KS m₀ F B rs3 (cv t k)) (cost3 t k) := by
  unfold cRad
  refine HTF.mono (P := KS m₀ F B rs2 (cv t k))
    ((ksmul cR qE qE).seq ((ksmul cR cR cR).seq ((ksadd cR cR cR).seq ((ksadd cR cR cR).seq
      ((ksmul cC cA0 qT).seq ((ksmul cC cC qT).seq ((ksadd cC cC cC).seq ((ksmul cR cR cC).seq
      ((ksmul cR cR cA0).seq ((ksmul cR cR cA0).seq ((ksmul cR cR qT).seq ((ksmul cR cR qT).seq
      ((ksmul cR cR cK1).seq (ksmul cR cR qN))))))))))))))
    (fun _ h => h) (fun c h => h.sub ?_) ?_
  · clear h c
    simp only [rs3, rs2, rs1, List.forall_mem_cons]
    simp +decide [Function.update_apply, cv, radInv, curv]
    ring
  · simp +decide [cv, curv, cost3]
    ring_nf; omega

/-- Stage 4: `L`, `N`. -/
theorem st4_spec (hZ0 : ZeroFrom m₀ F) (t k : ℕ) :
    HTF S F cIt (KS m₀ F B rs3 (cv t k)) (KS m₀ F B rs4 (cv t k)) (cost4 t k) := by
  unfold cIt
  refine HTF.mono (P := KS m₀ F B rs3 (cv t k))
    ((ksclog cL cR cW).seq ((ksadd cX qN qN).seq ((ksadd cX cX cX).seq ((ksadd cX cX cX).seq
      ((ksadd cX cX cX).seq ((ksaddc cY qN 1).seq ((ksmul cX cX cY).seq ((ksmul cX cX cL).seq
      (ksaddc qIt cX 1)))))))))
    (fun _ h => h) (fun c h => h.sub ?_) ?_
  · clear h c
    simp only [rs4, rs3, rs2, rs1, List.forall_mem_cons]
    simp +decide [Function.update_apply, cv, iters, logRad]
    exact Or.inl (by ring)
  · simp +decide [cv, logRad, cost4]

/-- Stage 5: `p`. -/
theorem st5_spec (hZ0 : ZeroFrom m₀ F) (t k : ℕ) (hn : 1 ≤ nDim t k) :
    HTF S F cPrec (KS m₀ F B rs4 (cv t k)) (KS m₀ F B rs5 (cv t k)) (cost5 t k) := by
  unfold cPrec
  refine HTF.mono (P := KS m₀ F B rs4 (cv t k))
    ((ksclog cZ cY cW2).seq ((ksmul cV cY cL).seq ((ksadd cV cV cV).seq ((ksadd cV cV cV).seq
      ((ksadd cV cV cV).seq ((ksadd cV cV cV).seq ((ksadd cV cV cV).seq ((ksadd cV cV cV).seq
      ((ksadd cB cZ cZ).seq ((ksadd cB cB cZ).seq ((ksadd qP cV cB).seq (ksaddc qP qP 15))))))))))))
    (fun _ h => h) (fun c h => h.sub ?_) ?_
  · clear h c
    simp only [rs5, rs4, rs3, rs2, rs1, List.forall_mem_cons]
    simp +decide [Function.update_apply, cv, prec_eq hn]
    ring
  · simp +decide [cv, cost5]

/-- Stage 6: `cN`, `cD`. -/
theorem st6_spec (hZ0 : ZeroFrom m₀ F) (t k : ℕ) :
    HTF S F cCN (KS m₀ F B rs5 (cv t k)) (KS m₀ F B rs6 (cv t k)) (cost6 t k) := by
  unfold cCN
  refine HTF.mono (P := KS m₀ F B rs5 (cv t k))
    ((ksmul cV qN cY).seq ((ksadd cV cV cV).seq ((ksadd cV cV cV).seq ((ksadd cV cV cV).seq
      ((ksadd cV cV cV).seq ((ksadd cV cV cV).seq ((ksaddc cB cV 1).seq ((ksmul cU qN qN).seq
      ((ksmul qCN cU cB).seq ((ksmul qCN qCN cB).seq ((ksmul qCN qCN cB).seq ((kssubc cU cU 1).seq
      ((ksmul qCD cU cV).seq ((ksmul qCD qCD cV).seq (ksmul qCD qCD cV)))))))))))))))
    (fun _ h => h) (fun c h => h.sub ?_) ?_
  · clear h c
    simp only [rs6, rs5, rs4, rs3, rs2, rs1, List.forall_mem_cons]
    simp +decide [Function.update_apply, cv, cNum, cDen, sq]
    constructor <;> ring
  · simp +decide [cv, cost6]
    ring_nf; omega

/-! ### The phase -/

/-- The constants of `QRegs` for `t` cycles of length `k`. -/
def CRegs (t k : ℕ) (c : Config) : Prop :=
  c.reg qT = t ∧ c.reg qK = k ∧ c.reg qKT = t * k ∧ c.reg qN = nDim t k ∧
    c.reg qD = dimKKT t k ∧ c.reg qM = nRows t k ∧ c.reg qIt = iters t k ∧
    c.reg qP = prec t k ∧ c.reg qE = bigE t k ∧ c.reg qCN = cNum t k ∧ c.reg qCD = cDen t k

/-- The cost of `stepConsts`. -/
def constCost (t k : ℕ) : ℕ :=
  cost1 t k + (cost2 t k + (cost3 t k + (cost4 t k + (cost5 t k + cost6 t k))))

/-- **The constants phase**: from `gT = t`, `gK = k`, `gKT = kt` (and `n ≥ 1`), the constants
of `QRegs` in `qT … qCD`; memory, `rFREE`, `qBH` and the output unchanged; accessing only the
addresses below any `S ≥ F + constCost t k` (the scratch tables of the multiplications). -/
theorem stepConsts_spec (hZ0 : ZeroFrom m₀ F) (t k : ℕ) (hn : 1 ≤ nDim t k) :
    HTF S F stepConsts
      (fun c => c.mem = m₀ ∧ c.reg rFREE = F ∧ c.reg qBH = B ∧ c.out = [] ∧
        c.reg ZeroCost.gT = t ∧ c.reg ZeroCost.gK = k ∧ c.reg ZeroCost.gKT = k * t)
      (fun c => c.mem = m₀ ∧ c.reg rFREE = F ∧ c.reg qBH = B ∧ c.out = [] ∧ CRegs t k c)
      (constCost t k) := by
  have h := (st1_spec (S := S) (B := B) hZ0 t k).seq ((st2_spec hZ0 t k).seq ((st3_spec hZ0 t k).seq
    ((st4_spec hZ0 t k).seq ((st5_spec hZ0 t k hn).seq (st6_spec hZ0 t k)))))
  refine HTF.mono h (fun c ⟨h1, h2, h3, h4, h5, h6, h7⟩ => ⟨h1, h2, h3, h4, ?_⟩)
    (fun c h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩) le_rfl
  · simp only [rs0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true]
    simp +decide [cv, h5, h6, h7]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (rw [h.get (by decide)]; simp +decide [cv, Nat.mul_comm])

end STACS2027.Runtimes.QPRam.Parse
