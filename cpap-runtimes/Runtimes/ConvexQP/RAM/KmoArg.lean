module

public import Runtimes.ConvexQP.RAM.KmoStepA
import Mathlib.Tactic

/-!
# Phases K, M, O on the RAM: the blocking row (`argMinRatio`)

`scan` runs over the rows `i < M` in order, as `argMinRatio ω σ` (`Move.lean`) folds `amStep`:
a row with `ω_i > 0` (sign bit `0`, magnitude `≠ 0`) becomes the best row if there is none yet
(`kFL = 0`) or if `σ_i ω_b < σ_b ω_i` (cross-multiplication with `smul`, `slt`); ties keep the
earlier row. The best row is kept as its row pointer `pG + b gs` (`kBP`) with `σ_b`, `ω_b` (`kSB`,
`kOB`). `scan_spec`: afterwards the registers represent `argMinRatio ω σ` (`AccRep`).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Kmo

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

/-- A second scratch pair `533, 534`. -/
abbrev kY : ℕ := 533

/-- The registers written by the scan: `rT`, the library, `522–539`. -/
def scanW : List ℕ := rT :: (List.range' 400 50 ++ List.range' 522 18)

theorem scrW_sub_scanW : ∀ r ∈ scrW, r ∈ scanW := by decide

variable {S : ℕ}

/-- The registers representing the accumulator of the scan. -/
def AccRep {M : ℕ} (pG gs : ℕ) (ω σ : Fin M → ℤ) : Option (Fin M) → Config → Prop
  | none, c => c.reg kFL = 0
  | some b, c => c.reg kFL = 1 ∧ c.reg kBP = pG + b * gs ∧ SReg c kSB (σ b) ∧ SReg c kOB (ω b)

/-- The best row so far: a new best row. -/
def scSet : Stmt := .seq (.const kFL 1) (.seq (mov kBP kPS) (.seq (sload kOB kP1) (sload kSB kP2)))

/-- Compare `σ_i / ω_i` with the best ratio (`ω_i` in `kX`). -/
def scCmp : Stmt :=
  .seq (sload kY kP2) (.seq (smul kY kY kOB) (.seq (smul kX kSB kX) (.seq (slt kA kY kX)
    (.ifz kA .skip scSet))))

/-- A row with `ω_i > 0`. -/
def scPos : Stmt := .ifz kFL scSet scCmp

/-- One row of the scan. -/
def scBody : Stmt :=
  .seq (sload kX kP1) (.seq (.ifz kX (.ifz (kX + 1) .skip scPos) .skip)
    (.seq (addc kP1 kP1 2) (.seq (addc kP2 kP2 2) (.add kPS kPS kGS))))

/-- The scan over the rows `i < reg qM`. -/
def scan : Stmt :=
  .seq (.seq (.const kFL 0) (.seq (mov kP1 kPOM) (.seq (mov kP2 kPSG) (mov kPS kPG))))
    (forUp kJ qM scBody)

section Scan

variable {M : ℕ} (R : Config → Prop) (m₀ : ℕ → ℕ) (pom psg pG gs : ℕ) (ω σ : Fin M → ℤ)

/-- The accumulator after `i` rows. -/
def accAt (i : ℕ) : Option (Fin M) := ((List.finRange M).take i).foldl (amStep ω σ) none

theorem accAt_succ {i : ℕ} (hi : i < M) :
    accAt ω σ (i + 1) = amStep ω σ (accAt ω σ i) ⟨i, hi⟩ := by
  unfold accAt
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem (by simpa using hi)]
  simp

theorem accAt_M : accAt ω σ M = argMinRatio ω σ := by
  unfold accAt argMinRatio
  rw [List.take_of_length_le (by simp)]

/-- The pointers of the scan before row `i`. -/
def ScQ (i : ℕ) (c : Config) : Prop :=
  R c ∧ c.mem = m₀ ∧ c.reg kP1 = pom + i * 2 ∧ c.reg kP2 = psg + i * 2 ∧ c.reg kPS = pG + i * gs

variable {R m₀ pom psg pG gs ω σ}

/-- The registers the body of the scan writes (besides the pointers). -/
def scBW : List ℕ :=
  rT :: (List.range' 400 50 ++ [kFL, kBP, kSB, kSB + 1, kOB, kOB + 1, kX, kX + 1, kY, kY + 1, kA,
    kJ])

theorem scBW_sub : ∀ r ∈ scBW, r ∈ scanW := by decide

theorem ScQ_indep (hR : RegIndep scanW R) (i : ℕ) {W : List ℕ} (hW : ∀ r ∈ W, r ∈ scBW) :
    Indep W (ScQ R m₀ pom psg pG gs i) :=
  (hR.mono fun r hr => scBW_sub r (hW r hr)).indep.and ((Indep.mem (· = m₀)).and
    ((Indep.reg (fun h => absurd (hW _ h) (by decide)) (· = pom + i * 2)).and
    ((Indep.reg (fun h => absurd (hW _ h) (by decide)) (· = psg + i * 2)).and
    (Indep.reg (fun h => absurd (hW _ h) (by decide)) (· = pG + i * gs)))))

theorem AccRep_indep {M : ℕ} (pG gs : ℕ) (ω σ : Fin M → ℤ) (acc : Option (Fin M)) {W : List ℕ}
    (hW : ∀ r ∈ W, r ∈ rT :: (List.range' 400 50 ++ [kX, kX + 1, kY, kY + 1, kA, kP1, kP2, kPS,
      kJ])) : Indep W (AccRep pG gs ω σ acc) := by
  have h0 : ∀ r ∈ [kFL, kBP, kSB, kSB + 1, kOB, kOB + 1], r ∉ rT :: (List.range' 400 50 ++
      [kX, kX + 1, kY, kY + 1, kA, kP1, kP2, kPS, kJ]) := by decide
  have hn : ∀ r ∈ [kFL, kBP, kSB, kSB + 1, kOB, kOB + 1], r ∉ W := fun r hr h => h0 r hr (hW r h)
  cases acc with
  | none => exact Indep.reg (hn kFL (by decide)) (· = 0)
  | some b =>
    exact (Indep.reg (hn kFL (by decide)) (· = 1)).and ((Indep.reg (hn kBP (by decide))
      (· = pG + b * gs)).and ((indep_sreg (hn kSB (by decide)) (hn (kSB + 1) (by decide)) _).and
      (indep_sreg (hn kOB (by decide)) (hn (kOB + 1) (by decide)) _)))

/-- Setting the best row to the current row `i`. -/
theorem scSet_spec (hR : RegIndep scanW R) {i : ℕ} (hi : i < M)
    (hω : SMem m₀ (pom + i * 2) (ω ⟨i, hi⟩)) (hσ : SMem m₀ (psg + i * 2) (σ ⟨i, hi⟩))
    (hSω : pom + i * 2 + 1 < S) (hSσ : psg + i * 2 + 1 < S) :
    HTB S scSet (ScQ R m₀ pom psg pG gs i)
      (fun c => ScQ R m₀ pom psg pG gs i c ∧ AccRep pG gs ω σ (some ⟨i, hi⟩) c) 11 :=
  HTB.run_le (by decide) (by decide) fun c ⟨hc, hm, h1, h2, hps⟩ => by
    refine ⟨by addr_ok [scSet, sload, h1, h2], ⟨(hR.mono (by decide)).run (by decide) hc, ?_, ?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩,
      ⟨?_, ?_⟩⟩ <;>
    simp +decide only [scSet, sload, run_seq', run_const, run_mov, run_load, run_addc, setReg_reg,
      setReg_mem, ↓reduceIte, hm, h1, h2, hps]
    · exact hσ.1
    · exact hσ.2
    · exact hω.1
    · exact hω.2

/-- The frame facts of the scan: `ZeroFrom` for the multiplications. -/
def ScZ (R : Config → Prop) (m₀ : ℕ → ℕ) : Prop := ∀ c, R c → ZeroFrom m₀ (c.reg rFREE)

/-- The space of the scan: the multiplications' tables (`2 B` cells from `rFREE`) below `S`. -/
def ScS (R : Config → Prop) (B S : ℕ) : Prop := ∀ c, R c → c.reg rFREE + 2 * B ≤ S

/-- Comparing the current row `i` (`ω_i > 0`) with the best row `b`. -/
theorem scCmp_spec (hR : RegIndep scanW R) (hZ : ScZ R m₀) {i : ℕ} (hi : i < M)
    (hω : SMem m₀ (pom + i * 2) (ω ⟨i, hi⟩)) (hσ : SMem m₀ (psg + i * 2) (σ ⟨i, hi⟩))
    (hpos : 0 < ω ⟨i, hi⟩) (b : Fin M) (B : ℕ) (hB : ∀ j, Nat.size (ω j).natAbs ≤ B)
    (hSB : ScS R B S) (hSω : pom + i * 2 + 1 < S) (hSσ : psg + i * 2 + 1 < S) :
    HTB S scCmp (fun c => (ScQ R m₀ pom psg pG gs i c ∧ SReg c kX (ω ⟨i, hi⟩)) ∧
        AccRep pG gs ω σ (some b) c)
      (fun c => ScQ R m₀ pom psg pG gs i c ∧
        AccRep pG gs ω σ (amStep ω σ (some b) ⟨i, hi⟩) c)
      (smulCost (ω b) + smulCost (ω ⟨i, hi⟩) + 63) := by
  have hZ' : ∀ {P : Config → Prop}, (∀ c, P c → ScQ R m₀ pom psg pG gs i c) →
      ∀ c, P c → ZeroFrom c.mem (c.reg rFREE) := fun hP c hc => by
    obtain ⟨hc', hm, _⟩ := hP c hc; rw [hm]; exact hZ c hc'
  have hS' : ∀ {P : Config → Prop}, (∀ c, P c → ScQ R m₀ pom psg pG gs i c) → ∀ (j : Fin M),
      ∀ c, P c → c.reg rFREE + 2 * Nat.size (ω j).natAbs ≤ S := fun hP j c hc => by
    have := hSB c (hP c hc).1; have := hB j; omega
  have hA := fun W hW => AccRep_indep (W := W) pG gs ω σ (some b) hW
  have hQ := fun W hW => ScQ_indep (R := R) (m₀ := m₀) (pom := pom) (psg := psg) (pG := pG)
    (gs := gs) hR i (W := W) hW
  -- `kY := σ_i`
  have c1 := HTB.sload (P := fun c => (ScQ R m₀ pom psg pG gs i c ∧ SReg c kX (ω ⟨i, hi⟩)) ∧
      AccRep pG gs ω σ (some b) c) (d := kY) (p := kP2) (a := psg + i * 2) (z := σ ⟨i, hi⟩)
    (by decide) (by decide) (by decide)
    (((hQ _ (by decide)).and (indep_sreg (by decide) (by decide) _)).and (hA _ (by decide))) hSσ
  -- `kY := σ_i ω_b`
  have c2 := HTB.smul (P := fun c => (ScQ R m₀ pom psg pG gs i c ∧ SReg c kX (ω ⟨i, hi⟩)) ∧
      AccRep pG gs ω σ (some b) c) (d := kY) (x := kY) (y := kOB) (u := σ ⟨i, hi⟩) (v := ω b)
    (by decide) (by decide) (by decide)
    (((hQ _ (by decide)).and (indep_sreg (by decide) (by decide) _)).and (hA _ (by decide)))
    (hZ' fun c h => h.1.1) (hS' (fun c h => h.1.1) b)
  -- `kX := σ_b ω_i`
  have c3 := HTB.smul (P := fun c => ScQ R m₀ pom psg pG gs i c ∧ AccRep pG gs ω σ (some b) c ∧
      SReg c kY (σ ⟨i, hi⟩ * ω b)) (d := kX) (x := kSB) (y := kX) (u := σ b) (v := ω ⟨i, hi⟩)
    (by decide) (by decide) (by decide)
    ((hQ _ (by decide)).and ((hA _ (by decide)).and (indep_sreg (by decide) (by decide) _)))
    (hZ' fun c h => h.1) (hS' (fun c h => h.1) ⟨i, hi⟩)
  have c4 := HTB.slt (S := S) (P := fun c => ScQ R m₀ pom psg pG gs i c ∧ AccRep pG gs ω σ (some b) c)
    (d := kA) (x := kY) (y := kX) (u := σ ⟨i, hi⟩ * ω b) (v := σ b * ω ⟨i, hi⟩)
    (by decide) (by decide) ((hQ _ (by decide)).and (hA _ (by decide)))
  have hstep : amStep ω σ (some b) ⟨i, hi⟩ = if σ ⟨i, hi⟩ * ω b < σ b * ω ⟨i, hi⟩ then
      some ⟨i, hi⟩ else some b := by simp [amStep, hpos]
  have c5 : HTB S (.ifz kA .skip scSet) (fun c => (ScQ R m₀ pom psg pG gs i c ∧
        AccRep pG gs ω σ (some b) c) ∧
        c.reg kA = if σ ⟨i, hi⟩ * ω b < σ b * ω ⟨i, hi⟩ then 1 else 0)
      (fun c => ScQ R m₀ pom psg pG gs i c ∧ AccRep pG gs ω σ (amStep ω σ (some b) ⟨i, hi⟩) c)
      12 := by
    rw [hstep]
    by_cases hlt : σ ⟨i, hi⟩ * ω b < σ b * ω ⟨i, hi⟩
    · simp only [hlt, ↓reduceIte]
      refine (HTB.ifz ?_ ?_).weaken le_rfl
      · exact HTB.of_false fun c ⟨⟨_, h1⟩, h0⟩ => by rw [h1] at h0; exact absurd h0 (by decide)
      · exact (scSet_spec hR hi hω hσ hSω hSσ).mono (fun c ⟨⟨⟨hc, _⟩, _⟩, _⟩ => hc) (fun c h => h)
          (by omega)
    · simp only [hlt, ↓reduceIte]
      refine (HTB.ifz ?_ ?_).weaken le_rfl
      · exact (HTB.skip.weaken (by omega)).mono (fun c h => h) (fun c ⟨⟨h, _⟩, _⟩ => h) le_rfl
      · exact HTB.of_false fun c ⟨⟨_, h1⟩, h0⟩ => h0 h1
  refine ((c1.pre fun c h => ⟨h, h.1.1.2.2.2.1, by rw [h.1.1.2.1]; exact hσ⟩).seq
    ((c2.pre fun c ⟨h, hy⟩ => ⟨h, hy, h.2.2.2.2⟩).seq
    ((c3.pre fun c ⟨⟨⟨hq, hx⟩, ha⟩, hy⟩ => ⟨⟨hq, ha, hy⟩, ha.2.2.1, hx⟩).seq
    ((c4.pre fun c ⟨⟨hq, ha, hy⟩, hx⟩ => ⟨⟨hq, ha⟩, hy, hx⟩).seq c5)))).weaken ?_
  simp only [smulCost, gCost]
  omega

/-- A row with `ω_i > 0`. -/
theorem scPos_spec (hR : RegIndep scanW R) (hZ : ScZ R m₀) {i : ℕ} (hi : i < M)
    (hω : SMem m₀ (pom + i * 2) (ω ⟨i, hi⟩)) (hσ : SMem m₀ (psg + i * 2) (σ ⟨i, hi⟩))
    (hpos : 0 < ω ⟨i, hi⟩) (B : ℕ) (hB : ∀ j, Nat.size (ω j).natAbs ≤ B)
    (acc : Option (Fin M)) (hSB : ScS R B S) (hSω : pom + i * 2 + 1 < S)
    (hSσ : psg + i * 2 + 1 < S) :
    HTB S scPos (fun c => (ScQ R m₀ pom psg pG gs i c ∧ SReg c kX (ω ⟨i, hi⟩)) ∧
        AccRep pG gs ω σ acc c)
      (fun c => ScQ R m₀ pom psg pG gs i c ∧ AccRep pG gs ω σ (amStep ω σ acc ⟨i, hi⟩) c)
      (62 * B + 134) := by
  cases acc with
  | none =>
    have e : amStep ω σ none ⟨i, hi⟩ = some ⟨i, hi⟩ := by simp [amStep, hpos]
    rw [e]
    refine (HTB.ifz (b := 62 * B + 133) ?_ ?_).weaken (by omega)
    · exact (scSet_spec hR hi hω hσ hSω hSσ).mono (fun c ⟨⟨⟨hc, _⟩, _⟩, _⟩ => hc) (fun c h => h)
        (by omega)
    · exact HTB.of_false fun c ⟨⟨_, h1⟩, h0⟩ => h0 h1
  | some b =>
    refine (HTB.ifz ?_ ?_).weaken le_rfl
    · exact HTB.of_false fun c ⟨⟨_, h1, _⟩, h0⟩ => by rw [h1] at h0; exact absurd h0 (by decide)
    · refine (scCmp_spec hR hZ hi hω hσ hpos b B hB hSB hSω hSσ).mono (fun c ⟨h, _⟩ => h) (fun c h => h) ?_
      have h1 := hB b
      have h2 := hB ⟨i, hi⟩
      simp only [smulCost, gCost]
      omega

/-- The test `ω_i > 0` and the update of the accumulator. -/
theorem scTest_spec (hR : RegIndep scanW R) (hZ : ScZ R m₀) {i : ℕ} (hi : i < M)
    (hω : SMem m₀ (pom + i * 2) (ω ⟨i, hi⟩)) (hσ : SMem m₀ (psg + i * 2) (σ ⟨i, hi⟩))
    (B : ℕ) (hB : ∀ j, Nat.size (ω j).natAbs ≤ B) (acc : Option (Fin M)) (hSB : ScS R B S)
    (hSω : pom + i * 2 + 1 < S) (hSσ : psg + i * 2 + 1 < S) :
    HTB S (.ifz kX (.ifz (kX + 1) .skip scPos) .skip)
      (fun c => (ScQ R m₀ pom psg pG gs i c ∧ SReg c kX (ω ⟨i, hi⟩)) ∧
        AccRep pG gs ω σ acc c)
      (fun c => ScQ R m₀ pom psg pG gs i c ∧ AccRep pG gs ω σ (amStep ω σ acc ⟨i, hi⟩) c)
      (62 * B + 136) := by
  by_cases hpos : 0 < ω ⟨i, hi⟩
  · refine (HTB.ifz (HTB.ifz ?_ ?_) ?_).weaken le_rfl
    · exact HTB.of_false fun c ⟨⟨⟨⟨_, _, h1⟩, _⟩, _⟩, h0⟩ => by
        rw [h1] at h0; omega
    · exact (scPos_spec hR hZ hi hω hσ hpos B hB acc hSB hSω hSσ).mono (fun c ⟨⟨h, _⟩, _⟩ => h)
        (fun c h => h) (by omega)
    · exact HTB.of_false fun c ⟨⟨⟨_, h1, _⟩, _⟩, h0⟩ => by
        rw [h1] at h0; simp [sgnBit, show ¬ ω ⟨i, hi⟩ < 0 by omega] at h0
  · have e : amStep ω σ acc ⟨i, hi⟩ = acc := by simp [amStep, hpos]
    rw [e]
    refine (HTB.ifz (HTB.ifz (b := 62 * B + 134) ?_ ?_) ?_).weaken (by omega)
    · exact (HTB.skip.weaken (by omega)).mono (fun c h => h)
        (fun c ⟨⟨⟨⟨hq, _⟩, ha⟩, _⟩, _⟩ => ⟨hq, ha⟩) le_rfl
    · exact HTB.of_false fun c ⟨⟨⟨⟨_, h0', h1⟩, _⟩, h0⟩, hne⟩ => by
        rw [h1] at hne; rw [h0'] at h0
        simp only [sgnBit] at h0
        split_ifs at h0
        omega
    · exact (HTB.skip.weaken (by omega)).mono (fun c h => h)
        (fun c ⟨⟨⟨hq, _⟩, ha⟩, _⟩ => ⟨hq, ha⟩) le_rfl

variable (R m₀ pom psg pG gs ω σ) in
/-- The state of the scan before row `i`. -/
def ScInv (i : ℕ) (c : Config) : Prop :=
  ScQ R m₀ pom psg pG gs i c ∧ AccRep pG gs ω σ (accAt ω σ i) c

/-- **One row of the scan.** -/
theorem scBody_spec (hR : RegIndep scanW R) (hZ : ScZ R m₀) (hgs : ∀ c, R c → c.reg kGS = gs)
    {i : ℕ} (hi : i < M)
    (hω : SMem m₀ (pom + i * 2) (ω ⟨i, hi⟩)) (hσ : SMem m₀ (psg + i * 2) (σ ⟨i, hi⟩))
    (B : ℕ) (hB : ∀ j, Nat.size (ω j).natAbs ≤ B) (hSB : ScS R B S)
    (hSω : pom + i * 2 + 1 < S) (hSσ : psg + i * 2 + 1 < S) :
    HTB S scBody (ScInv R m₀ pom psg pG gs ω σ i) (ScInv R m₀ pom psg pG gs ω σ (i + 1))
      (62 * B + 145) := by
  have hQ := fun W hW => ScQ_indep (R := R) (m₀ := m₀) (pom := pom) (psg := psg) (pG := pG)
    (gs := gs) hR i (W := W) hW
  have b1 := HTB.sload (P := fun c => ScQ R m₀ pom psg pG gs i c ∧
      AccRep pG gs ω σ (accAt ω σ i) c) (d := kX) (p := kP1) (a := pom + i * 2) (z := ω ⟨i, hi⟩)
    (by decide) (by decide) (by decide)
    ((hQ _ (by decide)).and (AccRep_indep pG gs ω σ _ (by decide))) hSω
  have b2 := scTest_spec (pG := pG) (gs := gs) hR hZ hi hω hσ B hB (accAt ω σ i) hSB hSω hSσ
  have b3 : HTB S (.seq (addc kP1 kP1 2) (.seq (addc kP2 kP2 2) (.add kPS kPS kGS)))
      (fun c => ScQ R m₀ pom psg pG gs i c ∧ AccRep pG gs ω σ (amStep ω σ (accAt ω σ i) ⟨i, hi⟩) c)
      (ScInv R m₀ pom psg pG gs ω σ (i + 1)) 5 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨hc, hm, h1, h2, hps⟩, ha⟩ => by
      rw [ScInv, accAt_succ ω σ hi]
      refine ⟨⟨(hR.mono (by decide)).run (by decide) hc, ?_, ?_, ?_, ?_⟩,
        (AccRep_indep pG gs ω σ _ (by decide)).run (by decide) rfl rfl ha⟩ <;>
      simp +decide only [run_seq', run_addc, run_add, setReg_reg, setReg_mem, ↓reduceIte, hm, h1,
        h2, hps, hgs c hc]
      · ring
      · ring
      · ring
  exact ((b1.pre fun c h => ⟨h, h.1.2.2.1, by rw [h.1.2.1]; exact hω⟩).seq
    ((b2.pre fun c ⟨⟨hq, ha⟩, hx⟩ => ⟨⟨hq, hx⟩, ha⟩).seq b3)).weaken (by omega)

/-- **The scan** over the rows `i < M`: afterwards the registers represent `argMinRatio ω σ`. -/
theorem scan_spec (hR : RegIndep scanW R) (hZ : ScZ R m₀)
    (hRg : ∀ c, R c → c.reg kGS = gs ∧ c.reg kPOM = pom ∧ c.reg kPSG = psg ∧ c.reg kPG = pG ∧
      c.reg qM = M)
    (hω : ∀ i : Fin M, SMem m₀ (pom + i * 2) (ω i)) (hσ : ∀ i : Fin M, SMem m₀ (psg + i * 2) (σ i))
    (B : ℕ) (hB : ∀ j, Nat.size (ω j).natAbs ≤ B) (hSB : ScS R B S)
    (hSω : pom + M * 2 ≤ S) (hSσ : psg + M * 2 ≤ S) :
    HTB S scan (fun c => R c ∧ c.mem = m₀)
      (fun c => R c ∧ c.mem = m₀ ∧ AccRep pG gs ω σ (argMinRatio ω σ) c)
      (M * (62 * B + 149) + 10) := by
  have h0 : HTB S (.seq (.const kFL 0) (.seq (mov kP1 kPOM) (.seq (mov kP2 kPSG) (mov kPS kPG))))
      (fun c => R c ∧ c.mem = m₀) (fun c => ScInv R m₀ pom psg pG gs ω σ 0 c ∧ c.reg qM = M) 7 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hc, hm⟩ => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hRg c hc
      refine ⟨⟨⟨(hR.mono (by decide)).run (by decide) hc, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩ <;>
      simp +decide only [run_seq', run_const, run_mov, setReg_reg, setReg_mem, ↓reduceIte, hm, h2,
        h3, h4, h5, accAt, List.take_zero, List.foldl_nil, AccRep] <;> ring
  have hl := HTB.forUpC (S := S) (i := kJ) (n := qM) (N := M) (body := scBody)
    (ScInv R m₀ pom psg pG gs ω σ) (62 * B + 145) (by decide) (by decide) (by decide)
    (fun j => (ScQ_indep hR j (by decide)).and (AccRep_indep pG gs ω σ _ (by decide)))
    (fun j hj => (scBody_spec hR hZ (fun c hc => (hRg c hc).1) hj (hω ⟨j, hj⟩) (hσ ⟨j, hj⟩) B
      hB hSB (addr_lt_of_stride (le_refl 2) hSω hj) (addr_lt_of_stride (le_refl 2) hSσ hj)).frameReg (F := fun c => c.reg kJ = j ∧ c.reg qM = M) (by indep))
  refine (h0.seq hl).mono (fun c h => h)
    (fun c ⟨⟨⟨hc, hm, _⟩, ha⟩, _⟩ => ⟨hc, hm, by rwa [accAt_M] at ha⟩) (le_of_eq (by ring))

end Scan

end STACS2027.Runtimes.QPRam.Kmo
