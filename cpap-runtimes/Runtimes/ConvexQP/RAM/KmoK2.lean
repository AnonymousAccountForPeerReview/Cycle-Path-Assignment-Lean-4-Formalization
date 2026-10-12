module

public import Runtimes.ConvexQP.RAM.KmoK1
import Mathlib.Tactic

/-!
# Phases K, M, O on the RAM: Phase K, part 2 (`π_c = min_j L_{c,j}`)

For every cycle `c`: the running minimum of `L_{c,0}, …, L_{c,k−1}` (`minAcc`, a strict
comparison replaces the accumulator), stored at `Zn[tk + c]`. `minAcc_pi`: the result is
`I.pi Xs c` (`Inst.pi_eq_of`).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Kmo

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

/-! ### The running minimum -/

/-- `min (g 0, …, g (j − 1))`, and `g 0` for `j = 0`. -/
def minAcc (g : ℕ → ℤ) : ℕ → ℤ
  | 0 => g 0
  | j + 1 => min (minAcc g j) (g j)

theorem minAcc_le (g : ℕ → ℤ) : ∀ j, ∀ i < j, minAcc g j ≤ g i
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | j + 1, i, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · exact (min_le_left _ _).trans (minAcc_le g j i h)
    · exact min_le_right _ _

theorem minAcc_mem (g : ℕ → ℤ) : ∀ j, ∃ i, i < max j 1 ∧ g i = minAcc g j
  | 0 => ⟨0, by simp, rfl⟩
  | j + 1 => by
    obtain ⟨i, hi, he⟩ := minAcc_mem g j
    by_cases h : minAcc g j ≤ g j
    · exact ⟨i, by omega, by rw [minAcc, min_eq_left h, he]⟩
    · exact ⟨j, by omega, by rw [minAcc, min_eq_right (by omega)]⟩

/-- The `L` of cycle `c` on the options. -/
def gL (I : Inst) (Xs : Fin I.t → Fin I.k → ℤ) (c : ℕ) (j : ℕ) : ℤ := Lf I Xs (c * I.k + j)

/-- **The minimum is `π_c`.** -/
theorem minAcc_pi (I : Inst) (Xs : Fin I.t → Fin I.k → ℤ) (hk : 0 < I.k) {c : ℕ} (hc : c < I.t) :
    minAcc (gL I Xs c) I.k = I.pi Xs ⟨c, hc⟩ := by
  have hL : ∀ j : Fin I.k, gL I Xs c j = I.L Xs ⟨c, hc⟩ j := fun j => by
    rw [gL, Lf, show c * I.k + (j : ℕ) = (⟨c, hc⟩ : Fin I.t) * I.k + j from rfl, mulVec_Hflat]
  symm
  apply Inst.pi_eq_of
  · intro j; rw [← hL j]; exact minAcc_le _ _ _ j.2
  · obtain ⟨i, hi, he⟩ := minAcc_mem (gL I Xs c) I.k
    exact ⟨⟨i, by omega⟩, by rw [← hL, he]⟩

/-! ### The program -/

/-- One option: `acc := min(acc, L_{c,j})`. -/
def piInner : Stmt :=
  .seq (sload kX kLP) (.seq (slt kA kX kHR) (.seq (.ifz kA .skip (smov kHR kX))
    (addc kLP kLP 2)))

/-- One cycle: `acc := L_{c,0}`, the options, `Zn[tk + c] := acc`. -/
def piOuter : Stmt :=
  .seq (sload kHR kLP) (.seq (forUp kJJ qK piInner) (.seq (sstore kPP kHR) (addc kPP kPP 2)))

/-- Pointers of the loop. -/
def piInit : Stmt := .seq (mov kLP kKL) (.seq (.add kA qKT qKT) (.add kPP kPZN kA))

/-- `π_c := min_j L_{c,j}` into `Zn[tk + c]`. -/
def kPi : Stmt := .seq piInit (forUp kC qT piOuter)

variable {S : ℕ}

section Pi

variable (I : Inst) (Xs : Fin I.t → Fin I.k → ℤ) (F₀ bh bx : ℕ)

/-- `π_c` as computed. -/
def piV (c : ℕ) : ℤ := minAcc (gL I Xs c) I.k

/-- The registers and the memory inside cycle `c`, before option `j`. -/
def PiQ (m : ℕ → ℕ) (c j : ℕ) (cfg : Config) : Prop :=
  KGl I F₀ bh bx cfg ∧ cfg.mem = m ∧ cfg.reg kLP = (lay I F₀).pL + (c * I.k + j) * 2 ∧
    cfg.reg kPP = (lay I F₀).pZn + 2 * (I.t * I.k) + c * 2 ∧ cfg.reg kC = c

theorem PiQ_regs (m : ℕ → ℕ) (c j : ℕ) {W : List ℕ}
    (hW : ∀ r ∈ W, r ∈ rT :: (List.range' 400 50 ++ [kA, kX, kX + 1, kHR, kHR + 1, kJJ])) :
    Indep W (PiQ I F₀ bh bx m c j) := by
  have h0 : ∀ r ∈ [kLP, kPP, kC], r ∉ rT :: (List.range' 400 50 ++
      [kA, kX, kX + 1, kHR, kHR + 1, kJJ]) := by decide
  have hn : ∀ r ∈ [kLP, kPP, kC], r ∉ W := fun r hr h => h0 r hr (hW r h)
  have hs : ∀ r ∈ rT :: (List.range' 400 50 ++ [kA, kX, kX + 1, kHR, kHR + 1, kJJ]), r ∈ kW := by
    decide
  exact ((KGl.regIndep' I F₀ bh bx (fun r hr => hs r (hW r hr))).indep.and
    ((Indep.mem (· = m)).and ((Indep.reg (hn kLP (by decide))
      (· = (lay I F₀).pL + (c * I.k + j) * 2)).and
    ((Indep.reg (hn kPP (by decide)) (· = (lay I F₀).pZn + 2 * (I.t * I.k) + c * 2)).and
      (Indep.reg (hn kC (by decide)) (· = c))))))

variable {I Xs F₀ bh bx}

/-- **One option** of the minimum. -/
theorem piInner_spec (m : ℕ → ℕ) (c j : ℕ)
    (hL : SMem m ((lay I F₀).pL + (c * I.k + j) * 2) (gL I Xs c j))
    (hSL : (lay I F₀).pL + (c * I.k + j) * 2 + 1 < S) :
    HTB S piInner (fun cfg => (PiQ I F₀ bh bx m c j cfg ∧ SReg cfg kHR (minAcc (gL I Xs c) j)) ∧
        cfg.reg kJJ = j ∧ cfg.reg qK = I.k)
      (fun cfg => (PiQ I F₀ bh bx m c (j + 1) cfg ∧
        SReg cfg kHR (minAcc (gL I Xs c) (j + 1))) ∧ cfg.reg kJJ = j ∧ cfg.reg qK = I.k) 34 := by
  set u := gL I Xs c j
  set v := minAcc (gL I Xs c) j
  let Q : Config → Prop := fun cfg => PiQ I F₀ bh bx m c j cfg ∧ cfg.reg kJJ = j ∧
    cfg.reg qK = I.k
  have hQ : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ rT :: (List.range' 400 50 ++
      [kA, kX, kX + 1, kHR, kHR + 1])) → Indep W Q := fun hW =>
    (PiQ_regs I F₀ bh bx m c j (fun r hr => by
      have := hW r hr; simp only [List.mem_cons, List.mem_append] at this ⊢; tauto)).and
      ((Indep.reg (fun h => absurd (hW _ h) (by decide)) (· = j)).and
      (Indep.reg (fun h => absurd (hW _ h) (by decide)) (· = I.k)))
  have s1 := HTB.sload (S := S) (P := fun cfg => Q cfg ∧ SReg cfg kHR v) (d := kX) (p := kLP)
    (a := (lay I F₀).pL + (c * I.k + j) * 2) (z := u) (by decide) (by decide) (by decide)
    ((hQ (by decide)).and (indep_sreg (by decide) (by decide) v)) hSL
  have s2 := HTB.slt (S := S) (P := fun cfg => Q cfg ∧ SReg cfg kHR v ∧ SReg cfg kX u) (d := kA) (x := kX)
    (y := kHR) (u := u) (v := v) (by decide) (by decide)
    ((hQ (by decide)).and ((indep_sreg (by decide) (by decide) v).and
      (indep_sreg (by decide) (by decide) u)))
  have s3 : HTB S (.ifz kA .skip (smov kHR kX))
      (fun cfg => (Q cfg ∧ SReg cfg kHR v ∧ SReg cfg kX u) ∧ cfg.reg kA = if u < v then 1 else 0)
      (fun cfg => Q cfg ∧ SReg cfg kHR (min v u)) 5 := HTB.of_HT rfl <| by
    by_cases huv : u < v
    · have e : min v u = u := min_eq_right huv.le
      rw [e]
      refine (HT.ifz ?_ ?_).weaken le_rfl
      · exact HT.of_false fun cfg ⟨⟨_, h1⟩, h0⟩ => by simp [huv] at h1; omega
      · exact (HT.smov (P := Q) (d := kHR) (x := kX) (z := u) (by decide) (by decide) (by decide)
          (by decide) (hQ (by decide))).mono (fun cfg ⟨⟨⟨hq, _, hx⟩, _⟩, _⟩ => ⟨hq, hx⟩)
          (fun cfg h => h) le_rfl
    · have e : min v u = v := min_eq_left (not_lt.mp huv)
      rw [e]
      refine (HT.ifz ?_ ?_).weaken le_rfl
      · exact (HT.skip.weaken (by omega)).mono (fun cfg h => h)
          (fun cfg ⟨⟨⟨hq, hv, _⟩, _⟩, _⟩ => ⟨hq, hv⟩) le_rfl
      · exact HT.of_false fun cfg ⟨⟨_, h1⟩, h0⟩ => by simp [huv] at h1; omega
  have s4 : HTB S (addc kLP kLP 2) (fun cfg => Q cfg ∧ SReg cfg kHR (min v u))
      (fun cfg => (PiQ I F₀ bh bx m c (j + 1) cfg ∧
        SReg cfg kHR (minAcc (gL I Xs c) (j + 1))) ∧ cfg.reg kJJ = j ∧ cfg.reg qK = I.k) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg ⟨⟨⟨hk, hm, hlp, hpp, hc⟩, hj, hqk⟩, hacc⟩ => by
      refine ⟨⟨⟨(KGl.regIndep' I F₀ bh bx (W := wregs (addc kLP kLP 2)) (by decide)).run
        (by decide) hk, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
      all_goals simp +decide only [run_addc, setReg_reg, setReg_mem, ↓reduceIte, hm, hlp, hpp,
        hc, hj, hqk, minAcc]
      · ring
      · exact hacc
  refine ((s1.pre fun cfg ⟨⟨hq, hacc⟩, hj, hk⟩ => ⟨⟨⟨hq, hj, hk⟩, hacc⟩, hq.2.2.1,
    by rw [hq.2.1]; exact hL⟩).seq ((s2.pre fun cfg ⟨⟨hq, hacc⟩, hx⟩ => ⟨⟨hq, hacc, hx⟩, hx,
      hacc⟩).seq (s3.seq s4))).weaken (by omega)

variable (I Xs F₀ bh bx) in
/-- The state of the outer loop before cycle `c`. -/
def PiO (m : ℕ → ℕ) (c : ℕ) (cfg : Config) : Prop :=
  KGl I F₀ bh bx cfg ∧ cfg.mem = wrArr m ((lay I F₀).pZn + 2 * (I.t * I.k)) 2 (piV I Xs) c ∧
    cfg.reg kLP = (lay I F₀).pL + (c * I.k) * 2 ∧
    cfg.reg kPP = (lay I F₀).pZn + 2 * (I.t * I.k) + c * 2

/-- **One cycle** of the minimum. -/
theorem piOuter_spec (hk0 : 0 < I.k) (m : ℕ → ℕ) (hl : SArr m (lay I F₀).pL 2 (I.t * I.k) (Lf I Xs))
    {c : ℕ} (hc : c < I.t) (hS : (lay I F₀).fe ≤ S) :
    HTB S piOuter (fun cfg => PiO I Xs F₀ bh bx m c cfg ∧ cfg.reg kC = c ∧ cfg.reg qT = I.t)
      (fun cfg => PiO I Xs F₀ bh bx m (c + 1) cfg ∧ cfg.reg kC = c ∧ cfg.reg qT = I.t)
      (I.k * 38 + 13) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  set mc := wrArr m ((lay I F₀).pZn + 2 * (I.t * I.k)) 2 (piV I Xs) c with hmc
  have hck : c * I.k + I.k ≤ I.t * I.k := succ_mul_le I.k hc
  have hread : ∀ j < I.k, SMem mc ((lay I F₀).pL + (c * I.k + j) * 2) (gL I Xs c j) := by
    intro j hj
    have := hl (c * I.k + j) (by omega)
    exact ⟨(wrArr_of_out (le_refl 2) (Or.inr (by omega))).trans this.1,
      (wrArr_of_out (le_refl 2) (Or.inr (by omega))).trans this.2⟩
  have o1 := HTB.sload (S := S) (P := fun cfg => PiQ I F₀ bh bx mc c 0 cfg ∧ cfg.reg qT = I.t) (d := kHR)
    (p := kLP) (a := (lay I F₀).pL + (c * I.k + 0) * 2) (z := gL I Xs c 0) (by decide)
    (by decide) (by decide) ((PiQ_regs I F₀ bh bx mc c 0 (by decide)).and (Indep.reg
      (by decide) (· = I.t))) (by omega)
  have o2 := (HTB.forUpC (S := S) (i := kJJ) (n := qK) (N := I.k) (body := piInner)
    (fun j cfg => PiQ I F₀ bh bx mc c j cfg ∧ SReg cfg kHR (minAcc (gL I Xs c) j)) 34
    (by decide) (by decide) (by decide)
    (fun j => (PiQ_regs I F₀ bh bx mc c j (by decide)).and (indep_sreg (by decide) (by decide) _))
    (fun j hj => piInner_spec mc c j (hread j hj) (by omega))).frameReg
    (F := fun cfg => cfg.reg qT = I.t) (by indep)
  have o3 := HTB.sstore (S := S) (F := fun cfg => (KGl I F₀ bh bx cfg ∧ cfg.reg kC = c ∧
      cfg.reg kLP = (lay I F₀).pL + ((c + 1) * I.k) * 2) ∧ cfg.reg qT = I.t) (p := kPP) (x := kHR)
    (a := (lay I F₀).pZn + 2 * (I.t * I.k) + c * 2) (z := minAcc (gL I Xs c) I.k) (m := mc)
    (by decide) (by decide) (by decide)
    (((KGl.regIndep' I F₀ bh bx (by decide)).and (by indep)).and (by indep)) (by omega)
  have o4 : HTB S (addc kPP kPP 2) (fun cfg => ((KGl I F₀ bh bx cfg ∧ cfg.reg kC = c ∧
        cfg.reg kLP = (lay I F₀).pL + ((c + 1) * I.k) * 2) ∧ cfg.reg qT = I.t) ∧
        SReg cfg kHR (minAcc (gL I Xs c) I.k) ∧
        cfg.reg kPP = (lay I F₀).pZn + 2 * (I.t * I.k) + c * 2 ∧
        cfg.mem = upd (upd mc ((lay I F₀).pZn + 2 * (I.t * I.k) + c * 2)
          (sgnBit (minAcc (gL I Xs c) I.k))) ((lay I F₀).pZn + 2 * (I.t * I.k) + c * 2 + 1)
          (minAcc (gL I Xs c) I.k).natAbs)
      (fun cfg => PiO I Xs F₀ bh bx m (c + 1) cfg ∧ cfg.reg kC = c ∧ cfg.reg qT = I.t) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg ⟨⟨⟨hk, hc', hlp⟩, hqt⟩, _, hpp, hm⟩ => by
      refine ⟨⟨(KGl.regIndep' I F₀ bh bx (W := wregs (addc kPP kPP 2)) (by decide)).run
        (by decide) hk, ?_, ?_, ?_⟩, ?_, ?_⟩
      all_goals simp +decide only [run_addc, setReg_reg, setReg_mem, ↓reduceIte, hm, hlp, hpp,
        hc', hqt]
      · rw [wrArr_succ]; rfl
      · ring
  refine ((o1.pre fun cfg ⟨⟨hk, hm, hlp, hpp⟩, hc', hqt⟩ => ⟨⟨⟨hk, hm, by rw [hlp]; ring, hpp,
    hc'⟩, hqt⟩, by rw [hlp]; ring, by rw [hm]; exact hread 0 hk0⟩).seq
    ((o2.pre fun cfg ⟨⟨hq, hqt⟩, hacc⟩ => ⟨⟨⟨hq, hacc⟩, by
      have := hq.1.glob.qregs; rw [qregs_iff] at this; exact this.2.1⟩, hqt⟩).seq
    ((o3.pre fun cfg ⟨⟨⟨⟨hk, hm, hlp, hpp, hc'⟩, hacc⟩, _, _⟩, hqt⟩ => ⟨⟨⟨hk, hc', by
      rw [hlp]; ring⟩, hqt⟩, hacc, hpp, hm⟩).seq o4))).weaken (by omega)

/-- **`π`**: `Zn[tk + c] := π_c` for all cycles. -/
theorem kPi_spec (hk0 : 0 < I.k) (m : ℕ → ℕ)
    (hl : SArr m (lay I F₀).pL 2 (I.t * I.k) (Lf I Xs)) (hS : (lay I F₀).fe ≤ S) :
    HTB S kPi (fun cfg => KGl I F₀ bh bx cfg ∧ cfg.mem = m)
      (fun cfg => KGl I F₀ bh bx cfg ∧
        cfg.mem = wrArr m ((lay I F₀).pZn + 2 * (I.t * I.k)) 2 (piV I Xs) I.t)
      (I.t * (I.k * 38 + 17) + 7) := by
  have h0 : HTB S piInit (fun cfg => KGl I F₀ bh bx cfg ∧ cfg.mem = m)
      (fun cfg => PiO I Xs F₀ bh bx m 0 cfg ∧ cfg.reg qT = I.t) 4 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun cfg ⟨hk, hm⟩ => by
      have hq := hk.glob.qregs
      rw [qregs_iff] at hq
      refine ⟨⟨(KGl.regIndep' I F₀ bh bx (W := wregs piInit) (by decide)).run (by decide) hk, ?_,
        ?_, ?_⟩, ?_⟩
      all_goals simp +decide only [piInit, run_seq', run_mov, run_add, setReg_reg, setReg_mem,
        ↓reduceIte, hm, hk.pL, hk.glob.pZn, hq.1, hq.2.2.1]
      · rfl
      · ring
      · ring
  have hl := HTB.forUpC (S := S) (i := kC) (n := qT) (N := I.t) (body := piOuter) (PiO I Xs F₀ bh bx m)
    (I.k * 38 + 13) (by decide) (by decide) (by decide)
    (fun c => ((KGl.regIndep' I F₀ bh bx (by decide)).indep.and (by indep)))
    (fun c hc => piOuter_spec hk0 m hl hc hS)
  exact (h0.seq hl).mono (fun _ h => h) (fun cfg ⟨⟨hk, hm, _⟩, _⟩ => ⟨hk, hm⟩)
    (le_of_eq (by ring))

end Pi

end STACS2027.Runtimes.QPRam.Kmo
