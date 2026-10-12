module

public import Runtimes.ConvexQP.RAM.KmoK5
import Mathlib.Tactic

/-!
# Phases K, M, O on the RAM: Phase K, part 6 (the rows of `(c, j)`)

For every option `a = c k + j` (nested loop over `c < t`, `j < k`): the test
`Xs_a ≤ L_a − π_c` (`zTest`, `zf_iff`: it decides `Zf a`, i.e. `kktZ`), then the three rows of
`(c, j)`: `rowsN` (`a ∉ Z`: `+H_a`/`−π_c`, `−H_a`/`+π_c`, `−e_a`) or `rowsZ` (`a ∈ Z`: `+e_a`,
`−e_a`, `−H_a`/`+π_c`), and the pointers advance (`xAdv`). `kX_spec`: all rows of `G` and `h'`
are written.
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Kmo

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

/-- Scratch pair of the test (`530, 531`). -/
abbrev kZt : ℕ := 530

/-! ### The test `Xs_a ≤ L_a − π_c` -/

variable {I : Inst} {Xs : Fin I.t → Fin I.k → ℤ}

/-- **The test of Phase K** decides the pattern `Z` (`kktZ`). -/
theorem zf_iff {a : ℕ} (ha : a < I.t * I.k) :
    Zf I Xs a = decide (ZnF₀ I Xs a ≤ Lf I Xs a - ZnF₀ I Xs (I.t * I.k + a / I.k)) := by
  have hc := div_lt_of_lt_tk ha
  have hj := mod_lt_of_lt_tk ha
  have e1 : ZnF₀ I Xs a = Xs ⟨a / I.k, hc⟩ ⟨a % I.k, hj⟩ := by
    rw [ZnF₀_x I Xs ha]; simp [flat, ha]
  have e2 : Lf I Xs a = I.L Xs ⟨a / I.k, hc⟩ ⟨a % I.k, hj⟩ := by
    rw [Lf, ← mulVec_Hflat I Xs ⟨a / I.k, hc⟩ ⟨a % I.k, hj⟩]
    congr 1
    exact (Nat.div_add_mod' a I.k).symm
  rw [e1, e2, ZnF₀_p I Xs hc]
  simp [Zf, ha, kktZ]

/-- `Xs_a ≤ L_a − π_c` into `kA`. -/
def zTest : Stmt :=
  .seq (sload kX kLP) (.seq (sload kZt kPP) (.seq (ssub kX kX kZt) (.seq (sload kZt kXP)
    (sle kA kZt kX))))

/-- The three rows of an option outside `Z`. -/
def rowsN : Stmt := .seq (rowA 0 kMONE) (.seq (rowA 1 kONE) (rowB kMONE))

/-- The three rows of an option in `Z`. -/
def rowsZ : Stmt := .seq (rowB kONE) (.seq (rowB kMONE) (rowA 1 kONE))

/-- The next option. -/
def xAdv : Stmt := .seq (addc kXP kXP 2) (.seq (addc kLP kLP 2) (.add kHR kHR kTK2))

/-- One option: the test, the three rows, the next option. -/
def xBody : Stmt := .seq zTest (.seq (.ifz kA rowsN rowsZ) xAdv)

/-- One cycle: its options, then `π_{c+1}`. -/
def xOuter : Stmt := .seq (forUp kJJ qK xBody) (addc kPP kPP 2)

/-- The pointers of the rows of `(c, j)`. -/
def xInit : Stmt :=
  .seq (mov kXP kPZN) (.seq (mov kLP kKL) (.seq (.add kTK2 qKT qKT) (.seq (.add kPP kPZN kTK2)
    (mov kHR qBH))))

/-- The rows of all `(c, j)`. -/
def kXR : Stmt := .seq xInit (forUp kC qT xOuter)

section XLoop

variable {F₀ bh bx : ℕ} {S : ℕ}

theorem zTest_spec {a c R : ℕ} (m : ℕ → ℕ) (x l p : ℤ)
    (hl : SMem m ((lay I F₀).pL + a * 2) l)
    (hp : SMem m ((lay I F₀).pZn + 2 * (I.t * I.k) + c * 2) p)
    (hx : SMem m ((lay I F₀).pZn + a * 2) x) (hSl : (lay I F₀).pL + a * 2 + 1 < S)
    (hSp : (lay I F₀).pZn + 2 * (I.t * I.k) + c * 2 + 1 < S)
    (hSx : (lay I F₀).pZn + a * 2 + 1 < S) :
    HTB S zTest (fun cfg => XG I F₀ bh bx a c R cfg ∧ cfg.mem = m)
      (fun cfg => (XG I F₀ bh bx a c R cfg ∧ cfg.mem = m) ∧
        cfg.reg kA = if x ≤ l - p then 1 else 0) 77 := by
  let P : Config → Prop := fun cfg => XG I F₀ bh bx a c R cfg ∧ cfg.mem = m
  have hP : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ rT :: (List.range' 400 50 ++ List.range' 530 10)) →
      Indep W P := fun hW =>
    ((XG_regIndep I F₀ bh bx a c R).mono fun r hr => by
      have := hW r hr; simp only [List.mem_cons, List.mem_append] at this ⊢; tauto).indep.and
      (Indep.mem (· = m))
  have z1 := HTB.sload (S := S) (P := P) (d := kX) (p := kLP) (a := (lay I F₀).pL + a * 2) (z := l)
    (by decide) (by decide) (by decide) (hP (by decide)) hSl
  have z2 := HTB.sload (S := S) (P := fun cfg => P cfg ∧ SReg cfg kX l) (d := kZt) (p := kPP)
    (a := (lay I F₀).pZn + 2 * (I.t * I.k) + c * 2) (z := p) (by decide) (by decide) (by decide)
    ((hP (by decide)).and (indep_sreg (by decide) (by decide) l)) hSp
  have z3 := HTB.ssub (S := S) (P := P) (d := kX) (x := kX) (y := kZt) (u := l) (v := p) (by decide)
    (by decide) (by decide) (hP (by decide))
  have z4 := HTB.sload (S := S) (P := fun cfg => P cfg ∧ SReg cfg kX (l - p)) (d := kZt) (p := kXP)
    (a := (lay I F₀).pZn + a * 2) (z := x) (by decide) (by decide) (by decide)
    ((hP (by decide)).and (indep_sreg (by decide) (by decide) _)) hSx
  have z5 := HTB.sle (S := S) (P := P) (d := kA) (x := kZt) (y := kX) (u := x) (v := l - p) (by decide)
    (by decide) (hP (by decide))
  refine ((z1.pre fun cfg h => ⟨h, h.1.2.2.2.2.1, by rw [h.2]; exact hl⟩).seq
    ((z2.pre fun cfg h => ⟨h, h.1.1.2.2.2.2.2.1, by rw [h.1.2]; exact hp⟩).seq
    ((z3.pre fun cfg h => ⟨h.1.1, h.1.2, h.2⟩).seq
    ((z4.pre fun cfg h => ⟨h, h.1.1.2.2.2.1, by rw [h.1.2]; exact hx⟩).seq
    (z5.pre fun cfg h => ⟨h.1.1, h.2, h.1.2⟩))))).weaken (by omega)

variable (I Xs F₀ bh bx) in
/-- The state before option `j` of cycle `c`. -/
def XInv (mπ : ℕ → ℕ) (c j : ℕ) (cfg : Config) : Prop :=
  XG I F₀ bh bx (c * I.k + j) c (2 * I.t + 3 * (c * I.k + j)) cfg ∧
    RowsK I Xs F₀ cfg.mem (2 * I.t + 3 * (c * I.k + j)) ∧ OutGH I F₀ mπ cfg.mem

theorem xinv_of {mπ : ℕ → ℕ} {c j a R : ℕ} {cfg : Config} (ha : a = c * I.k + j)
    (hR : R = 2 * I.t + 3 * (c * I.k + j))
    (h : XG I F₀ bh bx a c R cfg ∧ RowsK I Xs F₀ cfg.mem R ∧ OutGH I F₀ mπ cfg.mem) :
    XInv I Xs F₀ bh bx mπ c j cfg := by
  subst ha; subst hR; exact h

theorem rowA_of' {a b R : ℕ} (ha : a < I.t * I.k) (hb : b < 3) (hRb : R = 2 * I.t + 3 * a + b)
    (ng : ℕ) (hX : coefX (Zf I Xs a) ⟨b, hb⟩ = 0)
    (hL : coefL (Zf I Xs a) ⟨b, hb⟩ = sgnMul ng 1) {c : ℕ} (hac : a / I.k = c) :
    ∀ v < dd I + 1, Gx I Xs R v =
      if v < I.t * I.k then sgnMul ng (Hflat I a v)
      else if v = I.t * I.k + c then -sgnMul ng 1 else 0 := by
  subst hRb; subst hac; exact rowA_of ha hb ng hX hL

theorem rowB_of' {a b R : ℕ} (ha : a < I.t * I.k) (hb : b < 3) (hRb : R = 2 * I.t + 3 * a + b)
    (σ : ℤ) (hX : coefX (Zf I Xs a) ⟨b, hb⟩ = σ) (hL : coefL (Zf I Xs a) ⟨b, hb⟩ = 0) :
    ∀ v < dd I + 1, Gx I Xs R v = if v = a then σ else 0 := by
  subst hRb; exact rowB_of ha hb σ hX hL

theorem hpf_X' {a b R : ℕ} (ha : a < I.t * I.k) (hb : b < 3) (hRb : R = 2 * I.t + 3 * a + b) :
    hpf I R = 1 := by
  subst hRb; exact hpf_X I ha hb

/-- The three rows of an option outside `Z`. -/
theorem rowsN_spec {a c : ℕ} (ha : a < I.t * I.k) (hc : c < I.t) (hac : a / I.k = c)
    (hz : Zf I Xs a = false) (mπ : ℕ → ℕ) (hH : HMem I mπ bh) (hbh : bh + hCells I ≤ F₀)
    (hS : (lay I F₀).fe ≤ S) :
    HTB S rowsN (fun cfg => XG I F₀ bh bx a c (2 * I.t + 3 * a) cfg ∧
        RowsK I Xs F₀ cfg.mem (2 * I.t + 3 * a) ∧ OutGH I F₀ mπ cfg.mem)
      (fun cfg => XG I F₀ bh bx a c (2 * I.t + 3 * a + 1 + 1 + 1) cfg ∧
        RowsK I Xs F₀ cfg.mem (2 * I.t + 3 * a + 1 + 1 + 1) ∧ OutGH I F₀ mπ cfg.mem)
      (I.t * I.k * 54 + 66) := by
  have hM : MM I = 2 * I.t + 3 * (I.t * I.k) := nRows_eq I.t I.k
  obtain ⟨c0, c1, c2, c3, c4, c5, -, -, -, -, -, -⟩ := coef_values
  have r0 := rowA_spec (Xs := Xs) (F₀ := F₀) (bh := bh) (bx := bx) (R := 2 * I.t + 3 * a)
    (by omega) ha hc 0 kMONE (-1) (by decide) (fun cfg h => h.2.2.2.2.2.2.2.2.2)
    (rowA_of' ha (b := 0) (by norm_num) (by ring) 0 (by rw [hz]; exact c0)
      (by rw [hz, c1]; rfl) hac)
    (hpf_X' ha (b := 0) (by norm_num) (by ring)) mπ hH hbh hS
  have r1 := rowA_spec (Xs := Xs) (F₀ := F₀) (bh := bh) (bx := bx) (R := 2 * I.t + 3 * a + 1)
    (by omega) ha hc 1 kONE 1 (by decide) (fun cfg h => h.2.2.2.2.2.2.2.2.1)
    (rowA_of' ha (b := 1) (by norm_num) (by ring) 1 (by rw [hz]; exact c2)
      (by rw [hz, c3]; rfl) hac)
    (hpf_X' ha (b := 1) (by norm_num) (by ring)) mπ hH hbh hS
  have r2 := rowB_spec (Xs := Xs) (F₀ := F₀) (bh := bh) (bx := bx) (c := c)
    (R := 2 * I.t + 3 * a + 1 + 1) (by omega) ha kMONE (-1) (by decide)
    (fun cfg h => h.2.2.2.2.2.2.2.2.2)
    (rowB_of' ha (b := 2) (by norm_num) (by ring) (-1) (by rw [hz]; exact c4)
      (by rw [hz]; exact c5))
    (hpf_X' ha (b := 2) (by norm_num) (by ring)) mπ hS
  exact (r0.seq (r1.seq r2)).weaken (by omega)

/-- The three rows of an option in `Z`. -/
theorem rowsZ_spec {a c : ℕ} (ha : a < I.t * I.k) (hc : c < I.t) (hac : a / I.k = c)
    (hz : Zf I Xs a = true) (mπ : ℕ → ℕ) (hH : HMem I mπ bh) (hbh : bh + hCells I ≤ F₀)
    (hS : (lay I F₀).fe ≤ S) :
    HTB S rowsZ (fun cfg => XG I F₀ bh bx a c (2 * I.t + 3 * a) cfg ∧
        RowsK I Xs F₀ cfg.mem (2 * I.t + 3 * a) ∧ OutGH I F₀ mπ cfg.mem)
      (fun cfg => XG I F₀ bh bx a c (2 * I.t + 3 * a + 1 + 1 + 1) cfg ∧
        RowsK I Xs F₀ cfg.mem (2 * I.t + 3 * a + 1 + 1 + 1) ∧ OutGH I F₀ mπ cfg.mem)
      (I.t * I.k * 54 + 66) := by
  have hM : MM I = 2 * I.t + 3 * (I.t * I.k) := nRows_eq I.t I.k
  obtain ⟨-, -, -, -, -, -, c6, c7, c8, c9, c10, c11⟩ := coef_values
  have r0 := rowB_spec (Xs := Xs) (F₀ := F₀) (bh := bh) (bx := bx) (c := c)
    (R := 2 * I.t + 3 * a) (by omega) ha kONE 1 (by decide)
    (fun cfg h => h.2.2.2.2.2.2.2.2.1)
    (rowB_of' ha (b := 0) (by norm_num) (by ring) 1 (by rw [hz]; exact c6)
      (by rw [hz]; exact c7))
    (hpf_X' ha (b := 0) (by norm_num) (by ring)) mπ hS
  have r1 := rowB_spec (Xs := Xs) (F₀ := F₀) (bh := bh) (bx := bx) (c := c)
    (R := 2 * I.t + 3 * a + 1) (by omega) ha kMONE (-1) (by decide)
    (fun cfg h => h.2.2.2.2.2.2.2.2.2)
    (rowB_of' ha (b := 1) (by norm_num) (by ring) (-1) (by rw [hz]; exact c8)
      (by rw [hz]; exact c9))
    (hpf_X' ha (b := 1) (by norm_num) (by ring)) mπ hS
  have r2 := rowA_spec (Xs := Xs) (F₀ := F₀) (bh := bh) (bx := bx)
    (R := 2 * I.t + 3 * a + 1 + 1) (by omega) ha hc 1 kONE 1 (by decide)
    (fun cfg h => h.2.2.2.2.2.2.2.2.1)
    (rowA_of' ha (b := 2) (by norm_num) (by ring) 1 (by rw [hz]; exact c10)
      (by rw [hz, c11]; rfl) hac)
    (hpf_X' ha (b := 2) (by norm_num) (by ring)) mπ hH hbh hS
  exact (r0.seq (r1.seq r2)).weaken (by omega)

/-- **One option** `a = c k + j`. -/
theorem xBody_spec {c j : ℕ} (hc : c < I.t) (hj : j < I.k) (mπ : ℕ → ℕ)
    (hm : KM2 I Xs F₀ bh mπ) (hbh : bh + hCells I ≤ F₀) (hS : (lay I F₀).fe ≤ S) :
    HTB S xBody (XInv I Xs F₀ bh bx mπ c j) (XInv I Xs F₀ bh bx mπ c (j + 1))
      (77 + (I.t * I.k * 54 + 66 + 1) + 5) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd, hM, hgs, has⟩ :=
    lay_eqs I F₀
  have hC : hCells I = I.t * I.k * (2 * (I.t * I.k)) := rfl
  set a := c * I.k + j with ha_def
  have ha : a < I.t * I.k := by
    have := succ_mul_le I.k hc
    rw [Nat.mul_comm I.t I.k, Nat.mul_comm c I.k] at *
    omega
  have hac : a / I.k = c := by
    rw [ha_def, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj,
      Nat.zero_add]
  refine HTB.of_forall fun c₀ ⟨hX0, hR0, hO0⟩ => ?_
  have hread : ∀ {b n : ℕ} {f : ℕ → ℤ}, SArr mπ b 2 n f → (lay I F₀).pZn ≤ b →
      b + n * 2 ≤ (lay I F₀).php → ∀ i < n, SMem c₀.mem (b + i * 2) (f i) := by
    intro b n f hs hb1 hb2 i hi
    have := entry_lt (b := b) (s := 2) (le_refl 2) hi
    exact ⟨(hO0 _ (Or.inr (by omega)) (Or.inl (by omega))).trans (hs i hi).1,
      (hO0 _ (Or.inr (by omega)) (Or.inl (by omega))).trans (hs i hi).2⟩
  have hl : SMem c₀.mem ((lay I F₀).pL + a * 2) (Lf I Xs a) := by
    have := ha
    refine ⟨(hO0 _ (Or.inr (by omega)) (Or.inr (by omega))).trans (hm.l a ha).1,
      (hO0 _ (Or.inr (by omega)) (Or.inr (by omega))).trans (hm.l a ha).2⟩
  have hp : SMem c₀.mem ((lay I F₀).pZn + 2 * (I.t * I.k) + c * 2)
      (ZnF₀ I Xs (I.t * I.k + c)) := by
    have := hread hm.zn le_rfl (by omega) (I.t * I.k + c) (by omega)
    rwa [show (lay I F₀).pZn + (I.t * I.k + c) * 2 = (lay I F₀).pZn + 2 * (I.t * I.k) + c * 2 by
      ring] at this
  have hx : SMem c₀.mem ((lay I F₀).pZn + a * 2) (ZnF₀ I Xs a) :=
    hread hm.zn le_rfl (by omega) a (by omega)
  have t1 := zTest_spec (S := S) (F₀ := F₀) (bh := bh) (bx := bx) (a := a) (c := c)
    (R := 2 * I.t + 3 * a) c₀.mem _ _ _ hl hp hx (by omega) (by omega) (by omega)
  have hzf := zf_iff (Xs := Xs) ha
  rw [hac] at hzf
  have t2 : HTB S (.ifz kA rowsN rowsZ)
      (fun cfg => (XG I F₀ bh bx a c (2 * I.t + 3 * a) cfg ∧ cfg.mem = c₀.mem) ∧
        cfg.reg kA = if ZnF₀ I Xs a ≤ Lf I Xs a - ZnF₀ I Xs (I.t * I.k + c) then 1 else 0)
      (fun cfg => XG I F₀ bh bx a c (2 * I.t + 3 * a + 1 + 1 + 1) cfg ∧
        RowsK I Xs F₀ cfg.mem (2 * I.t + 3 * a + 1 + 1 + 1) ∧ OutGH I F₀ mπ cfg.mem)
      (I.t * I.k * 54 + 66 + 1) := by
    by_cases hcond : ZnF₀ I Xs a ≤ Lf I Xs a - ZnF₀ I Xs (I.t * I.k + c)
    · have hz : Zf I Xs a = true := by rw [hzf]; simpa using hcond
      refine HTB.ifz ?_ ?_
      · exact HTB.of_false fun cfg ⟨⟨_, hA⟩, h0⟩ => by
          simp only [hcond, ↓reduceIte] at hA; omega
      · exact (rowsZ_spec ha hc hac hz mπ hm.hmem hbh hS).pre
          fun cfg ⟨⟨⟨hx', hmem⟩, _⟩, _⟩ => ⟨hx', hmem ▸ hR0, hmem ▸ hO0⟩
    · have hz : Zf I Xs a = false := by rw [hzf]; simpa using hcond
      refine HTB.ifz ?_ ?_
      · exact (rowsN_spec ha hc hac hz mπ hm.hmem hbh hS).pre
          fun cfg ⟨⟨⟨hx', hmem⟩, _⟩, _⟩ => ⟨hx', hmem ▸ hR0, hmem ▸ hO0⟩
      · exact HTB.of_false fun cfg ⟨⟨_, hA⟩, h0⟩ => by
          simp only [hcond, ↓reduceIte] at hA; omega
  have t3 : HTB S xAdv
      (fun cfg => XG I F₀ bh bx a c (2 * I.t + 3 * a + 1 + 1 + 1) cfg ∧
        RowsK I Xs F₀ cfg.mem (2 * I.t + 3 * a + 1 + 1 + 1) ∧ OutGH I F₀ mπ cfg.mem)
      (XInv I Xs F₀ bh bx mπ c (j + 1)) 5 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
      fun cfg ⟨⟨hk, hrp, hhp, hxp, hlp, hpp, hhr, htk, hone, hmone⟩, hR, hO⟩ => by
      have hW : ∀ r ∈ wregs xAdv, r ∈ rT :: (List.range' 400 50 ++ List.range' 517 23) := by
        decide
      refine xinv_of (a := a + 1) (R := 2 * I.t + 3 * a + 1 + 1 + 1) (by omega) (by omega)
        ⟨⟨(KGl.regIndep' I F₀ bh bx hW).run (by decide) hk, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          (regIndep_sreg (by decide) (by decide) _).run (by decide) hone,
          (regIndep_sreg (by decide) (by decide) _).run (by decide) hmone⟩, ?_, ?_⟩
      all_goals simp +decide only [xAdv, run_seq', run_addc, run_add, setReg_reg, setReg_mem,
        ↓reduceIte, hrp, hhp, hxp, hlp, hpp, hhr, htk]
      · ring
      · ring
      · ring
      · exact hR
      · exact hO
  refine ((t1.pre fun cfg h => by subst h; exact ⟨hX0, rfl⟩).seq (t2.seq t3)).weaken le_rfl

/-- The registers that the rows of `(c, j)` keep. -/
theorem xBody_frame (c : ℕ) :
    RegIndep (wregs (forUp kJJ qK xBody)) (fun cfg => cfg.reg kC = c ∧ cfg.reg qT = I.t) := by
  indep

/-- **One cycle** of the rows of `(c, j)`. -/
theorem xOuter_spec {c : ℕ} (hc : c < I.t) (mπ : ℕ → ℕ) (hm : KM2 I Xs F₀ bh mπ)
    (hbh : bh + hCells I ≤ F₀) (hS : (lay I F₀).fe ≤ S) :
    HTB S xOuter (fun cfg => XInv I Xs F₀ bh bx mπ c 0 cfg ∧ cfg.reg kC = c ∧ cfg.reg qT = I.t)
      (fun cfg => XInv I Xs F₀ bh bx mπ (c + 1) 0 cfg ∧ cfg.reg kC = c ∧ cfg.reg qT = I.t)
      (I.k * (77 + (I.t * I.k * 54 + 66 + 1) + 5 + 4) + 3 + 2) := by
  have hl := (HTB.forUpC (S := S) (i := kJJ) (n := qK) (N := I.k) (body := xBody)
    (XInv I Xs F₀ bh bx mπ c) (77 + (I.t * I.k * 54 + 66 + 1) + 5) (by decide) (by decide)
    (by decide)
    (fun j => ((XG_regIndep I F₀ bh bx _ c _).mono (by decide)).indep.and
      ((Indep.mem (fun m' => RowsK I Xs F₀ m' _)).and (Indep.mem (OutGH I F₀ mπ))))
    (fun j hj => (xBody_spec hc hj mπ hm hbh hS).frameReg
      (F := fun cfg => cfg.reg kJJ = j ∧ cfg.reg qK = I.k) (by indep))).frameReg
    (xBody_frame (I := I) c)
  have h2 : HTB S (addc kPP kPP 2)
      (fun cfg => (XInv I Xs F₀ bh bx mπ c I.k cfg ∧ cfg.reg kJJ = I.k ∧ cfg.reg qK = I.k) ∧
        cfg.reg kC = c ∧ cfg.reg qT = I.t)
      (fun cfg => XInv I Xs F₀ bh bx mπ (c + 1) 0 cfg ∧ cfg.reg kC = c ∧ cfg.reg qT = I.t) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
      fun cfg ⟨⟨⟨⟨hk, hrp, hhp, hxp, hlp, hpp, hhr, htk, hone, hmone⟩, hR, hO⟩, _, _⟩, hC, hT⟩ => by
      have hW : ∀ r ∈ wregs (addc kPP kPP 2), r ∈ rT :: (List.range' 400 50 ++ List.range' 517 23) :=
        by decide
      refine ⟨xinv_of (a := c * I.k + I.k) (R := 2 * I.t + 3 * (c * I.k + I.k)) (by ring)
        (by ring)
        ⟨⟨(KGl.regIndep' I F₀ bh bx hW).run (by decide) hk, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          (regIndep_sreg (by decide) (by decide) _).run (by decide) hone,
          (regIndep_sreg (by decide) (by decide) _).run (by decide) hmone⟩, ?_, ?_⟩, ?_, ?_⟩
      all_goals simp +decide only [run_addc, setReg_reg, setReg_mem, ↓reduceIte, hrp, hhp, hxp,
        hlp, hpp, hhr, htk, hC, hT]
      · ring
      · exact hR
      · exact hO
  refine ((hl.pre fun cfg ⟨h, hC, hT⟩ => ⟨⟨h, by
      have hq := h.1.1.glob.qregs; rw [qregs_iff] at hq; exact hq.2.1⟩, hC, hT⟩).seq h2).weaken
    le_rfl

/-- The pointers of the rows of `(c, j)` after the rows `S`. -/
theorem xInit_spec (mπ : ℕ → ℕ) :
    HT xInit (SInv I Xs F₀ bh bx mπ I.t) (fun cfg => XInv I Xs F₀ bh bx mπ 0 0 cfg) 8 :=
  HT.run_le (by decide) (by decide)
    fun cfg ⟨⟨hk, hrp, hhp, _, _, _, _, hone, hmone⟩, hR, hO⟩ => by
    have hq := hk.glob.qregs
    rw [qregs_iff] at hq
    have hW : ∀ r ∈ wregs xInit, r ∈ rT :: (List.range' 400 50 ++ List.range' 517 23) := by
      decide
    refine xinv_of (a := 0) (R := 2 * I.t) (by ring) (by ring)
      ⟨⟨(KGl.regIndep' I F₀ bh bx hW).run (by decide) hk, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        (regIndep_sreg (by decide) (by decide) _).run (by decide) hone,
        (regIndep_sreg (by decide) (by decide) _).run (by decide) hmone⟩, ?_, ?_⟩
    all_goals (simp +decide only [xInit, run_seq', run_mov, run_add, setReg_reg, setReg_mem,
      ↓reduceIte, hrp, hhp, hk.glob.pZn, hk.pL, hk.bh, hq.2.2.1, hR, hO]; try ring)

/-- **The rows of all `(c, j)`**: all rows of `G` and `h'` are written. -/
theorem kX_spec (mπ : ℕ → ℕ) (hm : KM2 I Xs F₀ bh mπ) (hbh : bh + hCells I ≤ F₀)
    (hS : (lay I F₀).fe ≤ S) :
    HTB S kXR (SInv I Xs F₀ bh bx mπ I.t)
      (fun cfg => KGl I F₀ bh bx cfg ∧ RowsK I Xs F₀ cfg.mem (MM I) ∧ OutGH I F₀ mπ cfg.mem)
      (8 + (I.t * (I.k * (77 + (I.t * I.k * 54 + 66 + 1) + 5 + 4) + 3 + 2 + 4) + 3)) := by
  have hl := HTB.forUpC (S := S) (i := kC) (n := qT) (N := I.t) (body := xOuter)
    (fun c => XInv I Xs F₀ bh bx mπ c 0)
    (I.k * (77 + (I.t * I.k * 54 + 66 + 1) + 5 + 4) + 3 + 2) (by decide) (by decide) (by decide)
    (fun c => ((XG_regIndep I F₀ bh bx _ c _).mono (by decide)).indep.and
      ((Indep.mem (fun m' => RowsK I Xs F₀ m' _)).and (Indep.mem (OutGH I F₀ mπ))))
    (fun c hc => xOuter_spec hc mπ hm hbh hS)
  refine ((HTB.of_HT rfl (xInit_spec mπ)).seq (hl.pre fun cfg h => ⟨h, by
      have hq := h.1.1.glob.qregs; rw [qregs_iff] at hq; exact hq.1⟩)).mono (fun _ h => h)
    (fun cfg ⟨⟨hx, hR, hO⟩, _⟩ => ⟨hx.1, ?_, hO⟩) le_rfl
  convert hR using 2
  show nRows I.t I.k = _
  rw [nRows_eq]; ring

end XLoop

end STACS2027.Runtimes.QPRam.Kmo
