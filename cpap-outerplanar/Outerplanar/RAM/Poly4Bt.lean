module

public import Outerplanar.RAM.Poly4Seg
import Mathlib.Tactic

/-!
# Phase P4 of the polygon solver: the backtracking loop

The backtracking processes the segments `segOrder[m]` for `m = NS - 1, …, 0` (iteration `j`
handles `m = NS - j - 1`), as the `foldr` of `backtrack` does (`abAt`):

* `segHead`: `α := A[m]`, `β := ARG[TOFF[m] + α]` (`= argTab s α`), the offsets of the
  boundary list, the top cycles and the face of `s`, and a fresh array for the digits of `α`;
* `decode` twice: the digits of `α` (fresh array) and of `β` (into the values of the cycles
  with top `s`, `BtMem.wr_val`);
* the slot loop (`slotBody_spec`): every child gets its configuration.

`segBody_spec`: one iteration keeps `BtInv` (the state `abAt (NS - j)`); `btLoop_spec`: the
whole loop, from `abAt NS` (all zero) to `abAt 0 = backtrack`. Both are bounded triples
(`HTB S`) for `S ≥ F₁ + Lk k * NS` (every access is below the free pointer, which stays below
it, `BtInv`).
-/

@[expose] public section

namespace STACS2027.RAM.P4

open STACS2027.Poly

/-! ### Programs -/

/-- The data of the segment `m = NS - j - 1`, a fresh array for the digits of `α`, and the
arguments of its decoding. -/
def segHead : Stmt :=
  .seq (.sub rM gNS rJ) (.seq (dec rM) (.seq (ld rAL rA rM) (.seq (ld rBE gTOFF rM)
  (.seq (.add rBE rBE rAL) (.seq (ld rBE gARG rBE)
  (.seq (ld rBO gBOFF rM) (.seq (addc rNB rM 1) (.seq (ld rNB gBOFF rNB) (.seq (.sub rNB rNB rBO)
  (.seq (ld rTS gTST rM) (.seq (addc rTE rM 1) (.seq (ld rTE gTST rTE)
  (.seq (ld rFO gFOFF rM) (.seq (addc rNSL rM 1) (.seq (ld rNSL gFOFF rNSL)
  (.seq (.sub rNSL rNSL rFO) (.seq (dec rNSL)
  (.seq (alloc rAD rNB) (.seq (mov rDX rAL) (.seq (mov rDL rNB) (mov rDB rAD)))))))))))))))))))))

/-- The arguments of the decoding of `β` (into the values of the top cycles). -/
def segE : Stmt := .seq (mov rDX rBE) (.seq (.sub rDL rTE rTS) (.add rDB rVAL rTS))

/-- **One segment** of the backtracking. -/
def segBody : Stmt := .seq segHead (.seq decode (.seq segE (.seq decode (forUp rQ rNSL slotBody))))

/-! ### Bounds -/

/-- The bound of a decoding (at most `Lk k` digits of a number below `k ^ Lk k`). -/
def Tdec (k : ℕ) : ℕ := Lk k * (7 * k ^ Lk k + 13) + 3

/-- The bound of a segment without its slots. -/
def Tseg (k : ℕ) : ℕ := 2 * Tdec k + 45

/-- The number of slots of the segment `segOrder[j]`. -/
def nSl (pg : Graph) (n j : ℕ) : ℕ := (slots pg n ((segOrder pg n).getD j (0, 0))).length

/-! ### The invariant -/

/-- The invariant of the backtracking loop before iteration `j`: the state `abAt (NS - j)`; the
digits of `α` of the `j` segments done (at most `Lk k` cells each) lie between `F₁` and the
free pointer. -/
def BtInv (pg : Graph) (n k : ℕ) (c₀ : Config) (j : ℕ) (c : Config) : Prop :=
  Fix pg n k c₀ c ∧
    BtMem pg n k c₀ (abAt pg n k ((segOrder pg n).length - j)).1
      (abAt pg n k ((segOrder pg n).length - j)).2 ((segOrder pg n).length - j) c.mem ∧
    ZeroFrom c.mem (c.reg rFREE) ∧ F₁ pg n k c₀ ≤ c.reg rFREE ∧ c.out = c₀.out ∧
    c.reg rFREE ≤ F₁ pg n k c₀ + Lk k * j

/-- The registers kept from the head of a segment `s = segOrder[m]` to its end. -/
def SegR (pg : Graph) (n k : ℕ) (c₀ : Config) (m F : ℕ) (s : ℕ × ℕ) (j β : ℕ) (c : Config) :
    Prop :=
  SegRegs pg n k c₀ m F s c ∧ c.reg rJ = j ∧ c.reg gNS = (segOrder pg n).length ∧
    c.reg rNSL = (slots pg n s).length ∧ c.reg rBE = β ∧ c.reg rFREE = F + (bnd pg n k s).length

section Seg

variable {pg : Graph} {n k : ℕ} {omap : List ℕ} {c₀ : Config}

/-- Writing the digits of `β` into the values of the cycles with top `segOrder[m]`. -/
theorem BtMem.wr_val {fA : ℕ × ℕ → ℕ} {m : ℕ} {mem : ℕ → ℕ} (hm : m < (segOrder pg n).length)
    (h : BtMem pg n k c₀ fA (abAt pg n k (m + 1)).2 (m + 1) mem) (β : ℕ)
    (hβ : β = argTab pg n k (segOrder pg n)[m] ((abAt pg n k (m + 1)).1 (segOrder pg n)[m])) :
    BtMem pg n k c₀ fA (abAt pg n k m).2 m
      (wr mem (c₀.reg rFREE + (segOrder pg n).length + tst pg n k m)
        (cfg k (rpLen pg n k (segOrder pg n)[m]) β)) where
  same := sameOn_wr h.same (by omega) _
  a j hj := by rw [wr_of_lt _ (by omega)]; exact h.a j hj
  val i hi hp := by
    have hs := tst_succ (k := k) hm
    rw [abAt_succ_snd hm, ← hβ]
    by_cases hlt : i < tst pg n k (m + 1)
    · rw [valAt_update_self hm β ⟨hi, hlt⟩,
        show c₀.reg rFREE + (segOrder pg n).length + i = c₀.reg rFREE +
          (segOrder pg n).length + tst pg n k m + (i - tst pg n k m) by omega,
        wr, iteT ⟨by omega, by simp; omega⟩, Nat.add_sub_cancel_left, getD_cfg (by omega)]
    · rw [wr_of_ge (by simp; omega), valAt_update_ne hm β (by omega) hp]
      exact h.val i (by omega) hp

theorem arr_wr_of_lt {mem : ℕ → ℕ} {b b' : ℕ} {l l' : List ℕ} (h : Arr mem b l)
    (hb : b' + l'.length ≤ b) : Arr (wr mem b' l') b l := fun i hi => by
  rw [wr_of_ge (by omega)]; exact h i hi

/-- **The head of a segment** `m = NS - j - 1`. -/
theorem segHead_run (hk : 0 < k) (hc : Poly3Post pg n k omap c₀) {j m : ℕ}
    (hm : m < (segOrder pg n).length) (hmd : (segOrder pg n).length - j - 1 = m) {c : Config}
    (hF : Fix pg n k c₀ c)
    (hB : BtMem pg n k c₀ (abAt pg n k (m + 1)).1 (abAt pg n k (m + 1)).2 (m + 1) c.mem)
    (hJ : c.reg rJ = j) :
    (RAM.run segHead c).reg rM = m ∧
    (RAM.run segHead c).reg rAL = (abAt pg n k (m + 1)).1 (segOrder pg n)[m] ∧
    (RAM.run segHead c).reg rBE =
      argTab pg n k (segOrder pg n)[m] ((abAt pg n k (m + 1)).1 (segOrder pg n)[m]) ∧
    (RAM.run segHead c).reg rBO = bOff pg n k m ∧
    (RAM.run segHead c).reg rNB = (bnd pg n k (segOrder pg n)[m]).length ∧
    (RAM.run segHead c).reg rTS = tst pg n k m ∧
    (RAM.run segHead c).reg rTE = tst pg n k (m + 1) ∧
    (RAM.run segHead c).reg rFO = fOf pg n m ∧
    (RAM.run segHead c).reg rNSL = (slots pg n (segOrder pg n)[m]).length ∧
    (RAM.run segHead c).reg rAD = c.reg rFREE ∧
    (RAM.run segHead c).reg rFREE = c.reg rFREE + (bnd pg n k (segOrder pg n)[m]).length ∧
    (RAM.run segHead c).reg rDX = (abAt pg n k (m + 1)).1 (segOrder pg n)[m] ∧
    (RAM.run segHead c).reg rDL = (bnd pg n k (segOrder pg n)[m]).length ∧
    (RAM.run segHead c).reg rDB = c.reg rFREE := by
  have h1 := hB.a m hm
  have h2 := rd_toff hc hB.same (j := m) hm.le
  have h3 := rd_arg hc hB.same hm (abAt_fst_lt hk (m + 1) (segOrder pg n)[m])
  have h4 := rd_boff hc hB.same (j := m) hm.le
  have h5 := rd_boff hc hB.same (j := m + 1) hm
  rw [bOff_succ hm] at h5
  have h6 := rd_tst hc hB.same (j := m) hm.le
  have h7 := rd_tst hc hB.same (j := m + 1) hm
  have h8 := rd_foff hc hB.same (j := m) hm.le
  have h9 := rd_foff hc hB.same (j := m + 1) hm
  rw [fOf_succ hm] at h9
  have hsl := length_slots pg n (segOrder pg n)[m]
  simp +decide only [segHead, run_seq', run_sub, run_dec (show rM ≠ rT by decide),
    run_dec (show rNSL ≠ rT by decide), run_ld, run_add, run_addc (show rM ≠ rT by decide),
    run_alloc (show rNB ≠ rT by decide) (show rAD ≠ rNB by decide),
    run_mov (show rAL ≠ rT by decide), run_mov (show rNB ≠ rT by decide),
    run_mov (show rAD ≠ rT by decide), setReg_reg, ↓reduceIte, setReg_mem, hF.ns, hJ, hmd,
    hF.a, hF.toff, hF.arg, hF.boff, hF.tst, hF.foff, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    Nat.add_sub_cancel_left, hsl, true_and]

/-- The head of a segment reads only the arrays of P3 and `A`. -/
theorem segHead_addrOK {S : ℕ} (hk : 0 < k) (hc : Poly3Post pg n k omap c₀) {j m : ℕ}
    (hm : m < (segOrder pg n).length) (hmd : (segOrder pg n).length - j - 1 = m) {c : Config}
    (hF : Fix pg n k c₀ c)
    (hB : BtMem pg n k c₀ (abAt pg n k (m + 1)).1 (abAt pg n k (m + 1)).2 (m + 1) c.mem)
    (hJ : c.reg rJ = j) (hS : c₀.reg rFREE + (segOrder pg n).length ≤ S) : AddrOK S segHead c := by
  have h1 := hB.a m hm
  have h2 := rd_toff hc hB.same (j := m) hm.le
  have l1 := lt_toff hc (j := m) hm.le
  have l2 := lt_arg hc hm (abAt_fst_lt hk (m + 1) (segOrder pg n)[m])
  have l3 := lt_boff hc (j := m) hm.le
  have l4 := lt_boff hc (j := m + 1) hm
  have l5 := lt_tst hc (j := m) hm.le
  have l6 := lt_tst hc (j := m + 1) hm
  have l7 := lt_foff hc (j := m) hm.le
  have l8 := lt_foff hc (j := m + 1) hm
  addr_ok [segHead, hF.ns, hJ, hmd, hF.a, hF.toff, hF.arg, hF.boff, hF.tst, hF.foff, h1, h2]

theorem decode_le {k L x : ℕ} (hk : 0 < k) {L' : ℕ} (hL : L ≤ Lk k) (hx : x < k ^ L') (hL' : L' ≤ Lk k) :
    L * (7 * x + 13) + 3 ≤ Tdec k := by
  have h1 : x ≤ k ^ Lk k := (Nat.le_of_lt hx).trans (Nat.pow_le_pow_right hk hL')
  unfold Tdec
  have := Nat.mul_le_mul hL (show 7 * x + 13 ≤ 7 * k ^ Lk k + 13 by omega)
  omega

/-- **One segment** of the backtracking: from the state `abAt (m + 1)` to `abAt m`,
`m = NS - j - 1`. -/
theorem segBody_spec {S : ℕ} (hP : IsPolygon pg n) (hk : 3 ≤ k) (hc : Poly3Post pg n k omap c₀)
    (hSz : F₁ pg n k c₀ + Lk k * (segOrder pg n).length ≤ S) (j : ℕ)
    (hj : j < (segOrder pg n).length) :
    HTB S segBody (fun c => BtInv pg n k c₀ j c ∧ c.reg rJ = j ∧ c.reg gNS = (segOrder pg n).length)
      (fun c => BtInv pg n k c₀ (j + 1) c ∧ c.reg rJ = j ∧ c.reg gNS = (segOrder pg n).length)
      (Tseg k + nSl pg n ((segOrder pg n).length - j - 1) * (Tsl k + 4) + 3) := by
  intro c ⟨⟨hF, hB, hZ, hF1, hO, hFU⟩, hJ, hN⟩
  obtain ⟨m, hmd⟩ : ∃ m, (segOrder pg n).length - j - 1 = m := ⟨_, rfl⟩
  have hm : m < (segOrder pg n).length := by omega
  rw [show (segOrder pg n).length - j = m + 1 by omega] at hB
  have hk0 : 0 < k := by omega
  have hA₁ : AddrOK S segHead c := segHead_addrOK hk0 hc hm hmd hF hB hJ (by
    simp only [F₁] at hSz; omega)
  have hH := segHead_run hk0 hc hm hmd hF hB hJ
  obtain ⟨α, hα⟩ : ∃ α, (abAt pg n k (m + 1)).1 (segOrder pg n)[m] = α := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, argTab pg n k (segOrder pg n)[m] α = β := ⟨_, rfl⟩
  rw [hα, hβ] at hH
  obtain ⟨hM₁, hAL₁, hBE₁, hBO₁, hNB₁, hTS₁, hTE₁, hFO₁, hNSL₁, hAD₁, hFR₁, hDX₁, hDL₁, hDB₁⟩ := hH
  have hαlt : α < k ^ (bnd pg n k (segOrder pg n)[m]).length := hα ▸ abAt_fst_lt hk0 (m + 1) _
  have hβlt : β < k ^ (topIdx pg n k (segOrder pg n)[m]).length := hβ ▸ argTab_lt hk0 _ _
  have hnb := length_bnd_le' (k := k) hP (List.getElem_mem hm)
  have hnc := length_topIdx_le' (k := k) hP hk0 (segOrder pg n)[m]
  have hlc := length_topIdx (k := k) hm
  have hts := tst_succ (k := k) hm
  have htN : tst pg n k (m + 1) ≤ (pool pg n k).length := by
    rw [← tst_length]; exact tst_mono hm
  -- the registers kept until the end of the segment
  set F := c.reg rFREE with hFdef
  have hF1' : F₁ pg n k c₀ ≤ F := hF1
  -- 1. the head
  have hLj : Lk k * (j + 1) ≤ Lk k * (segOrder pg n).length := Nat.mul_le_mul_left _ (by omega)
  have eLk : Lk k * (j + 1) = Lk k * j + Lk k := by ring
  have hFS : F + (bnd pg n k (segOrder pg n)[m]).length ≤ S := by omega
  have e₁ := execB_run segHead (by decide) c hA₁
  have ht₁ := cost_le_size segHead c
  have hFx := (show RegIndep (wregs segHead) (fun c => Fix pg n k c₀ c ∧ c.reg gNS =
      (segOrder pg n).length) by indep [fix_iff]).run (by decide) ⟨hF, hN⟩
  have hJ' : (RAM.run segHead c).reg rJ = j := by
    rw [run_reg_of_not_mem (by decide) (by decide) c]; exact hJ
  have hm₁ : (RAM.run segHead c).mem = c.mem := run_mem_of_stores (by decide) (by decide) c
  have ho₁ : (RAM.run segHead c).out = c.out := run_out_of_writes (by decide) (by decide) c
  generalize RAM.run segHead c = c₁ at *
  generalize cost segHead c = t₁ at *
  have hR₁ : SegR pg n k c₀ m F (segOrder pg n)[m] j β c₁ :=
    ⟨⟨hFx.1, hBO₁, hNB₁, hTS₁, hTE₁, hFO₁, hAD₁, by rw [hFR₁]⟩, hJ', hFx.2, hNSL₁, hBE₁, hFR₁⟩
  -- 2. the digits of `α`
  obtain ⟨c₂, t₂, e₂, hm₂, ht₂⟩ := decode_spec (S := S) (k := k) (x := α)
    (L := (bnd pg n k (segOrder pg n)[m]).length) (b := F) (mm := c.mem) hk0 hFS c₁
    ⟨hDX₁, hDL₁, hDB₁, hR₁.1.fix.k, hm₁⟩
  have hR₂ := (show RegIndep (wregs decode) (SegR pg n k c₀ m F (segOrder pg n)[m] j β) by
    indep [SegR, segRegs_iff, fix_iff]).execB e₂ hR₁
  have ho₂ : c₂.out = c.out := (e₂.frame.out (by decide)).trans ho₁
  -- 3. the arguments of the second decoding
  have e₃ := execB_run (S := S) segE (by decide) c₂ (AddrOK.of_memFree rfl)
  have ht₃ := cost_le_size segE c₂
  have hR₃ := (show RegIndep (wregs segE) (SegR pg n k c₀ m F (segOrder pg n)[m] j β) by
    indep [SegR, segRegs_iff, fix_iff]).run (by decide) hR₂
  have hm₃ : (RAM.run segE c₂).mem = c₂.mem := run_mem_of_stores (by decide) (by decide) c₂
  have ho₃ : (RAM.run segE c₂).out = c₂.out := run_out_of_writes (by decide) (by decide) c₂
  have hE : (RAM.run segE c₂).reg rDX = β ∧
      (RAM.run segE c₂).reg rDL = rpLen pg n k (segOrder pg n)[m] ∧
      (RAM.run segE c₂).reg rDB = c₀.reg rFREE + (segOrder pg n).length + tst pg n k m ∧
      (RAM.run segE c₂).reg rK = k := by
    simp +decide only [segE, run_seq', run_mov (show rBE ≠ rT by decide), run_sub, run_add,
      setReg_reg, ↓reduceIte, hR₂.2.2.2.2.1, hR₂.1.te, hR₂.1.ts, hR₂.1.fix.val, hR₂.1.fix.k, hts,
      Nat.add_sub_cancel_left, and_true]
  generalize RAM.run segE c₂ = c₃ at *
  generalize cost segE c₂ = t₃ at *
  -- 4. the digits of `β`
  obtain ⟨c₄, t₄, e₄, hm₄, ht₄⟩ := decode_spec (S := S) (k := k) (x := β)
    (L := rpLen pg n k (segOrder pg n)[m])
    (b := c₀.reg rFREE + (segOrder pg n).length + tst pg n k m) (mm := c₃.mem) hk0
    (by simp only [F₁] at hF1'; omega) c₃
    ⟨hE.1, hE.2.1, hE.2.2.1, hE.2.2.2, rfl⟩
  have hR₄ := (show RegIndep (wregs decode) (SegR pg n k c₀ m F (segOrder pg n)[m] j β) by
    indep [SegR, segRegs_iff, fix_iff]).execB e₄ hR₃
  have ho₄ : c₄.out = c.out := (e₄.frame.out (by decide)).trans (ho₃.trans ho₂)
  -- 5. the slots
  have hα' : α = (abAt pg n k (m + 1)).1 (segOrder pg n)[m] := hα.symm
  have hβ' : β = argTab pg n k (segOrder pg n)[m] α := hβ.symm
  have hl := (HTB.forUpC (S := S) (i := rQ) (n := rNSL)
    (N := (slots pg n (segOrder pg n)[m]).length)
    (body := slotBody) (SlInv pg n k c₀ m F (segOrder pg n)[m] α β (abAt pg n k (m + 1)).1
      (abAt pg n k m).2) (Tsl k) (by decide) (by decide) (by decide)
    (fun q => by indep [SlInv, segRegs_iff, fix_iff])
    (fun q hq => slotBody_spec hP hk hc hm hα' hβ' hF1' hFS q hq)).frameReg
    (F := fun c => c.reg rJ = j ∧ c.reg gNS = (segOrder pg n).length) (by indep)
  have hvT : c₀.reg rFREE + (segOrder pg n).length + tst pg n k m +
      (cfg k (rpLen pg n k (segOrder pg n)[m]) β).length ≤ F := by
    simp only [length_cfg, F₁] at hF1' ⊢; omega
  have hS0 : SlInv pg n k c₀ m F (segOrder pg n)[m] α β (abAt pg n k (m + 1)).1
      (abAt pg n k m).2 0 c₄ := by
    refine ⟨hR₄.1, ?_, ?_, ?_, ho₄.trans hO⟩
    · rw [fPart_zero, hm₄, hm₃, hm₂]
      exact (hB.wr_above hF1' _).wr_val hm β (by rw [hα, hβ])
    · rw [hm₄, hm₃, hm₂]
      exact arr_wr_of_lt (arr_wr _ _ _) hvT
    · rw [hm₄, hm₃, hm₂, hR₄.2.2.2.2.2]
      refine zeroFrom_wr (zeroFrom_wr (hZ.mono (by omega)) (by simp)) (by omega)
  obtain ⟨c₅, t₅, e₅, ⟨⟨hS, -, -⟩, hJ₅, hN₅⟩, ht₅⟩ := hl c₄ ⟨⟨hS0, hR₄.2.2.2.1⟩, hR₄.2.1, hR₄.2.2.1⟩
  refine ⟨c₅, t₁ + (t₂ + (t₃ + (t₄ + t₅))),
    ExecB.seq e₁ (ExecB.seq e₂ (ExecB.seq e₃ (ExecB.seq e₄ e₅))),
    ⟨⟨hS.1.fix, ?_, hS.2.2.2.1, ?_, hS.2.2.2.2, ?_⟩, hJ₅, hN₅⟩, ?_⟩
  · rw [show (segOrder pg n).length - (j + 1) = m by omega, abAt_succ_fst hm, hα, hβ]
    exact hS.2.1
  · have := hS.1.free; omega
  · rw [e₅.frame.reg rFREE (by decide), hR₄.2.2.2.2.2]
    omega
  · have hs₁ : size segHead = 41 := by decide
    have hs₃ : size segE = 4 := by decide
    have h₂ := decode_le hk0 hnb hαlt hnb
    have h₄ := decode_le hk0 (hlc ▸ hnc) hβlt hnc
    have hns : nSl pg n ((segOrder pg n).length - j - 1) = (slots pg n (segOrder pg n)[m]).length := by
      rw [nSl, hmd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some]
    rw [hns]
    unfold Tseg
    omega

theorem sum_map_le' {α : Type*} (l : List α) (f g : α → ℕ) (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

/-- The slots of all faces: at most twice the number of edges. -/
theorem sum_nSl_le (hP : IsPolygon pg n) :
    ∑ j ∈ Finset.range (segOrder pg n).length, nSl pg n ((segOrder pg n).length - j - 1) ≤
      2 * pg.length := by
  have h1 : ∀ j ∈ Finset.range (segOrder pg n).length, nSl pg n ((segOrder pg n).length - j - 1) =
      nSl pg n ((segOrder pg n).length - 1 - j) := fun j _ => by rw [Nat.sub_right_comm]
  rw [Finset.sum_congr rfl h1, Finset.sum_range_reflect (fun j => nSl pg n j)]
  have h2 := P1.sum_range_getD (fun s => (slots pg n s).length) (0, 0) (segOrder pg n)
  simp only [nSl]
  rw [h2]
  refine (sum_map_le' _ _ (fun s => (faceVerts pg n s).length) (fun s _ => ?_)).trans ?_
  · rw [length_slots]; omega
  · have := P1.length_faceCat_le hP
    rw [faceCat, List.length_flatMap] at this
    exact this

/-- **The backtracking loop**: from the state `abAt NS` to `abAt 0 = backtrack`. -/
theorem btLoop_spec {S : ℕ} (hP : IsPolygon pg n) (hk : 3 ≤ k) (hc : Poly3Post pg n k omap c₀)
    (hSz : F₁ pg n k c₀ + Lk k * (segOrder pg n).length ≤ S) :
    HTB S (forUp rJ gNS segBody)
      (fun c => BtInv pg n k c₀ 0 c ∧ c.reg gNS = (segOrder pg n).length)
      (fun c => BtInv pg n k c₀ (segOrder pg n).length c ∧ c.reg rJ = (segOrder pg n).length ∧
        c.reg gNS = (segOrder pg n).length)
      ((segOrder pg n).length * (Tseg k + 7) + 2 * pg.length * (Tsl k + 4) + 3) := by
  refine (HTB.forUp (i := rJ) (n := gNS) (N := (segOrder pg n).length) (body := segBody)
    (BtInv pg n k c₀) (fun j => Tseg k + nSl pg n ((segOrder pg n).length - j - 1) * (Tsl k + 4) + 3)
    (by decide) (by decide) (by decide) (fun j => by indep [BtInv, fix_iff])
    (fun j hj => segBody_spec hP hk hc hSz j hj)).weaken ?_
  have h1 : ∀ j ∈ Finset.range (segOrder pg n).length,
      Tseg k + nSl pg n ((segOrder pg n).length - j - 1) * (Tsl k + 4) + 3 + 4 =
        (Tseg k + 7) + nSl pg n ((segOrder pg n).length - j - 1) * (Tsl k + 4) := fun j _ => by
    omega
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul, ← Finset.sum_mul]
  have := Nat.mul_le_mul_right (Tsl k + 4) (sum_nSl_le (pg := pg) hP)
  omega

end Seg

end STACS2027.RAM.P4
