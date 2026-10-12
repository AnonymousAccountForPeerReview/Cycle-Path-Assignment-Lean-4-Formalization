module

public import Outerplanar.RAM.Poly4Bt
import Mathlib.Tactic

/-!
# Phase P4 of the polygon solver (backtracking and output): the main triple

`poly4 k` runs

* `rK := k`;
* fresh arrays `A` (`NS` cells, zero: every segment starts with configuration `0`) and the
  values `VAL` of the pool cycles (`NP` cells);
* the backtracking loop (`btLoop_spec`, `Outerplanar/RAM/Poly4Bt.lean`): afterwards
  `VAL[i] = valOf i`;
* the output loop (`outLoop`): for every pool index `i` in order and every `t < k`, the label
  `omap[(cyc i)[(valOf i + t) % k]]` (the cycle `cyc i` at `gPOOL + k * i`), i.e. the cycle
  rotated to its omitted vertex (`map_rotateTo`), mapped to labels.

`poly4_specB`: from `Poly3Post pg n k omap`, `poly4 k` appends
`(Poly.polyOut pg n k).flatten` mapped by `omap` to the output within
`CP4 k * (n + |pg| + 1)` steps, allocating at most `M4 pg n k` fresh cells (`M4_le`), every
load and store below any bound `S` leaving room for these cells;
`poly4_wregs`: it writes only
`rT`, `rFREE` and registers at or above `gPx`.
-/

@[expose] public section

namespace STACS2027.RAM.P4

open STACS2027.Poly

/-! ### Registers and programs -/

/-- Output: the pool index. -/
abbrev rOI : ℕ := 121
/-- Output: the address of the pool cycle. -/
abbrev rPP : ℕ := 122
/-- Output: its value. -/
abbrev rV : ℕ := 123
/-- Output: the entry counter. -/
abbrev rOT : ℕ := 124
/-- Output: the position in the cycle. -/
abbrev rOP : ℕ := 125
/-- Output: the vertex, then its label. -/
abbrev rOX : ℕ := 126
/-- One entry `t` of the pool cycle: the label of `cyc[(v + t) % k]`. -/
def outInner : Stmt :=
  .seq (.add rOP rV rOT) (.seq (ifLe rK rOP (.sub rOP rOP rK) .skip) (.seq (ld rOX rPP rOP)
    (.seq (ld rOX gOMAP rOX) (.write rOX))))
/-- One pool cycle, rotated to its omitted vertex. -/
def outBody : Stmt := .seq (ld rV rVAL rOI) (.seq (forUp rOT rK outInner) (.add rPP rPP rK))
/-- The output. -/
def outLoop : Stmt := .seq (mov rPP gPOOL) (forUp rOI gNP outBody)

/-- **Phase P4** of the polygon solver (backtracking and output) for cycle length `k`. -/
def poly4 (k : ℕ) : Stmt :=
  .seq (.const rK k) (.seq (alloc rA gNS) (.seq (alloc rVAL gNP)
    (.seq (forUp rJ gNS segBody) outLoop)))

/-- The constant of the running time of P4. -/
def CP4 (k : ℕ) : ℕ := 29 + (Tseg k + 7) + 2 * (Tsl k + 4) + rpathBound k * (14 * k + 10)

/-! ### The output -/

section Out

variable {pg : Graph} {n k : ℕ} {omap : List ℕ} {c₀ : Config}

/-- The output of the first `i` pool cycles. -/
def outPre (pg : Graph) (n k : ℕ) (omap : List ℕ) (i : ℕ) : List ℕ :=
  ((List.range i).map fun i =>
    (rotateTo (cyc pg n k i) (valOf pg n k i)).map fun p => omap.getD p 0).flatten

/-- The invariant of the output loop after `i` pool cycles. -/
def OutInv (pg : Graph) (n k : ℕ) (omap : List ℕ) (c₀ : Config) (mm : ℕ → ℕ) (i : ℕ)
    (c : Config) : Prop :=
  c.reg rPP = c₀.reg gPOOL + k * i ∧ c.reg rK = k ∧ c.reg rVAL = c₀.reg rFREE +
    (segOrder pg n).length ∧ c.reg gOMAP = c₀.reg gOMAP ∧ c.mem = mm ∧
    c.out = c₀.out ++ outPre pg n k omap i

/-- The invariant of the loop over the entries of the pool cycle `i` (value `v`) after `t`
entries. -/
def InInv (pg : Graph) (n k : ℕ) (omap : List ℕ) (c₀ : Config) (mm : ℕ → ℕ) (i v : ℕ) (t : ℕ)
    (c : Config) : Prop :=
  c.reg rPP = c₀.reg gPOOL + k * i ∧ c.reg rV = v ∧ c.reg rK = k ∧
    c.reg gOMAP = c₀.reg gOMAP ∧ c.mem = mm ∧
    c.out = c₀.out ++ outPre pg n k omap i ++
      (List.range t).map fun t => omap.getD ((cyc pg n k i).getD ((v + t) % k) 0) 0

theorem outInner_spec {S : ℕ} (hP : IsPolygon pg n) (hk : 3 ≤ k) (hc : Poly3Post pg n k omap c₀)
    (hS : c₀.reg rFREE ≤ S)
    {mm : ℕ → ℕ} (hs : SameOn (· < c₀.reg rFREE) c₀.mem mm) {i v : ℕ}
    (hi : i < (pool pg n k).length) (hv : v < k) (t : ℕ) (ht : t < k) :
    HTB S outInner (fun c => InInv pg n k omap c₀ mm i v t c ∧ c.reg rOT = t ∧ c.reg rK = k)
      (fun c => InInv pg n k omap c₀ mm i v (t + 1) c ∧ c.reg rOT = t ∧ c.reg rK = k) 10 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7, _⟩ => ?_
  have hp : (v + t) % k < k := Nat.mod_lt _ (by omega)
  have hx := rd_pool hP hk hc hs hi hp
  have hxn : (cyc pg n k i).getD ((v + t) % k) 0 < n :=
    lt_of_mem_cyc hP hk hi (getD_mem 0 (by rw [length_cyc hP hk hi]; exact hp))
  have hom := rd_omap hc hs hxn
  have l1 := lt_pool hP hk hc hi hp
  have l2 := lt_omap hc hxn
  have hA : AddrOK S outInner c := by
    by_cases hkt : k ≤ v + t
    · have hmod : v + t - k = (v + t) % k := by
        rw [Nat.mod_eq_sub_mod hkt, Nat.mod_eq_of_lt (by omega)]
      addr_ok [outInner, h1, h2, h3, h4, h5, h7, hkt, hmod, hx]
    · have hmod : v + t = (v + t) % k := (Nat.mod_eq_of_lt (by omega)).symm
      rw [← hmod] at hx l1 l2
      addr_ok [outInner, h1, h2, h3, h4, h5, h7, hkt, hx]
  refine ⟨hA, ?_⟩
  have hR := (show RegIndep (wregs outInner) (fun c => c.reg rPP = c₀.reg gPOOL + k * i ∧
      c.reg rV = v ∧ c.reg rK = k ∧ c.reg gOMAP = c₀.reg gOMAP ∧ c.reg rOT = t) by indep).run
    (by decide) ⟨h1, h2, h3, h4, h7⟩
  have hm' : (RAM.run outInner c).mem = mm := (run_mem_of_stores (by decide) (by decide) c).trans h5
  have ho' : (RAM.run outInner c).out =
      c.out ++ [omap.getD ((cyc pg n k i).getD ((v + t) % k) 0) 0] := by
    by_cases hkt : k ≤ v + t
    · have hmod : v + t - k = (v + t) % k := by
        rw [Nat.mod_eq_sub_mod hkt, Nat.mod_eq_of_lt (by omega)]
      simp +decide only [outInner, run_seq', run_add, run_ifLe, run_sub, run_ld, run_write,
        setReg_reg, ↓reduceIte, setReg_mem, setReg_out, emit_out, h1, h2, h3,
        h4, h5, h7, hkt, hmod, hx, hom]
    · have hmod : v + t = (v + t) % k := (Nat.mod_eq_of_lt (by omega)).symm
      simp +decide only [outInner, run_seq', run_add, run_ifLe, run_ld, run_write,
        run_skip, setReg_reg, ↓reduceIte, setReg_mem, setReg_out, emit_out, h1, h2, h3,
        h4, h5, h7, hkt]
      rw [← hmod] at hx hom
      rw [hx, hom, ← hmod]
  refine ⟨⟨hR.1, hR.2.1, hR.2.2.1, hR.2.2.2.1, hm', ?_⟩, hR.2.2.2.2, hR.2.2.1⟩
  rw [ho', h6, List.range_succ, List.map_append, List.map_singleton, List.append_assoc]

theorem outPre_succ (i : ℕ) : outPre pg n k omap (i + 1) = outPre pg n k omap i ++
    (rotateTo (cyc pg n k i) (valOf pg n k i)).map fun p => omap.getD p 0 := by
  rw [outPre, outPre, List.range_succ, List.map_append, List.flatten_append, List.map_singleton,
    List.flatten_singleton]

theorem outPre_full :
    outPre pg n k omap (pool pg n k).length = (polyOut pg n k).flatten.map fun p => omap.getD p 0 := by
  rw [outPre, polyOut, List.map_flatten, List.map_map]
  rfl

theorem outBody_spec {S : ℕ} (hP : IsPolygon pg n) (hk : 3 ≤ k) (hc : Poly3Post pg n k omap c₀)
    (hS : F₁ pg n k c₀ ≤ S)
    {mm : ℕ → ℕ} (hs : SameOn (· < c₀.reg rFREE) c₀.mem mm)
    (hV : ∀ i, i < (pool pg n k).length →
      mm (c₀.reg rFREE + (segOrder pg n).length + i) = valOf pg n k i)
    (i : ℕ) (hi : i < (pool pg n k).length) :
    HTB S outBody (fun c => OutInv pg n k omap c₀ mm i c ∧ c.reg rOI = i ∧
        c.reg gNP = (pool pg n k).length)
      (fun c => OutInv pg n k omap c₀ mm (i + 1) c ∧ c.reg rOI = i ∧
        c.reg gNP = (pool pg n k).length) (14 * k + 6) := by
  have hv : valOf pg n k i < k := Nat.mod_lt _ (by omega)
  have h₀ : HTB S (ld rV rVAL rOI) (fun c => OutInv pg n k omap c₀ mm i c ∧ c.reg rOI = i ∧
        c.reg gNP = (pool pg n k).length)
      (fun c => (InInv pg n k omap c₀ mm i (valOf pg n k i) 0 c ∧ c.reg rK = k) ∧
        (c.reg rOI = i ∧ c.reg gNP = (pool pg n k).length ∧
          c.reg rVAL = c₀.reg rFREE + (segOrder pg n).length)) 2 :=
    HTB.run_le (by decide) (by decide) fun c ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7, h8⟩ => by
      refine ⟨by simp only [F₁] at hS; addr_ok [h3, h7], ?_⟩
      simp +decide only [InInv, run_ld, setReg_reg, ↓reduceIte, setReg_mem, setReg_out, h1, h2, h3,
        h4, h5, h6, h7, h8, hV i hi, List.range_zero, List.map_nil, List.append_nil, and_self]
  have hl := (HTB.forUpC (S := S) (i := rOT) (n := rK) (N := k) (body := outInner)
    (InInv pg n k omap c₀ mm i (valOf pg n k i)) 10 (by decide) (by decide) (by decide)
    (fun t => by indep [InInv])
    (fun t ht => outInner_spec hP hk hc (by simp only [F₁] at hS; omega) hs hi hv t ht)).frameReg
    (F := fun c => c.reg rOI = i ∧ c.reg gNP = (pool pg n k).length ∧
      c.reg rVAL = c₀.reg rFREE + (segOrder pg n).length) (by indep)
  have h₂ : HTB S (.add rPP rPP rK)
      (fun c => (InInv pg n k omap c₀ mm i (valOf pg n k i) k c ∧ c.reg rOT = k ∧ c.reg rK = k) ∧
        (c.reg rOI = i ∧ c.reg gNP = (pool pg n k).length ∧
          c.reg rVAL = c₀.reg rFREE + (segOrder pg n).length))
      (fun c => OutInv pg n k omap c₀ mm (i + 1) c ∧ c.reg rOI = i ∧
        c.reg gNP = (pool pg n k).length) 1 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
      fun c ⟨⟨⟨h1, _, h3, h4, h5, h6⟩, _, _⟩, h7, h8, h9⟩ => by
      have hrot := map_rotateTo (fun p => omap.getD p 0) (length_cyc hP hk hi) hv
      simp +decide only [OutInv, run_add, setReg_reg, ↓reduceIte, setReg_mem, setReg_out, h1, h3,
        h4, h5, h6, h7, h8, h9, outPre_succ, hrot, List.append_assoc, and_true]
      ring
  exact (h₀.seq (hl.seq h₂)).weaken (by omega)

/-- **The output loop.** -/
theorem outLoop_spec {S : ℕ} (hP : IsPolygon pg n) (hk : 3 ≤ k) (hc : Poly3Post pg n k omap c₀)
    (hS : F₁ pg n k c₀ ≤ S)
    {mm : ℕ → ℕ} (hs : SameOn (· < c₀.reg rFREE) c₀.mem mm)
    (hV : ∀ i, i < (pool pg n k).length →
      mm (c₀.reg rFREE + (segOrder pg n).length + i) = valOf pg n k i) :
    HTB S outLoop (fun c => Fix pg n k c₀ c ∧ c.mem = mm ∧ c.out = c₀.out)
      (fun c => c.mem = mm ∧
        c.out = c₀.out ++ (polyOut pg n k).flatten.map fun p => omap.getD p 0)
      ((pool pg n k).length * (14 * k + 10) + 5) := by
  have h₀ : HTB S (mov rPP gPOOL) (fun c => Fix pg n k c₀ c ∧ c.mem = mm ∧ c.out = c₀.out)
      (fun c => OutInv pg n k omap c₀ mm 0 c ∧ c.reg gNP = (pool pg n k).length) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hF, h1, h2⟩ => by
      simp +decide only [OutInv, run_mov (show gPOOL ≠ rT by decide), setReg_reg, ↓reduceIte,
        setReg_mem, setReg_out, hF.pl, hF.k, hF.val, hF.om, hF.np, h1, h2, outPre,
        List.range_zero, List.map_nil, List.flatten_nil, List.append_nil, Nat.mul_zero,
        Nat.add_zero, and_self]
  have hl := HTB.forUpC (S := S) (i := rOI) (n := gNP) (N := (pool pg n k).length) (body := outBody)
    (OutInv pg n k omap c₀ mm) (14 * k + 6) (by decide) (by decide) (by decide)
    (fun i => by indep [OutInv]) (fun i hi => outBody_spec hP hk hc hS hs hV i hi)
  refine (h₀.seq hl).mono (fun _ h => h) ?_
    (by rw [show 14 * k + 6 + 4 = 14 * k + 10 by omega]; omega)
  rintro c ⟨⟨_, _, _, _, h5, h6⟩, _, _⟩
  exact ⟨h5, by rw [h6, outPre_full]⟩

end Out

/-! ### The main triple -/

/-- The registers of the interface and `rK`, after the first instruction of P4. -/
def IfRegs (pg : Graph) (n k : ℕ) (c₀ c : Config) : Prop :=
  c.reg gPN = n ∧ c.reg gNS = (segOrder pg n).length ∧ c.reg gNP = (pool pg n k).length ∧
    c.reg gFSID = c₀.reg gFSID ∧ c.reg gFOFF = c₀.reg gFOFF ∧ c.reg gFV = c₀.reg gFV ∧
    c.reg gPOOL = c₀.reg gPOOL ∧ c.reg gTST = c₀.reg gTST ∧ c.reg gBOFF = c₀.reg gBOFF ∧
    c.reg gBIDX = c₀.reg gBIDX ∧ c.reg gTOFF = c₀.reg gTOFF ∧ c.reg gARG = c₀.reg gARG ∧
    c.reg gOMAP = c₀.reg gOMAP ∧ c.reg rK = k

/-- The fresh cells of P4: the configurations `A`, the values of the pool cycles, the digits of
`α` of every segment. -/
def M4 (pg : Graph) (n k : ℕ) : ℕ :=
  (segOrder pg n).length + (pool pg n k).length + Lk k * (segOrder pg n).length

theorem M4_le (hP : IsPolygon pg n) : M4 pg n k ≤ CP4 k * (n + pg.length + 1) := by
  have h1 : (segOrder pg n).length ≤ pg.length := by
    have := P1.length_segOrder (pg := pg) (n := n)
    have := P1.length_segEnum_le (pg := pg) (n := n)
    omega
  have h2 := length_pool_le (k := k) hP
  have hC : 1 + rpathBound k + Lk k ≤ CP4 k := by
    unfold CP4 Tseg Tdec
    have : rpathBound k ≤ rpathBound k * (14 * k + 10) := Nat.le_mul_of_pos_right _ (by omega)
    have : Lk k ≤ Lk k * (7 * k ^ Lk k + 13) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have e1 : Lk k * (segOrder pg n).length ≤ Lk k * pg.length := Nat.mul_le_mul_left _ h1
  have e2 : (1 + rpathBound k + Lk k) * pg.length ≤ CP4 k * pg.length := Nat.mul_le_mul_right _ hC
  have e3 : CP4 k * pg.length ≤ CP4 k * (n + pg.length + 1) := Nat.mul_le_mul_left _ (by omega)
  have e4 : (1 + rpathBound k + Lk k) * pg.length =
      pg.length + pg.length * rpathBound k + Lk k * pg.length := by ring
  unfold M4
  omega

/-- **Phase P4** (backtracking and output), bounded space: from `Poly3Post pg n k omap`,
`poly4 k` appends `(polyOut pg n k).flatten` mapped by `omap` to the output within
`CP4 k * (n + |pg| + 1)` steps, allocating at most `M4 pg n k ≤ CP4 k * (n + |pg| + 1)` fresh
cells, every load and store below any bound `S ≥ c₀.reg rFREE + CP4 k * (n + |pg| + 1)`. -/
theorem poly4_specB {k : ℕ} (hk : 3 ≤ k) (pg : Graph) (n : ℕ) (omap : List ℕ)
    (hP : IsPolygon pg n) (_hlt : ∀ e ∈ pg, e.1 < e.2) (_hnd : pg.Nodup) (S : ℕ) (c₀ : Config)
    (hS : c₀.reg rFREE + CP4 k * (n + pg.length + 1) ≤ S) :
    HTB S (poly4 k) (fun c => Poly3Post pg n k omap c ∧ c = c₀)
      (fun c => c.out = c₀.out ++ (Poly.polyOut pg n k).flatten.map (fun p => omap.getD p 0) ∧
        SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧ ZeroFrom c.mem (c.reg rFREE) ∧
        c₀.reg rFREE ≤ c.reg rFREE ∧ c.reg rFREE ≤ c₀.reg rFREE + CP4 k * (n + pg.length + 1))
      (CP4 k * (n + pg.length + 1)) := by
  intro c ⟨hc, hcc⟩
  subst c
  have hb := hc.p2.p1.base
  have hM4 := M4_le (k := k) hP
  unfold M4 at hM4
  -- 1. `rK := k`
  have e₁ := ExecB.const (S := S) rK k c₀
  have hG₁ : IfRegs pg n k c₀ (c₀.setReg rK k) := by
    simp +decide only [IfRegs, setReg_reg, ↓reduceIte, hb.pn, hc.p2.p1.ns, hc.p2.np, and_self]
  obtain ⟨c₂, hc₂⟩ : ∃ c₂, c₂ = c₀.setReg rK k := ⟨_, rfl⟩
  rw [← hc₂] at e₁ hG₁
  have hfree₂ : c₂.reg rFREE = c₀.reg rFREE := by rw [hc₂]; rfl
  have hm₂ : c₂.mem = c₀.mem := by rw [hc₂]; rfl
  have ho₂ : c₂.out = c₀.out := by rw [hc₂]; rfl
  -- 2. the arrays `A` and `VAL`
  have e₃ := execB_run (S := S) (alloc rA gNS) (by decide) c₂ (AddrOK.of_memFree rfl)
  have e₄ := execB_run (S := S) (alloc rVAL gNP) (by decide) (RAM.run (alloc rA gNS) c₂)
    (AddrOK.of_memFree rfl)
  have hr₄ : (RAM.run (alloc rVAL gNP) (RAM.run (alloc rA gNS) c₂)).reg rA = c₀.reg rFREE ∧
      (RAM.run (alloc rVAL gNP) (RAM.run (alloc rA gNS) c₂)).reg rVAL =
        c₀.reg rFREE + (segOrder pg n).length ∧
      (RAM.run (alloc rVAL gNP) (RAM.run (alloc rA gNS) c₂)).reg rFREE = F₁ pg n k c₀ ∧
      (RAM.run (alloc rVAL gNP) (RAM.run (alloc rA gNS) c₂)).mem = c₂.mem ∧
      (RAM.run (alloc rVAL gNP) (RAM.run (alloc rA gNS) c₂)).out = c₂.out := by
    simp +decide only [run_alloc (show gNS ≠ rT by decide) (show rA ≠ gNS by decide),
      run_alloc (show gNP ≠ rT by decide) (show rVAL ≠ gNP by decide), setReg_reg, ↓reduceIte,
      setReg_mem, setReg_out, hfree₂, hG₁.2.1, hG₁.2.2.1, F₁, and_self]
  generalize RAM.run (alloc rA gNS) c₂ = c₃ at *
  generalize RAM.run (alloc rVAL gNP) c₃ = c₄ at *
  have hG₃ := (show RegIndep (wregs (alloc rA gNS)) (IfRegs pg n k c₀) by
    indep [IfRegs]).execB e₃ hG₁
  have hG₄ := (show RegIndep (wregs (alloc rVAL gNP)) (IfRegs pg n k c₀) by
    indep [IfRegs]).execB e₄ hG₃
  have hZ₀ := hb.free
  have hNS := P1.length_segOrder (pg := pg) (n := n)
  have hNSle := P1.length_segEnum_le (pg := pg) (n := n)
  have hNP := length_pool_le (k := k) hP
  -- the state before the backtracking
  have hF₄ : Fix pg n k c₀ c₄ := by
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩ := hG₄
    exact ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, hr₄.1, hr₄.2.1⟩
  have hB₄ : BtInv pg n k c₀ 0 c₄ := by
    refine ⟨hF₄, ?_, ?_, by rw [hr₄.2.2.1], by rw [hr₄.2.2.2.2, ho₂], by rw [hr₄.2.2.1]; simp⟩
    · rw [Nat.sub_zero, abAt_length, hr₄.2.2.2.1, hm₂]
      refine ⟨SameOn.refl _ _, fun j hj => ?_, fun i hi hp => ?_⟩
      · exact hZ₀ _ (by omega)
      · rw [tst_length] at hi; omega
    · rw [hr₄.2.2.1, hr₄.2.2.2.1, hm₂]
      exact hZ₀.mono (by simp only [F₁]; omega)
  -- 4. the backtracking
  obtain ⟨c₅, t₅, e₅, ⟨⟨hF₅, hB₅, hZ₅, hF1₅, hO₅, hFU₅⟩, -, -⟩, ht₅⟩ :=
    btLoop_spec (S := S) hP hk hc (by simp only [F₁]; omega) c₄ ⟨hB₄, hF₄.ns⟩
  rw [Nat.sub_self, abAt_zero] at hB₅
  -- 5. the output
  obtain ⟨c₆, t₆, e₆, ⟨hm₆, ho₆⟩, ht₆⟩ := outLoop_spec (S := S) hP hk hc
    (by simp only [F₁]; omega) hB₅.same
    (fun i hi => hB₅.val i (by rw [tst_zero]; exact Nat.zero_le _) hi) c₅ ⟨hF₅, rfl, hO₅⟩
  have hfree₆ : c₆.reg rFREE = c₅.reg rFREE := e₆.frame.reg rFREE (by decide)
  refine ⟨c₆, _, ExecB.seq e₁ (ExecB.seq e₃ (ExecB.seq e₄ (ExecB.seq e₅ e₆))),
    ⟨ho₆, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hm₆]; exact hB₅.same
  · rw [hm₆, hfree₆]; exact hZ₅
  · rw [hfree₆]; simp only [F₁] at hF1₅; omega
  · rw [hfree₆]; simp only [F₁] at hFU₅; omega
  · have c3 := cost_le_size (alloc rA gNS) c₂
    have c4 := cost_le_size (alloc rVAL gNP) c₃
    simp only [size_alloc] at c3 c4
    have h1 : (segOrder pg n).length * (Tseg k + 7) ≤ pg.length * (Tseg k + 7) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (pool pg n k).length * (14 * k + 10) ≤ pg.length * (rpathBound k * (14 * k + 10)) := by
      rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hNP
    have h3 : CP4 k * (n + pg.length + 1) = CP4 k * n + (pg.length * (Tseg k + 7) +
        pg.length * (2 * (Tsl k + 4)) + pg.length * (rpathBound k * (14 * k + 10)) +
        29 * pg.length) + CP4 k := by
      unfold CP4; ring
    have h5 : 2 * pg.length * (Tsl k + 4) = pg.length * (2 * (Tsl k + 4)) := by ring
    have h6 : 29 ≤ CP4 k := by unfold CP4; omega
    omega

/-- **P4 writes only `rT`, `rFREE` and registers at or above `gPx`.** -/
theorem poly4_wregs (k : ℕ) : ∀ r ∈ wregs (poly4 k), r = rT ∨ r = rFREE ∨ gPx ≤ r := by
  simp only [poly4, outLoop, outBody, segBody, slotBody, child, digBody, lookup, decode,
    decBody, divmod, ifLe, wregs_seq, wregs_forUp, wregs_ifLt, wregs_whileC, wregs_mul,
    List.forall_mem_append, List.forall_mem_cons, show wregs (.const rK k) = [rK] from rfl]
  and_intros
  all_goals decide

end STACS2027.RAM.P4
