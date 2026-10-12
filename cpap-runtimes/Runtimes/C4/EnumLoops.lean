module

public import Runtimes.C4.SizeRAM
public import Runtimes.C4.EnumLists
import Mathlib.Tactic

/-!
# Phase ENUM, part 1: the generation of the 2-paths as triples

The first part of ENUM writes every inserted 2-path `(key x y, z)` of
`ins g (peelPos g)` as a triple: its key components at `X = F`, `Y = F + P` and its centre at
`Z = F + 2P` (`P = numPaths g (peelPos g)` cells each, `F` the initial `rFREE`), in insertion
order. The loops: allocate `X`, `Y`, `Z`; then for every vertex
`v` (`forUp xV gN outerB`, `xOv = OFF[v]`, `xDv = ODEG[v] = |l|`, `l = outL g (peelPos g) v`):

* type 1: for `a < |l|` (`mid1`): `j = l[a]`; for `b < |out j|` (`body1`): write
  `(v, j, out j [b])`;
* type 2: for `a < |l|` (`mid2`): `j = l[a]`; for `b ∈ [a + 1, |l|)` (`body2`): write
  `(j, v, l[b])`.

The invariants name the written prefix explicitly (`EnumLists.lean`); the costs telescope
(`HTB.forUpTele`, `HTB.forRangeTele`) with the weight `W L = KG · |L|` (one write costs at most
`KG - 4`), plus `14` per type-1 and `13` per type-2 outer iteration and `27 |l| + 14` per
vertex.

**`gen_spec`**: from `SizePost g`, `gen` reaches `GRep g c₀ (ins g (peelPos g))` (the triples
of all inserted 2-paths at `gTX`, `gTY`, `gTZ`) within `CG · (m + 1 + P)` steps, without output,
storing only at or above the initial `rFREE`, accessing only the addresses below any
`S ≥ F + 3P` (`genEnd`).
-/

@[expose] public section

namespace STACS2027.Runtimes.C4

open STACS2027 STACS2027.Algo STACS2027.RAM Finset

/-! ### The program -/

/-- Order the endpoints: `xX := min`, `xY := max`. -/
def insKey : Stmt := ifLt xY xX (swap xX xY) .skip

/-- Write the triple `(xX, xY, xZ)` (endpoints ordered first) at index `gNP`, `gNP += 1`. -/
def writeP : Stmt :=
  .seq insKey (.seq (st gTX gNP xX) (.seq (st gTY gNP xY) (.seq (st gTZ gNP xZ) (inc gNP))))

/-- Type 1, before the write: `k := OADJ[OFF[j] + b]`, the 2-path `v – j – k`. -/
def pre1 : Stmt :=
  .seq (.add xQ xOj xB) (.seq (ld xK gOADJ xQ) (.seq (mov xX xV) (.seq (mov xZ xJ) (mov xY xK))))
/-- Type 1, one 2-path. -/
def body1 : Stmt := .seq pre1 writeP
/-- Type 1, before the inner loop: `j := OADJ[OFF[v] + a]`, `xOj := OFF[j]`, `xDj := ODEG[j]`. -/
def midPre1 : Stmt :=
  .seq (.add xQ xOv xA) (.seq (ld xJ gOADJ xQ) (.seq (ld xOj gOFF xJ) (ld xDj gODEG xJ)))
/-- Type 1, one out-neighbour `j` of `v`. -/
def mid1 : Stmt := .seq midPre1 (forUp xB xDj body1)
/-- Type 2, before the write: `k := OADJ[OFF[v] + b]`, the 2-path `j – v – k`. -/
def pre2 : Stmt :=
  .seq (.add xQ xOv xB) (.seq (ld xK gOADJ xQ) (.seq (mov xX xJ) (.seq (mov xZ xV) (mov xY xK))))
/-- Type 2, one 2-path. -/
def body2 : Stmt := .seq pre2 writeP
/-- Type 2, before the inner loop: `j := OADJ[OFF[v] + a]`, `xA1 := a + 1`. -/
def midPre2 : Stmt := .seq (.add xQ xOv xA) (.seq (ld xJ gOADJ xQ) (addc xA1 xA 1))
/-- Type 2, one index `a`. -/
def mid2 : Stmt := .seq midPre2 (forRange xB xA1 xDv body2)
/-- One vertex `v`: `xOv := OFF[v]`, `xDv := ODEG[v]`. -/
def outerPre : Stmt := .seq (ld xOv gOFF xV) (ld xDv gODEG xV)
/-- One vertex `v`. -/
def outerB : Stmt := .seq outerPre (.seq (forUp xA xDv mid1) (forUp xA xDv mid2))
/-- The allocation of the triple arrays `X`, `Y`, `Z` (`P` cells each). -/
def genAlloc : Stmt :=
  .seq (alloc gTX gP) (.seq (alloc gTY gP) (.seq (alloc gTZ gP) (.const gNP 0)))
/-- **ENUM, part 1: the generation.** -/
def gen : Stmt := .seq genAlloc (forUp xV gN outerB)

/-! ### Layout and representation -/

/-- The end of the generation's memory: the three triple arrays. -/
def genEnd (g : Graph) (F : ℕ) : ℕ := F + 3 * numPaths g (peelPos g)

/-- The registers fixed during the generation (`F = c₀.reg rFREE`). -/
@[mk_iff] structure GGlob (g : Graph) (c₀ c : Config) : Prop where
  n : c.reg gN = numV g
  off : c.reg gOFF = c₀.reg gOFF
  odeg : c.reg gODEG = c₀.reg gODEG
  oadj : c.reg gOADJ = c₀.reg gOADJ
  p : c.reg gP = numPaths g (peelPos g)
  tx : c.reg gTX = c₀.reg rFREE
  ty : c.reg gTY = c₀.reg rFREE + numPaths g (peelPos g)
  tz : c.reg gTZ = c₀.reg rFREE + 2 * numPaths g (peelPos g)
  free : c.reg rFREE = genEnd g (c₀.reg rFREE)

/-- The memory during the generation: the triples of `L`. -/
structure GMem (g : Graph) (c₀ : Config) (L : Ins) (m : ℕ → ℕ) : Prop where
  same : SameOn (· < c₀.reg rFREE) c₀.mem m
  len : L.length ≤ numPaths g (peelPos g)
  tx : Arr m (c₀.reg rFREE) (L.map (·.1.1))
  ty : Arr m (c₀.reg rFREE + numPaths g (peelPos g)) (L.map (·.1.2))
  tz : Arr m (c₀.reg rFREE + 2 * numPaths g (peelPos g)) (L.map (·.2))
  zero : ZeroFrom m (genEnd g (c₀.reg rFREE))

/-- The machine has written the triples of `L` (a prefix of the insertions). -/
@[mk_iff] structure GRep (g : Graph) (c₀ : Config) (L : Ins) (c : Config) : Prop where
  glob : GGlob g c₀ c
  np : c.reg gNP = L.length
  pre : L <+: ins g (peelPos g)
  mem : GMem g c₀ L c.mem

/-- The scratch registers of the generation. -/
def WG : List ℕ := [rT, xI, xJ, xA, xB, xV, xW, xX, xY, xZ, xH, xQ, xD, xS, xP, xK, xOv, xDv,
  xOj, xDj, xC, xA1]

theorem GGlob.regIndep (g : Graph) (c₀ : Config) : RegIndep (gNP :: WG) (GGlob g c₀) := by
  indep [gGlob_iff, WG]

theorem GRep.indep (g : Graph) (c₀ : Config) (L : Ins) : Indep WG (GRep g c₀ L) := by
  indep [gRep_iff, gGlob_iff, WG]

/-- **Writing a triple** at index `|L|`. -/
theorem GMem.write {g : Graph} {c₀ : Config} {L : Ins} {m : ℕ → ℕ} (h : GMem g c₀ L m)
    (hlt : L.length < numPaths g (peelPos g)) (e : (ℕ × ℕ) × ℕ) :
    GMem g c₀ (L ++ [e])
      (RAM.upd (RAM.upd (RAM.upd m (c₀.reg rFREE + L.length) e.1.1)
        (c₀.reg rFREE + numPaths g (peelPos g) + L.length) e.1.2)
        (c₀.reg rFREE + 2 * numPaths g (peelPos g) + L.length) e.2) := by
  have hz := h.zero
  unfold genEnd at hz
  refine ⟨((h.same.upd_of_ge (by omega) _).upd_of_ge (by omega) _).upd_of_ge (by omega) _,
    by simp; omega, ?_, ?_, ?_, ?_⟩
  · rw [List.map_append, List.map_singleton]
    exact ((h.tx.upd_snoc (by simp)).upd_of_disjoint (by simp; omega)).upd_of_disjoint
      (by simp; omega)
  · rw [List.map_append, List.map_singleton]
    exact ((h.ty.upd_of_disjoint (by simp; omega)).upd_snoc (by simp)).upd_of_disjoint
      (by simp; omega)
  · rw [List.map_append, List.map_singleton]
    exact ((h.tz.upd_of_disjoint (by simp; omega)).upd_of_disjoint (by simp; omega)).upd_snoc
      (by simp)
  · unfold genEnd
    exact ((h.zero.upd (by unfold genEnd; omega)).upd (by unfold genEnd; omega)).upd
      (by unfold genEnd; omega)

/-- The registers written by the write block. -/
def WI : List ℕ := [rT, gNP, xX, xY]

theorem writeP_wregs : ∀ r ∈ wregs writeP, r ∈ WI := by decide +kernel

/-- The constant per written 2-path of the weight. -/
def KG : ℕ := 30

/-- The weight of the telescoping bounds. -/
abbrev W (L : Ins) : ℕ := KG * L.length

section

variable {g : Graph} {c₀ : Config} {S : ℕ}

local notation "pos" => peelPos g
local notation "out" => outL g (peelPos g)
local notation "ps" => R1.ps (idEdges g)

theorem W_snoc (L : Ins) (e : (ℕ × ℕ) × ℕ) : W (L ++ [e]) = W L + KG := by
  simp only [W, List.length_append, List.length_singleton]; ring

theorem W_mono {L L' : Ins} (h : L <+: L') : W L ≤ W L' :=
  Nat.mul_le_mul_left _ h.length_le

/-- **Writing** the 2-path `x – z – y`. -/
theorem writeP_spec (hSp : genEnd g (c₀.reg rFREE) ≤ S) {L : Ins} {x y z : ℕ}
    (hpre : L ++ [(key x y, z)] <+: ins g (peelPos g)) :
    HTB S writeP (fun c => GRep g c₀ L c ∧ c.reg xX = x ∧ c.reg xZ = z ∧ c.reg xY = y)
      (GRep g c₀ (L ++ [(key x y, z)])) (6 + 8) := by
  set k := key x y with hk
  have hlt : L.length < numPaths g (peelPos g) := by
    have := hpre.length_le
    simp only [List.length_append, List.length_singleton] at this
    exact this
  -- the key
  have h₁ : HTB S insKey (fun c => GRep g c₀ L c ∧ c.reg xX = x ∧ c.reg xZ = z ∧ c.reg xY = y)
      (fun c => GRep g c₀ L c ∧ c.reg xX = k.1 ∧ c.reg xZ = z ∧ c.reg xY = k.2) 6 := by
    refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hR, hX, hZ, hY⟩ => ?_
    rw [insKey, run_ifLt]
    by_cases hyx : c.reg xY < c.reg xX
    · simp only [hyx, ↓reduceIte, run_swap (show xX ≠ xY by decide)]
      refine ⟨(GRep.indep g c₀ L).setReg (by decide) _ ((GRep.indep g c₀ L).setReg (by decide) _
        ((GRep.indep g c₀ L).setReg (by decide) _ hR)), ?_, ?_, ?_⟩
      · simp +decide [hY, hk, key]; omega
      · simp +decide [hZ]
      · simp +decide [hX, hk, key]; omega
    · simp only [hyx, ↓reduceIte, run_skip]
      refine ⟨(GRep.indep g c₀ L).setReg (by decide) _ hR, ?_, ?_, ?_⟩
      · simp +decide [hX, hk, key]; omega
      · simp +decide [hZ]
      · simp +decide [hY, hk, key]; omega
  -- the three stores
  have h₂ : HTB S (.seq (st gTX gNP xX) (.seq (st gTY gNP xY) (.seq (st gTZ gNP xZ) (inc gNP))))
      (fun c => GRep g c₀ L c ∧ c.reg xX = k.1 ∧ c.reg xZ = z ∧ c.reg xY = k.2)
      (GRep g c₀ (L ++ [(k, z)])) 8 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨hR, hX, hZ, hY⟩ => ?_
    have hG := hR.glob
    have hnp := hR.np
    unfold genEnd at hSp
    refine ⟨by addr_ok [hG.tx, hG.ty, hG.tz, hnp], ?_⟩
    have hm := hR.mem.write hlt (k, z)
    refine ⟨(GGlob.regIndep g c₀).run_of_sub (by decide) (by decide) hG, ?_, hpre, ?_⟩
    · simp +decide [run_st, run_inc, hnp]
    · simpa +decide [run_st, run_inc, hG.tx, hG.ty, hG.tz, hnp, hX, hY, hZ] using hm
  exact h₁.seq h₂

/-- The read-only arrays of the generation fit below `S`. -/
theorem gen_fits (hS : SizePost g c₀) (hSp : genEnd g (c₀.reg rFREE) ≤ S) :
    c₀.reg gOFF + (numV g + 1) ≤ S ∧ c₀.reg gODEG + numV g ≤ S ∧
      c₀.reg gOADJ + 2 * (idEdges g).length ≤ S := by
  have h1 := hS.orient.peel.base.bounds
  have h2 := hS.orient.below
  unfold genEnd at hSp
  omega

/-- The out-list of `v` lies inside the segment of `nb v`. -/
theorem ps_out_le {v : ℕ} (hv : v < numV g) :
    R1.ps (idEdges g) v + (outL g (peelPos g) v).length ≤ 2 * (idEdges g).length := by
  have h1 : R1.ps (idEdges g) v + (nb g v).length ≤ R1.ps (idEdges g) (numV g) :=
    R1.ps_add_le (idEdges g) hv
  have h2 : (outL g (peelPos g) v).length ≤ (nb g v).length := length_outL_le _ _ _
  rw [R1.idEdges_ps] at h1
  omega

/-! ### Type 1 -/

/-- The invariant of the inner type-1 loop. -/
def I1 (g : Graph) (c₀ : Config) (v a b : ℕ) (c : Config) : Prop :=
  GRep g c₀ (insPre g (peelPos g) v ++ t1In g (peelPos g) v a b) c ∧
    c.reg xV = v ∧ c.reg xOv = R1.ps (idEdges g) v ∧ c.reg xA = a ∧
    c.reg xDv = (outL g (peelPos g) v).length ∧ c.reg xJ = (outL g (peelPos g) v).getD a 0 ∧
    c.reg xOj = R1.ps (idEdges g) ((outL g (peelPos g) v).getD a 0)

theorem I1.indep (g : Graph) (c₀ : Config) (v a b : ℕ) : Indep [xB, rT] (I1 g c₀ v a b) := by
  unfold I1
  exact ((GRep.indep g c₀ _).mono (by decide)).and (by indep)

/-- The prefix up to the inner type-1 position is a prefix of `ins`. -/
theorem t1_prefix {v a b : ℕ} (hv : v < numV g) (ha : a < (out v).length) :
    insPre g pos v ++ t1In g pos v a b <+: ins g pos := by
  refine ((List.prefix_append_right_inj _).mpr ((t1In_prefix ha b).trans
    (t1Pre_prefix (show a + 1 ≤ (out v).length by omega)))).trans ?_
  refine List.IsPrefix.trans ?_ (insPre_prefix (show v + 1 ≤ numV g by omega))
  rw [insPre_succ]
  exact List.prefix_append _ _

theorem body1_spec (hS : SizePost g c₀) (hSp : genEnd g (c₀.reg rFREE) ≤ S) {v a b : ℕ}
    (hv : v < numV g) (ha : a < (out v).length) (hb : b < (out ((out v).getD a 0)).length) :
    HTB S body1 (fun c => I1 g c₀ v a b c ∧ c.reg xB = b ∧
        c.reg xDj = (out ((out v).getD a 0)).length)
      (fun c => I1 g c₀ v a (b + 1) c ∧ c.reg xB = b ∧
        c.reg xDj = (out ((out v).getD a 0)).length)
      (W (insPre g pos v ++ t1In g pos v a (b + 1)) - W (insPre g pos v ++ t1In g pos v a b) - 4) := by
  set j := (out v).getD a 0 with hj
  set k := (out j).getD b 0 with hk
  have hjm : j ∈ out v := by rw [hj, getD_eq_getElem' ha]; exact List.getElem_mem _
  have hkm : k ∈ out j := by rw [hk, getD_eq_getElem' hb]; exact List.getElem_mem _
  have hjN : j < numV g := lt_of_mem_outL hjm
  have hkN : k < numV g := lt_of_mem_outL hkm
  set L := insPre g pos v ++ t1In g pos v a b with hL
  have hsucc : insPre g pos v ++ t1In g pos v a (b + 1) = L ++ [(key v k, j)] := by
    rw [t1In_succ hb, ← List.append_assoc]; rfl
  have hpre : L ++ [(key v k, j)] <+: ins g pos := hsucc ▸ t1_prefix hv ha
  have hO := hS.orient
  -- before the write
  have h₁ : HTB S pre1 (fun c => I1 g c₀ v a b c ∧ c.reg xB = b ∧ c.reg xDj = (out j).length)
      (fun c => (GRep g c₀ L c ∧ c.reg xX = v ∧ c.reg xZ = j ∧ c.reg xY = k) ∧
        (c.reg xV = v ∧ c.reg xOv = ps v ∧ c.reg xA = a ∧ c.reg xDv = (out v).length ∧
          c.reg xJ = j ∧ c.reg xOj = ps j ∧ c.reg xB = b ∧ c.reg xDj = (out j).length)) 9 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hR, hV, hOv, hA, hDv, hJ, hOj⟩, hB, hDj⟩ => ?_
    rw [← hj] at hJ hOj
    have hG := hR.glob
    have hk' : c.mem (c₀.reg gOADJ + (ps j + b)) = k := hO.oadjR hR.mem.same hjN hb
    have hF := gen_fits hS hSp
    have hpj := ps_out_le (g := g) hjN
    refine ⟨by addr_ok [pre1, hG.oadj, hOj, hB], ?_⟩
    refine ⟨⟨(GRep.indep g c₀ _).mono (W' := [xQ, xK, rT, xX, xZ, xY]) (by decide) c _
      (agree_run (by decide) rfl rfl (by decide) c) hR, ?_, ?_, ?_⟩, ?_⟩
    · simp +decide [pre1, run_mov, hV]
    · simp +decide [pre1, run_mov, hJ]
    · simp +decide [pre1, run_mov, hG.oadj, hOj, hB, hk']
    · simp +decide [pre1, run_mov, hV, hOv, hA, hDv, hJ, hOj, hB, hDj]
  have h₂ := (writeP_spec hSp hpre).frameReg
    (F := fun c => c.reg xV = v ∧ c.reg xOv = ps v ∧ c.reg xA = a ∧ c.reg xDv = (out v).length ∧
          c.reg xJ = j ∧ c.reg xOj = ps j ∧ c.reg xB = b ∧ c.reg xDj = (out j).length)
    ((by indep : RegIndep WI _).mono writeP_wregs)
  refine (h₁.seq h₂).mono (fun c h => h) (fun c ⟨hR, hV, hOv, hA, hDv, hJ, hOj, hB, hDj⟩ =>
    ⟨⟨by rw [hsucc]; exact hR, hV, hOv, hA, hDv, hJ, hOj⟩, hB, hDj⟩) ?_
  rw [hsucc, W_snoc]
  simp only [KG]
  omega

/-- The invariant of the middle type-1 loop. -/
def M1 (g : Graph) (c₀ : Config) (v a : ℕ) (c : Config) : Prop :=
  GRep g c₀ (insPre g (peelPos g) v ++ t1Pre g (peelPos g) v a) c ∧
    c.reg xV = v ∧ c.reg xOv = R1.ps (idEdges g) v

theorem M1.indep (g : Graph) (c₀ : Config) (v a : ℕ) : Indep [xA, rT] (M1 g c₀ v a) := by
  unfold M1
  exact ((GRep.indep g c₀ _).mono (by decide)).and (by indep)

/-- The bound function of the middle type-1 loop. -/
def f1 (g : Graph) (v a : ℕ) : ℕ := W (insPre g (peelPos g) v ++ t1Pre g (peelPos g) v a) + 14 * a

theorem W_t1In_step {v a b : ℕ} (hb : b < (out ((out v).getD a 0)).length) :
    W (insPre g pos v ++ t1In g pos v a b) + 4 ≤ W (insPre g pos v ++ t1In g pos v a (b + 1)) := by
  rw [t1In_succ hb, ← List.append_assoc, W_snoc]
  simp only [KG]
  omega

theorem mid1_spec (hS : SizePost g c₀) (hSp : genEnd g (c₀.reg rFREE) ≤ S) {v a : ℕ}
    (hv : v < numV g) (ha : a < (out v).length) :
    HTB S mid1 (fun c => M1 g c₀ v a c ∧ c.reg xA = a ∧ c.reg xDv = (out v).length)
      (fun c => M1 g c₀ v (a + 1) c ∧ c.reg xA = a ∧ c.reg xDv = (out v).length)
      (f1 g v (a + 1) - f1 g v a - 4) := by
  set j := (out v).getD a 0 with hj
  have hjm : j ∈ out v := by rw [hj, getD_eq_getElem' ha]; exact List.getElem_mem _
  have hjN : j < numV g := lt_of_mem_outL hjm
  have hO := hS.orient
  have h₁ : HTB S midPre1 (fun c => M1 g c₀ v a c ∧ c.reg xA = a ∧ c.reg xDv = (out v).length)
      (fun c => I1 g c₀ v a 0 c ∧ c.reg xDj = (out j).length) 7 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hR, hV, hOv⟩, hA, hDv⟩ => ?_
    have hG := hR.glob
    have hS' := hR.mem.same
    have hj' : c.mem (c₀.reg gOADJ + (ps v + a)) = j := hO.oadjR hS' hv ha
    have hoj : c.mem (c₀.reg gOFF + j) = ps j := hO.peel.base.offR hS' (by omega)
    have hdj : c.mem (c₀.reg gODEG + j) = (out j).length := hO.odegR hS' hjN
    have hF := gen_fits hS hSp
    have hpv := ps_out_le (g := g) hv
    refine ⟨by addr_ok [midPre1, hG.oadj, hG.off, hG.odeg, hOv, hA, hj'], ?_⟩
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [t1In_zero]
      exact (GRep.indep g c₀ _).mono (W' := [xQ, xJ, xOj, xDj]) (by decide) c _
        (agree_run (by decide) rfl rfl (by decide) c) hR
    · simp +decide [midPre1, hV]
    · simp +decide [midPre1, hOv]
    · simp +decide [midPre1, hA]
    · simp +decide [midPre1, hDv]
    · rw [← hj]; simp +decide [midPre1, hG.oadj, hOv, hA, hj']
    · rw [← hj]; simp +decide [midPre1, hG.oadj, hG.off, hOv, hA, hj', hoj]
    · simp +decide [midPre1, hG.oadj, hG.odeg, hOv, hA, hj', hdj]
  have h₂ := HTB.forUpTele (S := S) (i := xB) (n := xDj) (N := (out j).length) (body := body1)
    (I1 g c₀ v a) (fun b => W (insPre g pos v ++ t1In g pos v a b)) (by decide) (by decide)
    (by decide) (fun b => I1.indep g c₀ v a b) (fun b hb => W_t1In_step hb)
    (fun b hb => body1_spec hS hSp hv ha hb)
  have hmono : W (insPre g pos v ++ t1Pre g pos v a) ≤ W (insPre g pos v ++ t1Pre g pos v (a + 1)) :=
    W_mono ((List.prefix_append_right_inj _).mpr (t1Pre_prefix (by omega)))
  refine (h₁.seq h₂).mono (fun c h => h) (fun c ⟨⟨hR, hV, hOv, hA, hDv, _, _⟩, _, _⟩ =>
    ⟨⟨by rw [← t1In_full ha]; exact hR, hV, hOv⟩, hA, hDv⟩) ?_
  rw [t1In_full ha, t1In_zero]
  simp only [f1]
  omega

/-! ### Type 2 -/

/-- The invariant of the inner type-2 loop. -/
def I2 (g : Graph) (c₀ : Config) (v a b : ℕ) (c : Config) : Prop :=
  GRep g c₀ (insPre g (peelPos g) v ++ t1Pre g (peelPos g) v (outL g (peelPos g) v).length ++
        t2In g (peelPos g) v a b) c ∧
    c.reg xV = v ∧ c.reg xOv = R1.ps (idEdges g) v ∧ c.reg xA = a ∧
    c.reg xJ = (outL g (peelPos g) v).getD a 0

theorem I2.indep (g : Graph) (c₀ : Config) (v a b : ℕ) : Indep [xB, rT] (I2 g c₀ v a b) := by
  unfold I2
  exact ((GRep.indep g c₀ _).mono (by decide)).and (by indep)

theorem t2_prefix {v a b : ℕ} (hv : v < numV g) (ha : a < (out v).length)
    (hb : b ≤ (out v).length) :
    insPre g pos v ++ t1Pre g pos v (out v).length ++ t2In g pos v a b <+: ins g pos := by
  refine ((List.prefix_append_right_inj _).mpr ((t2In_prefix ha hb).trans
    (t2Pre_prefix (show a + 1 ≤ (out v).length by omega)))).trans ?_
  rw [← insPre_succ]
  exact insPre_prefix (show v + 1 ≤ numV g by omega)

theorem body2_spec (hS : SizePost g c₀) (hSp : genEnd g (c₀.reg rFREE) ≤ S) {v a b : ℕ}
    (hv : v < numV g) (ha : a < (out v).length) (hab : a + 1 ≤ b) (hb : b < (out v).length) :
    HTB S body2 (fun c => I2 g c₀ v a b c ∧ c.reg xB = b ∧ c.reg xDv = (out v).length)
      (fun c => I2 g c₀ v a (b + 1) c ∧ c.reg xB = b ∧ c.reg xDv = (out v).length)
      (W (insPre g pos v ++ t1Pre g pos v (out v).length ++ t2In g pos v a (b + 1)) -
        W (insPre g pos v ++ t1Pre g pos v (out v).length ++ t2In g pos v a b) - 4) := by
  set j := (out v).getD a 0 with hj
  set k := (out v).getD b 0 with hk
  have hjm : j ∈ out v := by rw [hj, getD_eq_getElem' ha]; exact List.getElem_mem _
  have hkm : k ∈ out v := by rw [hk, getD_eq_getElem' hb]; exact List.getElem_mem _
  have hjN : j < numV g := lt_of_mem_outL hjm
  have hkN : k < numV g := lt_of_mem_outL hkm
  set L := insPre g pos v ++ t1Pre g pos v (out v).length ++ t2In g pos v a b with hL
  have hsucc : insPre g pos v ++ t1Pre g pos v (out v).length ++ t2In g pos v a (b + 1) =
      L ++ [(key j k, v)] := by
    rw [t2In_succ hab, ← List.append_assoc]; rfl
  have hpre : L ++ [(key j k, v)] <+: ins g pos := hsucc ▸ t2_prefix hv ha (by omega)
  have hO := hS.orient
  have h₁ : HTB S pre2 (fun c => I2 g c₀ v a b c ∧ c.reg xB = b ∧ c.reg xDv = (out v).length)
      (fun c => (GRep g c₀ L c ∧ c.reg xX = j ∧ c.reg xZ = v ∧ c.reg xY = k) ∧
        (c.reg xV = v ∧ c.reg xOv = ps v ∧ c.reg xA = a ∧ c.reg xJ = j ∧ c.reg xB = b ∧
          c.reg xDv = (out v).length)) 9 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hR, hV, hOv, hA, hJ⟩, hB, hDv⟩ => ?_
    rw [← hj] at hJ
    have hG := hR.glob
    have hk' : c.mem (c₀.reg gOADJ + (ps v + b)) = k := hO.oadjR hR.mem.same hv hb
    have hF := gen_fits hS hSp
    have hpv := ps_out_le (g := g) hv
    refine ⟨by addr_ok [pre2, hG.oadj, hOv, hB], ?_⟩
    refine ⟨⟨(GRep.indep g c₀ _).mono (W' := [xQ, xK, rT, xX, xZ, xY]) (by decide) c _
      (agree_run (by decide) rfl rfl (by decide) c) hR, ?_, ?_, ?_⟩, ?_⟩
    · simp +decide [pre2, run_mov, hJ]
    · simp +decide [pre2, run_mov, hV]
    · simp +decide [pre2, run_mov, hG.oadj, hOv, hB, hk']
    · simp +decide [pre2, run_mov, hV, hOv, hA, hJ, hB, hDv]
  have h₂ := (writeP_spec hSp hpre).frameReg
    (F := fun c => c.reg xV = v ∧ c.reg xOv = ps v ∧ c.reg xA = a ∧ c.reg xJ = j ∧
      c.reg xB = b ∧ c.reg xDv = (out v).length)
    ((by indep : RegIndep WI _).mono writeP_wregs)
  refine (h₁.seq h₂).mono (fun c h => h) (fun c ⟨hR, hV, hOv, hA, hJ, hB, hDv⟩ =>
    ⟨⟨by rw [hsucc]; exact hR, hV, hOv, hA, hJ⟩, hB, hDv⟩) ?_
  rw [hsucc, W_snoc]
  simp only [KG]
  omega

/-- The invariant of the middle type-2 loop. -/
def M2 (g : Graph) (c₀ : Config) (v a : ℕ) (c : Config) : Prop :=
  GRep g c₀ (insPre g (peelPos g) v ++ t1Pre g (peelPos g) v (outL g (peelPos g) v).length ++
        t2Pre g (peelPos g) v a) c ∧
    c.reg xV = v ∧ c.reg xOv = R1.ps (idEdges g) v

theorem M2.indep (g : Graph) (c₀ : Config) (v a : ℕ) : Indep [xA, rT] (M2 g c₀ v a) := by
  unfold M2
  exact ((GRep.indep g c₀ _).mono (by decide)).and (by indep)

/-- The bound function of the middle type-2 loop. -/
def f2 (g : Graph) (v a : ℕ) : ℕ :=
  W (insPre g (peelPos g) v ++ t1Pre g (peelPos g) v (outL g (peelPos g) v).length ++
    t2Pre g (peelPos g) v a) + 13 * a

theorem W_t2In_step {v a b : ℕ} (hab : a + 1 ≤ b) :
    W (insPre g pos v ++ t1Pre g pos v (out v).length ++ t2In g pos v a b) + 4 ≤
      W (insPre g pos v ++ t1Pre g pos v (out v).length ++ t2In g pos v a (b + 1)) := by
  rw [t2In_succ hab, ← List.append_assoc, W_snoc]
  simp only [KG]
  omega

theorem mid2_spec (hS : SizePost g c₀) (hSp : genEnd g (c₀.reg rFREE) ≤ S) {v a : ℕ}
    (hv : v < numV g) (ha : a < (out v).length) :
    HTB S mid2 (fun c => M2 g c₀ v a c ∧ c.reg xA = a ∧ c.reg xDv = (out v).length)
      (fun c => M2 g c₀ v (a + 1) c ∧ c.reg xA = a ∧ c.reg xDv = (out v).length)
      (f2 g v (a + 1) - f2 g v a - 4) := by
  set j := (out v).getD a 0 with hj
  have hO := hS.orient
  have h₁ : HTB S midPre2 (fun c => M2 g c₀ v a c ∧ c.reg xA = a ∧ c.reg xDv = (out v).length)
      (fun c => I2 g c₀ v a (a + 1) c ∧ c.reg xA1 = a + 1 ∧ c.reg xDv = (out v).length ∧
        a + 1 ≤ (out v).length) 5 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hR, hV, hOv⟩, hA, hDv⟩ => ?_
    have hG := hR.glob
    have hj' : c.mem (c₀.reg gOADJ + (ps v + a)) = j := hO.oadjR hR.mem.same hv ha
    have hF := gen_fits hS hSp
    have hpv := ps_out_le (g := g) hv
    refine ⟨by addr_ok [midPre2, hG.oadj, hOv, hA], ?_⟩
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, by omega⟩
    · rw [t2In_start]
      exact (GRep.indep g c₀ _).mono (W' := [xQ, xJ, rT, xA1]) (by decide) c _
        (agree_run (by decide) rfl rfl (by decide) c) hR
    · simp +decide [midPre2, run_addc, hV]
    · simp +decide [midPre2, run_addc, hOv]
    · simp +decide [midPre2, run_addc, hA]
    · rw [← hj]; simp +decide [midPre2, run_addc, hG.oadj, hOv, hA, hj']
    · simp +decide [midPre2, run_addc, hA]
    · simp +decide [midPre2, run_addc, hDv]
  have h₂ := HTB.forRangeTele (S := S) (i := xB) (a := xA1) (n := xDv) (A := a + 1)
    (N := (out v).length) (body := body2) (I2 g c₀ v a)
    (fun b => W (insPre g pos v ++ t1Pre g pos v (out v).length ++ t2In g pos v a b))
    (by decide) (by decide) (by decide) (by decide) (fun b => I2.indep g c₀ v a b)
    (fun b hab _ => W_t2In_step hab) (fun b hab hb => body2_spec hS hSp hv ha hab hb)
  have hmono : W (insPre g pos v ++ t1Pre g pos v (out v).length ++ t2Pre g pos v a) ≤
      W (insPre g pos v ++ t1Pre g pos v (out v).length ++ t2Pre g pos v (a + 1)) :=
    W_mono ((List.prefix_append_right_inj _).mpr (t2Pre_prefix (by omega)))
  refine (h₁.seq h₂).mono (fun c h => h) (fun c ⟨⟨hR, hV, hOv, hA, _⟩, _, hDv⟩ =>
    ⟨⟨by rw [← t2In_full v a]; exact hR, hV, hOv⟩, hA, hDv⟩) ?_
  rw [t2In_full v a, t2In_start]
  simp only [f2]
  omega

/-! ### One vertex -/

/-- The bound function of the outer loop. -/
def fo (g : Graph) (v : ℕ) : ℕ :=
  W (insPre g (peelPos g) v) + ∑ u ∈ range v, (27 * (outL g (peelPos g) u).length + 14)

theorem outerB_spec (hS : SizePost g c₀) (hSp : genEnd g (c₀.reg rFREE) ≤ S) {v : ℕ}
    (hv : v < numV g) :
    HTB S outerB (fun c => GRep g c₀ (insPre g pos v) c ∧ c.reg xV = v ∧ c.reg gN = numV g)
      (fun c => GRep g c₀ (insPre g pos (v + 1)) c ∧ c.reg xV = v ∧ c.reg gN = numV g)
      (fo g (v + 1) - fo g v - 4) := by
  have hO := hS.orient
  have h₀ : HTB S outerPre (fun c => GRep g c₀ (insPre g pos v) c ∧ c.reg xV = v ∧
        c.reg gN = numV g)
      (fun c => M1 g c₀ v 0 c ∧ c.reg xDv = (out v).length) 4 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨hR, hV, _⟩ => ?_
    have hG := hR.glob
    have hov : c.mem (c₀.reg gOFF + v) = ps v := hO.peel.base.offR hR.mem.same (by omega)
    have hdv : c.mem (c₀.reg gODEG + v) = (out v).length := hO.odegR hR.mem.same hv
    have hF := gen_fits hS hSp
    refine ⟨by addr_ok [outerPre, hG.off, hG.odeg, hV], ?_⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [t1Pre_zero, List.append_nil]
      exact (GRep.indep g c₀ _).mono (W' := [xOv, xDv]) (by decide) c _
        (agree_run (by decide) rfl rfl (by decide) c) hR
    · simp +decide [outerPre, hV]
    · simp +decide [outerPre, hG.off, hV, hov]
    · simp +decide [outerPre, hG.odeg, hV, hdv]
  have h₁ := HTB.forUpTele (S := S) (i := xA) (n := xDv) (N := (out v).length) (body := mid1)
    (M1 g c₀ v) (f1 g v) (by decide) (by decide) (by decide) (fun a => M1.indep g c₀ v a)
    (fun a ha => by
      have := W_mono ((List.prefix_append_right_inj (insPre g pos v)).mpr
        (@t1Pre_prefix g (peelPos g) v a (a + 1) (by omega)))
      simp only [f1] at this ⊢
      omega)
    (fun a ha => mid1_spec hS hSp hv ha)
  have h₂ := HTB.forUpTele (S := S) (i := xA) (n := xDv) (N := (out v).length) (body := mid2)
    (M2 g c₀ v) (f2 g v) (by decide) (by decide) (by decide) (fun a => M2.indep g c₀ v a)
    (fun a ha => by
      have := W_mono ((List.prefix_append_right_inj
        (insPre g pos v ++ t1Pre g pos v (out v).length)).mpr
        (@t2Pre_prefix g (peelPos g) v a (a + 1) (by omega)))
      simp only [f2] at this ⊢
      omega)
    (fun a ha => mid2_spec hS hSp hv ha)
  have hm1 : f1 g v 0 ≤ f1 g v (out v).length := by
    have := W_mono ((List.prefix_append_right_inj (insPre g pos v)).mpr
      (@t1Pre_prefix g (peelPos g) v 0 (out v).length (by omega)))
    simp only [f1] at this ⊢
    omega
  have hm2 : f2 g v 0 ≤ f2 g v (out v).length := by
    have := W_mono ((List.prefix_append_right_inj
        (insPre g pos v ++ t1Pre g pos v (out v).length)).mpr
        (@t2Pre_prefix g (peelPos g) v 0 (out v).length (by omega)))
    simp only [f2] at this ⊢
    omega
  refine (h₀.seq ((h₁.post (Q' := fun c => M2 g c₀ v 0 c ∧ c.reg xDv = (out v).length)
    fun c ⟨hM, _, hDv⟩ => ⟨by unfold M2; rw [t2Pre_zero, List.append_nil]; exact hM, hDv⟩).seq
    (h₂.post fun c ⟨⟨hR, hV, _⟩, _, _⟩ => ⟨by rw [insPre_succ]; exact hR, hV, hR.glob.n⟩))).weaken ?_
  have e1 : f1 g v 0 = W (insPre g pos v) := by simp [f1, t1Pre_zero]
  have e2 : f2 g v (out v).length = W (insPre g pos (v + 1)) + 13 * (out v).length := by
    simp only [f2, insPre_succ]
  have e3 : f2 g v 0 = W (insPre g pos v ++ t1Pre g pos v (out v).length) := by
    simp [f2, t2Pre_zero]
  have e4 : f1 g v (out v).length =
      W (insPre g pos v ++ t1Pre g pos v (out v).length) + 14 * (out v).length := rfl
  have m1 : W (insPre g pos v) ≤ W (insPre g pos v ++ t1Pre g pos v (out v).length) :=
    W_mono (List.prefix_append _ _)
  have m2 : W (insPre g pos v ++ t1Pre g pos v (out v).length) ≤ W (insPre g pos (v + 1)) :=
    W_mono (by rw [insPre_succ]; exact List.prefix_append _ _)
  simp only [fo, Finset.sum_range_succ]
  omega

/-! ### The allocation and the main triple -/

theorem genAlloc_spec (hS : SizePost g c₀) :
    HTB S genAlloc (fun c => c = c₀) (fun c => GRep g c₀ [] c ∧ c.reg gN = numV g) 10 := by
  refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hc => ?_
  subst hc
  have hB := hS.orient.peel.base
  have hZ := hB.r1.base.free
  have hn := hB.r1.base.n
  simp only [genAlloc, run_seq', run_alloc (show gP ≠ rT by decide) (show gTX ≠ gP by decide),
    run_alloc (show gP ≠ rT by decide) (show gTY ≠ gP by decide),
    run_alloc (show gP ≠ rT by decide) (show gTZ ≠ gP by decide), run_const]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, List.nil_prefix, ?_⟩, ?_⟩
  all_goals try (simp +decide [hn, hS.p, genEnd]; done)
  all_goals try (simp +decide [hS.p, genEnd]; ring)
  · simp only [setReg_mem]
    exact ⟨SameOn.refl _ _, Nat.zero_le _, arr_nil _ _, arr_nil _ _, arr_nil _ _, hZ.mono (by
      unfold genEnd; omega)⟩

theorem gen_wregs : ∀ r ∈ wregs gen, r = rT ∨ r = rFREE ∨ (36 ≤ r ∧ r < 50) ∨
    (100 ≤ r ∧ r < 150) := by decide +kernel

theorem gen_writes : writes gen = false := by decide +kernel

/-- The constant of the running time of the generation. -/
def CG : ℕ := 100

/-- **ENUM, part 1** (the generation): from a `SizePost g` configuration `c₀`, `gen` writes the
triples of all inserted 2-paths (`GRep g c₀ (ins g (peelPos g))`) within
`CG · (m + 1 + P)` steps, without output, storing only at or above `F = c₀.reg rFREE` and
accessing only the addresses below any `S ≥ genEnd g F`. -/
theorem gen_spec (g : Graph) (c₀ : Config) (hSp : genEnd g (c₀.reg rFREE) ≤ S) :
    HTB S gen (fun c => SizePost g c ∧ c = c₀)
      (fun c => GRep g c₀ (ins g (peelPos g)) c ∧ Frame gen c₀ c)
      (CG * (g.length + 1 + numPaths g (peelPos g))) := by
  intro c ⟨hS, hc⟩
  subst hc
  have hl := HTB.forUpTele (S := S) (i := xV) (n := gN) (N := numV g) (body := outerB)
    (fun v c' => GRep g c (insPre g (peelPos g) v) c')
    (fo g) (by decide) (by decide) (by decide)
    (fun v => (GRep.indep g c _).mono (by decide))
    (fun v hv => by
      have := W_mono (@insPre_prefix g (peelPos g) v (v + 1) (by omega))
      simp only [fo, Finset.sum_range_succ] at this ⊢
      omega)
    (fun v hv => outerB_spec hS hSp hv)
  have h := (genAlloc_spec hS).seq hl
  obtain ⟨c', t, he, ⟨⟨hR, _, _⟩, hfr⟩, ht⟩ := h.withFrame c c ⟨rfl, rfl⟩
  rw [insPre_numV] at hR
  refine ⟨c', t, he, ⟨hR, hfr⟩, ?_⟩
  have h1 := numV_le g
  have h2 := length_idEdges_le g
  have h3 := sum_length_outL_le g (peelPos g)
  have hs : fo g (numV g) = W (ins g (peelPos g)) + (14 * numV g +
      27 * ∑ u ∈ range (numV g), (outL g (peelPos g) u).length) := by
    rw [fo, insPre_numV, ← sum_affine]
    congr 1
    exact Finset.sum_congr rfl fun u _ => by ring
  have h0 : fo g 0 = 0 := by simp [fo, insPre_zero, W]
  rw [hs, h0] at ht
  simp only [W, KG, CG, numPaths] at ht ⊢
  omega

end

end STACS2027.Runtimes.C4
