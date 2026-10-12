module

public import Outerplanar.RAM.Poly3Prog
public import Outerplanar.RAM.Poly3Spec
import Mathlib.Tactic

/-!
# Phase P3 of the polygon solver: the selected edges and the load costs

The computation of the total of one configuration does not store: it reads the data `Rd`
(the interface arrays, the table offsets, the tables of the earlier
segments, the relevant cycles `REL` and the digits `VAL` of the current segment). Its parts
are specified with a generic frame `G` (an assertion independent of the registers they
write, from which they read their arguments):

* `inCyc_spec`: `rSEL ≠ 0` iff `(ex, ey)` is an edge of the pool cycle `i`;
* `isSel_spec`: `rSEL ≠ 0` iff `(ex, ey)` is a selected edge of the cycle `i` with omitted
  index `v`;
* `loadCost_spec`: `loadCost` adds `pairCount (loadAt s vals (ex, ey))` to `rTOT`.

The tactic `indepG hG` proves the independence of an assertion containing such a frame `G c`
(given `hG : Indep W' G`), like `indep` for the rest of the assertion. All triples are bounded
(`HTB S`): `Rd S` records that every array read lies below `S`.
-/

@[expose] public section

namespace STACS2027.RAM.P3

open STACS2027.Poly STACS2027.RAM.P1

/-- `indepG hG`: like `indep`, for an assertion containing `G c`, given `hG : Indep W' G` with
`W ⊆ W'` (checked by `decide +kernel`). -/
macro "indepG " hG:term : tactic => `(tactic|
      (intro c c' hA hP
       (try simp +zetaDelta only [] at hP ⊢)
       have hGi := ($hG).iff (hA.mono (by decide +kernel))
       (try simp only [← hGi])
       have hr := hA.reg
       have hm := hA.mem
       have ho := hA.out
       (try simp (disch := decide) only [hr, hm, ho])
       exact hP))

variable {pg : Graph} {n k : ℕ}

/-- The segment `j` of `segOrder`. -/
def sg (pg : Graph) (n j : ℕ) : ℕ × ℕ := (segOrder pg n).getD j (0, 0)

theorem sg_eq {j : ℕ} (hj : j < (segOrder pg n).length) : sg pg n j = (segOrder pg n)[j] :=
  getD_of_lt hj _

theorem sg_mem {j : ℕ} (hj : j < (segOrder pg n).length) : sg pg n j ∈ IsPolygon.segs pg n := by
  rw [sg_eq hj]; exact mem_segOrder.mp (List.getElem_mem hj)

/-- **The data read by the computation of a configuration** of the segment `j` with the
values `vals` of its relevant cycles, below the bound `S`. -/
@[mk_iff] structure Rd (S : ℕ) (pg : Graph) (n k j : ℕ) (vals : List ℕ) (c : Config) : Prop where
  kk : c.reg rK = k
  pn : c.reg gPN = n
  pl : Arr c.mem (c.reg gPOOL) (pool pg n k).flatten
  fsid : Arr c.mem (c.reg gFSID) (fsidCat pg n)
  fv : Arr c.mem (c.reg gFV) (faceCat pg n)
  boff : Arr c.mem (c.reg gBOFF) (bndOffs pg n k)
  bidx : Arr c.mem (c.reg gBIDX) (bndCat pg n k)
  toff : Arr c.mem (c.reg gTOFF) (tabOffs pg n k)
  tb : Arr c.mem (c.reg gTAB) (tabDone pg n k j)
  rl : Arr c.mem (c.reg rREL) (rel pg n k (sg pg n j))
  vl : Arr c.mem (c.reg rVAL) vals
  nr : c.reg rNR = (rel pg n k (sg pg n j)).length
  fo : c.reg rFO = fOff pg n j
  fl : c.reg rFL = (faceVerts pg n (sg pg n j)).length - 1
  sa : c.reg rSA = (sg pg n j).1
  sb : c.reg rSB = (sg pg n j).2
  bpl : c.reg gPOOL + (pool pg n k).flatten.length ≤ S
  bfsid : c.reg gFSID + (fsidCat pg n).length ≤ S
  bfv : c.reg gFV + (faceCat pg n).length ≤ S
  bboff : c.reg gBOFF + (bndOffs pg n k).length ≤ S
  bbidx : c.reg gBIDX + (bndCat pg n k).length ≤ S
  btoff : c.reg gTOFF + (tabOffs pg n k).length ≤ S
  btb : c.reg gTAB + (tabDone pg n k j).length ≤ S
  brl : c.reg rREL + (rel pg n k (sg pg n j)).length ≤ S
  bvl : c.reg rVAL + vals.length ≤ S

/-- Reading the pool: the entry `v` of the cycle `i`. -/
theorem pool_read {m : ℕ → ℕ} {b i v : ℕ} (h : Arr m b (pool pg n k).flatten)
    (hi : i < (pool pg n k).length) (hv : v < k) :
    m (b + i * k + v) = (cyc pg n k i).getD v 0 := by
  have hlt : i * k + v < (pool pg n k).flatten.length := by
    rw [length_flatten_pool]
    have : (i + 1) * k ≤ (pool pg n k).length * k := Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at this; omega
  rw [Nat.add_assoc, h.getD hlt, getD_pool hi hv]

/-- The pool cycle `i` lies in the flattened pool. -/
theorem pool_bound {i : ℕ} (hi : i < (pool pg n k).length) :
    i * k + k ≤ (pool pg n k).flatten.length := by
  rw [length_flatten_pool]
  have : (i + 1) * k ≤ (pool pg n k).length * k := Nat.mul_le_mul_right _ hi
  rw [Nat.succ_mul] at this; omega

/-! ### The edge test -/

theorem run_chk (c : Config) : (RAM.run chk c).reg rSEL =
    if (c.reg rPA = c.reg rEX ∧ c.reg rPN = c.reg rEY) ∨ (c.reg rPA = c.reg rEY ∧ c.reg rPN = c.reg rEX)
    then 1 else c.reg rSEL := by
  simp only [chk]
  rw [run_ifEq (by decide) (by decide), run_ifEq (by decide) (by decide),
    run_ifEq (by decide) (by decide), run_ifEq (by decide) (by decide)]
  simp +decide only [run_const, run_skip, setReg_reg, ↓reduceIte]
  by_cases h1 : c.reg rPA = c.reg rEX <;> by_cases h2 : c.reg rPN = c.reg rEY <;>
    by_cases h3 : c.reg rPA = c.reg rEY <;> by_cases h4 : c.reg rPN = c.reg rEX <;>
    simp +decide [h1, h2, h3, h4] <;> intros <;> omega

/-- The proposition tested by `inCyc` after `jj` edges. -/
def EdgeIn (pg : Graph) (n k i ex ey jj : ℕ) : Prop :=
  ∃ j < jj, (ex, ey) = edge ((cyc pg n k i).getD j 0) ((cyc pg n k i).getD (nxt k j) 0)

theorem icBody_spec {S i ex ey : ℕ} (G : Config → Prop) (hG : Indep (wregs inCyc) G)
    (hGr : ∀ c, G c → Arr c.mem (c.reg gPOOL) (pool pg n k).flatten ∧
      c.reg rCB = c.reg gPOOL + i * k ∧ c.reg rEX = ex ∧ c.reg rEY = ey ∧
      c.reg gPOOL + (pool pg n k).flatten.length ≤ S)
    (hi : i < (pool pg n k).length) (hex : ex < ey) (jj : ℕ) (hjj : jj < k) :
    HTB S icBody (fun c => (G c ∧ (c.reg rSEL = 0 ↔ ¬ EdgeIn pg n k i ex ey jj)) ∧ c.reg rJJ = jj ∧
        c.reg rK = k)
      (fun c => (G c ∧ (c.reg rSEL = 0 ↔ ¬ EdgeIn pg n k i ex ey (jj + 1))) ∧ c.reg rJJ = jj ∧
        c.reg rK = k) 50 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hGc, hsel⟩, hj, hkk⟩ => ?_
  obtain ⟨hpool, hcb, hx, hy, hbp⟩ := hGr c hGc
  have hpb := pool_bound (pg := pg) (n := n) hi
  refine ⟨by addr_ok [icBody, chk, hcb, hj, hkk], ?_⟩
  have hag : Agree (wregs inCyc) c (RAM.run icBody c) := agree_run (by decide) rfl rfl (by decide) c
  have hnx : nxt k jj < k := by unfold nxt; split <;> omega
  have ha : c.mem (c.reg rCB + jj) = (cyc pg n k i).getD jj 0 := by
    rw [hcb]; exact pool_read hpool hi hjj
  have hb : c.mem (c.reg rCB + nxt k jj) = (cyc pg n k i).getD (nxt k jj) 0 := by
    rw [hcb]; exact pool_read hpool hi hnx
  refine ⟨⟨hG c _ hag hGc, ?_⟩, ?_, ?_⟩
  · simp only [icBody, run_seq']
    rw [run_chk]
    set c2 := RAM.run (ld rPN rCB rU) (RAM.run (ifEq rU rK (.const rU 0) .skip)
      (RAM.run (addc rU rJJ 1) (RAM.run (ld rPA rCB rJJ) c))) with hc2
    have hc2r : c2.reg rPA = (cyc pg n k i).getD jj 0 ∧
        c2.reg rPN = (cyc pg n k i).getD (nxt k jj) 0 ∧ c2.reg rEX = ex ∧ c2.reg rEY = ey ∧
        c2.reg rSEL = c.reg rSEL := by
      rw [hc2, run_ifEq (by decide) (by decide)]
      by_cases hjk : jj + 1 = k
      · have hn : nxt k jj = 0 := by simp [nxt, hjk]
        rw [hn, Nat.add_zero] at hb
        simp +decide only [run_ld, run_addc, run_const, setReg_reg, setReg_mem, ↓reduceIte, hj,
          hkk, hjk, Nat.add_zero, ha, hb, hx, hy, and_self, hn]
      · have hn : nxt k jj = jj + 1 := by simp [nxt, hjk]
        rw [hn] at hb
        simp +decide only [run_ld, run_addc, run_skip, setReg_reg, setReg_mem, ↓reduceIte, hj,
          hkk, hjk, ha, hb, hx, hy, and_self, hn]
    obtain ⟨h1, h2, h3, h4, h5⟩ := hc2r
    rw [h1, h2, h3, h4, h5]
    unfold EdgeIn
    split_ifs with he <;> rw [← eq_edge_iff hex] at he
    · simp only [false_iff, not_not]; exact ⟨jj, by omega, he⟩
    · rw [hsel]
      constructor
      · rintro h ⟨j', hj', he'⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h' | rfl
        · exact h ⟨j', h', he'⟩
        · exact he he'
      · rintro h ⟨j', hj', he'⟩; exact h ⟨j', by omega, he'⟩
  · rw [run_reg_of_not_mem (by decide) (by decide) c]; exact hj
  · rw [run_reg_of_not_mem (by decide) (by decide) c]; exact hkk

/-- **Edges of a cycle**: `rSEL ≠ 0` iff `(ex, ey)` is an edge of the pool cycle `i` (whose
base `POOL + i * k` is in `rCB`). -/
theorem inCyc_spec {S i ex ey : ℕ} (G : Config → Prop) (hG : Indep (wregs inCyc) G)
    (hGr : ∀ c, G c → Arr c.mem (c.reg gPOOL) (pool pg n k).flatten ∧
      c.reg rCB = c.reg gPOOL + i * k ∧ c.reg rEX = ex ∧ c.reg rEY = ey ∧ c.reg rK = k ∧
      c.reg gPOOL + (pool pg n k).flatten.length ≤ S)
    (hi : i < (pool pg n k).length) (hex : ex < ey) (hk : 0 < k) :
    HTB S inCyc (fun c => G c ∧ c.reg rSEL = 0)
      (fun c => G c ∧ (c.reg rSEL = 0 ↔ (ex, ey) ∉ cycleEdges (cyc pg n k i))) (k * 54 + 3) := by
  have hl := HTB.forUpC (S := S) (i := rJJ) (n := rK) (N := k) (body := icBody)
    (fun jj c => G c ∧ (c.reg rSEL = 0 ↔ ¬ EdgeIn pg n k i ex ey jj)) 50 (by decide) (by decide)
    (by decide) (fun jj => (hG.mono (by decide)).and (Indep.reg (by decide) (fun v => v = 0 ↔ _)))
    (fun jj hjj => icBody_spec G hG (fun c hc => let h := hGr c hc;
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩) hi hex jj hjj)
  refine hl.mono (fun c ⟨hc, h0⟩ => ⟨⟨hc, ?_⟩, (hGr c hc).2.2.2.2.1⟩) ?_ le_rfl
  · simp only [h0, true_iff]; rintro ⟨j, hj, -⟩; omega
  · rintro c ⟨⟨hc, hs⟩, -, -⟩
    refine ⟨hc, ?_⟩
    rw [hs, mem_cycleEdges_iff (length_cyc hi) hk]
    rfl

/-! ### Selected edges -/

theorem run_selPost (c : Config) : (RAM.run selPost c).reg rSEL =
    if c.reg rW = c.reg rEX ∨ c.reg rW = c.reg rEY then 0 else c.reg rSEL := by
  simp only [selPost, run_seq']
  rw [run_ifEq (by decide) (by decide), run_ifEq (by decide) (by decide)]
  by_cases h1 : c.reg rW = c.reg rEX <;> by_cases h2 : c.reg rW = c.reg rEY <;>
    simp +decide [h1, h2]

/-- **Selected edges**: `rSEL ≠ 0` iff `(ex, ey)` is a selected edge of the pool cycle `i`
with omitted index `v`. -/
theorem isSel_spec {S i v ex ey : ℕ} (G : Config → Prop) (hG : Indep (wregs isSel) G)
    (hGr : ∀ c, G c → Arr c.mem (c.reg gPOOL) (pool pg n k).flatten ∧ c.reg rK = k ∧
      c.reg rI = i ∧ c.reg rV = v ∧ c.reg rEX = ex ∧ c.reg rEY = ey ∧
      c.reg gPOOL + (pool pg n k).flatten.length ≤ S)
    (hi : i < (pool pg n k).length) (hv : v < k) (hex : ex < ey) (hk : 0 < k) :
    HTB S isSel G (fun c => G c ∧ (c.reg rSEL = 0 ↔
      (ex, ey) ∉ selectedAt (cyc pg n k i) ((cyc pg n k i).getD v 0))) (k * 59 + 27) := by
  have h₁ := HTB.mul (S := S) (P := G) (d := rM) (a := rI) (b := rK) (k := rMK) (x := i) (y := k)
    (by decide) (hG.mono (by decide)) (fun c hc => (hGr c hc).2.2.1) (fun c hc => (hGr c hc).2.1)
  let w := (cyc pg n k i).getD v 0
  have h₂ : HTB S (.seq (.add rCB gPOOL rM) (.seq (ld rW rCB rV) (.const rSEL 0)))
      (fun c => G c ∧ c.reg rM = i * k)
      (fun c => (G c ∧ c.reg rCB = c.reg gPOOL + i * k ∧ c.reg rW = w) ∧ c.reg rSEL = 0) 4 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨hc, hm⟩ => ?_
    obtain ⟨hpool, -, -, hvv, -, -, hbp⟩ := hGr c hc
    have hpb := pool_bound (pg := pg) (n := n) hi
    refine ⟨by addr_ok [hm, hvv], ?_⟩
    have hag : Agree (wregs isSel) c
        (RAM.run (.seq (.add rCB gPOOL rM) (.seq (ld rW rCB rV) (.const rSEL 0))) c) :=
      agree_run (by decide) rfl rfl (by decide) c
    refine ⟨⟨hG c _ hag hc, ?_, ?_⟩, ?_⟩
    all_goals simp +decide only [run_seq', run_add, run_ld, run_const, setReg_reg, ↓reduceIte,
      setReg_mem, hm, hvv]
    exact pool_read hpool hi hv
  have h₃ := inCyc_spec (pg := pg) (i := i) (ex := ex) (ey := ey)
    (fun c => G c ∧ c.reg rCB = c.reg gPOOL + i * k ∧ c.reg rW = w)
    (fun c c' hA ⟨hc, h1, h2⟩ => ⟨hG c c' (hA.mono (by decide)) hc,
      by rw [hA.reg _ (by decide), hA.reg _ (by decide)]; exact h1,
      by rw [hA.reg _ (by decide)]; exact h2⟩)
    (fun c ⟨hc, h1, _⟩ => let h := hGr c hc;
      ⟨h.1, h1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.1, h.2.2.2.2.2.2⟩) hi hex hk
  have h₄ : HTB S selPost
      (fun c => (G c ∧ c.reg rCB = c.reg gPOOL + i * k ∧ c.reg rW = w) ∧
        (c.reg rSEL = 0 ↔ (ex, ey) ∉ cycleEdges (cyc pg n k i)))
      (fun c => G c ∧ (c.reg rSEL = 0 ↔ (ex, ey) ∉ selectedAt (cyc pg n k i) w)) 14 := by
    refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨hc, _, hw⟩, hs⟩ => ?_
    obtain ⟨-, -, -, -, hx, hy, -⟩ := hGr c hc
    have hag : Agree (wregs isSel) c (RAM.run selPost c) :=
      agree_run (by decide) rfl rfl (by decide) c
    refine ⟨hG c _ hag hc, ?_⟩
    rw [selectedAt_mem, run_selPost, hw, hx, hy]
    by_cases h1 : w = ex
    · simp only [h1, true_or, ↓reduceIte, true_iff]; omega
    · by_cases h2 : w = ey
      · simp only [h2, or_true, ↓reduceIte, true_iff]; omega
      · simp only [h1, h2, or_self, ↓reduceIte, hs]
        constructor
        · intro h h'; exact h h'.1
        · intro h h'; exact h ⟨h', fun e => h1 e.symm, fun e => h2 e.symm⟩
  have := (h₁.seq h₂).seq (h₃.seq h₄)
  exact this.weaken (by omega)

/-! ### Load costs -/

/-- The load of `e` counted over the first `r` relevant cycles of the segment `j`. -/
def cntR (pg : Graph) (n k j : ℕ) (vals : List ℕ) (e : Edge) (r : ℕ) : ℕ :=
  (List.range r).countP (selQ pg n k (sg pg n j) vals e)

theorem countP_range_succ (p : ℕ → Bool) (r : ℕ) :
    (List.range (r + 1)).countP p = (List.range r).countP p + if p r then 1 else 0 := by
  rw [List.range_succ, List.countP_append]
  cases h : p r <;> simp [h]

/-- The bound of `isSel`. -/
def tSel (k : ℕ) : ℕ := k * 59 + 27

theorem lcBody_spec {S j : ℕ} {vals : List ℕ} {ex ey t0 : ℕ} (G : Config → Prop)
    (hG : Indep (wregs loadCost) G)
    (hGr : ∀ c, G c → Rd S pg n k j vals c ∧ c.reg rEX = ex ∧ c.reg rEY = ey)
    (hvk : ∀ x ∈ vals, x < k) (hvl : vals.length = (rel pg n k (sg pg n j)).length)
    (hex : ex < ey) (hk : 0 < k) (r : ℕ) (hr : r < (rel pg n k (sg pg n j)).length) :
    HTB S lcBody
      (fun c => (G c ∧ c.reg rCNT = cntR pg n k j vals (ex, ey) r ∧
        c.reg rTOT = t0 + pairCount (cntR pg n k j vals (ex, ey) r)) ∧ c.reg rR = r ∧
        c.reg rNR = (rel pg n k (sg pg n j)).length)
      (fun c => (G c ∧ c.reg rCNT = cntR pg n k j vals (ex, ey) (r + 1) ∧
        c.reg rTOT = t0 + pairCount (cntR pg n k j vals (ex, ey) (r + 1))) ∧ c.reg rR = r ∧
        c.reg rNR = (rel pg n k (sg pg n j)).length) (tSel k + 9) := by
  set s := sg pg n j
  set iv := (rel pg n k s).getD r 0
  set vv := vals.getD r 0
  let P : Config → Prop := fun c => (G c ∧ c.reg rCNT = cntR pg n k j vals (ex, ey) r ∧
    c.reg rTOT = t0 + pairCount (cntR pg n k j vals (ex, ey) r)) ∧ c.reg rR = r ∧
    c.reg rNR = (rel pg n k s).length
  have hA := HTB.ld (S := S) (P := P) (d := rI) (b := rREL) (i := rR) (v := iv) (by indepG hG)
    (fun c hc => by rw [hc.2.1]; exact ((hGr c hc.1.1).1.rl.getD hr))
    (fun c hc => by
      have h' : c.reg rREL + (rel pg n k s).length ≤ S := (hGr c hc.1.1).1.brl
      rw [hc.2.1]; omega)
  have hB := HTB.ld (S := S) (P := fun c => P c ∧ c.reg rI = iv) (d := rV) (b := rVAL) (i := rR)
    (v := vv) (by indepG hG)
    (fun c hc => by rw [hc.1.2.1]; exact ((hGr c hc.1.1.1).1.vl.getD (by omega)))
    (fun c hc => by
      have h' : c.reg rVAL + vals.length ≤ S := (hGr c hc.1.1.1).1.bvl
      rw [hc.1.2.1]; omega)
  have hiv : iv < (pool pg n k).length := lt_of_mem_rel (getD_mem 0 hr)
  have hvv : vv < k := hvk _ (getD_mem 0 (by omega))
  have hC := isSel_spec (pg := pg) (i := iv) (v := vv) (ex := ex) (ey := ey)
    (fun c => (P c ∧ c.reg rI = iv) ∧ c.reg rV = vv) (by indepG hG)
    (fun c hc => let h := hGr c hc.1.1.1.1
      ⟨h.1.pl, h.1.kk, hc.1.2, hc.2, h.2.1, h.2.2, h.1.bpl⟩) hiv hvv hex hk
  have hD : HTB S (.ifz rSEL .skip (.seq (.add rTOT rTOT rCNT) (inc rCNT)))
      (fun c => ((P c ∧ c.reg rI = iv) ∧ c.reg rV = vv) ∧ (c.reg rSEL = 0 ↔
        (ex, ey) ∉ selectedAt (cyc pg n k iv) ((cyc pg n k iv).getD vv 0)))
      (fun c => (G c ∧ c.reg rCNT = cntR pg n k j vals (ex, ey) (r + 1) ∧
        c.reg rTOT = t0 + pairCount (cntR pg n k j vals (ex, ey) (r + 1))) ∧ c.reg rR = r ∧
        c.reg rNR = (rel pg n k s).length) 5 := by
    refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
      fun c ⟨⟨⟨⟨⟨hg, hcnt, htot⟩, hrr, hnr⟩, _⟩, _⟩, hs⟩ => ?_
    have hag : Agree (wregs loadCost) c
        (RAM.run (.ifz rSEL .skip (.seq (.add rTOT rTOT rCNT) (inc rCNT))) c) :=
      agree_run (by decide) rfl rfl (by decide) c
    have hsucc : cntR pg n k j vals (ex, ey) (r + 1) = cntR pg n k j vals (ex, ey) r +
        if selQ pg n k s vals (ex, ey) r then 1 else 0 := countP_range_succ _ r
    have hq : selQ pg n k s vals (ex, ey) r =
        decide ((ex, ey) ∈ selectedAt (cyc pg n k iv) ((cyc pg n k iv).getD vv 0)) := rfl
    refine ⟨⟨hG c _ hag hg, ?_, ?_⟩, ?_, ?_⟩
    all_goals simp +decide only [run_ifz', run_skip, run_seq', run_add, run_inc, setReg_reg,
      ↓reduceIte, config_ite_reg]
    · by_cases h0 : c.reg rSEL = 0
      · have hn := hs.mp h0
        simp only [h0, ↓reduceIte, hcnt, hsucc, hq, hn, decide_false, Bool.false_eq_true,
          Nat.add_zero]
      · have hn : (ex, ey) ∈ selectedAt (cyc pg n k iv) ((cyc pg n k iv).getD vv 0) := by
          by_contra h; exact h0 (hs.mpr h)
        simp only [h0, ↓reduceIte, hcnt, hsucc, hq, hn, decide_true]
    · by_cases h0 : c.reg rSEL = 0
      · have hn := hs.mp h0
        simp only [h0, ↓reduceIte, htot, hsucc, hq, hn, decide_false, Bool.false_eq_true,
          Nat.add_zero]
      · have hn : (ex, ey) ∈ selectedAt (cyc pg n k iv) ((cyc pg n k iv).getD vv 0) := by
          by_contra h; exact h0 (hs.mpr h)
        simp only [h0, ↓reduceIte, htot, hcnt, hsucc, hq, hn, decide_true, pairCount]
        omega
    · split_ifs <;> exact hrr
    · split_ifs <;> exact hnr
  exact (hA.seq (hB.seq (hC.seq hD))).weaken (by unfold tSel; omega)

/-- The bound of `loadCost`. -/
def tLC (k : ℕ) : ℕ := 2 * Rb k * (tSel k + 13) + 4

/-- **Load costs**: `loadCost` adds `pairCount (loadAt s vals (ex, ey))` to `rTOT`. -/
theorem loadCost_spec {S j : ℕ} {vals : List ℕ} {ex ey t0 : ℕ} (G : Config → Prop)
    (hG : Indep (wregs loadCost) G)
    (hGr : ∀ c, G c → Rd S pg n k j vals c ∧ c.reg rEX = ex ∧ c.reg rEY = ey)
    (hP : IsPolygon pg n) (hj : j < (segOrder pg n).length)
    (hvk : ∀ x ∈ vals, x < k) (hvl : vals.length = (rel pg n k (sg pg n j)).length)
    (hex : ex < ey) (hk : 0 < k) :
    HTB S loadCost (fun c => G c ∧ c.reg rTOT = t0)
      (fun c => G c ∧ c.reg rTOT = t0 + pairCount (loadAt pg n k (sg pg n j) vals (ex, ey)))
      (tLC k) := by
  have h₀ : HTB S (.const rCNT 0) (fun c => G c ∧ c.reg rTOT = t0)
      (fun c => (G c ∧ c.reg rCNT = cntR pg n k j vals (ex, ey) 0 ∧
        c.reg rTOT = t0 + pairCount (cntR pg n k j vals (ex, ey) 0)) ∧
        c.reg rNR = (rel pg n k (sg pg n j)).length) 1 := by
    refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hc, ht⟩ => ?_
    have hag : Agree (wregs loadCost) c (RAM.run (.const rCNT 0) c) :=
      agree_run (by decide) rfl rfl (by decide) c
    refine ⟨⟨hG c _ hag hc, ?_, ?_⟩, ?_⟩
    all_goals simp +decide only [run_const, setReg_reg, ↓reduceIte, ht]
    · rfl
    · rfl
    · exact (hGr c hc).1.nr
  have hl := HTB.forUpC (S := S) (i := rR) (n := rNR) (N := (rel pg n k (sg pg n j)).length)
    (body := lcBody)
    (fun r c => G c ∧ c.reg rCNT = cntR pg n k j vals (ex, ey) r ∧
      c.reg rTOT = t0 + pairCount (cntR pg n k j vals (ex, ey) r)) (tSel k + 9)
    (by decide) (by decide) (by decide) (fun r => by indepG hG)
    (fun r hr => lcBody_spec G hG hGr hvk hvl hex hk r hr)
  have hrel := length_rel_le (k := k) hP (sg_mem hj)
  refine (h₀.seq hl).mono (fun _ h => h) ?_ ?_
  · rintro c ⟨⟨hc, -, ht⟩, -, -⟩
    refine ⟨hc, ?_⟩
    rw [ht, cntR, ← loadAt_eq _ _ _ hvl]
  · have : (rel pg n k (sg pg n j)).length * (tSel k + 9 + 4) ≤ 2 * Rb k * (tSel k + 13) :=
      Nat.mul_le_mul hrel le_rfl
    unfold tLC; omega

end STACS2027.RAM.P3
