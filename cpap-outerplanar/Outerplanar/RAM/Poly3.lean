module

public import Outerplanar.RAM.Poly3Pre
import Mathlib.Tactic

/-!
# Phase P3 of the polygon solver (the tables): the main triple

`poly3 k` (`Poly3Prog.lean`) runs

* `prep k`: loads `k`, writes the table offsets `tabOffs` (`toffInit_spec`) and allocates the
  tables `TAB`, `ARG`;
* `segLoop`: for every segment `s` of `segOrder` (children first), for every configuration `α`
  of its boundary cycles, the minimization over the configurations `β` of its top cycles of the
  local cost plus the children's table entries (`segLoop_spec`), storing `table s α` and
  `argTab s α` (`table_eq`, `argTab_eq`: the tables of `Poly.lean` are this minimization, by the
  fuel independence `tabArg_fuel`).

`poly3_specB`: from `Poly2Post`, `poly3 k` reaches `Poly3Post` within `CP3 k * (n + |pg| + 1)`
steps, allocating at most `M3 pg n k` fresh cells (`M3_le`), without output, every load and
store below any bound `S` leaving room for these cells (`PolyPhaseB`). Per segment, the
`k ^ (|bnd s| +
|topIdx s|)` configurations (at most `k ^ Rb k` each way) cost `O(|face s|)` each; the faces
sum to at most `2 |pg|` (`length_faceCat_le`). `poly3_wregs`, `poly3_writes`: the registers
written and no output.
-/

@[expose] public section

namespace STACS2027.RAM.P3

open STACS2027.Poly STACS2027.RAM.P1

variable {pg : Graph} {n k : ℕ}

/-! ### Footprint -/

theorem wregs_poly3 (k : ℕ) : wregs (poly3 k) = wregs (poly3 0) := rfl

theorem wregs_prep (k : ℕ) : wregs (prep k) = wregs (prep 0) := rfl

/-- **P3 writes only `rT`, `rFREE`, its interface registers `gTOFF … gARG` and registers at or
above `gPx`.** -/
theorem poly3_wregs (k : ℕ) :
    ∀ r ∈ wregs (poly3 k), r = rT ∨ r = rFREE ∨ (gTOFF ≤ r ∧ r ≤ gARG) ∨ gPx ≤ r := by
  rw [wregs_poly3]; decide +kernel

/-- **P3 does not write output.** -/
theorem poly3_writes (k : ℕ) : writes (poly3 k) = false := by
  show writes (poly3 0) = false; decide

/-- The registers of `Poly2Post` are not written by a program satisfying the footprint of P3. -/
theorem not_mem_of_footprint {W : List ℕ}
    (hW : ∀ r ∈ W, r = rT ∨ r = rFREE ∨ (gTOFF ≤ r ∧ r ≤ gARG) ∨ gPx ≤ r) {r : ℕ}
    (hr : r ∈ [rZERO, rONE, gPN, gPE, gPU, gPV, gOMAP, gNS, gSA, gSB, gFSID, gFOFF, gFV, gNP, gPOOL,
      gTST, gBOFF, gBIDX]) : r ∉ W := by
  intro h
  have := hW r h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> revert this <;> decide

/-- `Poly2Post` survives a run respecting the footprint of P3 that keeps the memory below the
initial free pointer. -/
theorem poly2Post_of_frame {omap : List ℕ} {W : List ℕ} {c₀ c : Config}
    (h : Poly2Post pg n k omap c₀)
    (hW : ∀ r ∈ W, r = rT ∨ r = rFREE ∨ (gTOFF ≤ r ∧ r ≤ gARG) ∨ gPx ≤ r)
    (hreg : ∀ r, r ∉ W → c.reg r = c₀.reg r) (hs : SameOn (· < c₀.reg rFREE) c₀.mem c.mem)
    (hz : ZeroFrom c.mem (c.reg rFREE)) (hF : c₀.reg rFREE ≤ c.reg rFREE) :
    Poly2Post pg n k omap c := by
  have e : ∀ r, r ∈ [rZERO, rONE, gPN, gPE, gPU, gPV, gOMAP, gNS, gSA, gSB, gFSID, gFOFF, gFV, gNP,
      gPOOL, gTST, gBOFF, gBIDX] → c.reg r = c₀.reg r :=
    fun r hr => hreg r (not_mem_of_footprint hW hr)
  have h1 := h.p1
  have hb := h1.base
  have hb1 := hb.below
  have hb2 := h1.below
  have hb3 := h.below
  have hfo : (faceOffs pg n).length = (segOrder pg n).length + 1 := by
    rw [faceOffs, length_prefixSums, List.length_map]
  have hts : (topStarts pg n k).length = (segOrder pg n).length + 1 := by
    rw [topStarts, length_prefixSums, List.length_map]
  have hbo : (bndOffs pg n k).length = (segOrder pg n).length + 1 := by
    rw [bndOffs, length_prefixSums, List.length_map]
  have e0 := e rZERO (by simp)
  have e1 := e rONE (by simp)
  have e2 := e gPN (by simp)
  have e3 := e gPE (by simp)
  have e4 := e gPU (by simp)
  have e5 := e gPV (by simp)
  have e6 := e gOMAP (by simp)
  have e7 := e gNS (by simp)
  have e8 := e gSA (by simp)
  have e9 := e gSB (by simp)
  have e10 := e gFSID (by simp)
  have e11 := e gFOFF (by simp)
  have e12 := e gFV (by simp)
  have e13 := e gNP (by simp)
  have e14 := e gPOOL (by simp)
  have e15 := e gTST (by simp)
  have e16 := e gBOFF (by simp)
  have e17 := e gBIDX (by simp)
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hb.omap_len, hz, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15,
    e16, e17]
  · exact hb.zero
  · exact hb.one
  · exact hb.pn
  · exact hb.pe
  · exact hb.pu.of_below hs (by simpa using hb1.1)
  · exact hb.pv.of_below hs (by simpa using hb1.2.1)
  · exact hb.om.of_below hs (by rw [hb.omap_len]; exact hb1.2.2)
  · omega
  · exact h1.ns
  · exact h1.sa.of_below hs (by simpa using hb2.1)
  · exact h1.sb.of_below hs (by simpa using hb2.2.1)
  · exact h1.fsid.of_below hs hb2.2.2.1
  · exact h1.foff.of_below hs (by rw [hfo]; exact hb2.2.2.2.1)
  · exact h1.fv.of_below hs hb2.2.2.2.2
  · omega
  · exact h.np
  · exact h.pl.of_below hs hb3.1
  · exact h.tst.of_below hs (by rw [hts]; exact hb3.2.1)
  · exact h.boff.of_below hs (by rw [hbo]; exact hb3.2.2.1)
  · exact h.bidx.of_below hs hb3.2.2.2
  · omega

/-! ### The first pass -/

/-- **The first pass**: `k`, the table offsets, the tables (allocated). -/
theorem prep_spec {S : ℕ} (hP : IsPolygon pg n) (omap : List ℕ) (c₀ : Config)
    (h₀ : Poly2Post pg n k omap c₀) (hSz : c₀.reg rFREE + ((segOrder pg n).length + 1) ≤ S) :
    HTB S (prep k) (fun c => c = c₀)
      (fun c => MSt pg n k c.mem (c₀.reg rFREE + ((segOrder pg n).length + 1))
        (c₀.reg rFREE + ((segOrder pg n).length + 1) + toffAt pg n k (segOrder pg n).length) 0 c ∧
        c.reg gNS = (segOrder pg n).length ∧ SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧
        c.reg rFREE = c₀.reg rFREE + ((segOrder pg n).length + 1) +
          toffAt pg n k (segOrder pg n).length + toffAt pg n k (segOrder pg n).length)
      ((segOrder pg n).length * (tToff k + 4) + 16) := by
  have hb2 := h₀.p1.below
  have hb3 := h₀.below
  -- the stages
  have h₁ : HTB S (.const rK k) (fun c => c = c₀)
      (fun c => ((c.reg gNS = (segOrder pg n).length ∧ c.reg rK = k ∧ c.reg gBOFF = c₀.reg gBOFF) ∧
        c.reg rFREE = c₀.reg rFREE ∧ c.mem = c₀.mem ∧ ZeroFrom c₀.mem (c₀.reg rFREE)) ∧
        c.reg rK = k) 1 := by
    refine HTB.of_HT rfl <| HT.run_le trivial le_rfl fun c hc => ?_
    subst hc
    refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, rfl, h₀.p1.base.free⟩, ?_⟩
    all_goals simp only [run_const, setReg_reg]
    all_goals simp +decide only [↓reduceIte, h₀.p1.ns]
  have h₂ := (toffInit_spec (S := S) (k := k) hP (c₀.reg rFREE) (c₀.reg gBOFF) c₀.mem h₀.boff
    hb3.2.2.1 hSz).frameReg (F := fun c => c.reg rK = k) (by indep)
  refine (((h₁.seq h₂).withFrame c₀).pre (fun c h => ⟨h, h⟩)).mono (fun _ h => h) ?_ (by omega)
  rintro c ⟨⟨⟨⟨hTOFF, hTAB, hARG, hF⟩, htoff, hs, hz⟩, hK⟩, hfr⟩
  have hW : ∀ r ∈ wregs (prep k), r = rT ∨ r = rFREE ∨ (gTOFF ≤ r ∧ r ≤ gARG) ∨ gPx ≤ r := by
    rw [wregs_prep]; decide +kernel
  have hp2 := poly2Post_of_frame h₀ hW hfr.reg hs hz (by omega)
  have hfo : (faceOffs pg n).length = (segOrder pg n).length + 1 := by
    rw [faceOffs, length_prefixSums, List.length_map]
  have hts : (topStarts pg n k).length = (segOrder pg n).length + 1 := by
    rw [topStarts, length_prefixSums, List.length_map]
  have e1 := hfr.reg gSA (not_mem_of_footprint hW (by decide))
  have e2 := hfr.reg gSB (not_mem_of_footprint hW (by decide))
  have e3 := hfr.reg gFSID (not_mem_of_footprint hW (by decide))
  have e4 := hfr.reg gFOFF (not_mem_of_footprint hW (by decide))
  have e5 := hfr.reg gFV (not_mem_of_footprint hW (by decide))
  have e6 := hfr.reg gPOOL (not_mem_of_footprint hW (by decide))
  have e7 := hfr.reg gTST (not_mem_of_footprint hW (by decide))
  have e8 := hfr.reg gBOFF (not_mem_of_footprint hW (by decide))
  have e9 := hfr.reg gBIDX (not_mem_of_footprint hW (by decide))
  refine ⟨⟨⟨⟨hK, hp2.p1.base.pn, hp2.p1.ns, hp2.p1.sa, hp2.p1.sb, hp2.p1.fsid, hp2.p1.foff,
    hp2.p1.fv, hp2.pl, hp2.tst, hp2.boff, hp2.bidx,
    by rw [hTOFF]; exact htoff, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hTAB⟩, hARG, by omega⟩,
    SameOn.refl _ _, by simp [tabDone], by simp [argDone], hz⟩, hp2.p1.ns, hs, hF⟩
  all_goals simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, hTOFF]
  all_goals omega

/-! ### The running time -/

/-- The constant of one segment (per face vertex). -/
def cSeg (k : ℕ) : ℕ :=
  k ^ Rb k * (k ^ Rb k * (tTot k + (Rb k * 19 + 34)) + (Rb k * 19 + 24)) + (Rb k * (10 * k + 50) + 64)

/-- The constant of the running time of P3. -/
def CT3 (k : ℕ) : ℕ := 3 * cSeg k + tToff k + 33

/-- The constant of the fresh cells of P3. -/
def CM3 (k : ℕ) : ℕ := 2 * k ^ Rb k + 4 * Rb k + 2

/-- **The constant of P3** (steps and fresh cells). -/
def CP3 (k : ℕ) : ℕ := CT3 k + CM3 k

/-- The fresh cells of P3: the table offsets, the tables `TAB`, `ARG`, and the relevant cycles
and digits of every segment. -/
def M3 (pg : Graph) (n k : ℕ) : ℕ :=
  ((segOrder pg n).length + 1) + 2 * toffAt pg n k (segOrder pg n).length +
    4 * Rb k * (segOrder pg n).length

theorem toffAt_le (hP : IsPolygon pg n) (hk : 1 ≤ k) :
    toffAt pg n k (segOrder pg n).length ≤ (segOrder pg n).length * k ^ Rb k := by
  unfold toffAt
  rw [List.take_length]
  exact sum_map_le_mul _ _ _ fun s hs =>
    Nat.pow_le_pow_right hk (length_bnd_le' hP (mem_segOrder.mp hs))

theorem M3_le (hP : IsPolygon pg n) (hk : 1 ≤ k) : M3 pg n k ≤ CP3 k * (n + pg.length + 1) := by
  have h1 := toffAt_le (k := k) hP hk
  have h3 : (segOrder pg n).length ≤ pg.length := by
    rw [length_segOrder]; exact length_segEnum_le
  have e1 : (segOrder pg n).length * k ^ Rb k ≤ pg.length * k ^ Rb k := Nat.mul_le_mul_right _ h3
  have e2 : 4 * Rb k * (segOrder pg n).length ≤ 4 * Rb k * pg.length := Nat.mul_le_mul_left _ h3
  have hCP : CM3 k * (n + pg.length + 1) ≤ CP3 k * (n + pg.length + 1) :=
    Nat.mul_le_mul_right _ (by unfold CP3; omega)
  refine le_trans ?_ hCP
  have e3 : CM3 k * (n + pg.length + 1) = CM3 k * n + 2 * (pg.length * k ^ Rb k) +
      4 * Rb k * pg.length + 2 * pg.length + CM3 k := by unfold CM3; ring
  have hC : 2 ≤ CM3 k := by unfold CM3; omega
  unfold M3
  rw [e3]
  have := Nat.zero_le (CM3 k * n)
  omega

theorem tSeg_le (k fl : ℕ) : tSeg k fl + 4 ≤ cSeg k * (fl + 1) := by
  have key : ∀ a b c X : ℕ, 1 ≤ X → a ≤ b * X → a + c ≤ (b + c) * X := fun a b c X hX h => by
    have : c ≤ c * X := Nat.le_mul_of_pos_right c hX
    rw [Nat.add_mul]; omega
  have key2 : ∀ q a b X : ℕ, a ≤ b * X → q * a ≤ (q * b) * X := fun q a b X h => by
    calc q * a ≤ q * (b * X) := Nat.mul_le_mul_left q h
      _ = q * b * X := by ring
  have hX : 1 ≤ fl + 1 := by omega
  have h1 := key (tTot k * (fl + 1)) (tTot k) (Rb k * 19 + 34) (fl + 1) hX le_rfl
  have h2 := key _ _ (Rb k * 19 + 24) _ hX (key2 (k ^ Rb k) _ _ _ h1)
  have h3 := key _ _ (Rb k * (10 * k + 50) + 64) _ hX (key2 (k ^ Rb k) _ _ _ h2)
  have e : tSeg k fl + 4 = k ^ Rb k * (k ^ Rb k * (tTot k * (fl + 1) + (Rb k * 19 + 34)) +
      (Rb k * 19 + 24)) + (Rb k * (10 * k + 50) + 64) := by
    unfold tSeg tAlpha tBeta; ring
  rw [e]; exact h3

/-- The faces sum to the concatenated faces. -/
theorem sum_faceVerts : ∑ j ∈ Finset.range (segOrder pg n).length, (faceVerts pg n (sg pg n j)).length =
    (faceCat pg n).length := by
  rw [sum_range_eq, faceCat, List.length_flatMap]
  exact congrArg List.sum (map_range_getD (fun s => (faceVerts pg n s).length) (0, 0) _)

theorem segLoop_bound (hP : IsPolygon pg n) (k : ℕ) :
    ∑ j ∈ Finset.range (segOrder pg n).length, (tSeg k (faceVerts pg n (sg pg n j)).length + 4) + 3 ≤
      cSeg k * (3 * pg.length) + 3 := by
  have h1 : ∑ j ∈ Finset.range (segOrder pg n).length, (tSeg k (faceVerts pg n (sg pg n j)).length + 4) ≤
      ∑ j ∈ Finset.range (segOrder pg n).length, cSeg k * ((faceVerts pg n (sg pg n j)).length + 1) :=
    Finset.sum_le_sum fun j _ => tSeg_le k _
  have h1' : ∑ j ∈ Finset.range (segOrder pg n).length,
      cSeg k * ((faceVerts pg n (sg pg n j)).length + 1) =
      cSeg k * ((faceCat pg n).length + (segOrder pg n).length) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_faceVerts]
    simp
  have h2 := length_faceCat_le (pg := pg) (n := n) hP
  have h3 : (segOrder pg n).length ≤ pg.length := by
    rw [length_segOrder]; exact length_segEnum_le
  have h4 : cSeg k * ((faceCat pg n).length + (segOrder pg n).length) ≤ cSeg k * (3 * pg.length) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-! ### Phase P3 -/

/-- **Phase P3** (the tables), bounded space: from `Poly2Post`, `poly3 k` reaches `Poly3Post`
(the tables `table s α`, the minimizing `argTab s α`, their offsets) within
`CP3 k * (n + |pg| + 1)` steps, allocating at most `M3 pg n k ≤ CP3 k * (n + |pg| + 1)` fresh
cells, without output, every load and store below `S`. -/
theorem poly3_specB {k : ℕ} (hk : 3 ≤ k) (pg : Graph) (n : ℕ) (omap : List ℕ)
    (hP : IsPolygon pg n) (hlt : ∀ e ∈ pg, e.1 < e.2) (hnd : pg.Nodup) :
    PolyPhaseB (poly3 k) pg n (Poly2Post pg n k omap) (Poly3Post pg n k omap) (CP3 k) := by
  -- (the edges' orientation and distinctness are not needed by this phase)
  have _ := hlt
  have _ := hnd
  intro S c₀ hSz
  refine HTB.of_forall fun c₁ ⟨h₀, hc⟩ => ?_
  subst hc
  have hM3 := M3_le (k := k) hP (by omega)
  unfold M3 at hM3
  have hpre := prep_spec (S := S) (k := k) hP omap c₁ h₀ (by omega)
  have hloop : HTB S segLoop
      (fun c => MSt pg n k c.mem (c₁.reg rFREE + ((segOrder pg n).length + 1))
        (c₁.reg rFREE + ((segOrder pg n).length + 1) + toffAt pg n k (segOrder pg n).length) 0 c ∧
        c.reg gNS = (segOrder pg n).length ∧ SameOn (· < c₁.reg rFREE) c₁.mem c.mem ∧
        c.reg rFREE = c₁.reg rFREE + ((segOrder pg n).length + 1) +
          toffAt pg n k (segOrder pg n).length + toffAt pg n k (segOrder pg n).length)
      (fun c => ∃ mR, (MSt pg n k mR (c₁.reg rFREE + ((segOrder pg n).length + 1))
        (c₁.reg rFREE + ((segOrder pg n).length + 1) + toffAt pg n k (segOrder pg n).length)
        (segOrder pg n).length c ∧ FrP pg n k
          (c₁.reg rFREE + ((segOrder pg n).length + 1) + toffAt pg n k (segOrder pg n).length)
          (segOrder pg n).length c) ∧ SameOn (· < c₁.reg rFREE) c₁.mem mR)
      (∑ j ∈ Finset.range (segOrder pg n).length, (tSeg k (faceVerts pg n (sg pg n j)).length + 4) + 3) :=
    HTB.of_forall fun c₂ ⟨hM, hns, hs, hfr⟩ =>
      (segLoop_spec (mR := c₂.mem) hP hk rfl (by omega)).mono
        (fun c hc => by subst hc; exact ⟨⟨hM, by unfold FrP; omega⟩, hns⟩)
        (fun _ h => ⟨c₂.mem, h, hs⟩) le_rfl
  refine (((hpre.seq hloop).withFrame c₁).pre (fun c h => ⟨h, h⟩)).mono (fun _ h => h) ?_ ?_
  · rintro c ⟨⟨mR, ⟨⟨⟨hg, harg, hAF⟩, hsame, htb, hag, hz⟩, hFP⟩, hs⟩, hfr⟩
    have hT : c₁.reg rFREE ≤ c₁.reg rFREE + ((segOrder pg n).length + 1) := by omega
    have hsF : SameOn (· < c₁.reg rFREE) c₁.mem c.mem :=
      hs.trans (hsame.mono fun a (ha : a < _) => show a < _ by omega)
    have hF : c₁.reg rFREE ≤ c.reg rFREE := by omega
    have hlen : (tabCat pg n k).length = toffAt pg n k (segOrder pg n).length := by
      rw [← tabDone_full, length_tabDone]
    have hlen' : (argCat pg n k).length = toffAt pg n k (segOrder pg n).length := by
      rw [← argDone_full, length_argDone]
    have hbt := hg.btoff
    refine ⟨⟨poly2Post_of_frame h₀ (poly3_wregs k) hfr.reg hsF hz hF, (hg.rd hsame).2.2.2.2.2.2.2.2.2,
      by rw [hg.tab, ← tabDone_full]; exact htb, by rw [harg, ← argDone_full]; exact hag, ?_, ?_, ?_⟩,
      hfr.out (poly3_writes k), hsF, hF, ?_⟩
    · omega
    · rw [hg.tab, hlen]; omega
    · rw [harg, hlen']; exact hAF
    · unfold FrP at hFP; omega
  · have hb := segLoop_bound hP k
    have h3 : (segOrder pg n).length ≤ pg.length := by
      rw [length_segOrder]; exact length_segEnum_le
    have hCP : CT3 k * (n + pg.length + 1) ≤ CP3 k * (n + pg.length + 1) :=
      Nat.mul_le_mul_right _ (by unfold CP3; omega)
    refine le_trans ?_ hCP
    have e1 : CT3 k * (n + pg.length + 1) = (3 * cSeg k + tToff k + 33) * n +
        3 * (cSeg k * pg.length) + tToff k * pg.length + 33 * pg.length +
        (3 * cSeg k + tToff k + 33) := by unfold CT3; ring
    have e2 : cSeg k * (3 * pg.length) = 3 * (cSeg k * pg.length) := by ring
    have e3 : (segOrder pg n).length * (tToff k + 4) ≤ tToff k * pg.length + 4 * pg.length := by
      have := Nat.mul_le_mul_right (tToff k + 4) h3
      linarith
    omega

end STACS2027.RAM.P3
