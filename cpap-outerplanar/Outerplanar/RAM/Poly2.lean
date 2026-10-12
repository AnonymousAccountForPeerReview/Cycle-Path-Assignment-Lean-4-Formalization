module

public import Outerplanar.RAM.Poly2StB
import Mathlib.Tactic

/-!
# Phase P2 of the polygon solver (cycles): the main triple

`poly2 k` runs

* the initialization (`p2Init`): `k`, `k - 1` and the tables of the final partial paths
  (`2 |segOrder|` cells, at the free pointer);
* stage R (`Poly2Reg`): the region paths of every segment, children first, memoized
  (`fin`, `rpF_eq_cfin`, `extendParts_eq`);
* stage P (`Poly2Pool`): the pool at `gPOOL`, its size `gNP`, `topStarts` at `gTST`;
* stage B (`Poly2StB`): the boundary lists `bndCat` at `gBIDX` with offsets `bndOffs` at
  `gBOFF`, by a scan of the pairs of the pool cycles, a grouping by first end and stable counting
  sorts (no table indexed by pairs of positions).

`poly2_specB`: from `Poly1Post pg n omap`, `poly2 k` reaches `Poly2Post pg n k omap` within
`CP2 k * (n + |pg| + 1)` steps, allocating at most `M2 pg n k` (`M2_le`: at most
`CP2 k * (n + |pg| + 1)`) fresh cells, without output, every load and store below any bound `S`
leaving room for these cells (`PolyPhaseB`);
`poly2_wregs`: it writes only `rT`, `rFREE`, `gNP … gBIDX` and registers `≥ gPx`;
`poly2_writes`: no output instruction.
-/

@[expose] public section

namespace STACS2027.RAM.P2

open STACS2027.Poly P1

/-! ### The initialization -/

/-- `k`, `k - 1`. -/
def iA (k : ℕ) : Stmt := .seq (.const rK k) (.const rKm1 (k - 1))
/-- The tables of the final partial paths. -/
def iB : Stmt := .seq (alloc rFB gNS) (alloc rFC gNS)
/-- **The initialization.** -/
def p2Init (k : ℕ) : Stmt := .seq (iA k) iB

/-- **Phase P2** of the polygon solver. -/
def poly2 (k : ℕ) : Stmt := .seq (p2Init k) (.seq stageR (.seq stageP stageB))

variable {pg : Graph} {n k : ℕ}

/-- The layout of stage R, from the state after P1: the tables of the final partial paths at
the free pointer, the region of the partial paths after them. -/
def lay (pg : Graph) (n : ℕ) (c₀ : Config) : Lay where
  sb := c₀.reg gSB
  fsid := c₀.reg gFSID
  fv := c₀.reg gFV
  foff := c₀.reg gFOFF
  sa := c₀.reg gSA
  fb := c₀.reg rFREE
  fc := c₀.reg rFREE + (segOrder pg n).length
  fr := c₀.reg rFREE + (segOrder pg n).length + (segOrder pg n).length

theorem layOK {omap : List ℕ} {c₀ : Config} (h : Poly1Post pg n omap c₀) :
    LayOK pg n (lay pg n c₀) := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := h.below
  rw [length_fsidCat] at b3
  exact ⟨by simpa [lay] using b2, by simpa [lay] using b3, by simpa [lay] using b5,
    by simpa [lay] using b4, by simpa [lay] using b1, by simp [lay], by simp [lay]⟩

/-- The state after the initialization. -/
def IOut (pg : Graph) (n k : ℕ) (c₀ c : Config) : Prop :=
  RCtx pg n k (lay pg n c₀) c ∧ FinOK pg n k (lay pg n c₀) 0 c ∧ Zf c ∧ c.reg rKm1 = k - 1 ∧
    c.mem = c₀.mem ∧ c.reg rFREE = (lay pg n c₀).fr

theorem p2Init_spec {omap : List ℕ} (k : ℕ) (c₀ : Config) (h1 : Poly1Post pg n omap c₀) :
    HT (p2Init k) (· = c₀) (IOut pg n k c₀) 10 := by
  have hb := h1.below
  have hns := h1.ns
  have hlf : LoopFree (p2Init k) := show LoopFree (p2Init 0) from by decide
  refine HT.run_le hlf (show size (p2Init 0) ≤ 10 by decide) fun c hc => ?_
  subst hc
  have hA : Agree [rK, rKm1, rT, rFB, rFC, rFREE] c (RAM.run (p2Init k) c) :=
    agree_run hlf rfl rfl (show ∀ r ∈ wregs (p2Init 0), _ by decide) c
  have hfr : (RAM.run (p2Init k) c).reg rFREE = (lay pg n c).fr := by
    simp +decide [p2Init, iA, iB, run_alloc, lay, hns]
  have hm := hA.mem
  have hk : ∀ r ∈ [gPN, gNS, gSB, gFSID, gFV, gFOFF, gSA], (RAM.run (p2Init k) c).reg r = c.reg r :=
    fun r hr => hA.reg r (by simp at hr; rcases hr with h | h | h | h | h | h | h <;> (subst h; decide))
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hk
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hk
  have hZ : Zf (RAM.run (p2Init k) c) := by
    unfold Zf; rw [hm, hfr]; exact h1.base.free.mono (by simp only [lay]; omega)
  refine ⟨⟨by simp +decide [p2Init, iA, iB, run_alloc], by rw [k1]; exact h1.base.pn, by rw [k2]; exact hns,
    by rw [k3]; rfl, by rw [k4]; rfl, by rw [k5]; rfl, by rw [k6]; rfl, by rw [k7]; rfl,
    by simp +decide [p2Init, iA, iB, run_alloc, lay],
    by simp +decide [p2Init, iA, iB, run_alloc, lay, hns], by rw [hm]; exact h1.sb,
    by rw [hm]; exact h1.fsid, by rw [hm]; exact h1.fv, by rw [hm]; exact h1.foff,
    by rw [hm]; exact h1.sa, by rw [hfr]⟩, ⟨by rw [hfr], fun t' ht' => absurd ht' (Nat.not_lt_zero _)⟩,
    hZ, by simp +decide [p2Init, iA, iB, run_alloc], hm, hfr⟩

/-! ### The stages in sequence -/

/-- The data produced by P2. -/
def P2New (pg : Graph) (n k : ℕ) (c : Config) : Prop :=
  c.reg gNP = (pool pg n k).length ∧ Arr c.mem (c.reg gPOOL) (pool pg n k).flatten ∧
    Arr c.mem (c.reg gTST) (topStarts pg n k) ∧ Arr c.mem (c.reg gBOFF) (bndOffs pg n k) ∧
    Arr c.mem (c.reg gBIDX) (bndCat pg n k) ∧
    c.reg gPOOL + (pool pg n k).flatten.length ≤ c.reg rFREE ∧
    c.reg gTST + ((segOrder pg n).length + 1) ≤ c.reg rFREE ∧
    c.reg gBOFF + ((segOrder pg n).length + 1) ≤ c.reg rFREE ∧
    c.reg gBIDX + (bndCat pg n k).length ≤ c.reg rFREE

/-- The steps of P2, stage by stage. -/
def T2 (pg : Graph) (n k : ℕ) : ℕ :=
  10 + ((faceCat pg n).length * (TSl k + 4) + 32 * (segOrder pg n).length + 3) +
    ((segOrder pg n).length * (TPo k + 4) + 13) + TB2 pg n k

/-- The fresh cells of P2, stage by stage: the tables of the final partial paths, the lists of
partial paths (at most `encB k` cells per face vertex), the pool and `topStarts`, stage B. -/
def M2 (pg : Graph) (n k : ℕ) : ℕ :=
  2 * (segOrder pg n).length + encB k * (faceCat pg n).length + ((segOrder pg n).length + 1) +
    (pool pg n k).flatten.length + MB2 pg n k

theorem poly2_main {S : ℕ} (hk : 3 ≤ k) (hP : IsPolygon pg n) {omap : List ℕ} (c₀ : Config)
    (h1 : Poly1Post pg n omap c₀) (hSz : c₀.reg rFREE + M2 pg n k ≤ S) :
    HTB S (poly2 k) (· = c₀)
      (fun c => P2New pg n k c ∧ SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧
        c₀.reg rFREE ≤ c.reg rFREE ∧ Zf c ∧ c.reg rFREE ≤ c₀.reg rFREE + M2 pg n k)
      (T2 pg n k) := by
  have hL := layOK h1
  set L := lay pg n c₀ with hLdef
  have hfb : c₀.reg rFREE = L.fb := by simp [hLdef, lay]
  have hfr0 : L.fr = c₀.reg rFREE + (segOrder pg n).length + (segOrder pg n).length := by
    simp [hLdef, lay]
  unfold M2 at hSz
  refine ((HTB.of_HT rfl (p2Init_spec k c₀ h1)).seq (b' := ((faceCat pg n).length * (TSl k + 4) +
    32 * (segOrder pg n).length + 3) + (((segOrder pg n).length * (TPo k + 4) + 13) + TB2 pg n k))
    (HTB.of_forall fun c₁ hc₁ => ?_)).weaken (by unfold T2; omega)
  obtain ⟨hR₁, hF₁, hZ₁, hkm₁, hm₁, hfr₁⟩ := hc₁
  -- stage R
  have hRs := (stageR_spec (S := S) (k := k) hP hL c₁.mem (by omega)).frame
    (F := fun c => c.reg rKm1 = k - 1) (fun c c' hfr h => (hfr.reg _ (by decide)).trans h)
  refine (hRs.pre fun c hc => ?_).seq (b' := ((segOrder pg n).length * (TPo k + 4) + 13) +
    TB2 pg n k) (HTB.of_forall fun c₂ hc₂ => ?_)
  · subst hc
    exact ⟨⟨⟨⟨⟨hR₁, hF₁, SameOn.refl _ _⟩, hZ₁⟩, by
      unfold FrS; rw [fOff_zero, Nat.mul_zero, Nat.add_zero]; exact hfr₁.le⟩, hR₁.ns⟩, hkm₁⟩
  obtain ⟨⟨⟨hI₂, hFS₂⟩, -, -⟩, hkm₂⟩ := hc₂
  unfold FrS at hFS₂
  rw [fOff_full] at hFS₂
  have hS₂ : SameOn (· < c₀.reg rFREE) c₀.mem c₂.mem := by
    have := hI₂.1.2.2; rw [hm₁] at this
    exact this.mono fun a (ha : a < c₀.reg rFREE) => show a < L.fb by omega
  have hle₂ : c₀.reg rFREE ≤ c₂.reg rFREE := by
    have := hI₂.1.1.fr; have := hL.fc; have := hL.fr; omega
  -- stage P
  refine ((stageP_spec (S := S) hP hL hk c₁.mem (c₂.reg rFREE) c₂.mem (by omega)).pre
    fun c hc => ?_).seq
    (b' := TB2 pg n k) (HTB.of_forall fun c₃ hc₃ => ?_)
  · subst hc; exact ⟨hI₂, hkm₂, rfl, rfl⟩
  obtain ⟨hQ, hT, hPl, hS₃, hTs, hSt, hnp⟩ := hc₃
  have hle₃ : c₂.reg rFREE + ((segOrder pg n).length + 1) ≤ c₃.reg rFREE := by
    have := hSt.2.1; omega
  -- stage B
  have hD := hQ.data
  have hFr := hD.le
  have hBC : BCtx pg n k (c₂.reg rFREE + ((segOrder pg n).length + 1)) (c₃.reg rMD) c₃ :=
    ⟨hQ.rk, hQ.rkm, rfl, hPl, hnp, hSt.bel⟩
  have hB := (stageB_spec (S := S) (pg := pg) (n := n) (k := k) (by omega)
    (PB := c₂.reg rFREE + ((segOrder pg n).length + 1)) (md := c₃.reg rMD) (sa := L.sa)
    (sb := L.sb)).bound c₃ (by have := hSt.2.1; omega)
  refine hB.mono (fun c hc => ?_) (fun c hc => ?_) le_rfl
  · subst hc
    refine ⟨⟨hBC, hQ.ns, hQ.pn, hQ.rsa, hQ.rsb, ⟨hD.sa, ?_⟩, ⟨hD.sb, ?_⟩, hSt.2.2⟩, rfl⟩
    · have := hL.sa; have := hL.fc; have := hL.fr; simp only [List.length_map]; omega
    · have := hL.sb; have := hL.fc; have := hL.fr; simp only [List.length_map]; omega
  · obtain ⟨⟨hbo, hbo', hbi, hbi', hZ⟩, hg, hmb⟩ := hc
    have hfr := hg.free
    have hpb := hSt.bel
    have hs3 := hSt.2.1
    refine ⟨⟨by rw [hg.reg _ (by decide), hnp], ?_, ?_, hbo, hbi, ?_, ?_, hbo', hbi'⟩,
      hS₂.trans ((hS₃.trans (hg.mem.mono fun a (ha : a < c₂.reg rFREE) =>
        show a < c₃.reg rFREE by omega)).mono fun a (ha : a < c₀.reg rFREE) =>
          show a < c₂.reg rFREE by omega), by omega, hZ, ?_⟩
    · rw [hg.reg _ (by decide), hPl]; exact hg.arr' hpb.1 hpb.2
    · rw [hg.reg _ (by decide), hT]; exact hg.arr' hTs (by simp [topStarts, prefixSums]; omega)
    · rw [hg.reg _ (by decide), hPl]; exact hpb.2.trans hfr
    · rw [hg.reg _ (by decide), hT]; omega
    · unfold M2; omega

/-! ### The bound -/

/-- The constant of the running time of P2. -/
def CT2 (k : ℕ) : ℕ :=
  2 * (TSl k + 4) + (TPo k + 4) + 3 * (rpathBound k * (k * (k * 26 + 9) + 11)) +
    100 * (rpathBound k * (k * k)) + 300

/-- The constant of the fresh cells of P2. -/
def CM2 (k : ℕ) : ℕ := 2 * encB k + k * rpathBound k + 8 * (rpathBound k * (k * k)) + 12

/-- **The constant of P2** (steps and fresh cells). -/
def CP2 (k : ℕ) : ℕ := CT2 k + CM2 k

theorem length_pool_le (hP : IsPolygon pg n) :
    (pool pg n k).length ≤ pg.length * rpathBound k := by
  have h1 : (pool pg n k).length ≤ (segOrder pg n).length * rpathBound k := by
    rw [pool, List.length_flatMap]
    exact sum_map_le_mul _ _ _ fun s _ => length_rpF_le hP _ _ _ _
  have h2 := length_segOrder (pg := pg) (n := n)
  have h3 := length_segEnum_le (pg := pg) (n := n)
  have := Nat.mul_le_mul_right (rpathBound k) (show (segOrder pg n).length ≤ pg.length by omega)
  omega

theorem flatten_pool_length : (pool pg n k).flatten.length = (pool pg n k).length * k := by
  have hk : ∀ u ∈ pool pg n k, u.length = k := fun u hu => by
    obtain ⟨s, -, hu⟩ := List.mem_flatMap.mp hu
    exact (sound_rpF hu).2
  rw [List.length_flatten, List.map_congr_left hk, List.map_const', List.sum_replicate,
    smul_eq_mul, mul_comm]

theorem T2_le (hP : IsPolygon pg n) : T2 pg n k ≤ CP2 k * (n + pg.length + 1) := by
  have h1 := length_faceCat_le hP
  have h2 : (segOrder pg n).length ≤ pg.length := by
    have := length_segOrder (pg := pg) (n := n); have := length_segEnum_le (pg := pg) (n := n); omega
  have h3 := length_pool_le (k := k) hP
  have h4 : (tAll pg n k).length ≤ (pool pg n k).length * (k * k) := length_trip_le le_rfl
  have hCP : CT2 k * (n + pg.length + 1) ≤ CP2 k * (n + pg.length + 1) :=
    Nat.mul_le_mul_right _ (by unfold CP2; omega)
  refine le_trans ?_ hCP
  unfold T2 TB2 TBs
  have hC : 300 ≤ CT2 k := by unfold CT2; omega
  have e1 : (faceCat pg n).length * (TSl k + 4) ≤ pg.length * (2 * (TSl k + 4)) := by
    calc _ ≤ (2 * pg.length) * (TSl k + 4) := Nat.mul_le_mul_right _ h1
      _ = _ := by ring
  have e2 : (segOrder pg n).length * (TPo k + 4) ≤ pg.length * (TPo k + 4) :=
    Nat.mul_le_mul_right _ h2
  have e3 : (pool pg n k).length * (k * (k * 26 + 9) + 11) ≤
      pg.length * (rpathBound k * (k * (k * 26 + 9) + 11)) := by
    calc _ ≤ (pg.length * rpathBound k) * (k * (k * 26 + 9) + 11) := Nat.mul_le_mul_right _ h3
      _ = _ := by ring
  have e4 : (pool pg n k).length * (k * k) ≤ pg.length * (rpathBound k * (k * k)) := by
    calc _ ≤ (pg.length * rpathBound k) * (k * k) := Nat.mul_le_mul_right _ h3
      _ = _ := by ring
  have e5 : CT2 k * (n + pg.length + 1) = CT2 k * n + pg.length * (2 * (TSl k + 4)) +
      pg.length * (TPo k + 4) + 3 * (pg.length * (rpathBound k * (k * (k * 26 + 9) + 11))) +
      100 * (pg.length * (rpathBound k * (k * k))) + 300 * pg.length + CT2 k := by
    unfold CT2; ring
  have e6 : 64 * n ≤ CT2 k * n := Nat.mul_le_mul_right n (by omega)
  rw [e5]
  omega

theorem M2_le (hP : IsPolygon pg n) : M2 pg n k ≤ CP2 k * (n + pg.length + 1) := by
  have h1 := length_faceCat_le hP
  have h2 : (segOrder pg n).length ≤ pg.length := by
    have := length_segOrder (pg := pg) (n := n); have := length_segEnum_le (pg := pg) (n := n); omega
  have h3 := length_pool_le (k := k) hP
  have h4 : (tAll pg n k).length ≤ (pool pg n k).length * (k * k) := length_trip_le le_rfl
  have hCP : CM2 k * (n + pg.length + 1) ≤ CP2 k * (n + pg.length + 1) :=
    Nat.mul_le_mul_right _ (by unfold CP2; omega)
  refine le_trans ?_ hCP
  unfold M2 MB2
  rw [flatten_pool_length]
  have e1 : encB k * (faceCat pg n).length ≤ pg.length * (2 * encB k) := by
    calc _ ≤ encB k * (2 * pg.length) := Nat.mul_le_mul_left _ h1
      _ = _ := by ring
  have e2 : (pool pg n k).length * k ≤ pg.length * (k * rpathBound k) := by
    calc _ ≤ (pg.length * rpathBound k) * k := Nat.mul_le_mul_right _ h3
      _ = _ := by ring
  have e3 : (pool pg n k).length * (k * k) ≤ pg.length * (rpathBound k * (k * k)) := by
    calc _ ≤ (pg.length * rpathBound k) * (k * k) := Nat.mul_le_mul_right _ h3
      _ = _ := by ring
  have e5 : CM2 k * (n + pg.length + 1) = CM2 k * n + pg.length * (2 * encB k) +
      pg.length * (k * rpathBound k) + 8 * (pg.length * (rpathBound k * (k * k))) +
      12 * pg.length + CM2 k := by
    unfold CM2; ring
  have hC : 12 ≤ CM2 k := by unfold CM2; omega
  have e6 : 6 * n ≤ CM2 k * n := Nat.mul_le_mul_right n (by omega)
  rw [e5]
  omega

/-! ### Keeping the state after P1 -/

theorem poly1Post_keep {omap : List ℕ} {c₀ c : Config} (h : Poly1Post pg n omap c₀)
    (hreg : ∀ r, r ∈ [rZERO, rONE, gPN, gPE, gPU, gPV, gOMAP, gNS, gSA, gSB, gFSID, gFOFF, gFV] →
      c.reg r = c₀.reg r)
    (hS : SameOn (· < c₀.reg rFREE) c₀.mem c.mem) (hF : c₀.reg rFREE ≤ c.reg rFREE)
    (hZ : ZeroFrom c.mem (c.reg rFREE)) : Poly1Post pg n omap c := by
  have hb := h.base.below
  have hb1 := h.below
  have hol := h.base.omap_len
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hol, hZ, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hreg _ (by simp)]; exact h.base.zero
  · rw [hreg _ (by simp)]; exact h.base.one
  · rw [hreg _ (by simp)]; exact h.base.pn
  · rw [hreg _ (by simp)]; exact h.base.pe
  · rw [hreg _ (by simp)]; exact h.base.pu.of_below hS (by simpa using hb.1)
  · rw [hreg _ (by simp)]; exact h.base.pv.of_below hS (by simpa using hb.2.1)
  · rw [hreg _ (by simp)]; exact h.base.om.of_below hS (by rw [hol]; exact hb.2.2)
  · rw [hreg gPU (by simp), hreg gPV (by simp), hreg gOMAP (by simp)]; omega
  · rw [hreg _ (by simp)]; exact h.ns
  · rw [hreg _ (by simp)]; exact h.sa.of_below hS (by simpa using hb1.1)
  · rw [hreg _ (by simp)]; exact h.sb.of_below hS (by simpa using hb1.2.1)
  · rw [hreg _ (by simp)]; exact h.fsid.of_below hS hb1.2.2.1
  · rw [hreg _ (by simp)]; exact h.foff.of_below hS (by simpa [faceOffs, prefixSums] using hb1.2.2.2.1)
  · rw [hreg _ (by simp)]; exact h.fv.of_below hS hb1.2.2.2.2
  · rw [hreg gSA (by simp), hreg gSB (by simp), hreg gFSID (by simp), hreg gFOFF (by simp),
      hreg gFV (by simp)]
    omega

/-! ### The main theorems -/

theorem wregs_poly2 (k : ℕ) : wregs (poly2 k) = wregs (poly2 0) := rfl

/-- The registers P2 may write. -/
def Ok2 (r : ℕ) : Prop := r = rT ∨ r = rFREE ∨ (gNP ≤ r ∧ r ≤ gBIDX) ∨ gPx ≤ r

instance (r : ℕ) : Decidable (Ok2 r) := by unfold Ok2; infer_instance

theorem ok_seq {s t : Stmt} (h₁ : ∀ r ∈ wregs s, Ok2 r) (h₂ : ∀ r ∈ wregs t, Ok2 r) :
    ∀ r ∈ wregs (.seq s t), Ok2 r := by
  rw [wregs_seq]; exact List.forall_mem_append.mpr ⟨h₁, h₂⟩

theorem ok_forUp {i n : ℕ} {body : Stmt} (hi : Ok2 i) (h : ∀ r ∈ wregs body, Ok2 r) :
    ∀ r ∈ wregs (forUp i n body), Ok2 r := by
  rw [wregs_forUp]
  intro r hr
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | hr | rfl | rfl | rfl
  · exact hi
  · exact Or.inl rfl
  · exact h r hr
  · exact Or.inl rfl
  · exact hi
  · exact Or.inl rfl

theorem ok_peBody : ∀ r ∈ wregs peBody, Ok2 r :=
  ok_seq (by decide) (ok_seq (by decide) (ok_seq (by decide) (ok_seq (by decide) (by decide))))

theorem ok_stageR : ∀ r ∈ wregs stageR, Ok2 r :=
  ok_forUp (by decide) (ok_seq (by decide) (ok_seq (by decide) (ok_seq (ok_forUp (by decide)
    (ok_seq (by decide) (ok_seq (by decide) (ok_seq (ok_forUp (by decide) ok_peBody) (by decide)))))
    (by decide))))

theorem ok_stageP : ∀ r ∈ wregs stageP, Ok2 r :=
  ok_seq (by decide) (ok_seq (ok_forUp (by decide) (by decide)) (by decide))

theorem ok_stageB : ∀ r ∈ wregs stageB, Ok2 r :=
  ok_seq (by decide) (ok_seq (by decide) (ok_seq (by decide) (ok_seq (by decide) (ok_seq (by decide)
    (ok_seq (by decide) (ok_seq (by decide) (ok_seq (by decide) (ok_seq (by decide) (ok_seq (by decide)
    (ok_seq (by decide) (ok_seq (by decide) (ok_seq (by decide) (ok_seq (by decide) (ok_seq (by decide)
    (ok_seq (by decide) (ok_seq (by decide) (ok_seq (by decide) (by decide))))))))))))))))))

/-- **P2 writes only `rT`, `rFREE`, `gNP … gBIDX` and registers at or above `gPx`.** -/
theorem poly2_wregs (k : ℕ) :
    ∀ r ∈ wregs (poly2 k), r = rT ∨ r = rFREE ∨ (gNP ≤ r ∧ r ≤ gBIDX) ∨ gPx ≤ r := by
  rw [wregs_poly2]
  exact ok_seq (by decide) (ok_seq ok_stageR (ok_seq ok_stageP ok_stageB))

/-- **P2 does not write output.** -/
theorem poly2_writes (k : ℕ) : writes (poly2 k) = false := rfl

/-- **Phase P2** (cycles), bounded space: from `Poly1Post pg n omap`, `poly2 k` reaches
`Poly2Post pg n k omap` (the pool, `topStarts`, the boundary lists and their offsets) within
`CP2 k * (n + |pg| + 1)` steps, allocating at most `M2 pg n k ≤ CP2 k * (n + |pg| + 1)` fresh
cells, without output, every load and store below `S`. -/
theorem poly2_specB {k : ℕ} (hk : 3 ≤ k) (pg : Graph) (n : ℕ) (omap : List ℕ)
    (hP : IsPolygon pg n) (hlt : ∀ e ∈ pg, e.1 < e.2) (hnd : pg.Nodup) :
    PolyPhaseB (poly2 k) pg n (Poly1Post pg n omap) (Poly2Post pg n k omap) (CP2 k) := by
  have _ := hlt
  have _ := hnd
  intro S c₀ hSz
  refine HTB.of_forall fun c₁ ⟨h1, hc⟩ => ?_
  subst hc
  have hM' := M2_le (k := k) hP
  refine ((poly2_main hk hP c₁ h1 (by omega)).withFrame c₁).mono (fun c hc => ⟨hc, hc⟩) ?_
    (T2_le hP)
  rintro c ⟨⟨hN, hS, hF, hZ, hM⟩, hfr⟩
  have hreg : ∀ r, r ∉ wregs (poly2 0) → c.reg r = c₁.reg r := fun r hr =>
    hfr.reg r (by rw [wregs_poly2]; exact hr)
  obtain ⟨hnp, hpl, hts, hbo, hbi, b1, b2, b3, b4⟩ := hN
  refine ⟨⟨poly1Post_keep h1 (fun r hr => hreg r fun hw => by
      have := poly2_wregs 0 r hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h <;> (subst h; revert this; decide))
    hS hF hZ, hnp, hpl, hts, hbo, hbi, ⟨b1, b2, b3, b4⟩⟩, hfr.out rfl, hS, hF, by omega⟩

end STACS2027.RAM.P2
