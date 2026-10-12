module

public import Outerplanar.RAM.Poly2Grp
import Mathlib.Tactic

/-!
# Phase P2 of the polygon solver, stage B: the boundary lists

Stage B (`stageB`) computes the boundary lists `bndCat` and their offsets `bndOffs` without a
table indexed by pairs of positions:

1. three runs of the pair scan (`bscan`, modes `0`, `1`, `2`) write the triples `(x, y, i)` of the
   pool cycles as three arrays `TX`, `TY`, `TI` (`trip`, `L` entries each);
2. a stable counting sort of the triples by `x` (`ORDT`, `OFFT`) and of the segments by their
   first end (`ORDS`, `OFFS`);
3. the grouped pass (`grpPass`) writes the keys `KEYS` of the triples in the grouped order
   (`tripX`, `keyOf`);
4. the pool indices in the grouped order (`VALS`, gathered through `ORDT`);
5. a stable counting sort of the keys (`|segOrder| + 1` buckets, the last one for the pairs that
   are not segments) and a gather of `VALS` through it: the first `|bndCat|` entries are the
   boundary lists (`bndCat_eq_trip`), the bucket starts the offsets (`bndOffs_eq_trip`).

Memory `O(n + |segOrder| + L)`, `L ≤ k² |pool|` (`length_trip_le`); time likewise. The stage is a
bounded growth triple (`HGMB S`, `MB2` fresh cells).
-/

@[expose] public section

namespace STACS2027.RAM.P2

open STACS2027.Poly P1

/-! ### Registers and program -/

/-- Base of the first entries of the triples. -/
abbrev rTX : ℕ := 177
/-- Base of the pool indices of the triples. -/
abbrev rTI : ℕ := 178
/-- The number `L` of triples. -/
abbrev rTL : ℕ := 179
/-- The free address before the grouped pass. -/
abbrev rKY : ℕ := 180
/-- Base of the pool indices in the grouped order. -/
abbrev rVB : ℕ := 181

/-- Mode `0`; the first entries start at the free pointer. -/
def bS1 : Stmt := .seq (.const rMD 0) (mov rTX rFREE)
/-- Mode `1`; the second entries start at the free pointer. -/
def bS2 : Stmt := .seq (.const rMD 1) (mov rGTY rFREE)
/-- Mode `2`; the pool indices start at the free pointer. -/
def bS3 : Stmt := .seq (.const rMD 2) (mov rTI rFREE)
/-- The arguments of the sort of the triples by first entry. -/
def bS4 : Stmt := .seq (.sub rTL rGTY rTX) (.seq (mov rKB rTX) (.seq (mov rKL rTL) (mov rKN gPN)))
/-- Keep the sort; the arguments of the sort of the segments by first end. -/
def bS5 : Stmt :=
  .seq (mov rGOT rKO) (.seq (mov rGFT rKF) (.seq (mov rKB gSA) (.seq (mov rKL gNS) (mov rKN gPN))))
/-- Keep the sort; the free address before the grouped pass. -/
def bS6 : Stmt := .seq (mov rGOS rKO) (.seq (mov rGFS rKF) (mov rKY rFREE))
/-- The arguments of the gather of the pool indices. -/
def bS7 : Stmt := .seq (mov rGI rGOT) (.seq (mov rGF rTI) (mov rGL rTL))
/-- Keep the pool indices; the arguments of the sort of the keys. -/
def bS8 : Stmt :=
  .seq (mov rVB rGO) (.seq (.add rKB rKY gPN) (.seq (.add rKB rKB gPN) (.seq (mov rKL rTL)
    (addc rKN gNS 1))))
/-- The arguments of the final gather. -/
def bS9 : Stmt := .seq (mov rGI rKO) (.seq (mov rGF rVB) (mov rGL rTL))
/-- The results. -/
def bS10 : Stmt := .seq (mov gBOFF rKF) (mov gBIDX rGO)
/-- **Stage B**: the boundary lists. -/
def stageB : Stmt :=
  .seq bS1 (.seq bscan (.seq bS2 (.seq bscan (.seq bS3 (.seq bscan (.seq bS4 (.seq csort
    (.seq bS5 (.seq csort (.seq bS6 (.seq grpPass (.seq bS7 (.seq gather (.seq bS8 (.seq csort
      (.seq bS9 (.seq gather bS10)))))))))))))))))

/-- The result of stage B. -/
def BOut (pg : Graph) (n k : ℕ) (c : Config) : Prop :=
  Arr c.mem (c.reg gBOFF) (bndOffs pg n k) ∧
    c.reg gBOFF + ((segOrder pg n).length + 1) ≤ c.reg rFREE ∧
    Arr c.mem (c.reg gBIDX) (bndCat pg n k) ∧ c.reg gBIDX + (bndCat pg n k).length ≤ c.reg rFREE ∧
    Zf c

variable {pg : Graph} {n k : ℕ}

theorem BCtx.of {PB md : ℕ} {c c' : Config} (h : BCtx pg n k PB md c) (md' : ℕ)
    (hreg : ∀ r ∈ [rK, rKm1, gPOOL, gNP], c'.reg r = c.reg r) (hm : c'.mem = c.mem)
    (hf : c.reg rFREE ≤ c'.reg rFREE) (hmd : c'.reg rMD = md') : BCtx pg n k PB md' c' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hreg
  exact ⟨hreg.1.trans h.rk, hreg.2.1.trans h.rkm, hmd, hreg.2.2.1.trans h.pl,
    hreg.2.2.2.trans h.np, h.pool.mono hm hf⟩

theorem pick_zero (l : List (ℕ × ℕ × ℕ)) : l.map (pick 0) = l.map Prod.fst := by simp [pick]
theorem pick_one (l : List (ℕ × ℕ × ℕ)) : l.map (pick 1) = l.map (·.2.1) := by simp [pick]
theorem pick_two (l : List (ℕ × ℕ × ℕ)) : l.map (pick 2) = l.map (·.2.2) := by simp [pick]

/-- The grouped pass as a bounded growth triple (the free address before it in `rKY`). -/
theorem grpPass_HG {S : ℕ} :
    HGB S grpPass (wregs grpPass)
      (fun c => (GPre pg n k (c.reg rFREE) c.mem c ∧ ZeroFrom c.mem (c.reg rFREE) ∧
        c.reg rKY = c.reg rFREE) ∧ c.reg rFREE + (2 * n + (tAll pg n k).length) ≤ S)
      (fun c => Strm (c.reg rKY + 2 * n) ((tripX pg n k).map (keyOf pg n)) c)
      (14 * (segOrder pg n).length + 24 * (tAll pg n k).length + 34 * n + 10) := by
  refine HGB.ofGhost (by decide) (fun _ h => h) fun F₀ m₀ => ?_
  refine HTB.of_forall fun c₀ hc₀ => ?_
  obtain ⟨⟨⟨hG, hZ, hY⟩, hB⟩, hF, hm⟩ := hc₀
  have h := (grpPass_spec (S := S) (pg := pg) (n := n) (k := k) F₀ m₀ (by omega)).frameReg
    (F := fun c => c.reg rKY = F₀) (by indep)
  refine h.mono (fun c hc => ?_) ?_ le_rfl
  · subst hc
    exact ⟨⟨by rw [← hF, ← hm]; exact hG, hF, hm, by rw [← hF, ← hm]; exact hZ⟩, by rw [hY, hF]⟩
  · rintro c ⟨⟨-, hS, hStr⟩, hY⟩
    exact ⟨by rw [hY]; exact hStr, hS, by have := hStr.2.1; omega⟩

/-- Reading the pool indices through the sort by first entry gives them in the grouped order. -/
theorem vals_eq : (bucketIdx (tkeys pg n k) n).map (fun i => ((tAll pg n k).map (·.2.2)).getD i 0) =
    (tripX pg n k).map (·.2.2) := by
  rw [map_bucketIdx (tAll pg n k) (0, 0, 0) Prod.fst (·.2.2) n]
  rfl

theorem tkeys_lt : ∀ x ∈ tkeys pg n k, x < n := by
  intro z hz; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz; exact (trip_lt le_rfl hp).1

theorem skeys_lt : ∀ x ∈ skeys pg n, x < n := by
  intro z hz; obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hz; have := lt_of_mem_segOrder hs; omega

theorem length_tripX' : (tripX pg n k).length = (tAll pg n k).length :=
  length_tripX fun _ hp => (trip_lt le_rfl hp).1

/-- Steps of stage B. -/
def TB2 (pg : Graph) (n k : ℕ) : ℕ :=
  3 * TBs pg n k + 100 * (tAll pg n k).length + 57 * (segOrder pg n).length + 64 * n + 200

/-- The fresh cells of stage B. -/
def MB2 (pg : Graph) (n k : ℕ) : ℕ :=
  8 * (tAll pg n k).length + 6 * n + 3 * (segOrder pg n).length + 5

/-- **Stage B**: the boundary lists and their offsets, within `TB2` steps and `MB2` fresh
cells. -/
theorem stageB_spec {S : ℕ} (hk : 1 ≤ k) {PB md sa sb : ℕ} :
    HGMB S stageB (wregs stageB)
      (fun c => BCtx pg n k PB md c ∧ c.reg gNS = (segOrder pg n).length ∧ c.reg gPN = n ∧
        c.reg gSA = sa ∧ c.reg gSB = sb ∧ Bel sa ((segOrder pg n).map Prod.fst) c ∧
        Bel sb ((segOrder pg n).map Prod.snd) c ∧ Zf c)
      (BOut pg n k) (TB2 pg n k) (MB2 pg n k) := by
  set A := tAll pg n k with hAdef
  set L := A.length with hLdef
  set NS := (segOrder pg n).length with hNS
  set KEYS := (tripX pg n k).map (keyOf pg n) with hKEYS
  set VALS := (tripX pg n k).map (·.2.2) with hVALS
  have hKl : KEYS.length = L := by rw [hKEYS, List.length_map, length_tripX']
  have hVl : VALS.length = L := by rw [hVALS, List.length_map, length_tripX']
  have hKlt : ∀ x ∈ KEYS, x < NS + 1 := by
    intro z hz; obtain ⟨p, -, rfl⟩ := List.mem_map.mp hz; exact keyOf_lt p
  have hbt := length_bucketIdx (tkeys pg n k) n tkeys_lt
  have hbs := length_bucketIdx (skeys pg n) n skeys_lt
  have hbk := length_bucketIdx KEYS (NS + 1) hKlt
  simp only [List.length_map] at hbt hbs
  refine HGMB.ghost (fun c => c.reg rFREE) fun q₁ => ?_
  -- the frame of the scans
  let F1 : Config → Prop := fun c => c.reg rTX = q₁ ∧ c.reg gNS = NS ∧ c.reg gPN = n ∧
    c.reg gSA = sa ∧ c.reg gSB = sb ∧ Bel sa ((segOrder pg n).map Prod.fst) c ∧
    Bel sb ((segOrder pg n).map Prod.snd) c
  -- 1. mode 0
  have h₁ : HGB S bS1 (wregs stageB)
      (fun c => (BCtx pg n k PB md c ∧ c.reg gNS = NS ∧ c.reg gPN = n ∧ c.reg gSA = sa ∧
        c.reg gSB = sb ∧ Bel sa ((segOrder pg n).map Prod.fst) c ∧
        Bel sb ((segOrder pg n).map Prod.snd) c ∧ Zf c) ∧ c.reg rFREE = q₁)
      (fun c => (BCtx pg n k PB 0 c ∧ Strm q₁ [] c) ∧ F1 c) 3 := by
    refine (HGB.runM (s := bS1) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    have hA : Agree [rMD, rT, rTX] c (RAM.run bS1 c) := agree_run (by decide) rfl rfl (by decide) c
    have hG := grow_of_agree (W := [rMD, rT, rTX]) hA (by decide) (by decide)
    obtain ⟨⟨hC, hns, hpn, hsa, hsb, hBa, hBb, hZ⟩, hq⟩ := hc
    refine ⟨⟨hC.of 0 (fun r hr => hA.reg r (by simp at hr; rcases hr with h | h | h | h <;>
      (subst h; decide))) hA.mem (by rw [hA.reg _ (by decide)]) (by simp +decide [bS1, run_mov]),
      strm_agree hA (by decide) ⟨by simp, by simp [hq], hZ⟩⟩, ?_, ?_⟩
    · simp +decide [bS1, run_mov, hq]
    · exact (show Stable [rMD, rT, rTX] (fun c => c.reg gNS = NS ∧ c.reg gPN = n ∧ c.reg gSA = sa ∧
        c.reg gSB = sb ∧ Bel sa ((segOrder pg n).map Prod.fst) c ∧
        Bel sb ((segOrder pg n).map Prod.snd) c) by stab) c _ ⟨hns, hpn, hsa, hsb, hBa, hBb⟩ hG
  -- 2. mode 1
  let F2 : Config → Prop := fun c => F1 c ∧ Bel q₁ (tkeys pg n k) c ∧ c.reg rGTY = q₁ + L
  have h₃ : HGB S bS2 (wregs stageB)
      (fun c => (BCtx pg n k PB 0 c ∧ Strm q₁ (A.map (pick 0)) c) ∧ F1 c)
      (fun c => (BCtx pg n k PB 1 c ∧ Strm (q₁ + L) [] c) ∧ F2 c) 3 := by
    refine (HGB.runM (s := bS2) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    have hA : Agree [rMD, rT, rGTY] c (RAM.run bS2 c) := agree_run (by decide) rfl rfl (by decide) c
    have hG := grow_of_agree (W := [rMD, rT, rGTY]) hA (by decide) (by decide)
    obtain ⟨⟨hC, hS⟩, hF⟩ := hc
    rw [pick_zero] at hS
    have hfr := hS.2.1
    simp only [List.length_map] at hfr
    refine ⟨⟨hC.of 1 (fun r hr => hA.reg r (by simp at hr; rcases hr with h | h | h | h <;>
      (subst h; decide))) hA.mem (by rw [hA.reg _ (by decide)]) (by simp +decide [bS2, run_mov]),
      strm_agree hA (by decide) ⟨by simp, by simp [hfr, hLdef, hAdef], hS.2.2⟩⟩,
      (show Stable [rMD, rT, rGTY] F1 by stab) c _ hF hG,
      hS.bel.mono hA.mem (by rw [hA.reg _ (by decide)]), ?_⟩
    simp +decide [bS2, run_mov, hfr, hLdef, hAdef]
  -- 3. mode 2
  let F3 : Config → Prop := fun c => F2 c ∧ Bel (q₁ + L) (A.map (·.2.1)) c ∧
    c.reg rTI = q₁ + L + L
  have h₅ : HGB S bS3 (wregs stageB)
      (fun c => (BCtx pg n k PB 1 c ∧ Strm (q₁ + L) (A.map (pick 1)) c) ∧ F2 c)
      (fun c => (BCtx pg n k PB 2 c ∧ Strm (q₁ + L + L) [] c) ∧ F3 c) 3 := by
    refine (HGB.runM (s := bS3) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    have hA : Agree [rMD, rT, rTI] c (RAM.run bS3 c) := agree_run (by decide) rfl rfl (by decide) c
    have hG := grow_of_agree (W := [rMD, rT, rTI]) hA (by decide) (by decide)
    obtain ⟨⟨hC, hS⟩, hF⟩ := hc
    rw [pick_one] at hS
    have hfr := hS.2.1
    simp only [List.length_map] at hfr
    refine ⟨⟨hC.of 2 (fun r hr => hA.reg r (by simp at hr; rcases hr with h | h | h | h <;>
      (subst h; decide))) hA.mem (by rw [hA.reg _ (by decide)]) (by simp +decide [bS3, run_mov]),
      strm_agree hA (by decide) ⟨by simp, by simp [hfr, hLdef, hAdef], hS.2.2⟩⟩,
      (show Stable [rMD, rT, rTI] F2 by stab) c _ hF hG,
      hS.bel.mono hA.mem (by rw [hA.reg _ (by decide)]), ?_⟩
    simp +decide [bS3, run_mov, hfr, hLdef, hAdef]
  -- 4. the sort of the triples by first entry
  let F4 : Config → Prop := fun c => F3 c ∧ Bel (q₁ + L + L) (A.map (·.2.2)) c ∧ c.reg rTL = L
  have h₇ : HGB S bS4 (wregs stageB)
      (fun c => (BCtx pg n k PB 2 c ∧ Strm (q₁ + L + L) (A.map (pick 2)) c) ∧ F3 c)
      (fun c => CsIn (tkeys pg n k) n c ∧ F4 c) 7 := by
    refine (HGB.runM (s := bS4) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    have hA : Agree [rTL, rT, rKB, rKL, rKN] c (RAM.run bS4 c) :=
      agree_run (by decide) rfl rfl (by decide) c
    have hG := grow_of_agree (W := [rTL, rT, rKB, rKL, rKN]) hA (by decide) (by decide)
    obtain ⟨⟨-, hS⟩, hF⟩ := hc
    rw [pick_two] at hS
    obtain ⟨⟨⟨htx, hns, hpn, -, -, -, -⟩, hBx, hty⟩, -, -⟩ := id hF
    have htl : (RAM.run bS4 c).reg rTL = L := by
      simp +decide [bS4, run_mov, hty, htx, hLdef, hAdef]
    refine ⟨⟨?_, ?_, ⟨?_, ?_⟩, ?_⟩, (show Stable [rTL, rT, rKB, rKL, rKN] F3 by stab) c _ hF hG,
      hS.bel.mono hA.mem (by rw [hA.reg _ (by decide)]), htl⟩
    · simp +decide [bS4, run_mov, hty, htx, hLdef, hAdef]
    · simp +decide [bS4, run_mov, hpn]
    · have : (RAM.run bS4 c).reg rKB = q₁ := by simp +decide [bS4, run_mov, htx]
      rw [this, hA.mem]; exact hBx.1
    · have : (RAM.run bS4 c).reg rKB = q₁ := by simp +decide [bS4, run_mov, htx]
      rw [this, hA.reg _ (by decide)]; have := hBx.2; simpa using this
    · rw [hA.mem, hA.reg _ (by decide)]; exact hS.2.2
  have h₈ := HGMB.frame (csort_specMB (S := S) (tkeys pg n k) n tkeys_lt) (F := F4) (by stab)
  -- 5. the sort of the segments by first end
  let F5 : Config → Prop := fun c => F4 c ∧ ArrAt rGOT (bucketIdx (tkeys pg n k) n) c ∧
    TabAt rGFT (n + 1) (offOf (tkeys pg n k)) c
  have h₉ : HGB S bS5 (wregs stageB)
      (fun c => (CsOut (tkeys pg n k) n c ∧ ZeroFrom c.mem (c.reg rFREE)) ∧ F4 c)
      (fun c => CsIn (skeys pg n) n c ∧ F5 c) 10 := by
    refine (HGB.runM (s := bS5) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    have hA : Agree [rGOT, rT, rGFT, rKB, rKL, rKN] c (RAM.run bS5 c) :=
      agree_run (by decide) rfl rfl (by decide) c
    have hG := grow_of_agree (W := [rGOT, rT, rGFT, rKB, rKL, rKN]) hA (by decide) (by decide)
    obtain ⟨⟨⟨hO, hT⟩, hZ⟩, hF⟩ := hc
    obtain ⟨⟨⟨⟨-, hns, hpn, hsa, -, hBa, -⟩, -, -⟩, -, -⟩, -, -⟩ := id hF
    have hfr : (RAM.run bS5 c).reg rFREE = c.reg rFREE := hA.reg _ (by decide)
    have hkb : (RAM.run bS5 c).reg rKB = sa := by simp +decide [bS5, run_mov, hsa]
    refine ⟨⟨by simp +decide [bS5, run_mov, hns, hNS], by simp +decide [bS5, run_mov, hpn],
      ⟨by rw [hkb, hA.mem]; exact hBa.1, by rw [hkb, hfr]; have := hBa.2; simpa using this⟩,
      by rw [hA.mem, hfr]; exact hZ⟩, (show Stable [rGOT, rT, rGFT, rKB, rKL, rKN] F4 by stab) c _ hF hG,
      hO.of_reg (by simp +decide [bS5, run_mov]) hA.mem hfr,
      hT.of_reg (by simp +decide [bS5, run_mov]) hA.mem hfr⟩
  have h₁₀ := HGMB.frame (csort_specMB (S := S) (skeys pg n) n skeys_lt) (F := F5)
    ((show Stable (wregs csort) F4 by stab).and ((Stable.arrAt (by decide) _).and
      (Stable.tabAt (by decide) _)))
  -- 6. the grouped pass
  let F6 : Config → Prop := fun c => F5 c ∧ ArrAt rGOS (bucketIdx (skeys pg n) n) c ∧
    TabAt rGFS (n + 1) (offOf (skeys pg n)) c
  have h₁₁ : HGB S bS6 (wregs stageB)
      (fun c => (CsOut (skeys pg n) n c ∧ ZeroFrom c.mem (c.reg rFREE)) ∧ F5 c)
      (fun c => (GPre pg n k (c.reg rFREE) c.mem c ∧ ZeroFrom c.mem (c.reg rFREE) ∧
        c.reg rKY = c.reg rFREE) ∧ F6 c) 6 := by
    refine (HGB.runM (s := bS6) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    have hA : Agree [rGOS, rT, rGFS, rKY] c (RAM.run bS6 c) :=
      agree_run (by decide) rfl rfl (by decide) c
    have hG := grow_of_agree (W := [rGOS, rT, rGFS, rKY]) hA (by decide) (by decide)
    obtain ⟨⟨⟨hO, hT⟩, hZ⟩, hF⟩ := hc
    have hfr : (RAM.run bS6 c).reg rFREE = c.reg rFREE := hA.reg _ (by decide)
    have hF' := (show Stable [rGOS, rT, rGFS, rKY] F5 from
      (show Stable [rGOS, rT, rGFS, rKY] F4 by stab).and ((Stable.arrAt (by decide) _).and
        (Stable.tabAt (by decide) _))) c _ hF hG
    have hO' : ArrAt rGOS (bucketIdx (skeys pg n) n) (RAM.run bS6 c) :=
      hO.of_reg (by simp +decide [bS6, run_mov]) hA.mem hfr
    have hT' : TabAt rGFS (n + 1) (offOf (skeys pg n)) (RAM.run bS6 c) :=
      hT.of_reg (by simp +decide [bS6, run_mov]) hA.mem hfr
    obtain ⟨⟨⟨⟨⟨-, hns, hpn, -, hsb, -, hBb⟩, -, hty⟩, hBy, -⟩, -, -⟩, hot, hft⟩ := id hF'
    refine ⟨⟨⟨hpn, hns, ?_, ?_, hot.1, ?_, hft.1, hft.2, ?_, ?_, hO'.1, ?_, hT'.1, hT'.2⟩,
      by rw [hA.mem, hfr]; exact hZ, by simp +decide [bS6, run_mov]⟩, hF', hO', hT'⟩
    · rw [hty]; exact hBy.1
    · rw [hty]; have := hBy.2; simpa using this
    · have := hot.2; rw [hbt] at this; exact this
    · rw [hsb]; exact hBb.1
    · rw [hsb]; have := hBb.2; simpa using this
    · have := hO'.2; rw [hbs] at this; exact this
  have hLt : (trip pg n k (pool pg n k).length).length = L := rfl
  have m₁ := HGMB.zero (h₁.pre fun _ h => h.1) (by decide)
  have m₃ := HGMB.zero (h₃.pre fun _ h => h.1) (by decide)
  have m₅ := HGMB.zero (h₅.pre fun _ h => h.1) (by decide)
  have m₇ := HGMB.zero (h₇.pre fun _ h => h.1) (by decide)
  have m₉ := HGMB.zero (h₉.pre fun _ h => h.1) (by decide)
  have m₁₁ := HGMB.zero (h₁₁.pre fun _ h => h.1) (by decide)
  -- the scans, with room for `L` cells above the start of the stream
  have hq : ∀ {q md : ℕ} {F : Config → Prop} {c : Config},
      ((BCtx pg n k PB md c ∧ Strm q [] c) ∧ F c) ∧ c.reg rFREE + L ≤ S → q + L ≤ S := by
    intro q md F c hc
    have e := hc.1.1.2.2.1; have := hc.2; simp only [List.length_nil] at e; omega
  have m₂ := HGMB.ofHG L (HGB.of_pre (fun c hc => hq hc) fun hS => (HGB.frame
    (bscan_spec (S := S) (pg := pg) (n := n) hk (PB := PB) (md := 0) (q := q₁)
      (by rw [hLt]; exact hS))
    (F := F1) (by stab)).mono (W' := wregs stageB) (by decide) (fun _ h => h.1) (fun _ h => h)
    le_rfl) fun c c' hc hc' => by
      have e1 := hc.1.2.2.1; have e2 := hc'.1.2.2.1
      simp only [List.length_map, List.length_nil, hLt] at e1 e2; omega
  have m₄ := HGMB.ofHG L (HGB.of_pre (fun c hc => hq hc) fun hS => (HGB.frame
    (bscan_spec (S := S) (pg := pg) (n := n) hk (PB := PB) (md := 1) (q := q₁ + L)
      (by rw [hLt]; exact hS))
    (F := F2) (by stab)).mono (W' := wregs stageB) (by decide) (fun _ h => h.1) (fun _ h => h)
    le_rfl) fun c c' hc hc' => by
      have e1 := hc.1.2.2.1; have e2 := hc'.1.2.2.1
      simp only [List.length_map, List.length_nil, hLt] at e1 e2; omega
  have m₆ := HGMB.ofHG L (HGB.of_pre (fun c hc => hq hc) fun hS => (HGB.frame
    (bscan_spec (S := S) (pg := pg) (n := n) hk (PB := PB) (md := 2) (q := q₁ + L + L)
      (by rw [hLt]; exact hS))
    (F := F3) (by stab)).mono (W' := wregs stageB) (by decide) (fun _ h => h.1) (fun _ h => h)
    le_rfl) fun c c' hc hc' => by
      have e1 := hc.1.2.2.1; have e2 := hc'.1.2.2.1
      simp only [List.length_map, List.length_nil, hLt] at e1 e2; omega
  have m₈ := h₈.mono (W' := wregs stageB) (by decide) (fun _ h => h) (fun _ h => h) le_rfl le_rfl
  have m₁₀ := h₁₀.mono (W' := wregs stageB) (by decide) (fun _ h => h) (fun _ h => h) le_rfl le_rfl
  have hrest : ∀ q₄, HGMB S (.seq grpPass (.seq bS7 (.seq gather (.seq bS8 (.seq csort (.seq bS9
      (.seq gather bS10)))))))
      (wregs stageB)
      (fun c => ((GPre pg n k (c.reg rFREE) c.mem c ∧ ZeroFrom c.mem (c.reg rFREE) ∧
        c.reg rKY = c.reg rFREE) ∧ F6 c) ∧ c.reg rKY = q₄)
      (BOut pg n k) (72 * L + 29 * NS + 34 * n + 83) (4 * L + 2 * n + 2 * NS + 3) := by
    intro q₄
    -- the grouped pass, with the free address `q₄` before it
    let F6' : Config → Prop := fun c => F6 c ∧ c.reg rKY = q₄
    have h₁₂ := HGB.frame (grpPass_HG (S := S) (pg := pg) (n := n) (k := k)) (F := F6')
      ((show Stable (wregs grpPass) F5 from
        (show Stable (wregs grpPass) F4 by stab).and ((Stable.arrAt (by decide) _).and
          (Stable.tabAt (by decide) _))).and ((Stable.arrAt (by decide) _).and
          (Stable.tabAt (by decide) _)) |>.and (Stable.regEq (by decide) _))
    -- 7. the pool indices in the grouped order
    let F7 : Config → Prop := fun c => F6' c ∧ Bel (q₄ + 2 * n) KEYS c
    have h₁₃ : HGB S bS7 (wregs stageB)
        (fun c => Strm (c.reg rKY + 2 * n) KEYS c ∧ F6' c)
        (fun c => GaIn (bucketIdx (tkeys pg n k) n) (A.map (·.2.2)) c ∧ F7 c) 6 := by
      refine (HGB.runM (s := bS7) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
      have hA : Agree [rGI, rT, rGF, rGL] c (RAM.run bS7 c) :=
        agree_run (by decide) rfl rfl (by decide) c
      have hG := grow_of_agree (W := [rGI, rT, rGF, rGL]) hA (by decide) (by decide)
      obtain ⟨hS, hF⟩ := hc
      have hfr : (RAM.run bS7 c).reg rFREE = c.reg rFREE := hA.reg _ (by decide)
      have hF' := (show Stable [rGI, rT, rGF, rGL] F6' from
        ((show Stable [rGI, rT, rGF, rGL] F5 from
        (show Stable [rGI, rT, rGF, rGL] F4 by stab).and ((Stable.arrAt (by decide) _).and
          (Stable.tabAt (by decide) _))).and ((Stable.arrAt (by decide) _).and
          (Stable.tabAt (by decide) _))).and (Stable.regEq (by decide) _)) c _ hF hG
      obtain ⟨⟨⟨⟨⟨-, -, hti⟩, hBi, htl⟩, hot, -⟩, -, -⟩, hky⟩ := id hF
      refine ⟨⟨by simp +decide [bS7, run_mov, htl, hbt, hLdef, hAdef], hot.of_reg (by simp +decide [bS7, run_mov])
        hA.mem hfr, ⟨?_, ?_⟩, by rw [hA.mem, hfr]; exact hS.2.2⟩, hF', ?_⟩
      · have : (RAM.run bS7 c).reg rGF = q₁ + L + L := by simp +decide [bS7, run_mov, hti]
        rw [this, hA.mem]; exact hBi.1
      · have : (RAM.run bS7 c).reg rGF = q₁ + L + L := by simp +decide [bS7, run_mov, hti]
        rw [this, hfr]; exact hBi.2
      · rw [hky] at hS; exact hS.bel.mono hA.mem (by rw [hfr])
    have h₁₄ := HGMB.frame (gather_spec (S := S) (bucketIdx (tkeys pg n k) n) (A.map (·.2.2))
      (fun i hi => by have := lt_of_mem_bucketIdx hi; simpa using this)) (F := F7)
      ((((show Stable (wregs gather) F5 from
        (show Stable (wregs gather) F4 by stab).and ((Stable.arrAt (by decide) _).and
          (Stable.tabAt (by decide) _))).and ((Stable.arrAt (by decide) _).and
          (Stable.tabAt (by decide) _))).and (Stable.regEq (by decide) _)).and (stable_bel _ _ _))
    -- 8. the sort of the keys
    let F8 : Config → Prop := fun c => ArrAt rVB VALS c ∧ c.reg rTL = L
    have h₁₅ : HGB S bS8 (wregs stageB)
        (fun c => (ArrAt rGO ((bucketIdx (tkeys pg n k) n).map fun i => (A.map (·.2.2)).getD i 0) c ∧
          ZeroFrom c.mem (c.reg rFREE)) ∧ F7 c)
        (fun c => CsIn KEYS (NS + 1) c ∧ F8 c) 10 := by
      refine (HGB.runM (s := bS8) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
      have hA : Agree [rVB, rT, rKB, rKL, rKN] c (RAM.run bS8 c) :=
        agree_run (by decide) rfl rfl (by decide) c
      obtain ⟨⟨hV, hZ⟩, hF⟩ := hc
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hns, hpn, -, -, -, -⟩, -, -⟩, -, -⟩, -, htl⟩, -, -⟩, -, -⟩, hky⟩, hBk⟩ := hF
      have hfr : (RAM.run bS8 c).reg rFREE = c.reg rFREE := hA.reg _ (by decide)
      have hkb : (RAM.run bS8 c).reg rKB = q₄ + 2 * n := by
        simp +decide [bS8, run_mov, run_addc, hky, hpn]; omega
      rw [vals_eq] at hV
      refine ⟨⟨by simp +decide [bS8, run_mov, run_addc, htl, hKl], by simp +decide [bS8, run_mov, run_addc, hns, hNS],
        ⟨by rw [hkb, hA.mem]; exact hBk.1, by rw [hkb, hfr]; exact hBk.2⟩,
        by rw [hA.mem, hfr]; exact hZ⟩, hV.of_reg (by simp +decide [bS8, run_mov, run_addc]) hA.mem hfr,
        by rw [hA.reg _ (by decide), htl]⟩
    have h₁₆ := HGMB.frame (csort_specMB (S := S) KEYS (NS + 1) hKlt) (F := F8)
      ((Stable.arrAt (by decide) _).and (Stable.regEq (by decide) _))
    -- 9. the boundary lists
    have h₁₇ : HGB S bS9 (wregs stageB)
        (fun c => (CsOut KEYS (NS + 1) c ∧ ZeroFrom c.mem (c.reg rFREE)) ∧ F8 c)
        (fun c => GaIn (bucketIdx KEYS (NS + 1)) VALS c ∧ TabAt rKF (NS + 1 + 1) (offOf KEYS) c) 6 := by
      refine (HGB.runM (s := bS9) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
      have hA : Agree [rGI, rT, rGF, rGL] c (RAM.run bS9 c) :=
        agree_run (by decide) rfl rfl (by decide) c
      obtain ⟨⟨⟨hO, hT⟩, hZ⟩, hV, htl⟩ := hc
      have hfr : (RAM.run bS9 c).reg rFREE = c.reg rFREE := hA.reg _ (by decide)
      refine ⟨⟨by simp +decide [bS9, run_mov, htl, hbk, hKl], hO.of_reg (by simp +decide [bS9, run_mov])
        hA.mem hfr, hV.of_reg (by simp +decide [bS9, run_mov]) hA.mem hfr,
        by rw [hA.mem, hfr]; exact hZ⟩, hT.of_reg (hA.reg _ (by decide)) hA.mem hfr⟩
    have h₁₈ := HGMB.frame (gather_spec (S := S) (bucketIdx KEYS (NS + 1)) VALS
      (fun i hi => by have := lt_of_mem_bucketIdx hi; rw [hVl]; rw [hKl] at this; exact this))
      (F := TabAt rKF (NS + 1 + 1) (offOf KEYS)) (Stable.tabAt (by decide) _)
    have h₁₉ : HGB S bS10 (wregs stageB)
        (fun c => (ArrAt rGO ((bucketIdx KEYS (NS + 1)).map fun i => VALS.getD i 0) c ∧
          ZeroFrom c.mem (c.reg rFREE)) ∧ TabAt rKF (NS + 1 + 1) (offOf KEYS) c)
        (BOut pg n k) 4 := by
      refine (HGB.runM (s := bS10) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
      have hA : Agree [rT, gBOFF, gBIDX] c (RAM.run bS10 c) :=
        agree_run (by decide) rfl rfl (by decide) c
      obtain ⟨⟨hG, hZ⟩, hT⟩ := hc
      have hfr : (RAM.run bS10 c).reg rFREE = c.reg rFREE := hA.reg _ (by decide)
      have hbo : (RAM.run bS10 c).reg gBOFF = c.reg rKF := by simp +decide [bS10, run_mov]
      have hbi : (RAM.run bS10 c).reg gBIDX = c.reg rGO := by simp +decide [bS10, run_mov]
      rw [bucketIdx_succ, List.map_append, bndCat_eq_trip] at hG
      refine ⟨?_, ?_, ?_, ?_, by unfold Zf; rw [hA.mem, hfr]; exact hZ⟩
      · rw [hbo, hA.mem, ← bndOffs_eq_trip]; exact (hT.1.mono (by omega)).toArr
      · rw [hbo, hfr]; have := hT.2; omega
      · rw [hbi, hA.mem]; exact Arr.prefix hG.1
      · rw [hbi, hfr]; have := hG.2; simp only [List.length_append] at this; omega
    have m₁₂ := HGMB.ofHG (2 * n + L) (h₁₂.mono (W' := wregs stageB) (by decide)
      (P' := fun c => ((GPre pg n k (c.reg rFREE) c.mem c ∧ ZeroFrom c.mem (c.reg rFREE) ∧
        c.reg rKY = c.reg rFREE) ∧ F6' c) ∧ c.reg rFREE + (2 * n + L) ≤ S)
      (fun _ ⟨⟨hP, hF⟩, hb⟩ => ⟨⟨hP, hb⟩, hF⟩) (fun _ h => h) le_rfl) fun c c' hc hc' => by
        have e1 := hc.1.2.2; have e2 := hc.2.2; have e3 := hc'.1.2.1; have e4 := hc'.2.2
        rw [hKl] at e3; omega
    have m₁₃ := HGMB.zero (h₁₃.pre fun _ h => h.1) (by decide)
    have m₁₅ := HGMB.zero (h₁₅.pre fun _ h => h.1) (by decide)
    have m₁₇ := HGMB.zero (h₁₇.pre fun _ h => h.1) (by decide)
    have m₁₉ := HGMB.zero (h₁₉.pre fun _ h => h.1) (by decide)
    have m₁₄ := h₁₄.mono (W' := wregs stageB) (by decide) (fun _ h => h) (fun _ h => h) le_rfl le_rfl
    have m₁₆ := h₁₆.mono (W' := wregs stageB) (by decide) (fun _ h => h) (fun _ h => h) le_rfl le_rfl
    have m₁₈ := h₁₈.mono (W' := wregs stageB) (by decide) (fun _ h => h) (fun _ h => h) le_rfl le_rfl
    refine ((m₁₂.pre fun c ⟨⟨hP, hF⟩, hky⟩ => ⟨hP, hF, hky⟩).seq (m₁₃.seq (m₁₄.seq (m₁₅.seq
      (m₁₆.seq (m₁₇.seq (m₁₈.seq m₁₉))))))).weaken ?_ ?_
    · rw [hbt, hbk, hKl, ← hLdef, ← hNS]; omega
    · rw [hbt, hbk, hKl, ← hLdef]; omega
  refine (m₁.seq (m₂.seq (m₃.seq (m₄.seq (m₅.seq (m₆.seq (m₇.seq (m₈.seq (m₉.seq (m₁₀.seq
    (m₁₁.seq (HGMB.ghost (fun c => c.reg rKY) hrest)))))))))))).weaken ?_ ?_
  · unfold TB2 TBs; simp only [List.length_map, hLdef, hAdef, hNS]; omega
  · unfold MB2; simp only [List.length_map, hLdef, hAdef, hNS]; omega

end STACS2027.RAM.P2
