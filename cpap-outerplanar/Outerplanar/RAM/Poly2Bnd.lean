module

public import Outerplanar.RAM.Poly2Scan
import Mathlib.Tactic

/-!
# Phase P2 of the polygon solver: the pair scan as a machine

`bscan` runs over the pool cycles `u` (index `i`, at `gPOOL + i * k`), the entries `x = u[a]`
and `y = u[b]`; for a pair other than the top of `u` it pushes `x` (mode `rMD = 0`), `y` (mode
`1`) or the pool index `i` (mode `2`) (`bscan_spec`): the stream receives
`(trip …).map (pick md)`. No segment ids are read here (they are found later by the grouped
pass, `Poly2Grp.lean`). The triples are bounded (`HGB S`) for `S` at or above the end of the
stream.
-/

@[expose] public section

namespace STACS2027.RAM.P2

open STACS2027.Poly P1

/-! ### Registers and programs -/

/-- The mode: push segment indices (`0`) or pool indices. -/
abbrev rMD : ℕ := 89
/-- The pool index `i`. -/
abbrev rBI : ℕ := 150
/-- The index `a` of `x`. -/
abbrev rBA : ℕ := 151
/-- The index `b` of `y`. -/
abbrev rBB : ℕ := 152
/-- The address of the cycle `i`. -/
abbrev rPC : ℕ := 153
/-- The first entry of the cycle. -/
abbrev rU0 : ℕ := 154
/-- The last entry of the cycle. -/
abbrev rUL : ℕ := 155
/-- `x`. -/
abbrev rBX : ℕ := 156
/-- `y`. -/
abbrev rBY : ℕ := 157
/-- Temporary. -/
abbrev rBW : ℕ := 160
/-- Temporary. -/
abbrev rBW2 : ℕ := 161

/-- Read `y`. -/
def bRd : Stmt := ld rBY rPC rBB
/-- `rBW := |x - u0| + |y - uL|`. -/
def bTop : Stmt :=
  .seq (.sub rBW rBX rU0) (.seq (.sub rBW2 rU0 rBX) (.seq (.add rBW rBW rBW2)
    (.seq (.sub rBW2 rBY rUL) (.seq (.add rBW rBW rBW2) (.seq (.sub rBW2 rUL rBY)
      (.add rBW rBW rBW2))))))
/-- Push `x`, `y` or the pool index, by the mode. -/
def bPush : Stmt := .ifz rMD (push rBX) (.seq (subc rBW rMD 1) (.ifz rBW (push rBY) (push rBI)))
/-- One pair. -/
def bbBody : Stmt := .seq bRd (.seq bTop (.ifz rBW .skip bPush))
/-- The entries `y`. -/
def bbLoop : Stmt := forUp rBB rK bbBody
/-- One entry `x`. -/
def baBody : Stmt := .seq (ld rBX rPC rBA) bbLoop
/-- The entries `x`. -/
def baLoop : Stmt := forUp rBA rK baBody
/-- Read the top of the cycle. -/
def biHead : Stmt := .seq (.load rU0 rPC) (ld rUL rPC rKm1)
/-- One pool cycle. -/
def biBody : Stmt := .seq biHead (.seq baLoop (.add rPC rPC rK))
/-- **The pair scan.** -/
def bscan : Stmt := .seq (mov rPC gPOOL) (forUp rBI gNP biBody)

/-! ### The context -/

/-- The value pushed for a triple in mode `md`. -/
def pick (md : ℕ) (p : ℕ × ℕ × ℕ) : ℕ := if md = 0 then p.1 else if md = 1 then p.2.1 else p.2.2

/-- The context of the scan. -/
@[mk_iff] structure BCtx (pg : Graph) (n k : ℕ) (PB md : ℕ) (c : Config) : Prop where
  rk : c.reg rK = k
  rkm : c.reg rKm1 = k - 1
  rmd : c.reg rMD = md
  pl : c.reg gPOOL = PB
  np : c.reg gNP = (pool pg n k).length
  pool : Bel PB (pool pg n k).flatten c

variable {pg : Graph} {n k : ℕ}

theorem BCtx.stable {PB md : ℕ} {W : List ℕ}
    (hW : ∀ r ∈ [rK, rKm1, rMD, gPOOL, gNP], r ∉ W) :
    Stable W (BCtx pg n k PB md) := fun c c' h hg => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hW
  exact ⟨(hg.reg _ hW.1).trans h.rk, (hg.reg _ hW.2.1).trans h.rkm,
    (hg.reg _ hW.2.2.1).trans h.rmd, (hg.reg _ hW.2.2.2.1).trans h.pl,
    (hg.reg _ hW.2.2.2.2).trans h.np, stable_bel W _ _ c c' h.pool hg⟩

/-- The pool cycle `i` in the flattened pool. -/
theorem bel_cyc {PB : ℕ} {c : Config} (h : Bel PB (pool pg n k).flatten c) {i : ℕ}
    (hi : i < (pool pg n k).length) : Bel (PB + i * k) (cyc pg n k i) c := by
  have hk : ∀ u ∈ pool pg n k, u.length = k := fun u hu => by
    obtain ⟨s, -, hu⟩ := List.mem_flatMap.mp hu
    exact (sound_rpF hu).2
  have hlen : ((pool pg n k).take i).flatten.length = i * k := by
    rw [List.length_flatten, List.map_congr_left (g := fun _ => k) fun u hu =>
      hk u (List.mem_of_mem_take hu), List.map_const', List.sum_replicate, smul_eq_mul,
      List.length_take, min_eq_left hi.le]
  have he : (pool pg n k).flatten = ((pool pg n k).take i).flatten ++ cyc pg n k i ++
      ((pool pg n k).drop (i + 1)).flatten := by
    rw [cyc, getD_of_lt hi, ← List.flatten_singleton (l := (pool pg n k)[i]), ← List.flatten_append,
      ← List.flatten_append, ← take_succ_eq hi, List.take_append_drop]
  rw [he] at h
  have := h.sub
  rwa [hlen] at this

/-- The top of a pool cycle. -/
theorem topOf_cyc {i : ℕ} (hi : i < (pool pg n k).length) (hk : 1 ≤ k) :
    ∃ (h0 : 0 < (cyc pg n k i).length) (h1 : k - 1 < (cyc pg n k i).length),
      topOf (cyc pg n k i) = ((cyc pg n k i)[0], (cyc pg n k i)[k - 1]) := by
  have hl := (cyc_facts (k := k) hi).2.2
  have hne : cyc pg n k i ≠ [] := by intro h; rw [h] at hl; simp at hl; omega
  refine ⟨by omega, by omega, ?_⟩
  rw [topOf_eq hne, List.head_eq_getElem, List.getLast_eq_getElem]
  simp [hl]

theorem HGB.push' {S : ℕ} (v q : ℕ) (out : List ℕ) (val : ℕ) (hq : q + out.length < S) :
    HGB S (push v) [rT, rFREE] (fun c => Strm q out c ∧ c.reg v = val)
      (fun c => Strm q (out ++ [val]) c) 3 :=
  HGB.run ⟨trivial, trivial, trivial⟩ le_rfl fun c ⟨hS, hv⟩ =>
    ⟨(addrOK_push v c).mpr (by rw [hS.2.1]; exact hq), by rw [← hv]; exact push_strm hS v,
      push_grow v c⟩

/-- The entries of a prefix of a list of items. -/
theorem length_flatMap_take_le {α β : Type*} (M : List α) (f : α → List β) {i j : ℕ}
    (hij : i ≤ j) : ((M.take i).flatMap f).length ≤ ((M.take j).flatMap f).length := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [List.take_add, List.flatMap_append, List.length_append]
  omega

/-! ### One pair -/

/-- The triples of the first `b` entries `y` for `x = u[a]`. -/
abbrev bRow (pg : Graph) (n k i a b : ℕ) : List (ℕ × ℕ × ℕ) :=
  ((cyc pg n k i).take b).flatMap (tElem (cyc pg n k i) i ((cyc pg n k i).getD a 0))

/-- The registers of the scan of the row `a` of the cycle `i`. -/
def BbF0 (pg : Graph) (n k : ℕ) (PB md i a : ℕ) (c : Config) : Prop :=
  BCtx pg n k PB md c ∧ c.reg rPC = PB + i * k ∧ c.reg rBI = i ∧ c.reg rBA = a ∧
    c.reg rBX = (cyc pg n k i).getD a 0 ∧ c.reg rU0 = (topOf (cyc pg n k i)).1 ∧
    c.reg rUL = (topOf (cyc pg n k i)).2

/-- With the counter of the entries `y`. -/
def BbFr (pg : Graph) (n k : ℕ) (PB md i a b : ℕ) (c : Config) : Prop :=
  BbF0 pg n k PB md i a c ∧ c.reg rBB = b

theorem BbF0.stable {PB md i a : ℕ} {W : List ℕ}
    (hW : ∀ r ∈ [rK, rKm1, rMD, gPOOL, gNP, rPC, rBI, rBA, rBX, rU0, rUL], r ∉ W) :
    Stable W (BbF0 pg n k PB md i a) := fun c c' h hg => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hW
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨BCtx.stable (by simp [hW.1, hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.1]) c c' h1 hg,
    (hg.reg _ hW.2.2.2.2.2.1).trans h2, (hg.reg _ hW.2.2.2.2.2.2.1).trans h3,
    (hg.reg _ hW.2.2.2.2.2.2.2.1).trans h4, (hg.reg _ hW.2.2.2.2.2.2.2.2.1).trans h5,
    (hg.reg _ hW.2.2.2.2.2.2.2.2.2.1).trans h6, (hg.reg _ hW.2.2.2.2.2.2.2.2.2.2).trans h7⟩

theorem BbFr.stable {PB md i a b : ℕ} {W : List ℕ}
    (hW : ∀ r ∈ [rK, rKm1, rMD, gPOOL, gNP, rPC, rBI, rBA, rBX, rU0, rUL], r ∉ W)
    (hB : rBB ∉ W) : Stable W (BbFr pg n k PB md i a b) := fun c c' h hg =>
  ⟨BbF0.stable hW c c' h.1 hg, (hg.reg _ hB).trans h.2⟩

theorem bbBody_spec {S PB md i a q : ℕ} {out : List ℕ}
    (hi : i < (pool pg n k).length) (b : ℕ) (hb : b < k)
    (hSz : q + (out ++ (bRow pg n k i a (b + 1)).map (pick md)).length ≤ S) :
    HGB S bbBody (wregs bbLoop)
      (fun c => BbFr pg n k PB md i a b c ∧ Strm q (out ++ (bRow pg n k i a b).map (pick md)) c)
      (fun c => BbFr pg n k PB md i a b c ∧
        Strm q (out ++ (bRow pg n k i a (b + 1)).map (pick md)) c) 22 := by
  obtain ⟨_, _, hl⟩ := cyc_facts (k := k) hi
  have hbl : b < (cyc pg n k i).length := by omega
  have hrow : bRow pg n k i a (b + 1) = bRow pg n k i a b ++
      tElem (cyc pg n k i) i ((cyc pg n k i).getD a 0) (cyc pg n k i)[b] := by
    simp only [bRow]
    rw [take_succ_eq hbl, List.flatMap_append, List.flatMap_singleton]
  set x := (cyc pg n k i).getD a 0 with hxdef
  set y := (cyc pg n k i)[b] with hydef
  have hlen : (out ++ (bRow pg n k i a (b + 1)).map (pick md)).length =
      (out ++ (bRow pg n k i a b).map (pick md)).length + (tElem (cyc pg n k i) i x y).length := by
    rw [hrow]; simp only [List.map_append, List.length_append, List.length_map]; omega
  -- reading `y`
  have h₁ : HGB S bRd (wregs bbLoop)
      (fun c => BbFr pg n k PB md i a b c ∧ Strm q (out ++ (bRow pg n k i a b).map (pick md)) c)
      (fun c => (BbFr pg n k PB md i a b c ∧ Strm q (out ++ (bRow pg n k i a b).map (pick md)) c) ∧
        c.reg rBY = y) 2 := by
    refine (HGB.runR (s := bRd) (by decide) (by decide) (by decide) (by decide) (by decide)
      fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    have hA : Agree [rBY] c (RAM.run bRd c) := agree_run (by decide) rfl rfl (by decide) c
    have hG := grow_of_agree (W := [rBY]) hA (by decide) (by decide)
    obtain ⟨hF, hS⟩ := hc
    have ⟨⟨hC, hpc, _, _, _, _, _⟩, hbb⟩ := hF
    have hcB := (bel_cyc hC.pool hi).2
    have hfr := hS.2.1
    refine ⟨by addr_ok [bRd, hpc, hbb], ?_⟩
    have hmy : c.mem (PB + i * k + b) = y := (bel_cyc hC.pool hi).get hbl
    refine ⟨⟨BbFr.stable (by decide) (by decide) c _ hF hG, strm_agree hA (by decide) hS⟩, ?_⟩
    simp +decide only [bRd, run_ld, setReg_reg, ↓reduceIte, hpc, hbb, hmy]
  -- the top test
  have h₂ : HGB S bTop (wregs bbLoop)
      (fun c => (BbFr pg n k PB md i a b c ∧ Strm q (out ++ (bRow pg n k i a b).map (pick md)) c) ∧
        c.reg rBY = y)
      (fun c => ((BbFr pg n k PB md i a b c ∧
        Strm q (out ++ (bRow pg n k i a b).map (pick md)) c) ∧ c.reg rBY = y) ∧
        (c.reg rBW = 0 ↔ (x, y) = topOf (cyc pg n k i))) 7 := by
    refine (HGB.runM (s := bTop) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    have hA : Agree [rBW, rBW2] c (RAM.run bTop c) := agree_run (by decide) rfl rfl (by decide) c
    have hG := grow_of_agree (W := [rBW, rBW2]) hA (by decide) (by decide)
    obtain ⟨⟨hF, hS⟩, hy⟩ := hc
    have ⟨⟨_, _, _, _, hbx, hu0, hul⟩, _⟩ := hF
    refine ⟨⟨⟨BbFr.stable (by decide) (by decide) c _ hF hG, strm_agree hA (by decide) hS⟩,
      by rw [hA.reg _ (by decide), hy]⟩, ?_⟩
    simp +decide only [bTop, run_seq', run_sub, run_add, setReg_reg, ↓reduceIte, hbx, hu0, hul,
      hy, Prod.ext_iff]
    omega
  -- the branches
  have hpost : ∀ c, BbFr pg n k PB md i a b c →
      Strm q (out ++ (bRow pg n k i a b).map (pick md) ++
        (tElem (cyc pg n k i) i x y).map (pick md)) c →
      BbFr pg n k PB md i a b c ∧ Strm q (out ++ (bRow pg n k i a (b + 1)).map (pick md)) c := by
    intro c hF hS
    rw [hrow, List.map_append, ← List.append_assoc]
    exact ⟨hF, hS⟩
  have h₃ : HGB S (.ifz rBW .skip bPush) (wregs bbLoop)
      (fun c => ((BbFr pg n k PB md i a b c ∧
        Strm q (out ++ (bRow pg n k i a b).map (pick md)) c) ∧ c.reg rBY = y) ∧
        (c.reg rBW = 0 ↔ (x, y) = topOf (cyc pg n k i)))
      (fun c => BbFr pg n k PB md i a b c ∧
        Strm q (out ++ (bRow pg n k i a (b + 1)).map (pick md)) c) 9 := by
    refine HGB.ifz ?_ ?_
    · -- the top
      refine HGB.of_pre (fun c h => h.1.2.mp h.2) fun htop => ?_
      refine (HGB.skip' (W := wregs bbLoop)).mono (by decide) (fun _ h => h) ?_ (by omega)
      rintro c ⟨⟨⟨⟨hF, hS⟩, -⟩, -⟩, -⟩
      refine hpost c hF ?_
      have hE0 : tElem (cyc pg n k i) i x y = [] := by unfold tElem; rw [ite_eq_left htop]
      rw [hE0, List.map_nil, List.append_nil]; exact hS
    · refine HGB.of_pre (fun c h => show (x, y) ≠ topOf (cyc pg n k i) from
        fun h' => h.2 (h.1.2.mpr h')) fun htop => ?_
      have hE : tElem (cyc pg n k i) i x y = [(x, y, i)] := by
        unfold tElem; rw [ite_eq_right htop]
      have hq : q + (out ++ (bRow pg n k i a b).map (pick md)).length < S := by
        rw [hE] at hlen; simp only [List.length_singleton] at hlen; omega
      have hpush : ∀ (v : ℕ) (val : ℕ), val = pick md (x, y, i) →
          HGB S (push v) (wregs bbLoop)
            (fun c => (BbFr pg n k PB md i a b c ∧
              Strm q (out ++ (bRow pg n k i a b).map (pick md)) c) ∧ c.reg v = val)
            (fun c => BbFr pg n k PB md i a b c ∧
              Strm q (out ++ (bRow pg n k i a (b + 1)).map (pick md)) c) 3 := by
        intro v val hval
        refine (HGB.frame (HGB.push' v q (out ++ (bRow pg n k i a b).map (pick md)) val hq)
          (F := BbFr pg n k PB md i a b) (BbFr.stable (by decide) (by decide))).mono (by decide)
          (fun c ⟨⟨hF, hS⟩, hv⟩ => ⟨⟨hS, hv⟩, hF⟩) (fun c ⟨hS, hF⟩ => hpost c hF ?_) le_rfl
        rw [hE]; simpa [hval] using hS
      refine HGB.ifz ?_ ?_
      · refine HGB.of_pre (fun c h => show md = 0 by rw [← h.1.1.1.1.1.1.1.rmd]; exact h.2)
          fun hmd => ?_
        refine (hpush rBX x (by simp [pick, hmd])).mono (by decide)
          (fun c ⟨⟨⟨⟨⟨hF, hS⟩, _⟩, _⟩, _⟩, _⟩ => ⟨⟨hF, hS⟩, hF.1.2.2.2.2.1⟩) (fun _ h => h) (by omega)
      · refine HGB.of_pre (fun c h => show md ≠ 0 by rw [← h.1.1.1.1.1.1.1.rmd]; exact h.2)
          fun hmd => ?_
        have hsub : HGB S (subc rBW rMD 1) (wregs bbLoop)
            (fun c => ((((BbFr pg n k PB md i a b c ∧
              Strm q (out ++ (bRow pg n k i a b).map (pick md)) c) ∧ c.reg rBY = y) ∧
              (c.reg rBW = 0 ↔ (x, y) = topOf (cyc pg n k i))) ∧ c.reg rBW ≠ 0) ∧ c.reg rMD ≠ 0)
            (fun c => ((BbFr pg n k PB md i a b c ∧
              Strm q (out ++ (bRow pg n k i a b).map (pick md)) c) ∧ c.reg rBY = y) ∧
              c.reg rBW = md - 1) 2 := by
          refine (HGB.runM (s := subc rBW rMD 1) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h)
            le_rfl
          have hA : Agree [rT, rBW] c (RAM.run (subc rBW rMD 1) c) :=
            agree_run (by decide) rfl rfl (by decide) c
          have hG := grow_of_agree (W := [rT, rBW]) hA (by decide) (by decide)
          obtain ⟨⟨⟨⟨⟨hF, hS⟩, hy⟩, -⟩, -⟩, -⟩ := hc
          refine ⟨⟨⟨BbFr.stable (by decide) (by decide) c _ hF hG, strm_agree hA (by decide) hS⟩,
            by rw [hA.reg _ (by decide), hy]⟩, ?_⟩
          simp +decide [run_subc, hF.1.1.rmd]
        refine (hsub.seq (b₂ := 4) (HGB.ifz ?_ ?_)).weaken (by omega)
        · refine HGB.of_pre (fun c h => show md - 1 = 0 by rw [← h.1.2]; exact h.2) fun hm1 => ?_
          refine (hpush rBY y (by simp [pick, show md = 1 by omega])).mono (by decide)
            (fun c ⟨⟨⟨⟨hF, hS⟩, hy⟩, _⟩, _⟩ => ⟨⟨hF, hS⟩, hy⟩) (fun _ h => h) (by omega)
        · refine HGB.of_pre (fun c h => show md - 1 ≠ 0 by rw [← h.1.2]; exact h.2) fun hm1 => ?_
          refine (hpush rBI i (by simp [pick, hmd, show md ≠ 1 by omega])).mono (by decide)
            (fun c ⟨⟨⟨⟨hF, hS⟩, _⟩, _⟩, _⟩ => ⟨⟨hF, hS⟩, hF.1.2.2.1⟩) (fun _ h => h) (by omega)
  exact (h₁.seq (h₂.seq h₃)).weaken (by omega)

/-! ### The loops -/

/-- The invariant of the entries `y`. -/
def BbInv (pg : Graph) (n k : ℕ) (PB md i a q : ℕ) (out : List ℕ) (b : ℕ) (c : Config) :
    Prop :=
  BbF0 pg n k PB md i a c ∧ Strm q (out ++ (bRow pg n k i a b).map (pick md)) c

theorem bbLoop_spec {S PB md i a q : ℕ} {out : List ℕ} (hi : i < (pool pg n k).length)
    (hSz : q + (out ++ (bRow pg n k i a k).map (pick md)).length ≤ S) :
    HGB S bbLoop (wregs bbLoop) (fun c => BbInv pg n k PB md i a q out 0 c ∧ c.reg rK = k)
      (fun c => BbInv pg n k PB md i a q out k c ∧ c.reg rBB = k ∧ c.reg rK = k) (k * 26 + 3) :=
  HGB.forUpC (W := wregs bbLoop) (i := rBB) (n := rK) (body := bbBody)
    (BbInv pg n k PB md i a q out) 22 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (fun b => by indep [BbInv, BbF0, bCtx_iff, Strm, Bel])
    (fun b hb => (bbBody_spec (PB := PB) (md := md) (a := a) (q := q) (out := out) hi b hb (by
      have : (bRow pg n k i a (b + 1)).length ≤ (bRow pg n k i a k).length :=
        length_flatMap_take_le _ _ (by omega)
      simp only [List.length_append, List.length_map] at hSz ⊢; omega)).mono
      (fun _ h => h) (fun c ⟨⟨hF, hS⟩, hb', _⟩ => ⟨⟨hF, hb'⟩, hS⟩)
      (fun c ⟨⟨hF, hb'⟩, hS⟩ => ⟨⟨hF, hS⟩, hb', hF.1.rk⟩) le_rfl)

/-- The triples of the first `a` entries `x` of the cycle `i`. -/
abbrev bAx (pg : Graph) (n k i a : ℕ) : List (ℕ × ℕ × ℕ) :=
  ((cyc pg n k i).take a).flatMap fun x => (cyc pg n k i).flatMap (tElem (cyc pg n k i) i x)

/-- The invariant of the entries `x`. -/
def BaInv (pg : Graph) (n k : ℕ) (PB md i q : ℕ) (out : List ℕ) (a : ℕ) (c : Config) :
    Prop :=
  BCtx pg n k PB md c ∧ c.reg rPC = PB + i * k ∧ c.reg rBI = i ∧
    c.reg rU0 = (topOf (cyc pg n k i)).1 ∧ c.reg rUL = (topOf (cyc pg n k i)).2 ∧
    Strm q (out ++ (bAx pg n k i a).map (pick md)) c

theorem baBody_spec {S PB md i q : ℕ} {out : List ℕ} (hi : i < (pool pg n k).length)
    (a : ℕ) (ha : a < k) (hSz : q + (out ++ (bAx pg n k i (a + 1)).map (pick md)).length ≤ S) :
    HGB S baBody (wregs baLoop)
      (fun c => BaInv pg n k PB md i q out a c ∧ c.reg rBA = a ∧ c.reg rK = k)
      (fun c => BaInv pg n k PB md i q out (a + 1) c ∧ c.reg rBA = a ∧ c.reg rK = k)
      (k * 26 + 5) := by
  obtain ⟨_, _, hl⟩ := cyc_facts (k := k) hi
  have hal : a < (cyc pg n k i).length := by omega
  have htk : (cyc pg n k i).take k = cyc pg n k i := List.take_of_length_le (by omega)
  have he : bAx pg n k i (a + 1) = bAx pg n k i a ++ bRow pg n k i a k := by
    simp only [bAx, bRow, take_succ_eq hal, List.flatMap_append, List.flatMap_singleton,
      getD_of_lt hal, htk]
  have hlen : (out ++ (bAx pg n k i (a + 1)).map (pick md)).length =
      (out ++ (bAx pg n k i a).map (pick md)).length + (bRow pg n k i a k).length := by
    rw [he]; simp only [List.map_append, List.length_append, List.length_map]; omega
  have h₁ : HGB S (ld rBX rPC rBA) (wregs baLoop)
      (fun c => BaInv pg n k PB md i q out a c ∧ c.reg rBA = a ∧ c.reg rK = k)
      (fun c => BbInv pg n k PB md i a q (out ++ (bAx pg n k i a).map (pick md)) 0 c ∧
        c.reg rK = k) 2 := by
    refine (HGB.runR (s := ld rBX rPC rBA) (by decide) (by decide) (by decide) (by decide)
      (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    have hA : Agree [rBX] c (RAM.run (ld rBX rPC rBA) c) := agree_run (by decide) rfl rfl (by decide) c
    have hG := grow_of_agree (W := [rBX]) hA (by decide) (by decide)
    obtain ⟨⟨hC, hpc, hbi, hu0, hul, hS⟩, hba, hk⟩ := hc
    have hcB := (bel_cyc hC.pool hi).2
    have hfr := hS.2.1
    refine ⟨by addr_ok [hpc, hba], ?_⟩
    have hmx : c.mem (PB + i * k + a) = (cyc pg n k i).getD a 0 := (bel_cyc hC.pool hi).1.getD hal
    refine ⟨⟨⟨BCtx.stable (by decide) c _ hC hG, by rw [hA.reg _ (by decide), hpc],
      by rw [hA.reg _ (by decide), hbi], by rw [hA.reg _ (by decide), hba], ?_,
      by rw [hA.reg _ (by decide), hu0], by rw [hA.reg _ (by decide), hul]⟩, ?_⟩,
      by rw [hA.reg _ (by decide), hk]⟩
    · simp +decide only [run_ld, setReg_reg, ↓reduceIte, hpc, hba, hmx]
    · simpa [bRow] using strm_agree hA (by decide) hS
  have hb : q + (out ++ (bAx pg n k i a).map (pick md) ++ (bRow pg n k i a k).map (pick md)).length
      ≤ S := by
    simp only [List.length_append, List.length_map] at hlen hSz ⊢
    omega
  refine (h₁.seq ((bbLoop_spec hi hb).mono (by decide) (fun _ h => h) ?_ le_rfl)).weaken
    (by omega)
  rintro c ⟨⟨⟨hC, hpc, hbi, hba, -, hu0, hul⟩, hS⟩, -, hk⟩
  refine ⟨⟨hC, hpc, hbi, hu0, hul, ?_⟩, hba, hk⟩
  rw [he, List.map_append, ← List.append_assoc]
  exact hS

theorem baLoop_spec {S PB md i q : ℕ} {out : List ℕ} (hi : i < (pool pg n k).length)
    (hSz : q + (out ++ (bAx pg n k i k).map (pick md)).length ≤ S) :
    HGB S baLoop (wregs baLoop) (fun c => BaInv pg n k PB md i q out 0 c ∧ c.reg rK = k)
      (fun c => BaInv pg n k PB md i q out k c ∧ c.reg rBA = k ∧ c.reg rK = k)
      (k * (k * 26 + 9) + 3) :=
  HGB.forUpC (W := wregs baLoop) (i := rBA) (n := rK) (body := baBody)
    (BaInv pg n k PB md i q out) (k * 26 + 5) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun a => by indep [BaInv, bCtx_iff, Strm, Bel])
    (fun a ha => baBody_spec hi a ha (by
      have : (bAx pg n k i (a + 1)).length ≤ (bAx pg n k i k).length :=
        length_flatMap_take_le _ _ (by omega)
      simp only [List.length_append, List.length_map] at hSz ⊢; omega))

/-- The invariant of the pool cycles. -/
def BiInv (pg : Graph) (n k : ℕ) (PB md q : ℕ) (i : ℕ) (c : Config) : Prop :=
  BCtx pg n k PB md c ∧ c.reg rPC = PB + i * k ∧ Strm q ((trip pg n k i).map (pick md)) c

theorem biBody_spec {S : ℕ} (hk : 1 ≤ k) {PB md q : ℕ} (i : ℕ) (hi : i < (pool pg n k).length)
    (hSz : q + (trip pg n k (i + 1)).length ≤ S) :
    HGB S biBody (wregs bscan)
      (fun c => BiInv pg n k PB md q i c ∧ c.reg rBI = i ∧ c.reg gNP = (pool pg n k).length)
      (fun c => BiInv pg n k PB md q (i + 1) c ∧ c.reg rBI = i ∧
        c.reg gNP = (pool pg n k).length) (k * (k * 26 + 9) + 7) := by
  obtain ⟨_, _, hl⟩ := cyc_facts (k := k) hi
  obtain ⟨h0, h1, htop⟩ := topOf_cyc hi hk
  have htk : (cyc pg n k i).take k = cyc pg n k i := List.take_of_length_le (by omega)
  have he : trip pg n k (i + 1) = trip pg n k i ++ bAx pg n k i k := by
    simp only [trip, bAx, List.range_succ, List.flatMap_append, List.flatMap_singleton, tCyc, htk]
  have h₁ : HGB S biHead (wregs bscan)
      (fun c => BiInv pg n k PB md q i c ∧ c.reg rBI = i ∧ c.reg gNP = (pool pg n k).length)
      (fun c => BaInv pg n k PB md i q ((trip pg n k i).map (pick md)) 0 c ∧ c.reg rK = k) 3 := by
    refine (HGB.runR (s := biHead) (by decide) (by decide) (by decide) (by decide)
      (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    have hA : Agree [rU0, rUL] c (RAM.run biHead c) := agree_run (by decide) rfl rfl (by decide) c
    have hG := grow_of_agree (W := [rU0, rUL]) hA (by decide) (by decide)
    obtain ⟨⟨hC, hpc, hS⟩, hbi, -⟩ := hc
    have hcB := (bel_cyc hC.pool hi).2
    have hfr := hS.2.1
    have hle : (trip pg n k i).length ≤ (trip pg n k (i + 1)).length := by
      rw [he, List.length_append]; omega
    simp only [List.length_map] at hfr
    refine ⟨by addr_ok [biHead, hpc, hC.rkm], ?_⟩
    have hm0 : c.mem (PB + i * k) = (cyc pg n k i)[0] := by
      have := (bel_cyc hC.pool hi).get h0; simpa using this
    have hml : c.mem (PB + i * k + (k - 1)) = (cyc pg n k i)[k - 1] := (bel_cyc hC.pool hi).get h1
    refine ⟨⟨BCtx.stable (by decide) c _ hC hG, by rw [hA.reg _ (by decide), hpc],
      by rw [hA.reg _ (by decide), hbi], ?_, ?_, by simpa [bAx] using strm_agree hA (by decide) hS⟩,
      by rw [hA.reg _ (by decide), hC.rk]⟩
    · rw [htop]; simp +decide [biHead, hpc, hm0]
    · rw [htop]; simp +decide [biHead, hpc, hC.rkm, hml]
  have h₃ : HGB S (.add rPC rPC rK) (wregs bscan)
      (fun c => BaInv pg n k PB md i q ((trip pg n k i).map (pick md)) k c ∧ c.reg rBA = k ∧
        c.reg rK = k)
      (fun c => BiInv pg n k PB md q (i + 1) c ∧ c.reg rBI = i ∧
        c.reg gNP = (pool pg n k).length) 1 := by
    refine (HGB.runM (s := .add rPC rPC rK) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h)
      le_rfl
    have hA : Agree [rPC] c (RAM.run (.add rPC rPC rK) c) := agree_run (by decide) rfl rfl (by decide) c
    have hG := grow_of_agree (W := [rPC]) hA (by decide) (by decide)
    obtain ⟨⟨hC, hpc, hbi, -, -, hS⟩, -, hk'⟩ := hc
    refine ⟨⟨BCtx.stable (by decide) c _ hC hG, ?_, ?_⟩, by rw [hA.reg _ (by decide), hbi],
      by rw [hA.reg _ (by decide), hC.np]⟩
    · simp +decide [hpc, hk']; ring
    · rw [he, List.map_append]; exact strm_agree hA (by decide) hS
  exact (h₁.seq (((baLoop_spec hi (by
    rw [he, List.length_append] at hSz; simp only [List.length_append, List.length_map]
    omega)).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl).seq h₃)).weaken (by omega)

theorem trip_len_le {i j : ℕ} (h : i ≤ j) : (trip pg n k i).length ≤ (trip pg n k j).length := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    simp only [trip, List.range_succ, List.flatMap_append, List.length_append] at ih ⊢; omega

/-- **The pair scan**: from an empty stream at `q`, the triples of all pool cycles, in mode
`md`. -/
theorem bscan_spec {S : ℕ} (hk : 1 ≤ k) {PB md q : ℕ}
    (hSz : q + (trip pg n k (pool pg n k).length).length ≤ S) :
    HGB S bscan (wregs bscan) (fun c => BCtx pg n k PB md c ∧ Strm q [] c)
      (fun c => BCtx pg n k PB md c ∧
        Strm q ((trip pg n k (pool pg n k).length).map (pick md)) c)
      ((pool pg n k).length * (k * (k * 26 + 9) + 11) + 5) := by
  have h₀ : HGB S (mov rPC gPOOL) (wregs bscan) (fun c => BCtx pg n k PB md c ∧ Strm q [] c)
      (fun c => BiInv pg n k PB md q 0 c ∧ c.reg gNP = (pool pg n k).length) 2 := by
    refine (HGB.runM (s := mov rPC gPOOL) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h)
      le_rfl
    have hA : Agree [rT, rPC] c (RAM.run (mov rPC gPOOL) c) :=
      agree_run (by decide) rfl rfl (by decide) c
    have hG := grow_of_agree (W := [rT, rPC]) hA (by decide) (by decide)
    obtain ⟨hC, hS⟩ := hc
    refine ⟨⟨BCtx.stable (by decide) c _ hC hG, ?_, by simpa [trip] using strm_agree hA (by decide) hS⟩,
      by rw [hA.reg _ (by decide), hC.np]⟩
    simp +decide [run_mov, hC.pl]
  have hl := HGB.forUpC (W := wregs bscan) (i := rBI) (n := gNP) (N := (pool pg n k).length)
    (body := biBody) (BiInv pg n k PB md q) (k * (k * 26 + 9) + 7) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (fun i => by indep [BiInv, bCtx_iff, Strm, Bel])
    (fun i hi => biBody_spec (S := S) hk i hi (by
      have := trip_len_le (pg := pg) (n := n) (k := k) (show i + 1 ≤ (pool pg n k).length by omega)
      omega))
  exact (h₀.seq (hl.mono (fun _ h => h) (fun _ h => h) (fun c ⟨⟨hC, _, hS⟩, _⟩ => ⟨hC, hS⟩)
    le_rfl)).weaken (by ring_nf; omega)

/-- Steps of the scan. -/
def TBs (pg : Graph) (n k : ℕ) : ℕ := (pool pg n k).length * (k * (k * 26 + 9) + 11) + 5

end STACS2027.RAM.P2
