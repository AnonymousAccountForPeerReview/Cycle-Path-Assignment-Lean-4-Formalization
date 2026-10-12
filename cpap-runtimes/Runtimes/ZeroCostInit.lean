module

public import Runtimes.ZeroCostProg
import Mathlib.Tactic

/-!
# Corollary 5 on the RAM: reading the input, the dictionary

Phases 1–3 of `zeroCostProg`, each within a space bound `S` (`HTB S`) above the end of its memory:
* `stepInit_spec` (`bD g k ≤ S`): from the initial configuration on `zeroCostInput g k`, the
  registers `gK = k`, `gT = t`, `gV = bV g` (the address of the cycles), `gKT = kt`,
  `gNV = 2kt`, `rFREE = bD g k` (the end of the input), within `5t + 20` steps;
* `stepMax_spec` (`bD g k ≤ S`): the largest label `gMX = maxV g k`;
* `stepDict_spec` (`bPU g k ≤ S`): the dictionary `Tab (bD g k) (M + 1) (dictOf (vl g k))`,
  `gN = nV g k` and `rFREE = bPU g k`. The dictionary costs `M + 1 ≤ labelBound g` cells of
  space (`maxV_lt_labelBound`) but no time: it is allocated, not cleared.
-/

@[expose] public section

namespace STACS2027.Runtimes.ZeroCost

open STACS2027 STACS2027.RAM STACS2027.RAM.R0

variable {S : ℕ}

/-! ### The registers fixed by phase 1 -/

/-- The registers set by phase 1 and kept until the end. -/
@[mk_iff] structure GA (g : Graph) (k : ℕ) (c : Config) : Prop where
  rk : c.reg gK = k
  rt : c.reg gT = (cycles g k).length
  rv : c.reg gV = bV g
  rkt : c.reg gKT = k * (cycles g k).length
  rnv : c.reg gNV = 2 * (k * (cycles g k).length)

/-- The state after phase 1. -/
@[mk_iff] structure InitPost (g : Graph) (k : ℕ) (c : Config) : Prop where
  ga : GA g k c
  rfree : c.reg rFREE = bD g k
  mverts : Arr c.mem (bV g) (verts g k)
  mzero : ZeroFrom c.mem (bD g k)
  rout : c.out = []

/-! ### Phase 1 -/

theorem input_facts (g : Graph) (k : ℕ) :
    (initial (zeroCostInput g k)).mem 0 = g.length ∧
      (initial (zeroCostInput g k)).mem (2 * g.length + 1) = k ∧
      (initial (zeroCostInput g k)).mem (2 * g.length + 2) = (cycles g k).length ∧
      Arr (initial (zeroCostInput g k)).mem (bV g) (verts g k) ∧
      ZeroFrom (initial (zeroCostInput g k)).mem (bD g k) := by
  have hA : Arr (initial (zeroCostInput g k)).mem 0
      (graphInput g ++ (k :: (cycles g k).length :: verts g k)) := arr_initial (zeroCostInput g k)
  have hZ := zeroFrom_initial (zeroCostInput g k)
  rw [length_zeroCostInput] at hZ
  rw [arr_append] at hA
  obtain ⟨hG, hR⟩ := hA
  rw [length_graphInput, arr_cons, arr_cons] at hR
  rw [graphInput, arr_cons] at hG
  refine ⟨by simpa using hG.1, by simpa using hR.1, by simpa [Nat.add_assoc] using hR.2.1, ?_, hZ⟩
  have := hR.2.2
  rwa [show 0 + (2 * g.length + 1) + 1 + 1 = bV g by rw [bV]; omega] at this

theorem initRead_spec (g : Graph) (k : ℕ) (hS : bD g k ≤ S) :
    HTB S initRead (fun c => c = initial (zeroCostInput g k))
      (fun c => c.reg gK = k ∧ c.reg gT = (cycles g k).length ∧ c.reg gV = bV g ∧
        c.reg rFREE = 0 ∧ c.mem = (initial (zeroCostInput g k)).mem ∧ c.out = []) 10 :=
    HTB.of_HT_addrOK (by decide) (fun c hc => by
      subst hc
      obtain ⟨h0, -, -, -, -⟩ := input_facts g k
      have hb : bD g k = 2 * g.length + 3 + k * (cycles g k).length := rfl
      addr_ok [initRead, initial_reg, h0]) <| by
  refine HT.run_le (by decide) (by decide) fun c hc => ?_
  subst hc
  obtain ⟨h0, hk, ht, -, -⟩ := input_facts g k
  have e1 : 2 * g.length + 3 - 2 = 2 * g.length + 1 := by omega
  have e2 : 2 * g.length + 3 - 1 = 2 * g.length + 2 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp +decide only [initRead, run_seq', run_load, run_add, run_addc, run_subc, setReg_reg,
    setReg_mem, setReg_out, ↓reduceIte, initial_reg, h0, initial_out]
  · rw [show g.length + g.length + 3 - 2 = 2 * g.length + 1 by omega, hk]
  · rw [show g.length + g.length + 3 - 1 = 2 * g.length + 2 by omega, ht]
  · simp [bV]; omega

/-- **Phase 1**: reading `m`, `k`, `t`. -/
theorem stepInit_spec (g : Graph) (k : ℕ) (hS : bD g k ≤ S) :
    HTB S stepInit (fun c => c = initial (zeroCostInput g k)) (InitPost g k)
      (5 * (cycles g k).length + 16) := by
  have h1 := initRead_spec g k hS
  have h2 := HTB.mul (S := S) (d := gKT) (a := gK) (b := gT) (k := sQ) (x := k)
    (y := (cycles g k).length)
    (P := fun c => c.reg gK = k ∧ c.reg gT = (cycles g k).length ∧ c.reg gV = bV g ∧
        c.reg rFREE = 0 ∧ c.mem = (initial (zeroCostInput g k)).mem ∧ c.out = [])
    (by decide) (by indep) (fun c h => h.1) (fun c h => h.2.1)
  have h3 : HTB S initFin (fun c => (c.reg gK = k ∧ c.reg gT = (cycles g k).length ∧
        c.reg gV = bV g ∧ c.reg rFREE = 0 ∧ c.mem = (initial (zeroCostInput g k)).mem ∧ c.out = []) ∧
        c.reg gKT = k * (cycles g k).length) (InitPost g k) 2 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨hk, ht, hv, _, hm, ho⟩, hkt⟩ => ?_
    obtain ⟨-, -, -, hV, hZ⟩ := input_facts g k
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    all_goals simp +decide only [initFin, run_seq', run_add, setReg_reg, setReg_mem, setReg_out,
      ↓reduceIte, hk, ht, hv, hkt, hm, ho]
    · ring
    · simp [bD]
    · exact hV
    · exact hZ
  exact (h1.seq (h2.seq h3)).weaken (by omega)

/-! ### Phase 2: the largest label -/

/-- The invariant of the largest-label scan after `q` entries. -/
def MaxInv (g : Graph) (k : ℕ) (q : ℕ) (c : Config) : Prop :=
  InitPost g k c ∧ c.reg gMX = ((verts g k).take q).foldl max 0

theorem maxBody_spec (g : Graph) (k : ℕ) (hS : bD g k ≤ S) (q : ℕ)
    (hq : q < k * (cycles g k).length) :
    HTB S maxBody (fun c => MaxInv g k q c ∧ c.reg sQ = q ∧ c.reg gKT = k * (cycles g k).length)
      (fun c => MaxInv g k (q + 1) c ∧ c.reg sQ = q ∧ c.reg gKT = k * (cycles g k).length) 8 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hI, hmx⟩, hi, hn⟩ => ⟨?_, ?_⟩
  · have hb : bD g k = bV g + k * (cycles g k).length := rfl
    addr_ok [maxBody, hI.ga.rv, hi]
  have hq' : q < (verts g k).length := by rw [length_verts]; exact hq
  have hx : c.mem (c.reg gV + c.reg sQ) = (verts g k)[q] := by
    rw [hI.ga.rv, hi]; exact hI.mverts.get hq'
  have hfold := foldl_max_take_succ (verts g k) q hq'
  have hag : Agree [sX, gMX, rT] c (run maxBody c) := agree_run (by decide) rfl rfl (by decide) c
  have hI' : InitPost g k (run maxBody c) :=
    (show Indep [sX, gMX, rT] (InitPost g k) by indep [initPost_iff, gA_iff]) c _ hag hI
  refine ⟨⟨hI', ?_⟩, by rw [hag.reg sQ (by decide)]; exact hi,
    by rw [hag.reg gKT (by decide)]; exact hn⟩
  simp only [maxBody, run_seq', run_ld, run_ifLt, run_mov (show sX ≠ rT by decide), run_skip]
  simp +decide only [setReg_reg, ↓reduceIte, hx, hmx, hfold]
  split_ifs with hlt <;> simp +decide <;> omega

/-- **Phase 2**: the largest label. -/
theorem stepMax_spec (g : Graph) (k : ℕ) (hS : bD g k ≤ S) :
    HTB S stepMax (InitPost g k) (fun c => InitPost g k c ∧ c.reg gMX = maxV g k)
      (k * (cycles g k).length * 12 + 4) := by
  have h0 : HTB S (.const gMX 0) (InitPost g k)
      (fun c => MaxInv g k 0 c ∧ c.reg gKT = k * (cycles g k).length) 1 := HTB.of_HT rfl <|
    HT.run_le (by decide) (by decide) fun c hI =>
      ⟨⟨(show Indep [gMX] (InitPost g k) by indep [initPost_iff, gA_iff]).setReg (by decide) _ hI,
        by simp⟩, by simp +decide [hI.ga.rkt]⟩
  have hl := HTB.forUpC (i := sQ) (n := gKT) (N := k * (cycles g k).length) (body := maxBody)
    (MaxInv g k) 8 (by decide) (by decide) (by decide)
    (fun j => by indep [MaxInv, initPost_iff, gA_iff]) (fun j hj => maxBody_spec g k hS j hj)
  refine (h0.seq hl).mono (fun _ h => h) (fun c ⟨⟨hI, hmx⟩, _, _⟩ => ⟨hI, ?_⟩) (by ring_nf; omega)
  rw [hmx, ← length_verts, List.take_length]; rfl

/-! ### Phase 3: the dictionary -/

/-- The invariant of the dictionary pass after `q` entries. -/
def DictInv (g : Graph) (k q : ℕ) (c : Config) : Prop :=
  GA g k c ∧ c.reg gMX = maxV g k ∧ c.reg gD = bD g k ∧ c.reg rFREE = bPU g k ∧
    c.reg gN = (vprefix g k q).length ∧ Arr c.mem (bV g) (verts g k) ∧
    Tab c.mem (bD g k) (maxV g k + 1) (dictOf (vprefix g k q)) ∧ ZeroFrom c.mem (bPU g k) ∧
    c.out = []

theorem dictInit_spec (g : Graph) (k : ℕ) :
    HTB S dictInit (fun c => InitPost g k c ∧ c.reg gMX = maxV g k)
      (fun c => DictInv g k 0 c ∧ c.reg gKT = k * (cycles g k).length) 7 := HTB.of_HT rfl <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨hI, hmx⟩ => ?_
  have hL := layout_eqs g k
  have hga : GA g k (run dictInit c) :=
    (show RegIndep [rT, gD, rFREE, gN] (GA g k) by indep [gA_iff]).run_of_sub (by decide)
      (by decide) hI.ga
  refine ⟨⟨hga, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals simp +decide only [dictInit, run_seq', run_mov (show rFREE ≠ rT by decide), run_add,
    run_inc (show rFREE ≠ rT by decide), run_const, setReg_reg, setReg_mem, setReg_out, ↓reduceIte,
    hmx, hI.rfree, hI.rout, hI.ga.rkt]
  · simp only [bPU]
  · simp [vprefix]
  · exact hI.mverts
  · simpa [vprefix] using hI.mzero.tab (le_refl _) (maxV g k + 1)
  · exact hI.mzero.mono (by omega)

/-- The dictionary after a new label. -/
theorem dictOf_vprefix_succ {g : Graph} {k q : ℕ} (hq : q < (verts g k).length) :
    dictOf (vprefix g k (q + 1)) = if (verts g k).getD q 0 ∈ vprefix g k q then dictOf (vprefix g k q)
      else Function.update (dictOf (vprefix g k q)) ((verts g k).getD q 0) ((vprefix g k q).length + 1) := by
  rw [vprefix_succ hq]
  split
  · rename_i h; rw [ext_of_mem h]
  · rename_i h; rw [ext_of_not_mem h, dictOf_snoc h]

theorem dictBody_spec (g : Graph) (k : ℕ) (hS : bPU g k ≤ S) (q : ℕ)
    (hq : q < k * (cycles g k).length) :
    HTB S dictBody (fun c => DictInv g k q c ∧ c.reg sQ = q ∧ c.reg gKT = k * (cycles g k).length)
      (fun c => DictInv g k (q + 1) c ∧ c.reg sQ = q ∧ c.reg gKT = k * (cycles g k).length) 12 := by
  refine HTB.run_le (by decide) (by decide)
    fun c ⟨⟨hga, hmx, hd, hfr, hn, hV, hT, hZ, ho⟩, hi, hkt⟩ => ?_
  have hq' : q < (verts g k).length := by rw [length_verts]; exact hq
  set x := (verts g k).getD q 0 with hxdef
  have hxv : x ∈ verts g k := verts_getD_mem hq
  have hxM : x ≤ maxV g k := le_maxV hxv
  have hx : c.mem (c.reg gV + c.reg sQ) = x := by
    rw [hga.rv, hi]; exact hV.getD hq'
  have hx' : c.mem (bV g + q) = x := by rw [← hga.rv, ← hi]; exact hx
  refine ⟨by
    have hb : bD g k = bV g + k * (cycles g k).length := rfl
    have hb' : bPU g k = bD g k + maxV g k + 1 := rfl
    addr_ok [dictBody, hga.rv, hd, hi, hx'], ?_⟩
  have hL := layout_eqs g k
  have hdx : c.mem (bD g k + x) = dictOf (vprefix g k q) x := hT.get (by omega)
  have hga' : ∀ c', (∀ r, r ≠ sX → r ≠ sY → r ≠ sZ → r ≠ gN → r ≠ rT → c'.reg r = c.reg r) → GA g k c' :=
    fun c' h => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hga
      exact ⟨(h _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h1,
        (h _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2,
        (h _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h3,
        (h _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h4,
        (h _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h5⟩
  have hlen := length_vprefix_le (g := g) (k := k) q
  simp only [dictBody, run_seq', run_ld, run_add, run_load, run_ifz', run_inc (show gN ≠ rT by decide),
    run_store, run_skip]
  simp +decide only [setReg_reg, setReg_mem, ↓reduceIte, hx, hd, hdx]
  by_cases hmem : x ∈ vprefix g k q
  · have h0 : dictOf (vprefix g k q) x ≠ 0 := fun h => dictOf_eq_zero_iff.mp h hmem
    have hvp : vprefix g k (q + 1) = vprefix g k q := by rw [vprefix_succ hq', ext_of_mem hmem]
    simp only [h0, ↓reduceIte]
    refine ⟨⟨hga' _ (fun r h1 h2 h3 _ _ => by simp [h1, h2, h3]), ?_, ?_, ?_, ?_, hV, ?_, hZ, ho⟩, ?_, ?_⟩
    all_goals simp +decide only [setReg_reg, ↓reduceIte, hmx, hd, hfr, hn, hvp, hi, hkt]
    exact hT
  · have h0 : dictOf (vprefix g k q) x = 0 := dictOf_eq_zero_iff.mpr hmem
    have hvp : vprefix g k (q + 1) = vprefix g k q ++ [x] := by rw [vprefix_succ hq', ext_of_not_mem hmem]
    simp only [h0, ↓reduceIte, setMem_reg]
    refine ⟨⟨hga' _ (fun r h1 h2 h3 h4 h5 => by simp [h1, h2, h3, h4, h5]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ho⟩, ?_, ?_⟩
    all_goals simp +decide only [setReg_reg, ↓reduceIte, setMem_reg, hmx, hd, hfr, hn, hvp, hi, hkt]
    · simp
    · exact hV.upd_of_disjoint (by rw [length_verts]; omega)
    · rw [dictOf_snoc hmem]
      exact hT.upd (by omega)
    · exact hZ.upd (by omega)

/-- The state after phase 3. -/
@[mk_iff] structure DictPost (g : Graph) (k : ℕ) (c : Config) : Prop where
  ga : GA g k c
  rd : c.reg gD = bD g k
  rn : c.reg gN = nV g k
  rfree : c.reg rFREE = bPU g k
  mverts : Arr c.mem (bV g) (verts g k)
  mdict : Tab c.mem (bD g k) (maxV g k + 1) (dictOf (vl g k))
  mzero : ZeroFrom c.mem (bPU g k)
  rout : c.out = []

/-- **Phase 3**: the label dictionary. -/
theorem stepDict_spec (g : Graph) (k : ℕ) (hS : bPU g k ≤ S) :
    HTB S stepDict (fun c => InitPost g k c ∧ c.reg gMX = maxV g k) (DictPost g k)
      (k * (cycles g k).length * 16 + 10) := by
  have hl := HTB.forUpC (i := sQ) (n := gKT) (N := k * (cycles g k).length) (body := dictBody)
    (DictInv g k) 12 (by decide) (by decide) (by decide)
    (fun j => by indep [DictInv, gA_iff]) (fun j hj => dictBody_spec g k hS j hj)
  refine ((dictInit_spec g k).seq hl).mono (fun _ h => h) (fun c ⟨⟨hga, _, hd, hfr, hn, hV, hT, hZ, ho⟩, _, _⟩ => ?_)
    (by ring_nf; omega)
  rw [vprefix_full] at hn hT
  exact ⟨hga, hd, hn, hfr, hV, hT, hZ, ho⟩

end STACS2027.Runtimes.ZeroCost
