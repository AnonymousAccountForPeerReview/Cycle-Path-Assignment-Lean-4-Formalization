module

public import Runtimes.Flow.Prog
import Mathlib.Tactic

/-!
# The edge pass, phases 1–3: reading the input, the largest label, the label dictionary

The construction machines begin with Corollary 5's front end, whose programs
(`Runtimes/ZeroCostProg.lean`) read `k`, `t` and the vertices from the input and run unchanged on
`flowInput g cs k` for any list `cs` of simple `k`-cycles of `g`. Corollary 5's
specifications (`Runtimes/ZeroCostInit.lean`) are stated for `cycles g k`; here they are restated
for a general list `cs`, each within a space bound `S` (`HTB S`) above the end of its memory
(the proofs follow `Runtimes/ZeroCostInit.lean`):
* `stepInit_spec` (`bD g cs k ≤ S`): from the initial configuration on `flowInput g cs k`, the
  registers `gK = k`, `gT = t`, `gV = bV g` (the address of the cycles), `gKT = kt`,
  `gNV = 2kt`, `rFREE = bD g cs k` (the end of the input), within `5t + 16` steps;
* `stepMax_spec` (`bD g cs k ≤ S`): the largest label `gMX = maxV cs`;
* `stepDict_spec` (`bPU g cs k ≤ S`): the dictionary `Tab (bD g cs k) (M + 1) (dictOf (vl cs))`,
  `gN = nV cs` and `rFREE = bPU g cs k`. The dictionary costs `M + 1 ≤ labelBound g` cells of
  space (`maxV_lt_labelBound`) but no time: it is allocated, not cleared.
-/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027 STACS2027.RAM STACS2027.RAM.R0
open ZeroCost (initRead initFin stepInit maxBody stepMax dictInit dictBody stepDict)

variable {S : ℕ}

/-! ### The input -/

theorem length_flowInput {g : Graph} {cs : List Cycle} {k : ℕ} (hcs : ∀ c ∈ cs, IsCycle g k c) :
    (flowInput g cs k).length = bD g cs k := by
  simp [flowInput, bD, bV, length_verts hcs]; ring

/-- The input facts, for the input followed by anything. -/
theorem input_facts {g : Graph} {cs : List Cycle} {k : ℕ} (hcs : ∀ c ∈ cs, IsCycle g k c)
    (rest : List ℕ) :
    (initial (flowInput g cs k ++ rest)).mem 0 = g.length ∧
      (initial (flowInput g cs k ++ rest)).mem (2 * g.length + 1) = k ∧
      (initial (flowInput g cs k ++ rest)).mem (2 * g.length + 2) = cs.length ∧
      Arr (initial (flowInput g cs k ++ rest)).mem (bV g) (verts cs) ∧
      Arr (initial (flowInput g cs k ++ rest)).mem (bD g cs k) rest := by
  have hA : Arr (initial (flowInput g cs k ++ rest)).mem 0 (flowInput g cs k ++ rest) :=
    arr_initial _
  generalize (initial (flowInput g cs k ++ rest)).mem = m at hA ⊢
  rw [arr_append, length_flowInput hcs] at hA
  obtain ⟨hA, hrest⟩ := hA
  rw [flowInput, arr_append] at hA
  obtain ⟨hG, hR⟩ := hA
  rw [length_graphInput, arr_cons, arr_cons] at hR
  rw [graphInput, arr_cons] at hG
  refine ⟨by simpa using hG.1, by simpa using hR.1, by simpa [Nat.add_assoc] using hR.2.1, ?_,
    by simpa using hrest⟩
  have := hR.2.2
  rwa [show 0 + (2 * g.length + 1) + 1 + 1 = bV g by rw [bV]; omega] at this

theorem zeroFrom_flowInput {g : Graph} {cs : List Cycle} {k : ℕ} (hcs : ∀ c ∈ cs, IsCycle g k c) :
    ZeroFrom (initial (flowInput g cs k)).mem (bD g cs k) := by
  have := zeroFrom_initial (flowInput g cs k)
  rwa [length_flowInput hcs] at this

/-! ### The registers fixed by phase 1 -/

/-- The registers set by phase 1 and kept until the end of the edge pass. -/
@[mk_iff] structure GA (g : Graph) (cs : List Cycle) (k : ℕ) (c : Config) : Prop where
  rk : c.reg gK = k
  rt : c.reg gT = cs.length
  rv : c.reg gV = bV g
  rkt : c.reg gKT = k * cs.length
  rnv : c.reg gNV = 2 * (k * cs.length)

/-- The state after phase 1. -/
@[mk_iff] structure InitPost (g : Graph) (cs : List Cycle) (k : ℕ) (c : Config) : Prop where
  ga : GA g cs k c
  rfree : c.reg rFREE = bD g cs k
  mverts : Arr c.mem (bV g) (verts cs)
  mzero : ZeroFrom c.mem (bD g cs k)
  rout : c.out = []

section phases

variable {g : Graph} {cs : List Cycle} {k : ℕ}

/-! ### Phase 1 -/

theorem initRead_spec (hcs : ∀ c ∈ cs, IsCycle g k c) (hS : bD g cs k ≤ S) :
    HTB S initRead (fun c => c = initial (flowInput g cs k))
      (fun c => c.reg gK = k ∧ c.reg gT = cs.length ∧ c.reg gV = bV g ∧
        c.reg rFREE = 0 ∧ c.mem = (initial (flowInput g cs k)).mem ∧ c.out = []) 10 :=
    HTB.of_HT_addrOK (by decide) (fun c hc => by
      subst hc
      obtain ⟨h0, -, -, -, -⟩ := input_facts hcs []
      simp only [List.append_nil] at h0
      have hb : bD g cs k = 2 * g.length + 3 + k * cs.length := rfl
      addr_ok [initRead, initial_reg, h0]) <| by
  refine HT.run_le (by decide) (by decide) fun c hc => ?_
  subst hc
  obtain ⟨h0, hk, ht, -, -⟩ := input_facts hcs []
  simp only [List.append_nil] at h0 hk ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp +decide only [initRead, run_seq', run_load, run_add, run_addc, run_subc, setReg_reg,
    setReg_mem, setReg_out, ↓reduceIte, initial_reg, h0, initial_out]
  · rw [show g.length + g.length + 3 - 2 = 2 * g.length + 1 by omega, hk]
  · rw [show g.length + g.length + 3 - 1 = 2 * g.length + 2 by omega, ht]
  · simp [bV]; omega

/-- **Phase 1**: reading `m`, `k`, `t`. -/
theorem stepInit_spec (hcs : ∀ c ∈ cs, IsCycle g k c) (hS : bD g cs k ≤ S) :
    HTB S stepInit (fun c => c = initial (flowInput g cs k)) (InitPost g cs k)
      (5 * cs.length + 16) := by
  have h1 := initRead_spec hcs hS
  have h2 := HTB.mul (S := S) (d := gKT) (a := gK) (b := gT) (k := ZeroCost.sQ) (x := k)
    (y := cs.length)
    (P := fun c => c.reg gK = k ∧ c.reg gT = cs.length ∧ c.reg gV = bV g ∧
        c.reg rFREE = 0 ∧ c.mem = (initial (flowInput g cs k)).mem ∧ c.out = [])
    (by decide) (by indep) (fun c h => h.1) (fun c h => h.2.1)
  have h3 : HTB S initFin (fun c => (c.reg gK = k ∧ c.reg gT = cs.length ∧
        c.reg gV = bV g ∧ c.reg rFREE = 0 ∧ c.mem = (initial (flowInput g cs k)).mem ∧
        c.out = []) ∧ c.reg gKT = k * cs.length) (InitPost g cs k) 2 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨hk, ht, hv, _, hm, ho⟩, hkt⟩ => ?_
    obtain ⟨-, -, -, hV, -⟩ := input_facts hcs []
    simp only [List.append_nil] at hV
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    all_goals simp +decide only [initFin, run_seq', run_add, setReg_reg, setReg_mem, setReg_out,
      ↓reduceIte, hk, ht, hv, hkt, hm, ho]
    · ring
    · simp [bD]
    · exact hV
    · exact zeroFrom_flowInput hcs
  exact (h1.seq (h2.seq h3)).weaken (by omega)

/-! ### Phase 2: the largest label -/

/-- The invariant of the largest-label scan after `q` entries. -/
def MaxInv (g : Graph) (cs : List Cycle) (k q : ℕ) (c : Config) : Prop :=
  InitPost g cs k c ∧ c.reg gMX = ((verts cs).take q).foldl max 0

theorem maxBody_spec (hcs : ∀ c ∈ cs, IsCycle g k c) (hS : bD g cs k ≤ S) (q : ℕ)
    (hq : q < k * cs.length) :
    HTB S maxBody (fun c => MaxInv g cs k q c ∧ c.reg ZeroCost.sQ = q ∧ c.reg gKT = k * cs.length)
      (fun c => MaxInv g cs k (q + 1) c ∧ c.reg ZeroCost.sQ = q ∧ c.reg gKT = k * cs.length) 8 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hI, hmx⟩, hi, hn⟩ => ⟨?_, ?_⟩
  · have hb : bD g cs k = bV g + k * cs.length := rfl
    addr_ok [maxBody, hI.ga.rv, hi]
  have hq' : q < (verts cs).length := by rw [length_verts hcs]; exact hq
  have hx : c.mem (c.reg gV + c.reg ZeroCost.sQ) = (verts cs)[q] := by
    rw [hI.ga.rv, hi]; exact hI.mverts.get hq'
  have hfold := foldl_max_take_succ (verts cs) q hq'
  have hag : Agree [ZeroCost.sX, gMX, rT] c (run maxBody c) :=
    agree_run (by decide) rfl rfl (by decide) c
  have hI' : InitPost g cs k (run maxBody c) :=
    (show Indep [ZeroCost.sX, gMX, rT] (InitPost g cs k) by indep [initPost_iff, gA_iff]) c _ hag hI
  refine ⟨⟨hI', ?_⟩, by rw [hag.reg ZeroCost.sQ (by decide)]; exact hi,
    by rw [hag.reg gKT (by decide)]; exact hn⟩
  simp only [maxBody, run_seq', run_ld, run_ifLt, run_mov (show ZeroCost.sX ≠ rT by decide), run_skip]
  simp +decide only [setReg_reg, ↓reduceIte, hx, hmx, hfold]
  split_ifs with hlt <;> simp +decide <;> omega

/-- **Phase 2**: the largest label. -/
theorem stepMax_spec (hcs : ∀ c ∈ cs, IsCycle g k c) (hS : bD g cs k ≤ S) :
    HTB S stepMax (InitPost g cs k) (fun c => InitPost g cs k c ∧ c.reg gMX = maxV cs)
      (k * cs.length * 12 + 4) := by
  have h0 : HTB S (.const gMX 0) (InitPost g cs k)
      (fun c => MaxInv g cs k 0 c ∧ c.reg gKT = k * cs.length) 1 := HTB.of_HT rfl <|
    HT.run_le (by decide) (by decide) fun c hI =>
      ⟨⟨(show Indep [gMX] (InitPost g cs k) by indep [initPost_iff, gA_iff]).setReg (by decide) _ hI,
        by simp⟩, by simp +decide [hI.ga.rkt]⟩
  have hl := HTB.forUpC (i := ZeroCost.sQ) (n := gKT) (N := k * cs.length) (body := maxBody)
    (MaxInv g cs k) 8 (by decide) (by decide) (by decide)
    (fun j => by indep [MaxInv, initPost_iff, gA_iff]) (fun j hj => maxBody_spec hcs hS j hj)
  refine (h0.seq hl).mono (fun _ h => h) (fun c ⟨⟨hI, hmx⟩, _, _⟩ => ⟨hI, ?_⟩) (by ring_nf; omega)
  rw [hmx, ← length_verts hcs, List.take_length]; rfl

/-! ### Phase 3: the dictionary -/

/-- The invariant of the dictionary pass after `q` entries. -/
def DictInv (g : Graph) (cs : List Cycle) (k q : ℕ) (c : Config) : Prop :=
  GA g cs k c ∧ c.reg gMX = maxV cs ∧ c.reg gD = bD g cs k ∧ c.reg rFREE = bPU g cs k ∧
    c.reg gN = (vprefix cs q).length ∧ Arr c.mem (bV g) (verts cs) ∧
    Tab c.mem (bD g cs k) (maxV cs + 1) (dictOf (vprefix cs q)) ∧ ZeroFrom c.mem (bPU g cs k) ∧
    c.out = []

theorem dictInit_spec :
    HTB S dictInit (fun c => InitPost g cs k c ∧ c.reg gMX = maxV cs)
      (fun c => DictInv g cs k 0 c ∧ c.reg gKT = k * cs.length) 7 := HTB.of_HT rfl <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨hI, hmx⟩ => ?_
  have hL := layout_eqs g cs k
  have hga : GA g cs k (run dictInit c) :=
    (show RegIndep [rT, gD, rFREE, gN] (GA g cs k) by indep [gA_iff]).run_of_sub (by decide)
      (by decide) hI.ga
  refine ⟨⟨hga, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals simp +decide only [dictInit, run_seq', run_mov (show rFREE ≠ rT by decide), run_add,
    run_inc (show rFREE ≠ rT by decide), run_const, setReg_reg, setReg_mem, setReg_out, ↓reduceIte,
    hmx, hI.rfree, hI.rout, hI.ga.rkt]
  · simp only [bPU]
  · simp [vprefix]
  · exact hI.mverts
  · simpa [vprefix] using hI.mzero.tab (le_refl _) (maxV cs + 1)
  · exact hI.mzero.mono (by omega)

/-- The dictionary after a new label. -/
theorem dictOf_vprefix_succ {q : ℕ} (hq : q < (verts cs).length) :
    dictOf (vprefix cs (q + 1)) = if (verts cs).getD q 0 ∈ vprefix cs q then dictOf (vprefix cs q)
      else Function.update (dictOf (vprefix cs q)) ((verts cs).getD q 0) ((vprefix cs q).length + 1) := by
  rw [vprefix_succ hq]
  split
  · rename_i h; rw [ext_of_mem h]
  · rename_i h; rw [ext_of_not_mem h, dictOf_snoc h]

theorem dictBody_spec (hcs : ∀ c ∈ cs, IsCycle g k c) (hS : bPU g cs k ≤ S) (q : ℕ)
    (hq : q < k * cs.length) :
    HTB S dictBody
      (fun c => DictInv g cs k q c ∧ c.reg ZeroCost.sQ = q ∧ c.reg gKT = k * cs.length)
      (fun c => DictInv g cs k (q + 1) c ∧ c.reg ZeroCost.sQ = q ∧ c.reg gKT = k * cs.length) 12 := by
  refine HTB.run_le (by decide) (by decide)
    fun c ⟨⟨hga, hmx, hd, hfr, hn, hV, hT, hZ, ho⟩, hi, hkt⟩ => ?_
  have hq' : q < (verts cs).length := by rw [length_verts hcs]; exact hq
  set x := (verts cs).getD q 0 with hxdef
  have hxv : x ∈ verts cs := verts_getD_mem hcs hq
  have hxM : x ≤ maxV cs := le_maxV hxv
  have hx : c.mem (c.reg gV + c.reg ZeroCost.sQ) = x := by
    rw [hga.rv, hi]; exact hV.getD hq'
  have hx' : c.mem (bV g + q) = x := by rw [← hga.rv, ← hi]; exact hx
  refine ⟨by
    have hb : bD g cs k = bV g + k * cs.length := rfl
    have hb' : bPU g cs k = bD g cs k + maxV cs + 1 := rfl
    addr_ok [dictBody, hga.rv, hd, hi, hx'], ?_⟩
  have hL := layout_eqs g cs k
  have hdx : c.mem (bD g cs k + x) = dictOf (vprefix cs q) x := hT.get (by omega)
  have hga' : ∀ c', (∀ r, r ≠ ZeroCost.sX → r ≠ ZeroCost.sY → r ≠ ZeroCost.sZ → r ≠ gN → r ≠ rT →
      c'.reg r = c.reg r) → GA g cs k c' := fun c' h => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hga
    exact ⟨(h _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h1,
      (h _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2,
      (h _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h3,
      (h _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h4,
      (h _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h5⟩
  have hlen := length_vprefix_le (cs := cs) q
  simp only [dictBody, run_seq', run_ld, run_add, run_load, run_ifz',
    run_inc (show gN ≠ rT by decide), run_store, run_skip]
  simp +decide only [setReg_reg, setReg_mem, ↓reduceIte, hx, hd, hdx]
  by_cases hmem : x ∈ vprefix cs q
  · have h0 : dictOf (vprefix cs q) x ≠ 0 := fun h => dictOf_eq_zero_iff.mp h hmem
    have hvp : vprefix cs (q + 1) = vprefix cs q := by rw [vprefix_succ hq', ext_of_mem hmem]
    simp only [h0, ↓reduceIte]
    refine ⟨⟨hga' _ (fun r h1 h2 h3 _ _ => by simp [h1, h2, h3]), ?_, ?_, ?_, ?_, hV, ?_, hZ, ho⟩,
      ?_, ?_⟩
    all_goals simp +decide only [setReg_reg, ↓reduceIte, hmx, hd, hfr, hn, hvp, hi, hkt]
    exact hT
  · have h0 : dictOf (vprefix cs q) x = 0 := dictOf_eq_zero_iff.mpr hmem
    have hvp : vprefix cs (q + 1) = vprefix cs q ++ [x] := by
      rw [vprefix_succ hq', ext_of_not_mem hmem]
    simp only [h0, ↓reduceIte, setMem_reg]
    refine ⟨⟨hga' _ (fun r h1 h2 h3 h4 h5 => by simp [h1, h2, h3, h4, h5]), ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ho⟩, ?_, ?_⟩
    all_goals simp +decide only [setReg_reg, ↓reduceIte, setMem_reg, hmx, hd, hfr, hn, hvp, hi, hkt]
    · simp
    · exact hV.upd_of_disjoint (by rw [length_verts hcs]; omega)
    · rw [dictOf_snoc hmem]
      exact hT.upd (by omega)
    · exact hZ.upd (by omega)

/-- The state after phase 3. -/
@[mk_iff] structure DictPost (g : Graph) (cs : List Cycle) (k : ℕ) (c : Config) : Prop where
  ga : GA g cs k c
  rd : c.reg gD = bD g cs k
  rn : c.reg gN = nV cs
  rfree : c.reg rFREE = bPU g cs k
  mverts : Arr c.mem (bV g) (verts cs)
  mdict : Tab c.mem (bD g cs k) (maxV cs + 1) (dictOf (vl cs))
  mzero : ZeroFrom c.mem (bPU g cs k)
  rout : c.out = []

/-- **Phase 3**: the label dictionary. -/
theorem stepDict_spec (hcs : ∀ c ∈ cs, IsCycle g k c) (hS : bPU g cs k ≤ S) :
    HTB S stepDict (fun c => InitPost g cs k c ∧ c.reg gMX = maxV cs) (DictPost g cs k)
      (k * cs.length * 16 + 10) := by
  have hl := HTB.forUpC (i := ZeroCost.sQ) (n := gKT) (N := k * cs.length) (body := dictBody)
    (DictInv g cs k) 12 (by decide) (by decide) (by decide)
    (fun j => by indep [DictInv, gA_iff]) (fun j hj => dictBody_spec hcs hS j hj)
  refine (dictInit_spec.seq hl).mono (fun _ h => h)
    (fun c ⟨⟨hga, _, hd, hfr, hn, hV, hT, hZ, ho⟩, _, _⟩ => ?_) (by ring_nf; omega)
  rw [vprefix_full hcs] at hn hT
  exact ⟨hga, hd, hn, hfr, hV, hT, hZ, ho⟩

end phases

end STACS2027.Runtimes.Flow
