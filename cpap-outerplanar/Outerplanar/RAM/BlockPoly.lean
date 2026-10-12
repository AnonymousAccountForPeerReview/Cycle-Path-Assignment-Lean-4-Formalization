module

public import Outerplanar.RAM.BlockPre
import Mathlib.Tactic

/-!
# The block solver: the polygon branch

On entry (`DRep`, the state after step 5): the vertices `vs = blockVerts E` at `gVS`, the
local graph `L = locG E` at `gLU`, `gLV`, the memory below `F = c₀.reg rFREE` the initial one.
In the polygon case (`N = |vs| ≥ 3`, not a `K₄`, and the polygon hypothesis
`IsPolygon (pgOf E) N` given by `BlockGood`):

* `ear_step`: the ear elimination (`EarSpec`, taken as a hypothesis, with its hypothesis that
  `L` has an outerplanar Hamiltonian cycle: `ham` itself, `HamFacts.outerplanarHam`) stores
  `ham = hamOf E = Ear.earHam N L` at `gHAM`; its footprint keeps our registers (`ERep`), and
  its new free address `Fe` is at most `F + 6m + CE (N + m + 1)`;
* `pInit_spec`: the allocations of `POS`, `PU`, `PV`, `OMAP` at the new `rFREE = Fe`
  (`PRep`: the state of the rest of the branch, its memory `PMem`; every store is at or
  above `Fe`, so the data below `Fe` survives);
* `posLoop_spec`: `POS[ham[p]] := p`, i.e. `POS[u] = ham.idxOf u` for `u < N` (`ham` is a
  permutation of `0, …, N - 1`, `HamFacts`);
* `pgLoop_spec`: the polygon `pgOf E = localEdges ham L`;
* `omLoop_spec`: the output map `omapOf g E` (`p ↦ labels[vs[ham[p]]]`);
* `poly_step`: the polygon solver (`PolySpecB`, taken as a hypothesis) writes the output;
* `polyBranch_spec`: the whole branch.

All triples are `HTB S` triples: the branch touches the data of steps 1–5 (below
`F + 6m`), the memory of the ear elimination and of the polygon solver (bounded by their
specifications), and the four arrays of `pInit` (`2N + 2m` cells at `Fe`), so it runs below
every `S ≥ F + polyMem CE CP N m` (`polyMem`: `6m + CE (N + m + 1) + 2N + 2m + CP (N + m + 1)`),
and its final `rFREE` is at most `F + polyMem CE CP N m`.
-/

@[expose] public section

namespace STACS2027.RAM.Block

open STACS2027.Algo

variable {S : ℕ}

/-- The Hamiltonian cycle of the polygon branch. -/
abbrev hamOf (E : List Edge) : List ℕ := Ear.earHam (blockVerts E).length (locG E)

/-- The polygon of the polygon branch. -/
abbrev pgOf (E : List Edge) : Graph := localEdges (hamOf E) (locG E)

/-- The state on entry to the dispatch (after step 5). -/
abbrev DRep (g : Graph) (E : List Edge) (c₀ : Config) : Config → Prop :=
  Rep g E c₀ (E.map Prod.fst) (E.map Prod.snd) (blockVerts E) (fun _ => 0)
    ((locG E).map Prod.fst) ((locG E).map Prod.snd)

/-- The postcondition of the block solver (`B`: an upper bound on the final `rFREE`). -/
def BPost (k : ℕ) (g : Graph) (E : List Edge) (c₀ : Config) (B : ℕ) (c : Config) : Prop :=
  c.out = c₀.out ++ (solveBlock k E).flatten.map (labelOf g) ∧
    SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧ ZeroFrom c.mem (c.reg rFREE) ∧
    c₀.reg rFREE ≤ c.reg rFREE ∧ c.reg rFREE ≤ B

/-- The memory of the polygon branch beyond `F`: the six arrays of steps 1–5, the ear
elimination, the four arrays of `pInit` and the polygon solver. -/
def polyMem (CE CP N m : ℕ) : ℕ := 6 * m + CE * (N + m + 1) + 2 * N + 2 * m + CP * (N + m + 1)

theorem length_locG (E : List Edge) : (locG E).length = E.length := length_localEdges _ _

theorem length_pgOf (E : List Edge) : (pgOf E).length = E.length := by
  rw [length_localEdges, length_locG]

/-! ### The ear elimination -/

/-- The state after the ear elimination. -/
@[mk_iff] structure ERep (g : Graph) (E : List Edge) (c₀ c : Config) : Prop where
  glob : Glob c₀ c
  vn : c.reg gVN = (blockVerts E).length
  vs : c.reg gVS = c₀.reg rFREE + 2 * E.length
  lu : c.reg gLU = c₀.reg rFREE + 4 * E.length
  lv : c.reg gLV = c₀.reg rFREE + 5 * E.length
  ln : c.reg gLN = E.length
  out : c.out = c₀.out
  mvs : Arr c.mem (c₀.reg rFREE + 2 * E.length) (blockVerts E)
  mlu : Arr c.mem (c₀.reg rFREE + 4 * E.length) ((locG E).map Prod.fst)
  mlv : Arr c.mem (c₀.reg rFREE + 5 * E.length) ((locG E).map Prod.snd)
  same : SameOn (· < c₀.reg rFREE) c₀.mem c.mem
  ham : Arr c.mem (c.reg gHAM) (hamOf E)
  hamb : c.reg gHAM + (blockVerts E).length ≤ c.reg rFREE
  le : c₀.reg rFREE + 6 * E.length ≤ c.reg rFREE
  zero : ZeroFrom c.mem (c.reg rFREE)

theorem not_mem_ear {s : Stmt} (hW : ∀ r ∈ wregs s, r = rT ∨ r = rFREE ∨ r = gHAM ∨ rS ≤ r)
    {r : ℕ} (h1 : r ≠ rT) (h2 : r ≠ rFREE) (h3 : r ≠ gHAM) (h4 : r < rS) : r ∉ wregs s :=
  fun hr => by
    rcases hW r hr with h | h | h | h
    · exact h1 h
    · exact h2 h
    · exact h3 h
    · exact absurd h4 (Nat.not_lt.mpr h)

theorem ear_footprint {s : Stmt} (hW : ∀ r ∈ wregs s, r = rT ∨ r = rFREE ∨ r = gHAM ∨ rS ≤ r) :
    ∀ r ∈ wregs s, r = rT ∨ r = rFREE ∨ gVN ≤ r := fun r hr => by
  rcases hW r hr with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · right; right; rw [h]; decide
  · right; right; exact le_trans (by decide) h

/-- **The ear elimination** (from its specification and footprint). -/
theorem ear_step {earProg : Stmt} {CE : ℕ} (hear : EarSpec earProg CE)
    (hearW : ∀ r ∈ wregs earProg, r = rT ∨ r = rFREE ∨ r = gHAM ∨ rS ≤ r)
    (hearO : writes earProg = false) {g : Graph} {E : List Edge} {c₀ : Config} (hB : BlockIn g E c₀)
    (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.2 < numV g) (hnd : E.Nodup) (hN3 : 3 ≤ (blockVerts E).length)
    (hham : ∃ ham0, OuterplanarHam (locG E) ham0 ∧ ∀ v, v < (blockVerts E).length → v ∈ ham0)
    (hS : c₀.reg rFREE + 6 * E.length + CE * ((blockVerts E).length + E.length + 1) ≤ S) :
    HTB S earProg (DRep g E c₀) (fun c => ERep g E c₀ c ∧
      c.reg rFREE ≤ c₀.reg rFREE + 6 * E.length + CE * ((blockVerts E).length + E.length + 1))
      (CE * ((blockVerts E).length + E.length + 1)) := by
  refine HTB.of_forall fun ce hce => ?_
  have hE' : ∀ e ∈ E, e.1 < e.2 := fun e he => (hE e he).1
  have hlen := length_locG E
  have hNm := length_blockVerts_le E
  have hF := hce.lay.free
  have hin : EarIn (blockVerts E).length (locG E) ce := by
    refine ⟨hce.glob.zero, hce.glob.one, hce.vn, by rw [hce.lay.ln, hlen], ?_, ?_, ?_, ?_⟩
    · rw [hce.lay.lu]; exact hce.mem.mlu
    · rw [hce.lay.lv]; exact hce.mem.mlv
    · rw [hF]; exact hce.mem.zero
    · rw [hce.lay.lu, hce.lay.lv, hF, hlen]; omega
  have h := (HTB.withFrame (hear S _ _ ce (localEdges_bounds hE') (localEdges_nodup' hE' hnd) hN3
    hham (by rw [hF, hlen]; exact hS)) ce).pre (P' := fun c => c = ce)
    (fun c hc => ⟨⟨hc ▸ hin, hc⟩, hc⟩)
  refine (h.post fun c ⟨⟨hham, hhb, _, hsame, hzero, hle, hfre⟩, hfr⟩ => ?_).weaken
    (le_of_eq (by rw [hlen]))
  rw [hF, hlen] at hfre
  refine ⟨?_, hfre⟩
  have hreg : ∀ r, r ≠ rT → r ≠ rFREE → r ≠ gHAM → r < rS → c.reg r = ce.reg r :=
    fun r h1 h2 h3 h4 => hfr.reg r (not_mem_ear hearW h1 h2 h3 h4)
  refine ⟨hce.glob.frame (ear_footprint hearW) hfr, ?_, ?_, ?_, ?_, ?_,
    (hfr.out hearO).trans hce.out, ?_, ?_, ?_, ?_, hham, hhb, ?_, hzero⟩
  · rw [hreg _ (by decide) (by decide) (by decide) (by decide), hce.vn]
  · rw [hreg _ (by decide) (by decide) (by decide) (by decide), hce.lay.vs]
  · rw [hreg _ (by decide) (by decide) (by decide) (by decide), hce.lay.lu]
  · rw [hreg _ (by decide) (by decide) (by decide) (by decide), hce.lay.lv]
  · rw [hreg _ (by decide) (by decide) (by decide) (by decide), hce.lay.ln]
  · exact hce.mem.mvs.of_below hsame (by rw [hF]; omega)
  · exact hce.mem.mlu.of_below hsame (by rw [hF]; simp only [List.length_map, hlen]; omega)
  · exact hce.mem.mlv.of_below hsame (by rw [hF]; simp only [List.length_map, hlen]; omega)
  · exact (hce.mem.sameOn_zero hB.loc).trans
      (hsame.mono fun a (ha : a < c₀.reg rFREE) => show a < ce.reg rFREE by omega)
  · omega

/-! ### The state of the rest of the branch -/

/-- The memory after the allocations of the polygon branch at `Fe` (the `rFREE` after the ear
elimination; `hb`: the base of `ham`): the data below `Fe`, the positions `pos` (a table on
`N` cells at `Fe`), the polygon's ends `pu`, `pv`, the output map `om`. -/
structure PMem (g : Graph) (E : List Edge) (c₀ : Config) (Fe hb : ℕ) (pos : ℕ → ℕ)
    (pu pv om : List ℕ) (m : ℕ → ℕ) : Prop where
  mvs : Arr m (c₀.reg rFREE + 2 * E.length) (blockVerts E)
  mlu : Arr m (c₀.reg rFREE + 4 * E.length) ((locG E).map Prod.fst)
  mlv : Arr m (c₀.reg rFREE + 5 * E.length) ((locG E).map Prod.snd)
  same : SameOn (· < c₀.reg rFREE) c₀.mem m
  ham : Arr m hb (hamOf E)
  mpos : Tab m Fe (blockVerts E).length pos
  mpu : Arr m (Fe + (blockVerts E).length) pu
  mpv : Arr m (Fe + (blockVerts E).length + E.length) pv
  mom : Arr m (Fe + (blockVerts E).length + 2 * E.length) om
  zero : ZeroFrom m (Fe + 2 * (blockVerts E).length + 2 * E.length)
  lpu : pu.length ≤ E.length
  lpv : pv.length ≤ E.length
  lom : om.length ≤ (blockVerts E).length
  hamb : hb + (blockVerts E).length ≤ Fe
  le : c₀.reg rFREE + 6 * E.length ≤ Fe

section PMem

variable {g : Graph} {E : List Edge} {c₀ : Config} {Fe hb : ℕ} {pos : ℕ → ℕ} {pu pv om : List ℕ}
  {m : ℕ → ℕ}

/-- A store at or above `Fe` keeps the data below `Fe`. -/
theorem PMem.below_upd (h : PMem g E c₀ Fe hb pos pu pv om m) {a : ℕ} (ha : Fe ≤ a) (x : ℕ) :
    Arr (upd m a x) (c₀.reg rFREE + 2 * E.length) (blockVerts E) ∧
      Arr (upd m a x) (c₀.reg rFREE + 4 * E.length) ((locG E).map Prod.fst) ∧
      Arr (upd m a x) (c₀.reg rFREE + 5 * E.length) ((locG E).map Prod.snd) ∧
      SameOn (· < c₀.reg rFREE) c₀.mem (upd m a x) ∧ Arr (upd m a x) hb (hamOf E) := by
  have hN := length_blockVerts_le E
  have hl := length_locG E
  have hH : (hamOf E).length = (blockVerts E).length := length_earHam _ _
  have h1 := h.hamb
  have h2 := h.le
  have hlu : ((locG E).map Prod.fst).length = E.length := by simp [hl]
  have hlv : ((locG E).map Prod.snd).length = E.length := by simp [hl]
  exact ⟨h.mvs.upd_of_disjoint (by omega), h.mlu.upd_of_disjoint (by omega),
    h.mlv.upd_of_disjoint (by omega), h.same.upd_of_ge (by omega) x,
    h.ham.upd_of_disjoint (by omega)⟩

theorem PMem.upd_pos (h : PMem g E c₀ Fe hb pos pu pv om m) {i : ℕ}
    (hi : i < (blockVerts E).length) {a : ℕ} (ha : a = Fe + i) (x : ℕ) :
    PMem g E c₀ Fe hb (Function.update pos i x) pu pv om (upd m a x) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h.below_upd (a := a) (by omega) x
  have := h.lpu
  have := h.lpv
  have := h.lom
  exact ⟨h1, h2, h3, h4, h5, h.mpos.upd ha, h.mpu.upd_of_disjoint (by omega),
    h.mpv.upd_of_disjoint (by omega), h.mom.upd_of_disjoint (by omega), h.zero.upd (by omega),
    h.lpu, h.lpv, h.lom, h.hamb, h.le⟩

theorem PMem.upd_pu (h : PMem g E c₀ Fe hb pos pu pv om m) (hlen : pu.length < E.length) {a : ℕ}
    (ha : a = Fe + (blockVerts E).length + pu.length) (x : ℕ) :
    PMem g E c₀ Fe hb pos (pu ++ [x]) pv om (upd m a x) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h.below_upd (a := a) (by omega) x
  have := h.lpu
  have := h.lpv
  have := h.lom
  exact ⟨h1, h2, h3, h4, h5, h.mpos.upd_of_disjoint (by omega), h.mpu.upd_snoc ha,
    h.mpv.upd_of_disjoint (by omega), h.mom.upd_of_disjoint (by omega), h.zero.upd (by omega),
    by simp; omega, h.lpv, h.lom, h.hamb, h.le⟩

theorem PMem.upd_pv (h : PMem g E c₀ Fe hb pos pu pv om m) (hlen : pv.length < E.length) {a : ℕ}
    (ha : a = Fe + (blockVerts E).length + E.length + pv.length) (x : ℕ) :
    PMem g E c₀ Fe hb pos pu (pv ++ [x]) om (upd m a x) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h.below_upd (a := a) (by omega) x
  have := h.lpu
  have := h.lpv
  have := h.lom
  exact ⟨h1, h2, h3, h4, h5, h.mpos.upd_of_disjoint (by omega), h.mpu.upd_of_disjoint (by omega),
    h.mpv.upd_snoc ha, h.mom.upd_of_disjoint (by omega), h.zero.upd (by omega),
    h.lpu, by simp; omega, h.lom, h.hamb, h.le⟩

theorem PMem.upd_om (h : PMem g E c₀ Fe hb pos pu pv om m)
    (hlen : om.length < (blockVerts E).length) {a : ℕ}
    (ha : a = Fe + (blockVerts E).length + 2 * E.length + om.length) (x : ℕ) :
    PMem g E c₀ Fe hb pos pu pv (om ++ [x]) (upd m a x) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h.below_upd (a := a) (by omega) x
  have := h.lpu
  have := h.lpv
  have := h.lom
  exact ⟨h1, h2, h3, h4, h5, h.mpos.upd_of_disjoint (by omega), h.mpu.upd_of_disjoint (by omega),
    h.mpv.upd_of_disjoint (by omega), h.mom.upd_snoc ha, h.zero.upd (by omega),
    h.lpu, h.lpv, by simp; omega, h.hamb, h.le⟩

end PMem

/-- The state of the polygon branch after the allocations. -/
@[mk_iff] structure PRep (g : Graph) (E : List Edge) (c₀ : Config) (Fe hb : ℕ) (pos : ℕ → ℕ)
    (pu pv om : List ℕ) (c : Config) : Prop where
  glob : Glob c₀ c
  vn : c.reg gVN = (blockVerts E).length
  vs : c.reg gVS = c₀.reg rFREE + 2 * E.length
  lu : c.reg gLU = c₀.reg rFREE + 4 * E.length
  lv : c.reg gLV = c₀.reg rFREE + 5 * E.length
  ln : c.reg gLN = E.length
  hamr : c.reg gHAM = hb
  posr : c.reg gPOS = Fe
  pur : c.reg gPU = Fe + (blockVerts E).length
  pvr : c.reg gPV = Fe + (blockVerts E).length + E.length
  omr : c.reg gOMAP = Fe + (blockVerts E).length + 2 * E.length
  pe : c.reg gPE = E.length
  pn : c.reg gPN = (blockVerts E).length
  free : c.reg rFREE = Fe + 2 * (blockVerts E).length + 2 * E.length
  out : c.out = c₀.out
  mem : PMem g E c₀ Fe hb pos pu pv om c.mem

theorem PRep.indep (g : Graph) (E : List Edge) (c₀ : Config) (Fe hb : ℕ) (pos : ℕ → ℕ)
    (pu pv om : List ℕ) : Indep W (PRep g E c₀ Fe hb pos pu pv om) := by
  indep [pRep_iff, glob_iff]

/-- A loop-free block writing scratch registers only, with a new memory. -/
theorem PRep.run_of {g : Graph} {E : List Edge} {c₀ : Config} {Fe hb : ℕ} {pos : ℕ → ℕ}
    {pu pv om : List ℕ} {s : Stmt} (hs : LoopFree s) (hW : ∀ r ∈ wregs s, r ∈ W)
    (hw : writes s = false) {c : Config} (hR : PRep g E c₀ Fe hb pos pu pv om c)
    {pos' : ℕ → ℕ} {pu' pv' om' : List ℕ}
    (hm : PMem g E c₀ Fe hb pos' pu' pv' om' (RAM.run s c).mem) :
    PRep g E c₀ Fe hb pos' pu' pv' om' (RAM.run s c) := by
  have hr : ∀ r, r ∉ W → (RAM.run s c).reg r = c.reg r := fun r hr =>
    run_reg_of_not_mem hs (fun h => hr (hW r h)) c
  refine ⟨hR.glob.run hs (footprint_of_W hW), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, hm⟩
  · rw [hr _ (by decide), hR.vn]
  · rw [hr _ (by decide), hR.vs]
  · rw [hr _ (by decide), hR.lu]
  · rw [hr _ (by decide), hR.lv]
  · rw [hr _ (by decide), hR.ln]
  · rw [hr _ (by decide), hR.hamr]
  · rw [hr _ (by decide), hR.posr]
  · rw [hr _ (by decide), hR.pur]
  · rw [hr _ (by decide), hR.pvr]
  · rw [hr _ (by decide), hR.omr]
  · rw [hr _ (by decide), hR.pe]
  · rw [hr _ (by decide), hR.pn]
  · rw [hr _ (by decide), hR.free]
  · rw [run_out_of_writes hs hw, hR.out]

/-- **The allocations** of the polygon branch at `Fe`. -/
theorem pInit_spec {g : Graph} {E : List Edge} {c₀ : Config} (Fe hb : ℕ) :
    HTB S pInit (fun c => ERep g E c₀ c ∧ c.reg rFREE = Fe ∧ c.reg gHAM = hb)
      (PRep g E c₀ Fe hb (fun _ => 0) [] [] []) 16 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨hR, hF, hH⟩ => ⟨AddrOK.of_memFree rfl, ?_⟩
  have hvn := hR.vn
  have hln := hR.ln
  refine ⟨hR.glob.run (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [run_reg_of_not_mem (by decide) (by decide), hvn]
  · rw [run_reg_of_not_mem (by decide) (by decide), hR.vs]
  · rw [run_reg_of_not_mem (by decide) (by decide), hR.lu]
  · rw [run_reg_of_not_mem (by decide) (by decide), hR.lv]
  · rw [run_reg_of_not_mem (by decide) (by decide), hln]
  · rw [run_reg_of_not_mem (by decide) (by decide), hH]
  all_goals try (simp +decide [pInit, run_alloc, run_mov, hvn, hln, hF]; try omega)
  · exact hR.out
  · have h1 := hR.hamb
    have h2 := hR.le
    have h3 := hR.ham
    have h4 := hR.zero
    rw [hF, hH] at h1
    rw [hF] at h2 h4
    rw [hH] at h3
    exact ⟨hR.mvs, hR.mlu, hR.mlv, hR.same, h3, h4.tab le_rfl _, arr_nil _ _, arr_nil _ _,
      arr_nil _ _, h4.mono (by omega), by simp, by simp, by simp, h1, h2⟩

/-! ### The positions -/

/-- The positions after `j` rounds: `ham.idxOf u` for the first `j` entries `u` of `ham`. -/
def posF (ham : List ℕ) (j u : ℕ) : ℕ := if u ∈ ham.take j then ham.idxOf u else 0

theorem posF_zero (ham : List ℕ) : posF ham 0 = fun _ => 0 := by
  funext u; simp [posF]

theorem posF_succ {N : ℕ} {ham : List ℕ} (hH : HamFacts N ham) {j : ℕ} (hj : j < ham.length) :
    posF ham (j + 1) = Function.update (posF ham j) ham[j] j := by
  funext u
  have hmem : u ∈ ham.take (j + 1) ↔ u ∈ ham.take j ∨ u = ham[j] := by
    rw [take_succ_eq ham hj, List.mem_append, List.mem_singleton]
  simp only [posF, Function.update_apply, hmem]
  by_cases hu : u = ham[j]
  · simp only [hu, or_true, ↓reduceIte, hH.idx j hj]
  · simp only [hu, or_false, ↓reduceIte]

theorem posF_full {N : ℕ} {ham : List ℕ} (hH : HamFacts N ham) {u : ℕ} (hu : u < N) :
    posF ham N u = ham.idxOf u := by
  rw [← hH.len]
  simp [posF, hH.mem u hu]

theorem posBody_spec {g : Graph} {E : List Edge} {c₀ : Config}
    (hH : HamFacts (blockVerts E).length (hamOf E)) (Fe hb : ℕ)
    (hS : Fe + 2 * (blockVerts E).length + 2 * E.length ≤ S) (j : ℕ)
    (hj : j < (blockVerts E).length) :
    HTB S posBody
      (fun c => PRep g E c₀ Fe hb (posF (hamOf E) j) [] [] [] c ∧ c.reg rI = j ∧
        c.reg gVN = (blockVerts E).length)
      (fun c => PRep g E c₀ Fe hb (posF (hamOf E) (j + 1)) [] [] [] c ∧ c.reg rI = j ∧
        c.reg gVN = (blockVerts E).length) 4 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨hR, hi, hn⟩ => ?_
  have hjh : j < (hamOf E).length := by rw [hH.len]; exact hj
  have hx : c.mem (c.reg gHAM + j) = (hamOf E)[j] := by
    rw [hR.hamr, hR.mem.ham.get hjh]
  have hA : AddrOK S posBody c := by
    have hx' : c.mem (hb + j) = (hamOf E)[j] := by rw [← hx, hR.hamr]
    have := hR.mem.hamb
    have := hH.lt j hjh
    addr_ok [posBody, hR.hamr, hR.posr, hi, hx']
  refine ⟨hA, ?_⟩
  have hmem : (RAM.run posBody c).mem = upd c.mem (Fe + (hamOf E)[j]) j := by
    simp +decide only [posBody, run_seq', run_ld, run_st (show rI ≠ rT by decide), setReg_mem,
      setMem_mem_upd, setReg_reg, ↓reduceIte, hx, hR.posr, hi]
  refine ⟨hR.run_of (by decide) (by decide) (by decide) ?_,
    (run_reg_of_not_mem (by decide) (by decide) c).trans hi,
    (run_reg_of_not_mem (by decide) (by decide) c).trans hn⟩
  rw [hmem, posF_succ hH hjh]
  exact hR.mem.upd_pos (hH.lt j hjh) rfl j

/-- **The positions**: `POS[u] = ham.idxOf u` for `u < N`. -/
theorem posLoop_spec {g : Graph} {E : List Edge} {c₀ : Config}
    (hH : HamFacts (blockVerts E).length (hamOf E)) (Fe hb : ℕ)
    (hS : Fe + 2 * (blockVerts E).length + 2 * E.length ≤ S) :
    HTB S posLoop (PRep g E c₀ Fe hb (fun _ => 0) [] [] [])
      (PRep g E c₀ Fe hb (posF (hamOf E) (blockVerts E).length) [] [] [])
      ((blockVerts E).length * 8 + 3) := by
  have hl := HTB.forUpC (i := rI) (n := gVN) (N := (blockVerts E).length) (body := posBody)
    (fun j => PRep g E c₀ Fe hb (posF (hamOf E) j) [] [] []) 4 (by decide) (by decide) (by decide)
    (fun j => (PRep.indep _ _ _ _ _ _ _ _ _).mono (by decide))
    (fun j hj => posBody_spec hH Fe hb hS j hj)
  exact hl.mono (fun c h => ⟨by rw [posF_zero]; exact h, h.vn⟩) (fun c ⟨h, _⟩ => h) le_rfl

/-! ### The polygon -/

theorem pgBody_spec {g : Graph} {E : List Edge} {c₀ : Config}
    (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.2 < numV g) (hH : HamFacts (blockVerts E).length (hamOf E))
    (Fe hb : ℕ) (hS : Fe + 2 * (blockVerts E).length + 2 * E.length ≤ S) (j : ℕ)
    (hj : j < E.length) :
    HTB S pgBody
      (fun c => PRep g E c₀ Fe hb (posF (hamOf E) (blockVerts E).length)
        (((pgOf E).take j).map Prod.fst) (((pgOf E).take j).map Prod.snd) [] c ∧ c.reg rI = j ∧
        c.reg gLN = E.length)
      (fun c => PRep g E c₀ Fe hb (posF (hamOf E) (blockVerts E).length)
        (((pgOf E).take (j + 1)).map Prod.fst) (((pgOf E).take (j + 1)).map Prod.snd) [] c ∧
        c.reg rI = j ∧ c.reg gLN = E.length) 22 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨hR, hi, hn⟩ => ?_
  have hjL : j < (locG E).length := by rw [length_locG]; exact hj
  have hLb := localEdges_bounds (fun e he => (hE e he).1) _ (List.getElem_mem hjL)
  have hu : c.mem (c.reg gLU + c.reg rI) = (locG E)[j].1 := by
    rw [hR.lu, hi, hR.mem.mlu.get (by simpa using hjL)]; simp
  have hv : c.mem (c.reg gLV + c.reg rI) = (locG E)[j].2 := by
    rw [hR.lv, hi, hR.mem.mlv.get (by simpa using hjL)]; simp
  have hA : AddrOK S pgBody c := by
    have hu' : c.mem (c₀.reg rFREE + 4 * E.length + j) = (locG E)[j].1 := by rw [← hu, hR.lu, hi]
    have hv' : c.mem (c₀.reg rFREE + 5 * E.length + j) = (locG E)[j].2 := by rw [← hv, hR.lv, hi]
    have := hR.mem.le
    addr_ok [pgBody, pgRead, order, hR.lu, hR.lv, hR.posr, hR.pur, hR.pvr, hi, hu', hv']
  refine ⟨hA, ?_⟩
  have hpu : c.mem (c.reg gPOS + (locG E)[j].1) = (hamOf E).idxOf (locG E)[j].1 := by
    rw [hR.posr, hR.mem.mpos.get (by omega), posF_full hH (by omega)]
  have hpv : c.mem (c.reg gPOS + (locG E)[j].2) = (hamOf E).idxOf (locG E)[j].2 := by
    rw [hR.posr, hR.mem.mpos.get (by omega), posF_full hH (by omega)]
  have hr4 : (RAM.run pgRead c).reg rU = (hamOf E).idxOf (locG E)[j].1 ∧
      (RAM.run pgRead c).reg rV = (hamOf E).idxOf (locG E)[j].2 := by
    constructor <;> simp +decide [pgRead, hu, hv, hpu, hpv]
  have hag4 : Agree W c (RAM.run pgRead c) := agree_run (by decide) rfl rfl (by decide) c
  obtain ⟨h7u, h7v, hag7⟩ := order_run (RAM.run pgRead c)
  rw [hr4.1, hr4.2] at h7u h7v
  have hag := hag4.trans (hag7.mono (by decide))
  have hjP : j < (pgOf E).length := by rw [length_pgOf]; exact hj
  have hri : (RAM.run order (RAM.run pgRead c)).reg rI = j := by
    rw [run_reg_of_not_mem (by decide) (by decide), run_reg_of_not_mem (by decide) (by decide), hi]
  have hmem : (RAM.run pgBody c).mem = upd (upd c.mem (Fe + (blockVerts E).length + j)
      ((pgOf E)[j]).1) (Fe + (blockVerts E).length + E.length + j) ((pgOf E)[j]).2 := by
    rw [getElem_localEdges]
    simp +decide only [pgBody, run_seq', run_st (show rU ≠ rT by decide),
      run_st (show rV ≠ rT by decide), setReg_mem, setMem_mem_upd, setReg_reg, setMem_reg,
      ↓reduceIte, h7u, h7v, hag.mem, hag.reg gPU (by decide), hag.reg gPV (by decide),
      hri, hR.pur, hR.pvr]
  refine ⟨hR.run_of (by decide) (by decide) (by decide) ?_,
    (run_reg_of_not_mem (by decide) (by decide) c).trans hi,
    (run_reg_of_not_mem (by decide) (by decide) c).trans hn⟩
  rw [hmem, map_take_succ _ _ hjP, map_take_succ _ _ hjP]
  exact (hR.mem.upd_pu (by simp; omega) (by simp; omega) _).upd_pv (by simp; omega)
    (by simp; omega) _

/-- **The polygon** `pgOf E` at `gPU`, `gPV`. -/
theorem pgLoop_spec {g : Graph} {E : List Edge} {c₀ : Config}
    (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.2 < numV g) (hH : HamFacts (blockVerts E).length (hamOf E))
    (Fe hb : ℕ) (hS : Fe + 2 * (blockVerts E).length + 2 * E.length ≤ S) :
    HTB S pgLoop (PRep g E c₀ Fe hb (posF (hamOf E) (blockVerts E).length) [] [] [])
      (PRep g E c₀ Fe hb (posF (hamOf E) (blockVerts E).length) ((pgOf E).map Prod.fst)
        ((pgOf E).map Prod.snd) []) (E.length * 26 + 3) := by
  have hl := HTB.forUpC (i := rI) (n := gLN) (N := E.length) (body := pgBody)
    (fun j => PRep g E c₀ Fe hb (posF (hamOf E) (blockVerts E).length)
      (((pgOf E).take j).map Prod.fst) (((pgOf E).take j).map Prod.snd) [])
    22 (by decide) (by decide) (by decide)
    (fun j => (PRep.indep _ _ _ _ _ _ _ _ _).mono (by decide))
    (fun j hj => pgBody_spec hE hH Fe hb hS j hj)
  refine hl.mono (fun c h => ⟨by simpa using h, h.ln⟩) (fun c ⟨h, _⟩ => ?_) le_rfl
  rw [← length_pgOf E, List.take_length] at h
  exact h

/-! ### The output map -/

theorem getElem_omapOf (g : Graph) (E : List Edge) {j : ℕ} (hj : j < (omapOf g E).length) :
    (omapOf g E)[j] = (labels g).getD ((blockVerts E).getD ((hamOf E).getD j 0) 0) 0 := by
  simp [omapOf, labelOf]

theorem length_omapOf (g : Graph) (E : List Edge) : (omapOf g E).length = (blockVerts E).length := by
  simp [omapOf]

theorem omBody_spec {g : Graph} {E : List Edge} {c₀ : Config} (hB : BlockIn g E c₀)
    (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.2 < numV g) (hH : HamFacts (blockVerts E).length (hamOf E))
    (Fe hb : ℕ) (hS : Fe + 2 * (blockVerts E).length + 2 * E.length ≤ S) (j : ℕ)
    (hj : j < (blockVerts E).length) :
    HTB S omBody
      (fun c => PRep g E c₀ Fe hb (posF (hamOf E) (blockVerts E).length) ((pgOf E).map Prod.fst)
        ((pgOf E).map Prod.snd) ((omapOf g E).take j) c ∧ c.reg rI = j ∧
        c.reg gVN = (blockVerts E).length)
      (fun c => PRep g E c₀ Fe hb (posF (hamOf E) (blockVerts E).length) ((pgOf E).map Prod.fst)
        ((pgOf E).map Prod.snd) ((omapOf g E).take (j + 1)) c ∧ c.reg rI = j ∧
        c.reg gVN = (blockVerts E).length) 8 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨hR, hi, hn⟩ => ?_
  have hjh : j < (hamOf E).length := by rw [hH.len]; exact hj
  have hjo : j < (omapOf g E).length := by rw [length_omapOf]; exact hj
  have h1 : c.mem (c.reg gHAM + j) = (hamOf E).getD j 0 := by
    rw [hR.hamr, hR.mem.ham.getD hjh]
  have hx1 : (hamOf E).getD j 0 < (blockVerts E).length := by
    rw [getD_eq_getElem' hjh]; exact hH.lt j hjh
  have h2 : c.mem (c.reg gVS + (hamOf E).getD j 0) =
      (blockVerts E).getD ((hamOf E).getD j 0) 0 := by
    rw [hR.vs, hR.mem.mvs.getD hx1]
  have hx2 : (blockVerts E).getD ((hamOf E).getD j 0) 0 < numV g := by
    rw [getD_eq_getElem' hx1]; exact lt_of_mem_blockVerts hE (List.getElem_mem _)
  have h3 : c.mem (c.reg gLB + (blockVerts E).getD ((hamOf E).getD j 0) 0) =
      (labels g).getD ((blockVerts E).getD ((hamOf E).getD j 0) 0) 0 := by
    have hb := hB.below
    rw [hR.glob.lb, hR.mem.same _ (show _ < c₀.reg rFREE by omega), hB.lb.getD hx2]
  have hA : AddrOK S omBody c := by
    have h1' : c.mem (hb + j) = (hamOf E).getD j 0 := by rw [← h1, hR.hamr]
    have h2' : c.mem (c₀.reg rFREE + 2 * E.length + (hamOf E).getD j 0) =
        (blockVerts E).getD ((hamOf E).getD j 0) 0 := by rw [← h2, hR.vs]
    have := hR.mem.hamb
    have := hR.mem.le
    have := hB.below
    have := length_blockVerts_le E
    addr_ok [omBody, hR.hamr, hR.vs, hR.glob.lb, hR.omr, hi, h1', h2']
  refine ⟨hA, ?_⟩
  have hmem : (RAM.run omBody c).mem = upd c.mem (Fe + (blockVerts E).length + 2 * E.length + j)
      ((omapOf g E)[j]) := by
    rw [getElem_omapOf]
    simp +decide only [omBody, run_seq', run_ld, run_st (show rA ≠ rT by decide), setReg_mem,
      setMem_mem_upd, setReg_reg, ↓reduceIte, h1, h2, h3, hR.omr, hi]
  refine ⟨hR.run_of (by decide) (by decide) (by decide) ?_,
    (run_reg_of_not_mem (by decide) (by decide) c).trans hi,
    (run_reg_of_not_mem (by decide) (by decide) c).trans hn⟩
  rw [hmem, take_succ_eq _ hjo]
  exact hR.mem.upd_om (by simp; omega) (by simp; omega) _

/-- **The output map** `omapOf g E` at `gOMAP`. -/
theorem omLoop_spec {g : Graph} {E : List Edge} {c₀ : Config} (hB : BlockIn g E c₀)
    (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.2 < numV g) (hH : HamFacts (blockVerts E).length (hamOf E))
    (Fe hb : ℕ) (hS : Fe + 2 * (blockVerts E).length + 2 * E.length ≤ S) :
    HTB S omLoop (PRep g E c₀ Fe hb (posF (hamOf E) (blockVerts E).length) ((pgOf E).map Prod.fst)
        ((pgOf E).map Prod.snd) [])
      (PRep g E c₀ Fe hb (posF (hamOf E) (blockVerts E).length) ((pgOf E).map Prod.fst)
        ((pgOf E).map Prod.snd) (omapOf g E)) ((blockVerts E).length * 12 + 3) := by
  have hl := HTB.forUpC (i := rI) (n := gVN) (N := (blockVerts E).length) (body := omBody)
    (fun j => PRep g E c₀ Fe hb (posF (hamOf E) (blockVerts E).length) ((pgOf E).map Prod.fst)
      ((pgOf E).map Prod.snd) ((omapOf g E).take j))
    8 (by decide) (by decide) (by decide)
    (fun j => (PRep.indep _ _ _ _ _ _ _ _ _).mono (by decide))
    (fun j hj => omBody_spec hB hE hH Fe hb hS j hj)
  refine hl.mono (fun c h => ⟨by simpa using h, h.vn⟩) (fun c ⟨h, _⟩ => ?_) le_rfl
  have ht := List.take_length (l := omapOf g E)
  rw [length_omapOf] at ht
  rw [ht] at h
  exact h

/-! ### The polygon solver and the whole branch -/

/-- **The polygon solver** (from its specification `PolySpecB`) writes the output of the
block; `B`: an upper bound on its final `rFREE`, at most the space bound `S`. -/
theorem poly_step {k : ℕ} (hk : 3 ≤ k) {polyProg : Stmt} {CP : ℕ} (hpoly : PolySpecB k polyProg CP)
    {g : Graph} {E : List Edge} {c₀ : Config} (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.2 < numV g)
    (hnd : E.Nodup) (h2 : ¬ (blockVerts E).length ≤ 2)
    (h46 : ¬ ((blockVerts E).length = 4 ∧ E.length = 6))
    (hP : IsPolygon (pgOf E) (blockVerts E).length) (Fe hb B : ℕ)
    (hBd : Fe + 2 * (blockVerts E).length + 2 * E.length +
      CP * ((blockVerts E).length + E.length + 1) ≤ B) (hS : B ≤ S) :
    HTB S polyProg (PRep g E c₀ Fe hb (posF (hamOf E) (blockVerts E).length)
        ((pgOf E).map Prod.fst) ((pgOf E).map Prod.snd) (omapOf g E))
      (BPost k g E c₀ B) (CP * ((blockVerts E).length + E.length + 1)) := by
  refine HTB.of_forall fun cp hcp => ?_
  have hE' : ∀ e ∈ E, e.1 < e.2 := fun e he => (hE e he).1
  have hLb := localEdges_bounds hE'
  have hH : HamFacts _ (hamOf E) := hamFacts (length_earHam _ _) hLb hP
  have hpgl := length_pgOf E
  have hin : PolyIn (pgOf E) (blockVerts E).length (omapOf g E) cp := by
    refine ⟨hcp.glob.zero, hcp.glob.one, hcp.pn, by rw [hcp.pe, hpgl], ?_, ?_, ?_,
      length_omapOf g E, ?_, ?_⟩
    · rw [hcp.pur]; exact hcp.mem.mpu
    · rw [hcp.pvr]; exact hcp.mem.mpv
    · rw [hcp.omr]; exact hcp.mem.mom
    · rw [hcp.free]; exact hcp.mem.zero
    · rw [hcp.pur, hcp.pvr, hcp.omr, hcp.free, hpgl]; omega
  have hF := hcp.free
  have h := (hpoly S _ _ _ cp hP (pg_lt hH hLb) (pg_nodup hH hLb (localEdges_nodup' hE' hnd))
    (by rw [hF, hpgl]; omega)).pre (P' := fun c => c = cp) (fun c hc => ⟨hc ▸ hin, hc⟩)
  refine (h.post fun c ⟨hout, hsame, hzero, hle, hfre⟩ => ?_).weaken (le_of_eq (by rw [hpgl]))
  have hle2 := hcp.mem.le
  rw [hpgl, hF] at hfre
  refine ⟨?_, hcp.mem.same.trans
    (hsame.mono fun a (ha : a < c₀.reg rFREE) => show a < cp.reg rFREE by omega), hzero, by omega,
    by omega⟩
  rw [hout, hcp.out, out_poly_omap hk h2 h46 hP]

/-- **The polygon branch**, in the space `F + polyMem CE CP N m`. -/
theorem polyBranch_spec {k : ℕ} (hk : 3 ≤ k) {earProg polyProg : Stmt} {CE CP : ℕ}
    (hear : EarSpec earProg CE)
    (hearW : ∀ r ∈ wregs earProg, r = rT ∨ r = rFREE ∨ r = gHAM ∨ rS ≤ r)
    (hearO : writes earProg = false) (hpoly : PolySpecB k polyProg CP)
    {g : Graph} {E : List Edge} {c₀ : Config} (hB : BlockIn g E c₀)
    (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.2 < numV g) (hnd : E.Nodup) (h2 : ¬ (blockVerts E).length ≤ 2)
    (h46 : ¬ ((blockVerts E).length = 4 ∧ E.length = 6))
    (hP : IsPolygon (pgOf E) (blockVerts E).length)
    (hS : c₀.reg rFREE + polyMem CE CP (blockVerts E).length E.length ≤ S) :
    HTB S (polyBranch earProg polyProg) (DRep g E c₀)
      (BPost k g E c₀ (c₀.reg rFREE + polyMem CE CP (blockVerts E).length E.length))
      (CE * ((blockVerts E).length + E.length + 1) + (16 + ((blockVerts E).length * 8 + 3 +
        (E.length * 26 + 3 + ((blockVerts E).length * 12 + 3 +
          CP * ((blockVerts E).length + E.length + 1)))))) := by
  have hH : HamFacts _ (hamOf E) :=
    hamFacts (length_earHam _ _) (localEdges_bounds fun e he => (hE e he).1) hP
  have hrest : HTB S (.seq pInit (.seq posLoop (.seq pgLoop (.seq omLoop polyProg))))
      (fun c => ERep g E c₀ c ∧ c.reg rFREE ≤
        c₀.reg rFREE + 6 * E.length + CE * ((blockVerts E).length + E.length + 1))
      (BPost k g E c₀ (c₀.reg rFREE + polyMem CE CP (blockVerts E).length E.length))
      (16 + ((blockVerts E).length * 8 + 3 + (E.length * 26 + 3 +
        ((blockVerts E).length * 12 + 3 + CP * ((blockVerts E).length + E.length + 1))))) := by
    refine HTB.of_forall fun c1 ⟨hc1, hfe⟩ => ?_
    have hS1 : c1.reg rFREE + 2 * (blockVerts E).length + 2 * E.length ≤ S := by
      simp only [polyMem] at hS; omega
    exact ((pInit_spec (c₀ := c₀) (c1.reg rFREE) (c1.reg gHAM)).seq ((posLoop_spec hH _ _ hS1).seq
      ((pgLoop_spec hE hH _ _ hS1).seq ((omLoop_spec hB hE hH _ _ hS1).seq
        (poly_step hk hpoly hE hnd h2 h46 hP _ _ _ (by simp only [polyMem]; omega) hS))))).pre
      fun c hc => by subst hc; exact ⟨hc1, rfl, rfl⟩
  exact (ear_step hear hearW hearO hB hE hnd (by omega)
    ⟨hamOf E, hH.outerplanarHam (localEdges_bounds fun e he => (hE e he).1) hP, hH.mem⟩
    (by simp only [polyMem] at hS; omega)).seq hrest

end STACS2027.RAM.Block
