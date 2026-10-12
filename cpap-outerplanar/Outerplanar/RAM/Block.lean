module

public import Outerplanar.RAM.BlockPoly
import Mathlib.Tactic

/-!
# The block solver: the main triple

`blockProg_spec`: given the specifications `EarSpec` of the ear elimination and `PolySpecB` of
the polygon solver (with the footprint of the ear elimination), the block solver
`blockProg k earProg polyProg` (`Outerplanar/RAM/BlockProg.lean`) satisfies `BlockSpec` with the
constant `CB k CE CP = 3 CE + 3 CP + 6 |k4Base k| + 200`: on a block `E` it appends the labels of
`(solveBlock k E).flatten` within `CB * (|E| + 1)` steps, allocating fresh memory only and
restoring the memory below the initial `rFREE`, in linear space: below every bound
`S ≥ F + CB * (|E| + 1)`, with the final `rFREE` at most `F + CB * (|E| + 1)` (all triples are
`HTB S` triples; the memory of the polygon branch is `polyMem CE CP N |E| ≤ CB (|E| + 1)`).

* steps 1–5 (`BlockPre.lean`): the copies of the edges, the vertices, the local graph, `LOC`
  reset;
* the dispatch (`dispatch_spec`): `N ≤ 2` — nothing (`out_small`); `N = 4 ∧ |E| = 6` — the
  `K₄` patterns (`k4_spec`, `wlabs_run`); otherwise the polygon branch (`BlockPoly.lean`),
  whose polygon hypothesis is `BlockGood E`.

The time: steps 1–5 cost `O(|E| + N)`, the polygon branch `CE (N + |E| + 1) + CP (N + |E| + 1)`
plus `O(N + |E|)`, with `N ≤ 2 |E|` (`length_blockVerts_le`); the space likewise.
-/

@[expose] public section

namespace STACS2027.RAM.Block

open STACS2027.Algo

variable {S : ℕ}

/-! ### The `K₄` branch -/

theorem wlab_run (i : ℕ) (c : Config) :
    (RAM.run (wlab i) c).out = c.out ++ [c.mem (c.reg gLB + c.mem (c.reg gVS + i))] ∧
      (RAM.run (wlab i) c).mem = c.mem ∧
      ∀ r, r ≠ rI → r ≠ rA → (RAM.run (wlab i) c).reg r = c.reg r := by
  refine ⟨by simp +decide [wlab], by simp [wlab], fun r h1 h2 => by simp [wlab, h1, h2]⟩

/-- Writing the labels of `vs[i]` for the indices of `l`. -/
theorem wlabs_run (l : List ℕ) (c : Config) :
    (RAM.run (wlabs l) c).out =
        c.out ++ l.map (fun i => c.mem (c.reg gLB + c.mem (c.reg gVS + i))) ∧
      (RAM.run (wlabs l) c).mem = c.mem ∧
      ∀ r, r ≠ rI → r ≠ rA → (RAM.run (wlabs l) c).reg r = c.reg r := by
  induction l generalizing c with
  | nil => exact ⟨by simp [wlabs], rfl, fun _ _ _ => rfl⟩
  | cons i l ih =>
    obtain ⟨h1, h2, h3⟩ := wlab_run i c
    obtain ⟨h4, h5, h6⟩ := ih (RAM.run (wlab i) c)
    have hw : wlabs (i :: l) = .seq (wlab i) (wlabs l) := rfl
    rw [hw, run_seq']
    refine ⟨?_, h5.trans h2, fun r hr1 hr2 => (h6 r hr1 hr2).trans (h3 r hr1 hr2)⟩
    rw [h4, h1, h2, h3 _ (by decide) (by decide), h3 _ (by decide) (by decide)]
    simp

/-- The addresses of the label writes: `VS[i]` and `LB[VS[i]]`. -/
theorem wlabs_addrOK (l : List ℕ) (c : Config)
    (h : ∀ i ∈ l, c.reg gVS + i < S ∧ c.reg gLB + c.mem (c.reg gVS + i) < S) :
    AddrOK S (wlabs l) c := by
  induction l generalizing c with
  | nil => exact AddrOK.of_memFree rfl
  | cons i l ih =>
    have hw : wlabs (i :: l) = .seq (wlab i) (wlabs l) := rfl
    obtain ⟨-, h2, h3⟩ := wlab_run i c
    rw [hw, addrOK_seq]
    refine ⟨?_, ih _ fun i' hi' => ?_⟩
    · have := h i List.mem_cons_self
      addr_ok [wlab]
    · rw [h2, h3 _ (by decide) (by decide), h3 _ (by decide) (by decide)]
      exact h i' (List.mem_cons_of_mem _ hi')

theorem length_k4Base_flatten (k : ℕ) : (k4Base k).flatten.length ≤ 12 := by
  unfold k4Base
  split_ifs <;> decide

/-- **The `K₄` branch** (`B`: a bound on the final `rFREE`). -/
theorem k4_spec {k : ℕ} {g : Graph} {E : List Edge} {c₀ : Config} (hB : BlockIn g E c₀)
    (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.2 < numV g) (h4 : (blockVerts E).length = 4)
    (h6 : E.length = 6) {B : ℕ} (hBd : c₀.reg rFREE + 6 * E.length ≤ B) (hSB : B ≤ S) :
    HTB S (k4Prog k) (DRep g E c₀) (BPost k g E c₀ B) (6 * (k4Base k).flatten.length + 1) := by
  refine HTB.run_le (loopFree_wlabs _) (by rw [k4Prog, size_wlabs]) fun c hR => ?_
  obtain ⟨hout, hmem, hreg⟩ := wlabs_run (k4Base k).flatten c
  have hS := hR.mem.sameOn_zero hB.loc
  have hb := hB.below
  have hfree : (RAM.run (k4Prog k) c).reg rFREE = c₀.reg rFREE + 6 * E.length :=
    (hreg rFREE (by decide) (by decide)).trans hR.lay.free
  refine ⟨wlabs_addrOK _ c fun i hi => ?_, ?_⟩
  · have hiN : i < (blockVerts E).length := by have := k4Base_lt k i hi; omega
    have hv := lt_of_mem_blockVerts hE (SolveAux.getD_mem hiN)
    rw [hR.lay.vs, hR.mem.mvs.getD hiN, hR.glob.lb]
    omega
  refine ⟨?_, by rw [k4Prog, hmem]; exact hS, ?_, by rw [hfree]; omega, by rw [hfree]; omega⟩
  · rw [k4Prog, hout, hR.out, out_k4 h4 h6]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    have hiN : i < (blockVerts E).length := by have := k4Base_lt k i hi; omega
    have hv := lt_of_mem_blockVerts hE (SolveAux.getD_mem hiN)
    rw [hR.lay.vs, hR.mem.mvs.getD hiN, hR.glob.lb, hS _ (show _ < c₀.reg rFREE by omega),
      hB.lb.getD hv]
    rfl
  · rw [hfree, k4Prog, hmem]; exact hR.mem.zero

/-! ### The dispatch -/

/-- The bound of the polygon branch. -/
def polyBound (CE CP N m : ℕ) : ℕ :=
  CE * (N + m + 1) + (16 + (N * 8 + 3 + (m * 26 + 3 + (N * 12 + 3 + CP * (N + m + 1)))))

/-- **The dispatch** on the number of vertices and edges, in the space
`F + polyMem CE CP N |E|`. -/
theorem dispatch_spec {k : ℕ} (hk : 3 ≤ k) {earProg polyProg : Stmt} {CE CP : ℕ}
    (hear : EarSpec earProg CE)
    (hearW : ∀ r ∈ wregs earProg, r = rT ∨ r = rFREE ∨ r = gHAM ∨ rS ≤ r)
    (hearO : writes earProg = false) (hpoly : PolySpecB k polyProg CP)
    {g : Graph} {E : List Edge} {c₀ : Config} (hB : BlockIn g E c₀)
    (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.2 < numV g) (hnd : E.Nodup) (hgood : BlockGood E)
    (hS : c₀.reg rFREE + polyMem CE CP (blockVerts E).length E.length ≤ S) :
    HTB S (dispatch k earProg polyProg) (DRep g E c₀)
      (BPost k g E c₀ (c₀.reg rFREE + polyMem CE CP (blockVerts E).length E.length))
      (2 + (10 + 6 * (k4Base k).flatten.length +
        polyBound CE CP (blockVerts E).length E.length + 1)) := by
  have h6 : c₀.reg rFREE + 6 * E.length ≤ c₀.reg rFREE + polyMem CE CP (blockVerts E).length E.length := by
    simp only [polyMem]; omega
  have hs : HTB S smallTest (DRep g E c₀) (fun c => DRep g E c₀ c ∧ c.reg rX = (blockVerts E).length - 2) 2 :=
    HTB.run_le (by decide) (by decide) fun c hR => ⟨AddrOK.of_memFree rfl,
      ((Rep.indep _ _ _ _ _ _ _ _ _).mono (by decide)).run (by decide) rfl rfl hR,
        by simp +decide [smallTest, hR.vn]⟩
  have hsmall : HTB S .skip (fun c => (DRep g E c₀ c ∧ c.reg rX = (blockVerts E).length - 2) ∧
      c.reg rX = 0) (BPost k g E c₀ (c₀.reg rFREE + polyMem CE CP (blockVerts E).length E.length))
      (10 + 6 * (k4Base k).flatten.length + polyBound CE CP (blockVerts E).length E.length) := by
    refine (HTB.skip.post fun c ⟨⟨hR, hx⟩, h0⟩ => ?_).weaken (by omega)
    have hS := hR.mem.sameOn_zero hB.loc
    have hF := hR.lay.free
    exact ⟨by rw [hR.out, out_small (by omega), List.append_nil], hS,
      by rw [hF]; exact hR.mem.zero, by omega, by omega⟩
  have ht : HTB S k4Test (fun c => (DRep g E c₀ c ∧ c.reg rX = (blockVerts E).length - 2) ∧
      c.reg rX ≠ 0) (fun c => DRep g E c₀ c ∧ ¬ (blockVerts E).length ≤ 2 ∧
        (c.reg rX = 0 ↔ (blockVerts E).length = 4 ∧ E.length = 6)) 9 :=
    HTB.run_le (by decide) (by decide) fun c ⟨⟨hR, hx⟩, h0⟩ => by
      refine ⟨AddrOK.of_memFree rfl,
        ((Rep.indep _ _ _ _ _ _ _ _ _).mono (by decide)).run (by decide) rfl rfl hR, by omega, ?_⟩
      have hbl : c.reg gBL = E.length := hR.glob.bl.trans hB.bl
      simp +decide [k4Test, hR.vn, hbl]
      omega
  have hk4 : HTB S (k4Prog k) (fun c => (DRep g E c₀ c ∧ ¬ (blockVerts E).length ≤ 2 ∧
      (c.reg rX = 0 ↔ (blockVerts E).length = 4 ∧ E.length = 6)) ∧ c.reg rX = 0)
      (BPost k g E c₀ (c₀.reg rFREE + polyMem CE CP (blockVerts E).length E.length))
      (6 * (k4Base k).flatten.length + polyBound CE CP (blockVerts E).length E.length) := by
    refine HTB.of_forall fun c1 ⟨⟨_, _, hiff⟩, h0⟩ => ?_
    obtain ⟨h4, h6'⟩ := hiff.mp h0
    exact ((k4_spec hB hE h4 h6' h6 hS).weaken (by simp only [polyBound]; omega)).pre
      fun c hc => by subst hc; assumption
  have hpb : HTB S (polyBranch earProg polyProg) (fun c => (DRep g E c₀ c ∧
      ¬ (blockVerts E).length ≤ 2 ∧ (c.reg rX = 0 ↔ (blockVerts E).length = 4 ∧ E.length = 6)) ∧
      c.reg rX ≠ 0) (BPost k g E c₀ (c₀.reg rFREE + polyMem CE CP (blockVerts E).length E.length))
      (6 * (k4Base k).flatten.length + polyBound CE CP (blockVerts E).length E.length) := by
    refine HTB.of_forall fun c1 ⟨⟨_, h2, hiff⟩, h0⟩ => ?_
    have h46 : ¬ ((blockVerts E).length = 4 ∧ E.length = 6) := fun h => h0 (hiff.mpr h)
    exact ((polyBranch_spec hk hear hearW hearO hpoly hB hE hnd h2 h46
      (hgood (by omega) h46) hS).weaken (by simp only [polyBound]; omega)).pre
      fun c hc => by subst hc; assumption
  exact (hs.seq (HTB.ifz hsmall ((ht.seq (HTB.ifz hk4 hpb)).weaken (by omega)))).weaken (by omega)

/-! ### The main triple -/

/-- **The constant of the block solver.** -/
def CB (k CE CP : ℕ) : ℕ := 3 * CE + 3 * CP + 6 * (k4Base k).flatten.length + 200

/-- The memory of the polygon branch is within the block solver's bound. -/
theorem polyMem_le (k CE CP : ℕ) (E : List Edge) :
    polyMem CE CP (blockVerts E).length E.length ≤ CB k CE CP * (E.length + 1) := by
  have hN := length_blockVerts_le E
  have h1 : CE * ((blockVerts E).length + E.length + 1) ≤ 3 * (CE * (E.length + 1)) := by
    calc CE * ((blockVerts E).length + E.length + 1) ≤ CE * (3 * (E.length + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 3 * (CE * (E.length + 1)) := by ring
  have h2 : CP * ((blockVerts E).length + E.length + 1) ≤ 3 * (CP * (E.length + 1)) := by
    calc CP * ((blockVerts E).length + E.length + 1) ≤ CP * (3 * (E.length + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 3 * (CP * (E.length + 1)) := by ring
  have h3 : CB k CE CP * (E.length + 1) = 3 * (CE * (E.length + 1)) + 3 * (CP * (E.length + 1)) +
      6 * (k4Base k).flatten.length * (E.length + 1) + 200 * (E.length + 1) := by
    simp only [CB]; ring
  simp only [polyMem]
  omega

/-- **The block solver** (`BlockSpec`, in linear space), given the ear elimination (`EarSpec`,
with its footprint: registers `rT`, `rFREE`, `gHAM`, scratch; no output) and the polygon solver
(`PolySpecB`). The footprint of the polygon solver is not needed here (the polygon solver runs
last); it is used for `blockProg_wregs`. -/
theorem blockProg_spec {k : ℕ} (hk : 3 ≤ k) {earProg polyProg : Stmt} {CE CP : ℕ}
    (hear : EarSpec earProg CE)
    (hearW : ∀ r ∈ wregs earProg, r = rT ∨ r = rFREE ∨ r = gHAM ∨ rS ≤ r)
    (hearO : writes earProg = false)
    (hpoly : PolySpecB k polyProg CP)
    (_hpolyW : ∀ r ∈ wregs polyProg, r = rT ∨ r = rFREE ∨ gP0 ≤ r) :
    BlockSpec k (blockProg k earProg polyProg) (CB k CE CP) := by
  intro S g E c₀ hE hnd hgood hSb c ⟨hB, hc⟩
  subst hc
  have hpm := polyMem_le k CE CP E
  have hS : c.reg rFREE + polyMem CE CP (blockVerts E).length E.length ≤ S := by omega
  have hS6 : c.reg rFREE + 6 * E.length ≤ S := by simp only [polyMem] at hS; omega
  have h := (initB_spec hB).seq ((copy_spec hB hS6).seq ((collect_spec hB hE hS6).seq
    ((localE_spec hB hE hS6).seq ((reset_spec hB hE hS6).seq
      (dispatch_spec hk hear hearW hearO hpoly hB hE hnd hgood hS)))))
  refine ((h.post fun c' ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, by omega⟩).weaken ?_) c ⟨hB, rfl⟩
  have hN := length_blockVerts_le E
  have h1 : CE * ((blockVerts E).length + E.length + 1) ≤ 3 * (CE * (E.length + 1)) := by
    calc CE * ((blockVerts E).length + E.length + 1) ≤ CE * (3 * (E.length + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 3 * (CE * (E.length + 1)) := by ring
  have h2 : CP * ((blockVerts E).length + E.length + 1) ≤ 3 * (CP * (E.length + 1)) := by
    calc CP * ((blockVerts E).length + E.length + 1) ≤ CP * (3 * (E.length + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 3 * (CP * (E.length + 1)) := by ring
  have h3 : CB k CE CP * (E.length + 1) = 3 * (CE * (E.length + 1)) + 3 * (CP * (E.length + 1)) +
      6 * (k4Base k).flatten.length * (E.length + 1) + 200 * (E.length + 1) := by
    simp only [CB]; ring
  have h4 : 6 * (k4Base k).flatten.length ≤ 6 * (k4Base k).flatten.length * (E.length + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  simp only [polyBound]
  omega

end STACS2027.RAM.Block
