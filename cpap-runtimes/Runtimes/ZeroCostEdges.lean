module

public import Runtimes.ZeroCostInit
import Mathlib.Tactic

/-!
# Corollary 5 on the RAM: edge identifiers (B2), counts and offsets

Phases 4 and 5 of `zeroCostProg`, each within a space bound `S` (`HTB S`) above the end of its
memory:
* `stepEdges_spec` (`bOFF g k ≤ S`): for every occurrence `q = ik + j` (in the order of the
  cycles), the machine reads the ends `verts[q]`, `verts[ik + next k j]` of its edge
  `e = occs[q]`, orders them, looks up their ids in the dictionary and stores the id pair
  `idPr e = (idv e.1, idv e.2)` as `(PU[q], PV[q])` (`edgeBody_spec`); then outerplanar package's module
  `PairIds.pairIds` (B2: a stable counting sort of the pairs by first id and a timestamped scan,
  `O(N + kt)` time and space, no `N × N` table) stores the first-occurrence identifiers
  `PairIds.eids (prs g k)` and their class sizes. As the id pair is injective on the edges of
  the cycles, these are `EID[q] = eidOf g k q` (the index of `e` in `edgesOnCycles g k`,
  `eids_prs`) and `CNT[e'] = cntF g k (kt) e'` (`count_eids_prs`), and `gNE` is the number of
  distinct edges (`EdgesPost`, as before);
* `stepOff_spec` (`bCL g k ≤ S`): `OFF[e'] = offF g k e'` for every identifier, and a zero
  array `SEEN` (`OffPost`).
-/

@[expose] public section

namespace STACS2027.Runtimes.ZeroCost

open STACS2027 STACS2027.RAM STACS2027.RAM.R0

variable {S : ℕ}

/-! ### The state of the id pass -/

/-- The registers fixed during the id pass. -/
@[mk_iff] structure GE (g : Graph) (k : ℕ) (c : Config) : Prop where
  ga : GA g k c
  rd : c.reg gD = bD g k
  rn : c.reg gN = nV g k
  rpu : c.reg gPU = bPU g k
  rpv : c.reg gPV = bPV g k
  rfree : c.reg rFREE = bPI g k

/-- The registers written by the id pass. -/
def WE : List ℕ := [rT, sQ, sX, sP, sY, sU, sV, sJ, sI, sBase]

theorem GE.regIndep (g : Graph) (k : ℕ) : RegIndep WE (GE g k) := by indep [gE_iff, gA_iff]

/-- The memory of the id pass: the id pairs of the first `q` occurrences are stored. -/
structure EMem (g : Graph) (k : ℕ) (q : ℕ) (m : ℕ → ℕ) : Prop where
  mverts : Arr m (bV g) (verts g k)
  mdict : Tab m (bD g k) (maxV g k + 1) (dictOf (vl g k))
  mpu : Tab m (bPU g k) q fun q' => idv g k ((occs g k).getD q' (0, 0)).1
  mpv : Tab m (bPV g k) q fun q' => idv g k ((occs g k).getD q' (0, 0)).2
  mzero : ZeroFrom m (bPI g k)

/-- The state of the id pass after `q` occurrences. -/
def EInv (g : Graph) (k q : ℕ) (c : Config) : Prop :=
  GE g k c ∧ EMem g k q c.mem ∧ c.out = []

theorem occ_lt {k i j t : ℕ} (hi : i < t) (hj : j < k) : i * k + j < k * t := by
  have : (i + 1) * k ≤ t * k := Nat.mul_le_mul_right k hi
  rw [Nat.add_mul, one_mul] at this; rw [Nat.mul_comm k]; omega

/-- Recording the id pair of occurrence `q`: two stores. -/
theorem EMem.put {g : Graph} {k q : ℕ} {m : ℕ → ℕ} (h : EMem g k q m)
    (hq : q < k * (cycles g k).length) :
    EMem g k (q + 1) (upd (upd m (bPU g k + q) (idv g k ((occs g k).getD q (0, 0)).1))
      (bPV g k + q) (idv g k ((occs g k).getD q (0, 0)).2)) := by
  have hl := layout_eqs g k
  refine ⟨(h.mverts.upd_of_disjoint (by rw [length_verts]; omega)).upd_of_disjoint
      (by rw [length_verts]; omega), (h.mdict.upd_of_disjoint (by omega)).upd_of_disjoint (by omega),
    ((h.mpu.upd_of_disjoint (by omega)).snoc (by simp)).upd_of_disjoint (by omega),
    (h.mpv.upd_of_disjoint (by omega)).upd_of_disjoint (by omega) |>.snoc (by simp),
    (h.mzero.upd (by omega)).upd (by omega)⟩

/-! ### Reading an occurrence -/

theorem nextPos_run {c : Config} {base j k : ℕ} (hJ : c.reg sJ = j) (hK : c.reg gK = k)
    (hQ : c.reg sQ = base + j) (hB : c.reg sBase = base) :
    (run nextPos c).reg sP = base + next k j ∧ Agree [sP, rT] c (run nextPos c) := by
  refine ⟨?_, agree_run (by decide) rfl rfl (by decide) c⟩
  simp only [nextPos, run_seq', run_addc (show sJ ≠ rT by decide), run_ifLt,
    run_addc (show sQ ≠ rT by decide), run_mov (show sBase ≠ rT by decide)]
  unfold next
  by_cases h : j + 1 < k
  · simp +decide [hJ, hK, hQ, h]; omega
  · simp +decide [hJ, hK, hB, h]

theorem minmax_run (c : Config) :
    (run minmax c).reg sX = min (c.reg sX) (c.reg sY) ∧
      (run minmax c).reg sY = max (c.reg sX) (c.reg sY) ∧ Agree [sX, sY, rT] c (run minmax c) := by
  refine ⟨?_, ?_, agree_run (by decide) rfl rfl (by decide) c⟩ <;>
  · simp only [minmax, run_ifLt, run_swap (show sX ≠ sY by decide), run_skip]
    by_cases h : c.reg sY < c.reg sX
    · simp +decide [h]; omega
    · simp +decide [h]; omega

theorem edgeA_run (c : Config) :
    (run edgeA c).reg sQ = c.reg sBase + c.reg sJ ∧
      (run edgeA c).reg sX = c.mem (c.reg gV + (c.reg sBase + c.reg sJ)) ∧
      Agree [sQ, sX] c (run edgeA c) :=
  ⟨by simp +decide [edgeA], by simp +decide [edgeA], agree_run (by decide) rfl rfl (by decide) c⟩

theorem ldY_run (c : Config) :
    (run (ld sY gV sP) c).reg sY = c.mem (c.reg gV + c.reg sP) ∧ Agree [sY] c (run (ld sY gV sP) c) :=
  ⟨by simp, agree_run (by decide) rfl rfl (by decide) c⟩

theorem edgeIds_run (c : Config) :
    (run edgeIds c).reg sU = c.mem (c.reg gD + c.reg sX) - 1 ∧
      (run edgeIds c).reg sV = c.mem (c.reg gD + c.reg sY) - 1 ∧
      Agree [sU, sV, rT] c (run edgeIds c) :=
  ⟨by simp +decide [edgeIds, run_dec], by simp +decide [edgeIds, run_dec],
    agree_run (by decide) rfl rfl (by decide) c⟩

/-- The registers written by `edgeRead`. -/
def WR : List ℕ := [sQ, sX, sP, sY, sU, sV, rT]

/-- **Reading occurrence `q = ik + j`**: `sQ = q`, and `sU`, `sV` are the ids of the ends of its
edge (smaller end first); the accesses are in the cycle part of the input and the dictionary. -/
theorem edgeRead_run {g : Graph} {k i j : ℕ} {q' : ℕ} {c : Config} (hS : bPU g k ≤ S)
    (hi : i < (cycles g k).length) (hj : j < k)
    (hG : GE g k c) (hM : EMem g k q' c.mem) (hJ : c.reg sJ = j) (hB : c.reg sBase = i * k) :
    (run edgeRead c).reg sQ = i * k + j ∧
      (run edgeRead c).reg sU = idv g k ((occs g k).getD (i * k + j) (0, 0)).1 ∧
      (run edgeRead c).reg sV = idv g k ((occs g k).getD (i * k + j) (0, 0)).2 ∧
      Agree WR c (run edgeRead c) ∧ AddrOK S edgeRead c := by
  have hq := occ_lt hi hj
  have hk : 0 < k := by omega
  have hq2 : i * k + next k j < k * (cycles g k).length := occ_lt hi (next_lt hk)
  have hlay : bD g k = bV g + k * (cycles g k).length ∧ bPU g k = bD g k + maxV g k + 1 :=
    ⟨rfl, rfl⟩
  set x := (verts g k).getD (i * k + j) 0
  set y := (verts g k).getD (i * k + next k j) 0
  have he : (occs g k).getD (i * k + j) (0, 0) = edge x y := occs_getD hi hj
  have hx : c.mem (bV g + (i * k + j)) = x := hM.mverts.getD (by rw [length_verts]; exact hq)
  have hy : c.mem (bV g + (i * k + next k j)) = y := hM.mverts.getD (by rw [length_verts]; exact hq2)
  have hev := occs_mem_verts (occs_getD_mem hq)
  rw [he] at hev
  have hle1 := le_maxV hev.1
  have hle2 := le_maxV hev.2
  have hdx := hM.mdict.get (i := (edge x y).1) (by omega)
  have hdy := hM.mdict.get (i := (edge x y).2) (by omega)
  rw [dictOf_vl hev.1] at hdx
  rw [dictOf_vl hev.2] at hdy
  obtain ⟨h1q, h1x, a1⟩ := edgeA_run c
  obtain ⟨h2p, a2⟩ := nextPos_run (c := run edgeA c) (base := i * k)
    (by rw [a1.reg sJ (by decide), hJ]) (by rw [a1.reg gK (by decide), hG.ga.rk])
    (by rw [h1q, hB, hJ]) (by rw [a1.reg sBase (by decide), hB])
  obtain ⟨h3y, a3⟩ := ldY_run (run nextPos (run edgeA c))
  obtain ⟨h4x, h4y, a4⟩ := minmax_run (run (ld sY gV sP) (run nextPos (run edgeA c)))
  obtain ⟨h5u, h5v, a5⟩ := edgeIds_run (run minmax (run (ld sY gV sP) (run nextPos (run edgeA c))))
  have a14 : Agree WR c (run minmax (run (ld sY gV sP) (run nextPos (run edgeA c)))) :=
    (((a1.mono (by decide)).trans (a2.mono (by decide))).trans (a3.mono (by decide))).trans
      (a4.mono (by decide))
  have a15 : Agree WR c (run edgeRead c) := a14.trans (a5.mono (by decide))
  have e3x : (run (ld sY gV sP) (run nextPos (run edgeA c))).reg sX = x := by
    rw [a3.reg sX (by decide), a2.reg sX (by decide), h1x, hG.ga.rv, hB, hJ, hx]
  have e3y : (run (ld sY gV sP) (run nextPos (run edgeA c))).reg sY = y := by
    rw [h3y, a2.mem, a1.mem, a2.reg gV (by decide), a1.reg gV (by decide), h2p, hG.ga.rv, hy]
  have e4x : (run minmax (run (ld sY gV sP) (run nextPos (run edgeA c)))).reg sX = (edge x y).1 := by
    rw [h4x, e3x, e3y]; rfl
  have e4y : (run minmax (run (ld sY gV sP) (run nextPos (run edgeA c)))).reg sY = (edge x y).2 := by
    rw [h4y, e3x, e3y]; rfl
  have e4d : (run minmax (run (ld sY gV sP) (run nextPos (run edgeA c)))).reg gD = bD g k := by
    rw [a14.reg gD (by decide), hG.rd]
  refine ⟨?_, ?_, ?_, a15, ?_⟩
  · show (run edgeIds (run minmax (run (ld sY gV sP) (run nextPos (run edgeA c))))).reg sQ = _
    rw [a5.reg sQ (by decide), a4.reg sQ (by decide), a3.reg sQ (by decide), a2.reg sQ (by decide),
      h1q, hB, hJ]
  · show (run edgeIds (run minmax (run (ld sY gV sP) (run nextPos (run edgeA c))))).reg sU = _
    rw [h5u, e4x, e4d, a14.mem, hdx, Nat.add_sub_cancel, he]
  · show (run edgeIds (run minmax (run (ld sY gV sP) (run nextPos (run edgeA c))))).reg sV = _
    rw [h5v, e4y, e4d, a14.mem, hdy, Nat.add_sub_cancel, he]
  · refine AddrOK.seq (by addr_ok [edgeA, hG.ga.rv, hB, hJ]) (AddrOK.seq (AddrOK.of_memFree rfl)
      (AddrOK.seq ?_ (AddrOK.seq (AddrOK.of_memFree rfl) ?_)))
    · rw [addrOK_ld, a2.reg gV (by decide), a1.reg gV (by decide), h2p, hG.ga.rv]; omega
    · show AddrOK S edgeIds (run minmax (run (ld sY gV sP) (run nextPos (run edgeA c))))
      generalize run minmax (run (ld sY gV sP) (run nextPos (run edgeA c))) = c₄ at e4x e4y e4d
      addr_ok [edgeIds, e4x, e4y, e4d]

/-! ### The id pass -/

/-- The invariant of the inner loop (cycle `i`) after `j` positions. -/
def JInv (g : Graph) (k i j : ℕ) (c : Config) : Prop :=
  EInv g k (i * k + j) c ∧ c.reg sBase = i * k ∧ c.reg sI = i

theorem not_mem_of_sub {r : ℕ} {W W' : List ℕ} (h : r ∉ W) (hs : ∀ x ∈ W', x ∈ W) : r ∉ W' :=
  fun h' => h (hs r h')

/-- One occurrence of the id pass: its id pair into `PU`, `PV`. -/
theorem edgeBody_spec (g : Graph) (k : ℕ) (hS : bPI g k ≤ S) (i j : ℕ)
    (hi : i < (cycles g k).length) (hj : j < k) :
    HTB S edgeBody (fun c => JInv g k i j c ∧ c.reg sJ = j ∧ c.reg gK = k)
      (fun c => JInv g k i (j + 1) c ∧ c.reg sJ = j ∧ c.reg gK = k) 32 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨⟨hG, hM, ho⟩, hB, hI⟩, hJ, hK⟩ => ?_
  have hq := occ_lt hi hj
  have hl := layout_eqs g k
  obtain ⟨r1q, r1u, r1v, a1, A1⟩ := edgeRead_run (S := S) (by omega) hi hj hG hM hJ hB
  have hG1 : GE g k (run edgeRead c) := (GE.regIndep g k).indep.mono (by decide) c _ a1 hG
  have hfin : run edgeBody c = run edgePut (run edgeRead c) := rfl
  have hmem : (run edgeBody c).mem = upd (upd c.mem (bPU g k + (i * k + j))
      (idv g k ((occs g k).getD (i * k + j) (0, 0)).1)) (bPV g k + (i * k + j))
      (idv g k ((occs g k).getD (i * k + j) (0, 0)).2) := by
    rw [hfin]
    simp +decide only [edgePut, run_seq', run_st (show sU ≠ rT by decide),
      run_st (show sV ≠ rT by decide), setReg_mem, setMem_mem_upd, setReg_reg, setMem_reg,
      ↓reduceIte, hG1.rpu, hG1.rpv, r1q, r1u, r1v, a1.mem]
  have hreg : ∀ r, r ∉ [rT, sQ, sX, sP, sY, sU, sV] → (run edgeBody c).reg r = c.reg r := by
    intro r hr
    rw [hfin, run_reg_of_not_mem (s := edgePut) (by decide) (fun h => hr (by
      have : ∀ x ∈ wregs edgePut, x ∈ [rT, sQ, sX, sP, sY, sU, sV] := by decide
      exact this r h)), a1.reg r (not_mem_of_sub hr (by decide))]
  refine ⟨AddrOK.seq A1 (by addr_ok [edgePut, hG1.rpu, hG1.rpv, r1q]),
    ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩⟩
  · exact ((GE.regIndep g k).mono (by decide)) _ _ hreg hG
  · rw [hmem, ← Nat.add_assoc]; exact hM.put hq
  · rw [hfin, run_out_of_writes (s := edgePut) (by decide) rfl, a1.out, ho]
  · rw [hreg sBase (by decide), hB]
  · rw [hreg sI (by decide), hI]
  · rw [hreg sJ (by decide), hJ]
  · rw [hreg gK (by decide), hK]

/-- One cycle of the id pass. -/
theorem edgeRow_spec (g : Graph) (k : ℕ) (hS : bPI g k ≤ S) (i : ℕ) (hi : i < (cycles g k).length) :
    HTB S edgeRow (fun c => (EInv g k (i * k) c ∧ c.reg sBase = i * k) ∧ c.reg sI = i ∧
        c.reg gT = (cycles g k).length)
      (fun c => (EInv g k ((i + 1) * k) c ∧ c.reg sBase = (i + 1) * k) ∧ c.reg sI = i ∧
        c.reg gT = (cycles g k).length) (k * 36 + 4) := by
  have hl := HTB.forUpC (i := sJ) (n := gK) (N := k) (body := edgeBody)
    (fun j c => JInv g k i j c ∧ c.reg gT = (cycles g k).length) 32 (by decide) (by decide)
    (by decide) (fun j => by indep [JInv, EInv, gE_iff, gA_iff])
    (fun j hj => (edgeBody_spec g k hS i j hi hj).frame (F := fun c => c.reg gT = (cycles g k).length)
      (fun c c' hfr h => by rw [hfr.reg gT (by decide), h]) |>.mono
      (fun c ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨⟨h1, h3, h4⟩, h2⟩) (fun c ⟨⟨h1, h3, h4⟩, h2⟩ => ⟨⟨h1, h2⟩, h3, h4⟩)
      le_rfl)
  have h2 : HTB S (.add sBase sBase gK)
      (fun c => (JInv g k i k c ∧ c.reg gT = (cycles g k).length) ∧ c.reg sJ = k ∧ c.reg gK = k)
      (fun c => (EInv g k ((i + 1) * k) c ∧ c.reg sBase = (i + 1) * k) ∧ c.reg sI = i ∧
        c.reg gT = (cycles g k).length) 1 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨⟨hE, hB, hI⟩, hT⟩, _, hK⟩ => ?_
    have hE' : EInv g k ((i + 1) * k) c := by rw [show (i + 1) * k = i * k + k by ring]; exact hE
    refine ⟨⟨(show Indep [sBase] (EInv g k ((i + 1) * k)) by indep [EInv, gE_iff, gA_iff]).setReg
      (by decide) _ hE', ?_⟩, ?_, ?_⟩
    · simp +decide [hB, hK]; ring
    · simp +decide [hI]
    · simp +decide [hT]
  refine (hl.seq h2).mono
    (fun c ⟨⟨hE, hB⟩, hI, hT⟩ => ⟨⟨⟨by simpa using hE, hB, hI⟩, hT⟩, hE.1.ga.rk⟩)
    (fun _ h => h) (by omega)

/-! ### Phase 4: the identifiers -/

/-- The state after phase 4. -/
@[mk_iff] structure EdgesPost (g : Graph) (k : ℕ) (c : Config) : Prop where
  ga : GA g k c
  reid : c.reg gEID = bEID g k
  rcnt : c.reg gCNT = bCNT g k
  rne : c.reg gNE = (edgesOnCycles g k).length
  rfree : c.reg rFREE = bOFF g k
  mverts : Arr c.mem (bV g) (verts g k)
  meid : Tab c.mem (bEID g k) (k * (cycles g k).length) (eidOf g k)
  mcnt : Tab c.mem (bCNT g k) (k * (cycles g k).length) (cntF g k (k * (cycles g k).length))
  mzero : ZeroFrom c.mem (bOFF g k)
  rout : c.out = []

/-- The state at the call of `PairIds.pairIds`. -/
def IdsPre (g : Graph) (k : ℕ) (c : Config) : Prop :=
  PairIds.PIn (prs g k) (nV g k) c ∧ GA g k c ∧ c.reg rFREE = bPI g k ∧
    Arr c.mem (bV g) (verts g k) ∧ c.out = []

/-- The state after `PairIds.pairIds`. -/
def IdsMid (g : Graph) (k : ℕ) (c : Config) : Prop :=
  GA g k c ∧ c.reg PairIds.rID = bEID g k ∧ c.reg PairIds.rCT = bCNT g k ∧
    c.reg PairIds.rNE = (edgesOnCycles g k).length ∧ c.reg rFREE = bOFF g k ∧
    Arr c.mem (bV g) (verts g k) ∧ Tab c.mem (bEID g k) (k * (cycles g k).length) (eidOf g k) ∧
    Tab c.mem (bCNT g k) (k * (cycles g k).length) (cntF g k (k * (cycles g k).length)) ∧
    ZeroFrom c.mem (bOFF g k) ∧ c.out = []

/-- An array of the values of `f` on `0, …, n - 1` is a table of `f`. -/
theorem tab_of_arr_map_range {m : ℕ → ℕ} {b n : ℕ} {f : ℕ → ℕ}
    (h : Arr m b ((List.range n).map f)) : Tab m b n f := fun i hi => by
  have := h.get (i := i) (by simpa using hi)
  simpa using this

/-- The call of `PairIds.pairIds` on the id pairs. -/
theorem pairIds_zeroCost (g : Graph) (k : ℕ) (hS : bOFF g k ≤ S) :
    HTB S PairIds.pairIds (IdsPre g k) (IdsMid g k)
      (PairIds.CI * (nV g k + k * (cycles g k).length + 1)) := by
  refine HTB.of_forall fun c₀ ⟨hIn, hga, hF, hV, ho⟩ => ?_
  have hS' : PairIds.idsEnd (nV g k) (prs g k).length (c₀.reg rFREE) ≤ S := by
    rw [length_prs, hF, idsEnd_eq]; exact hS
  refine (PairIds.pairIds_spec (prs g k) (nV g k) prs_below c₀ hS').mono
    (fun c hc => ⟨hc ▸ hIn, hc⟩) (fun c ⟨hO, hfr⟩ => ?_) (by rw [length_prs])
  have hk : ∀ r, 250 ≤ r → c.reg r = c₀.reg r := fun r hr =>
    hfr.reg r fun h => by
      rcases PairIds.pairIds_wregs r h with rfl | rfl | ⟨_, h2⟩ | ⟨_, h2⟩
      · exact absurd hr (by decide)
      · exact absurd hr (by decide)
      · omega
      · have e : PairIds.rLD = 124 := rfl
        omega
  have hrid := hO.rid
  have hrct := hO.rct
  have hfree := hO.free
  have hsame := hO.same
  rw [length_prs, hF] at hrid hrct hfree
  rw [hF] at hsame
  have hfree' : c.reg rFREE = bOFF g k := hfree.trans (idsEnd_eq g k)
  refine ⟨?_, hrid, hrct, ?_, hfree', hV.of_below hsame (by
    rw [length_verts]; have := layout_eqs g k; omega), ?_, ?_,
    by rw [← hfree']; exact hO.zero, by rw [hfr.out PairIds.pairIds_writes, ho]⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hga
    exact ⟨(hk _ (by decide)).trans h1, (hk _ (by decide)).trans h2, (hk _ (by decide)).trans h3,
      (hk _ (by decide)).trans h4, (hk _ (by decide)).trans h5⟩
  · rw [hO.ne, length_eraseDups_prs]
  · have := hO.id
    rw [hrid, eids_prs] at this
    exact tab_of_arr_map_range this
  · have := hO.ct
    rw [hrct, length_prs] at this
    exact this.congr_fun fun e _ => count_eids_prs e

/-- **Phase 4**: the id pairs of the occurrences, then their identifiers and counts. -/
theorem stepEdges_spec (g : Graph) (k : ℕ) (hS : bOFF g k ≤ S) :
    HTB S stepEdges (DictPost g k) (EdgesPost g k)
      ((cycles g k).length * (k * 36 + 8) + PairIds.CI * (nV g k + k * (cycles g k).length + 1) +
        24) := by
  have hl0 := layout_eqs g k
  have hSI : bPI g k ≤ S := by omega
  have h0 : HTB S (.seq (.seq (alloc gPU gKT) (alloc gPV gKT)) (.const sBase 0))
      (DictPost g k) (fun c => (EInv g k (0 * k) c ∧ c.reg sBase = 0 * k) ∧
        c.reg gT = (cycles g k).length) 7 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c hP => ?_
    have hga : GA g k (run (.seq (.seq (alloc gPU gKT) (alloc gPV gKT)) (.const sBase 0)) c) :=
      (show RegIndep [rT, gPU, rFREE, gPV, sBase] (GA g k) by indep [gA_iff]).run_of_sub
        (by decide) (by decide) hP.ga
    simp only [Nat.zero_mul]
    refine ⟨⟨⟨⟨hga, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩, ?_⟩
    all_goals simp +decide only [run_seq',
      run_alloc (show gKT ≠ rT by decide) (show gPU ≠ gKT by decide),
      run_alloc (show gKT ≠ rT by decide) (show gPV ≠ gKT by decide), run_const, setReg_reg,
      setReg_mem, setReg_out, ↓reduceIte, hP.rd, hP.rn, hP.rfree, hP.rout, hP.ga.rkt, hP.ga.rt]
    · simp [hl0]
    · simp [hl0]
    · exact ⟨hP.mverts, hP.mdict, by simp, by simp, hP.mzero.mono (by omega)⟩
  have hl := HTB.forUpC (i := sI) (n := gT) (N := (cycles g k).length) (body := edgeRow)
    (fun i c => EInv g k (i * k) c ∧ c.reg sBase = i * k) (k * 36 + 4) (by decide) (by decide)
    (by decide) (fun j => by indep [EInv, gE_iff, gA_iff]) (fun i hi => edgeRow_spec g k hSI i hi)
  have h1 : HTB S idsArgs (fun c => (EInv g k ((cycles g k).length * k) c ∧
        c.reg sBase = (cycles g k).length * k) ∧ c.reg sI = (cycles g k).length ∧
        c.reg gT = (cycles g k).length) (IdsPre g k) 8 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨⟨hG, hM, ho⟩, _⟩, _, _⟩ => ?_
    rw [Nat.mul_comm] at hM
    have hAg : Agree [rT, PairIds.rPU, PairIds.rPV, PairIds.rPL, PairIds.rPN] c (run idsArgs c) :=
      agree_run (by decide) rfl rfl (by decide) c
    have hpu : (run idsArgs c).reg PairIds.rPU = bPU g k := by
      simp +decide [idsArgs, run_mov, hG.rpu]
    have hpv : (run idsArgs c).reg PairIds.rPV = bPV g k := by
      simp +decide [idsArgs, run_mov, hG.rpv]
    have hF : (run idsArgs c).reg rFREE = bPI g k := (hAg.reg _ (by decide)).trans hG.rfree
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, (show RegIndep [rT, PairIds.rPU, PairIds.rPV, PairIds.rPL,
      PairIds.rPN] (GA g k) by indep [gA_iff]).indep c _ hAg hG.ga, hF,
      by rw [hAg.mem]; exact hM.mverts, by rw [hAg.out]; exact ho⟩
    · simp +decide [idsArgs, run_mov, hG.ga.rkt, length_prs]
    · simp +decide [idsArgs, run_mov, hG.rn]
    · rw [hpu, hAg.mem, ← map_fst_prs]; exact hM.mpu.toArr
    · rw [hpv, hAg.mem, ← map_snd_prs]; exact hM.mpv.toArr
    · rw [hpu, hpv, hF, length_prs]; exact ⟨by omega, by omega⟩
    · rw [hF, hAg.mem]; exact hM.mzero
  have h3 : HTB S idsBack (IdsMid g k) (EdgesPost g k) 6 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide)
      fun c ⟨hga, hid, hct, hne, hF, hV, hE, hC, hZ, ho⟩ => ?_
    have hAg : Agree [rT, gEID, gCNT, gNE] c (run idsBack c) :=
      agree_run (by decide) rfl rfl (by decide) c
    refine ⟨(show RegIndep [rT, gEID, gCNT, gNE] (GA g k) by indep [gA_iff]).indep c _ hAg hga,
      ?_, ?_, ?_, (hAg.reg _ (by decide)).trans hF, by rw [hAg.mem]; exact hV,
      by rw [hAg.mem]; exact hE, by rw [hAg.mem]; exact hC, by rw [hAg.mem]; exact hZ,
      by rw [hAg.out]; exact ho⟩
    · simp +decide [idsBack, run_mov, hid]
    · simp +decide [idsBack, run_mov, hct]
    · simp +decide [idsBack, run_mov, hne]
  refine HTB.assoc (HTB.assoc ((h0.seq (hl.seq (h1.seq ((pairIds_zeroCost g k hS).seq
    h3)))).weaken ?_))
  have : (cycles g k).length * (k * 36 + 4 + 4) = (cycles g k).length * (k * 36 + 8) := by ring
  omega

/-! ### Phase 5: the offsets -/

/-- The invariant of the offset pass after `e` identifiers. -/
def OffInv (g : Graph) (k e : ℕ) (c : Config) : Prop :=
  GA g k c ∧ c.reg gEID = bEID g k ∧ c.reg gCNT = bCNT g k ∧ c.reg gOFF = bOFF g k ∧
    c.reg gSEEN = bSEEN g k ∧ c.reg rFREE = bCL g k ∧ c.reg sAcc = offF g k e ∧
    Arr c.mem (bV g) (verts g k) ∧ Tab c.mem (bEID g k) (k * (cycles g k).length) (eidOf g k) ∧
    Tab c.mem (bCNT g k) (k * (cycles g k).length) (cntF g k (k * (cycles g k).length)) ∧
    Tab c.mem (bOFF g k) e (offF g k) ∧ ZeroFrom c.mem (bSEEN g k) ∧ c.out = []

theorem offBody_spec (g : Graph) (k : ℕ) (hS : bCL g k ≤ S) (e : ℕ)
    (he : e < (edgesOnCycles g k).length) :
    HTB S offBody (fun c => OffInv g k e c ∧ c.reg sE = e ∧ c.reg gNE = (edgesOnCycles g k).length)
      (fun c => OffInv g k (e + 1) c ∧ c.reg sE = e ∧ c.reg gNE = (edgesOnCycles g k).length) 7 := by
  refine HTB.run_le (by decide) (by decide)
    fun c ⟨⟨hga, heid, hcnt, hoff, hseen, hfr, hacc, hV, hE, hC, hO, hZ, ho⟩, hi, hn⟩ => ?_
  have hne := nE_le g k
  refine ⟨by have := fits g k hS; addr_ok [offBody, hoff, hcnt, hi], ?_⟩
  have hl := layout_eqs g k
  have hpos := cntF_final_pos he
  have hc : c.mem (bCNT g k + e) = cntF g k (k * (cycles g k).length) e := hC.get (by omega)
  have hga' : GA g k (run offBody c) :=
    (show RegIndep [rT, sC, sAcc] (GA g k) by indep [gA_iff]).run_of_sub (by decide) (by decide) hga
  refine ⟨⟨hga', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals simp +decide only [offBody, run_seq', run_st (show sAcc ≠ rT by decide), run_ld, run_add,
    run_dec (show sAcc ≠ rT by decide), setReg_reg, setReg_mem, setReg_out, setMem_reg, setMem_mem_upd,
    setMem_out, ↓reduceIte, heid, hcnt, hoff, hseen, hfr, hacc, hi, hn, ho, upd_apply]
  · rw [offF_succ]
    have : ¬ (bCNT g k + e = bOFF g k + e) := by omega
    simp only [this, ↓reduceIte, hc]; omega
  · exact hV.upd_of_disjoint (by rw [length_verts]; omega)
  · exact hE.upd_of_disjoint (by omega)
  · exact hC.upd_of_disjoint (by omega)
  · exact (hO.upd_of_disjoint (by omega)).snoc (by simp)
  · exact hZ.upd (by omega)

/-- The state after phase 5. -/
@[mk_iff] structure OffPost (g : Graph) (k : ℕ) (c : Config) : Prop where
  ga : GA g k c
  reid : c.reg gEID = bEID g k
  rcnt : c.reg gCNT = bCNT g k
  roff : c.reg gOFF = bOFF g k
  rseen : c.reg gSEEN = bSEEN g k
  rfree : c.reg rFREE = bCL g k
  mverts : Arr c.mem (bV g) (verts g k)
  meid : Tab c.mem (bEID g k) (k * (cycles g k).length) (eidOf g k)
  mcnt : Tab c.mem (bCNT g k) (k * (cycles g k).length) (cntF g k (k * (cycles g k).length))
  moff : Tab c.mem (bOFF g k) (edgesOnCycles g k).length (offF g k)
  mseen : Tab c.mem (bSEEN g k) (edgesOnCycles g k).length (cntF g k 0)
  mzero : ZeroFrom c.mem (bCL g k)
  rout : c.out = []

/-- **Phase 5**: the offsets. -/
theorem stepOff_spec (g : Graph) (k : ℕ) (hS : bCL g k ≤ S) :
    HTB S stepOff (EdgesPost g k) (OffPost g k) ((edgesOnCycles g k).length * 11 + 11) := by
  have hl0 := layout_eqs g k
  have h0 : HTB S (.seq (.seq (alloc gOFF gNE) (alloc gSEEN gNE)) (mov sAcc gKT)) (EdgesPost g k)
      (fun c => OffInv g k 0 c ∧ c.reg gNE = (edgesOnCycles g k).length) 8 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c hP => ?_
    have hga : GA g k (run (.seq (.seq (alloc gOFF gNE) (alloc gSEEN gNE)) (mov sAcc gKT)) c) :=
      (show RegIndep [rT, gOFF, rFREE, gSEEN, sAcc] (GA g k) by indep [gA_iff]).run_of_sub
        (by decide) (by decide) hP.ga
    refine ⟨⟨hga, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals simp +decide only [run_seq', run_alloc (show gNE ≠ rT by decide) (show gOFF ≠ gNE by decide),
      run_alloc (show gNE ≠ rT by decide) (show gSEEN ≠ gNE by decide),
      run_mov (show gKT ≠ rT by decide), setReg_reg, setReg_mem,
      setReg_out, ↓reduceIte, hP.reid, hP.rcnt, hP.rne, hP.rfree, hP.rout, hP.ga.rkt]
    · simp [hl0]
    · simp [hl0]
    · rw [offF_zero]
    · exact hP.mverts
    · exact hP.meid
    · exact hP.mcnt
    · simp
    · exact hP.mzero.mono (by omega)
  have hl := HTB.forUpC (i := sE) (n := gNE) (N := (edgesOnCycles g k).length) (body := offBody)
    (OffInv g k) 7 (by decide) (by decide) (by decide)
    (fun j => by indep [OffInv, gA_iff]) (fun e he => offBody_spec g k hS e he)
  refine HTB.assoc (HTB.assoc ((h0.seq hl).mono (fun _ h => h) (fun c ⟨⟨hga, heid, hcnt, hoff, hseen, hfr,
    _, hV, hE, hC, hO, hZ, ho⟩, _, _⟩ => ⟨hga, heid, hcnt, hoff, hseen, hfr, hV, hE, hC, hO, ?_, ?_, ho⟩)
    (le_of_eq (by ring))))
  · rw [cntF_zero]; exact hZ.tab (le_refl _) _
  · exact hZ.mono (by omega)

end STACS2027.Runtimes.ZeroCost
