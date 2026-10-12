module

public import Runtimes.Flow.Front
public import Runtimes.ZeroCostEdges
import Mathlib.Tactic

/-!
# The edge pass, phase 4: the edge identifiers (B2) and the counts

Phase 4 of the construction machines is Corollary 5's `stepEdges` (`Runtimes/ZeroCostProg.lean`),
restated here for a general list `cs` of simple `k`-cycles (the proofs follow
`Runtimes/ZeroCostEdges.lean`, and reuse its lemmas on the loop-free blocks), within a space bound
`S ≥ bOFF g cs k`:
* for every occurrence `q = ik + j` (in the order of the cycles), the machine reads the ends
  `verts[q]`, `verts[ik + next k j]` of its edge `e = occs[q]`, orders them, looks up their ids
  in the dictionary and stores the id pair `idPr cs e = (idv e.1, idv e.2)` as `(PU[q], PV[q])`
  (`edgeBody_spec`);
* then outerplanar package's module `PairIds.pairIds` (B2: a stable counting sort of the pairs by first
  id and a timestamped scan, `O(N + kt)` time and space, no table indexed by pairs of labels)
  stores the first-occurrence identifiers `PairIds.eids (prs cs)` and their class sizes: as the
  id pair is injective on the edges of the cycles, these are `EID[q] = eid cs q` (the index of
  `e` in `eList cs`, `eids_prs`) and `CNT[r] = cntF cs (kt) r` (`count_eids_prs`), and `gNE` is
  the number of distinct edges (`EdgesPost`).

`edgePhase_spec` assembles the four phases: from the input, within `300 kt + 15t + 160` steps,
accessing only the addresses below any `S ≥ bOFF g cs k` (`bOFF_le`: at most
`11 (labelBound g + kt + m + 1)`; the label dictionary costs space but no time).
-/

@[expose] public section

namespace STACS2027.Runtimes.Flow

open STACS2027 STACS2027.RAM STACS2027.RAM.R0
open ZeroCost (edgeA nextPos minmax edgeIds edgeRead edgePut edgeBody edgeRow idsArgs idsBack
  stepEdges)

variable {S : ℕ}

/-! ### The state of the id pass -/

/-- The registers fixed during the id pass. -/
@[mk_iff] structure GE (g : Graph) (cs : List Cycle) (k : ℕ) (c : Config) : Prop where
  ga : GA g cs k c
  rd : c.reg gD = bD g cs k
  rn : c.reg gN = nV cs
  rpu : c.reg gPU = bPU g cs k
  rpv : c.reg gPV = bPV g cs k
  rfree : c.reg rFREE = bPI g cs k

theorem GE.regIndep (g : Graph) (cs : List Cycle) (k : ℕ) : RegIndep ZeroCost.WE (GE g cs k) := by
  indep [gE_iff, gA_iff]

/-- The memory of the id pass: the id pairs of the first `q` occurrences are stored. -/
structure EMem (g : Graph) (cs : List Cycle) (k : ℕ) (q : ℕ) (m : ℕ → ℕ) : Prop where
  mverts : Arr m (bV g) (verts cs)
  mdict : Tab m (bD g cs k) (maxV cs + 1) (dictOf (vl cs))
  mpu : Tab m (bPU g cs k) q fun q' => idv cs ((occs cs).getD q' (0, 0)).1
  mpv : Tab m (bPV g cs k) q fun q' => idv cs ((occs cs).getD q' (0, 0)).2
  mzero : ZeroFrom m (bPI g cs k)

/-- The state of the id pass after `q` occurrences. -/
def EInv (g : Graph) (cs : List Cycle) (k q : ℕ) (c : Config) : Prop :=
  GE g cs k c ∧ EMem g cs k q c.mem ∧ c.out = []

section phase4

variable {g : Graph} {cs : List Cycle} {k : ℕ}

/-- Recording the id pair of occurrence `q`: two stores. -/
theorem EMem.put (hcs : ∀ c ∈ cs, IsCycle g k c) {q : ℕ} {m : ℕ → ℕ} (h : EMem g cs k q m)
    (hq : q < k * cs.length) :
    EMem g cs k (q + 1) (upd (upd m (bPU g cs k + q) (idv cs ((occs cs).getD q (0, 0)).1))
      (bPV g cs k + q) (idv cs ((occs cs).getD q (0, 0)).2)) := by
  have hl := layout_eqs g cs k
  refine ⟨(h.mverts.upd_of_disjoint (by rw [length_verts hcs]; omega)).upd_of_disjoint
      (by rw [length_verts hcs]; omega),
    (h.mdict.upd_of_disjoint (by omega)).upd_of_disjoint (by omega),
    ((h.mpu.upd_of_disjoint (by omega)).snoc (by simp)).upd_of_disjoint (by omega),
    (h.mpv.upd_of_disjoint (by omega)).upd_of_disjoint (by omega) |>.snoc (by simp),
    (h.mzero.upd (by omega)).upd (by omega)⟩

/-! ### Reading an occurrence -/

/-- **Reading occurrence `q = ik + j`**: `sQ = q`, and `sU`, `sV` are the ids of the ends of its
edge (smaller end first); the accesses are in the cycle part of the input and the dictionary. -/
theorem edgeRead_run (hcs : ∀ c ∈ cs, IsCycle g k c) {i j : ℕ} {q' : ℕ} {c : Config}
    (hS : bPU g cs k ≤ S) (hi : i < cs.length) (hj : j < k)
    (hG : GE g cs k c) (hM : EMem g cs k q' c.mem) (hJ : c.reg ZeroCost.sJ = j)
    (hB : c.reg ZeroCost.sBase = i * k) :
    (run edgeRead c).reg ZeroCost.sQ = i * k + j ∧
      (run edgeRead c).reg ZeroCost.sU = idv cs ((occs cs).getD (i * k + j) (0, 0)).1 ∧
      (run edgeRead c).reg ZeroCost.sV = idv cs ((occs cs).getD (i * k + j) (0, 0)).2 ∧
      Agree ZeroCost.WR c (run edgeRead c) ∧ AddrOK S edgeRead c := by
  have hq := occ_lt hi hj
  have hk : 0 < k := by omega
  have hq2 : i * k + next k j < k * cs.length := occ_lt hi (next_lt hk)
  have hlay : bD g cs k = bV g + k * cs.length ∧ bPU g cs k = bD g cs k + maxV cs + 1 :=
    ⟨rfl, rfl⟩
  set x := (verts cs).getD (i * k + j) 0
  set y := (verts cs).getD (i * k + next k j) 0
  have he : (occs cs).getD (i * k + j) (0, 0) = edge x y := occs_getD hcs hi hj
  have hx : c.mem (bV g + (i * k + j)) = x := hM.mverts.getD (by rw [length_verts hcs]; exact hq)
  have hy : c.mem (bV g + (i * k + next k j)) = y :=
    hM.mverts.getD (by rw [length_verts hcs]; exact hq2)
  have hev := occs_mem_verts (occs_getD_mem (cs := cs) (by rw [length_occs hcs]; exact hq))
  rw [he] at hev
  have hle1 := le_maxV hev.1
  have hle2 := le_maxV hev.2
  have hdx := hM.mdict.get (i := (edge x y).1) (by omega)
  have hdy := hM.mdict.get (i := (edge x y).2) (by omega)
  rw [dictOf_vl hev.1] at hdx
  rw [dictOf_vl hev.2] at hdy
  obtain ⟨h1q, h1x, a1⟩ := ZeroCost.edgeA_run c
  obtain ⟨h2p, a2⟩ := ZeroCost.nextPos_run (c := run edgeA c) (base := i * k)
    (by rw [a1.reg ZeroCost.sJ (by decide), hJ]) (by rw [a1.reg gK (by decide), hG.ga.rk])
    (by rw [h1q, hB, hJ]) (by rw [a1.reg ZeroCost.sBase (by decide), hB])
  obtain ⟨h3y, a3⟩ := ZeroCost.ldY_run (run nextPos (run edgeA c))
  obtain ⟨h4x, h4y, a4⟩ := ZeroCost.minmax_run (run (ld ZeroCost.sY gV ZeroCost.sP) (run nextPos (run edgeA c)))
  obtain ⟨h5u, h5v, a5⟩ :=
    ZeroCost.edgeIds_run (run minmax (run (ld ZeroCost.sY gV ZeroCost.sP) (run nextPos (run edgeA c))))
  have a14 : Agree ZeroCost.WR c (run minmax (run (ld ZeroCost.sY gV ZeroCost.sP) (run nextPos (run edgeA c)))) :=
    (((a1.mono (by decide)).trans (a2.mono (by decide))).trans (a3.mono (by decide))).trans
      (a4.mono (by decide))
  have a15 : Agree ZeroCost.WR c (run edgeRead c) := a14.trans (a5.mono (by decide))
  have e3x : (run (ld ZeroCost.sY gV ZeroCost.sP) (run nextPos (run edgeA c))).reg ZeroCost.sX = x := by
    rw [a3.reg ZeroCost.sX (by decide), a2.reg ZeroCost.sX (by decide), h1x, hG.ga.rv, hB, hJ, hx]
  have e3y : (run (ld ZeroCost.sY gV ZeroCost.sP) (run nextPos (run edgeA c))).reg ZeroCost.sY = y := by
    rw [h3y, a2.mem, a1.mem, a2.reg gV (by decide), a1.reg gV (by decide), h2p, hG.ga.rv, hy]
  have e4x : (run minmax (run (ld ZeroCost.sY gV ZeroCost.sP) (run nextPos (run edgeA c)))).reg ZeroCost.sX =
      (edge x y).1 := by
    rw [h4x, e3x, e3y]; rfl
  have e4y : (run minmax (run (ld ZeroCost.sY gV ZeroCost.sP) (run nextPos (run edgeA c)))).reg ZeroCost.sY =
      (edge x y).2 := by
    rw [h4y, e3x, e3y]; rfl
  have e4d : (run minmax (run (ld ZeroCost.sY gV ZeroCost.sP) (run nextPos (run edgeA c)))).reg gD =
      bD g cs k := by
    rw [a14.reg gD (by decide), hG.rd]
  refine ⟨?_, ?_, ?_, a15, ?_⟩
  · show (run edgeIds (run minmax (run (ld ZeroCost.sY gV ZeroCost.sP) (run nextPos (run edgeA c))))).reg
      ZeroCost.sQ = _
    rw [a5.reg ZeroCost.sQ (by decide), a4.reg ZeroCost.sQ (by decide), a3.reg ZeroCost.sQ (by decide),
      a2.reg ZeroCost.sQ (by decide), h1q, hB, hJ]
  · show (run edgeIds (run minmax (run (ld ZeroCost.sY gV ZeroCost.sP) (run nextPos (run edgeA c))))).reg
      ZeroCost.sU = _
    rw [h5u, e4x, e4d, a14.mem, hdx, Nat.add_sub_cancel, he]
  · show (run edgeIds (run minmax (run (ld ZeroCost.sY gV ZeroCost.sP) (run nextPos (run edgeA c))))).reg
      ZeroCost.sV = _
    rw [h5v, e4y, e4d, a14.mem, hdy, Nat.add_sub_cancel, he]
  · refine AddrOK.seq (by addr_ok [edgeA, hG.ga.rv, hB, hJ]) (AddrOK.seq (AddrOK.of_memFree rfl)
      (AddrOK.seq ?_ (AddrOK.seq (AddrOK.of_memFree rfl) ?_)))
    · rw [addrOK_ld, a2.reg gV (by decide), a1.reg gV (by decide), h2p, hG.ga.rv]; omega
    · show AddrOK S edgeIds (run minmax (run (ld ZeroCost.sY gV ZeroCost.sP) (run nextPos (run edgeA c))))
      generalize run minmax (run (ld ZeroCost.sY gV ZeroCost.sP) (run nextPos (run edgeA c))) = c₄
        at e4x e4y e4d
      addr_ok [edgeIds, e4x, e4y, e4d]

/-! ### The id pass -/

/-- The invariant of the inner loop (cycle `i`) after `j` positions. -/
def JInv (g : Graph) (cs : List Cycle) (k i j : ℕ) (c : Config) : Prop :=
  EInv g cs k (i * k + j) c ∧ c.reg ZeroCost.sBase = i * k ∧ c.reg ZeroCost.sI = i

/-- One occurrence of the id pass: its id pair into `PU`, `PV`. -/
theorem edgeBody_spec (hcs : ∀ c ∈ cs, IsCycle g k c) (hS : bPI g cs k ≤ S) (i j : ℕ)
    (hi : i < cs.length) (hj : j < k) :
    HTB S edgeBody (fun c => JInv g cs k i j c ∧ c.reg ZeroCost.sJ = j ∧ c.reg gK = k)
      (fun c => JInv g cs k i (j + 1) c ∧ c.reg ZeroCost.sJ = j ∧ c.reg gK = k) 32 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨⟨hG, hM, ho⟩, hB, hI⟩, hJ, hK⟩ => ?_
  have hq := occ_lt hi hj
  have hl := layout_eqs g cs k
  obtain ⟨r1q, r1u, r1v, a1, A1⟩ := edgeRead_run (S := S) hcs (by omega) hi hj hG hM hJ hB
  have hG1 : GE g cs k (run edgeRead c) := (GE.regIndep g cs k).indep.mono (by decide) c _ a1 hG
  have hfin : run edgeBody c = run edgePut (run edgeRead c) := rfl
  have hmem : (run edgeBody c).mem = upd (upd c.mem (bPU g cs k + (i * k + j))
      (idv cs ((occs cs).getD (i * k + j) (0, 0)).1)) (bPV g cs k + (i * k + j))
      (idv cs ((occs cs).getD (i * k + j) (0, 0)).2) := by
    rw [hfin]
    simp +decide only [edgePut, run_seq', run_st (show ZeroCost.sU ≠ rT by decide),
      run_st (show ZeroCost.sV ≠ rT by decide), setReg_mem, setMem_mem_upd, setReg_reg, setMem_reg,
      ↓reduceIte, hG1.rpu, hG1.rpv, r1q, r1u, r1v, a1.mem]
  have hreg : ∀ r, r ∉ [rT, ZeroCost.sQ, ZeroCost.sX, ZeroCost.sP, ZeroCost.sY, ZeroCost.sU, ZeroCost.sV] →
      (run edgeBody c).reg r = c.reg r := by
    intro r hr
    rw [hfin, run_reg_of_not_mem (s := edgePut) (by decide) (fun h => hr (by
      have : ∀ x ∈ wregs edgePut, x ∈ [rT, ZeroCost.sQ, ZeroCost.sX, ZeroCost.sP, ZeroCost.sY, ZeroCost.sU,
        ZeroCost.sV] := by decide
      exact this r h)), a1.reg r (ZeroCost.not_mem_of_sub hr (by decide))]
  refine ⟨AddrOK.seq A1 (by addr_ok [edgePut, hG1.rpu, hG1.rpv, r1q]),
    ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩⟩
  · exact ((GE.regIndep g cs k).mono (by decide)) _ _ hreg hG
  · rw [hmem, ← Nat.add_assoc]; exact hM.put hcs hq
  · rw [hfin, run_out_of_writes (s := edgePut) (by decide) rfl, a1.out, ho]
  · rw [hreg ZeroCost.sBase (by decide), hB]
  · rw [hreg ZeroCost.sI (by decide), hI]
  · rw [hreg ZeroCost.sJ (by decide), hJ]
  · rw [hreg gK (by decide), hK]

/-- One cycle of the id pass. -/
theorem edgeRow_spec (hcs : ∀ c ∈ cs, IsCycle g k c) (hS : bPI g cs k ≤ S) (i : ℕ)
    (hi : i < cs.length) :
    HTB S edgeRow (fun c => (EInv g cs k (i * k) c ∧ c.reg ZeroCost.sBase = i * k) ∧
        c.reg ZeroCost.sI = i ∧ c.reg gT = cs.length)
      (fun c => (EInv g cs k ((i + 1) * k) c ∧ c.reg ZeroCost.sBase = (i + 1) * k) ∧
        c.reg ZeroCost.sI = i ∧ c.reg gT = cs.length) (k * 36 + 4) := by
  have hl := HTB.forUpC (i := ZeroCost.sJ) (n := gK) (N := k) (body := edgeBody)
    (fun j c => JInv g cs k i j c ∧ c.reg gT = cs.length) 32 (by decide) (by decide)
    (by decide) (fun j => by indep [JInv, EInv, gE_iff, gA_iff])
    (fun j hj => (edgeBody_spec hcs hS i j hi hj).frame (F := fun c => c.reg gT = cs.length)
      (fun c c' hfr h => by rw [hfr.reg gT (by decide), h]) |>.mono
      (fun c ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨⟨h1, h3, h4⟩, h2⟩) (fun c ⟨⟨h1, h3, h4⟩, h2⟩ => ⟨⟨h1, h2⟩, h3, h4⟩)
      le_rfl)
  have h2 : HTB S (.add ZeroCost.sBase ZeroCost.sBase gK)
      (fun c => (JInv g cs k i k c ∧ c.reg gT = cs.length) ∧ c.reg ZeroCost.sJ = k ∧ c.reg gK = k)
      (fun c => (EInv g cs k ((i + 1) * k) c ∧ c.reg ZeroCost.sBase = (i + 1) * k) ∧
        c.reg ZeroCost.sI = i ∧ c.reg gT = cs.length) 1 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨⟨hE, hB, hI⟩, hT⟩, _, hK⟩ => ?_
    have hE' : EInv g cs k ((i + 1) * k) c := by rw [show (i + 1) * k = i * k + k by ring]; exact hE
    refine ⟨⟨(show Indep [ZeroCost.sBase] (EInv g cs k ((i + 1) * k)) by
      indep [EInv, gE_iff, gA_iff]).setReg (by decide) _ hE', ?_⟩, ?_, ?_⟩
    · simp +decide [hB, hK]; ring
    · simp +decide [hI]
    · simp +decide [hT]
  refine (hl.seq h2).mono
    (fun c ⟨⟨hE, hB⟩, hI, hT⟩ => ⟨⟨⟨by simpa using hE, hB, hI⟩, hT⟩, hE.1.ga.rk⟩)
    (fun _ h => h) (by omega)

/-! ### Phase 4: the identifiers -/

/-- **The state after the edge pass**: the identifiers `EID[q] = eid cs q` of the occurrences
and the counts `CNT[r] = cntF cs (kt) r`, `gNE = |eList cs|`, the free address `bOFF g cs k`. -/
@[mk_iff] structure EdgesPost (g : Graph) (cs : List Cycle) (k : ℕ) (c : Config) : Prop where
  ga : GA g cs k c
  reid : c.reg gEID = bEID g cs k
  rcnt : c.reg gCNT = bCNT g cs k
  rne : c.reg gNE = (eList cs).length
  rfree : c.reg rFREE = bOFF g cs k
  mverts : Arr c.mem (bV g) (verts cs)
  meid : Tab c.mem (bEID g cs k) (k * cs.length) (eid cs)
  mcnt : Tab c.mem (bCNT g cs k) (k * cs.length) (cntF cs (k * cs.length))
  mzero : ZeroFrom c.mem (bOFF g cs k)
  rout : c.out = []

/-- The state at the call of `PairIds.pairIds`. -/
def IdsPre (g : Graph) (cs : List Cycle) (k : ℕ) (c : Config) : Prop :=
  PairIds.PIn (prs cs) (nV cs) c ∧ GA g cs k c ∧ c.reg rFREE = bPI g cs k ∧
    Arr c.mem (bV g) (verts cs) ∧ c.out = []

/-- The state after `PairIds.pairIds`. -/
def IdsMid (g : Graph) (cs : List Cycle) (k : ℕ) (c : Config) : Prop :=
  GA g cs k c ∧ c.reg PairIds.rID = bEID g cs k ∧ c.reg PairIds.rCT = bCNT g cs k ∧
    c.reg PairIds.rNE = (eList cs).length ∧ c.reg rFREE = bOFF g cs k ∧
    Arr c.mem (bV g) (verts cs) ∧ Tab c.mem (bEID g cs k) (k * cs.length) (eid cs) ∧
    Tab c.mem (bCNT g cs k) (k * cs.length) (cntF cs (k * cs.length)) ∧
    ZeroFrom c.mem (bOFF g cs k) ∧ c.out = []

/-- The call of `PairIds.pairIds` on the id pairs. -/
theorem pairIds_flow (hcs : ∀ c ∈ cs, IsCycle g k c) (hS : bOFF g cs k ≤ S) :
    HTB S PairIds.pairIds (IdsPre g cs k) (IdsMid g cs k)
      (PairIds.CI * (nV cs + k * cs.length + 1)) := by
  refine HTB.of_forall fun c₀ ⟨hIn, hga, hF, hV, ho⟩ => ?_
  have hS' : PairIds.idsEnd (nV cs) (prs cs).length (c₀.reg rFREE) ≤ S := by
    rw [length_prs hcs, hF, idsEnd_eq]; exact hS
  refine (PairIds.pairIds_spec (prs cs) (nV cs) prs_below c₀ hS').mono
    (fun c hc => ⟨hc ▸ hIn, hc⟩) (fun c ⟨hO, hfr⟩ => ?_) (by rw [length_prs hcs])
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
  rw [length_prs hcs, hF] at hrid hrct hfree
  rw [hF] at hsame
  have hfree' : c.reg rFREE = bOFF g cs k := hfree.trans (idsEnd_eq g cs k)
  refine ⟨?_, hrid, hrct, ?_, hfree', hV.of_below hsame (by
    rw [length_verts hcs]; have := layout_eqs g cs k; omega), ?_, ?_,
    by rw [← hfree']; exact hO.zero, by rw [hfr.out PairIds.pairIds_writes, ho]⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hga
    exact ⟨(hk _ (by decide)).trans h1, (hk _ (by decide)).trans h2, (hk _ (by decide)).trans h3,
      (hk _ (by decide)).trans h4, (hk _ (by decide)).trans h5⟩
  · rw [hO.ne, length_eraseDups_prs]
  · have := hO.id
    rw [hrid, eids_prs hcs] at this
    exact ZeroCost.tab_of_arr_map_range this
  · have := hO.ct
    rw [hrct, length_prs hcs] at this
    exact this.congr_fun fun e _ => count_eids_prs hcs e

/-- **Phase 4**: the id pairs of the occurrences, then their identifiers and counts. -/
theorem stepEdges_spec (hcs : ∀ c ∈ cs, IsCycle g k c) (hS : bOFF g cs k ≤ S) :
    HTB S stepEdges (DictPost g cs k) (EdgesPost g cs k)
      (cs.length * (k * 36 + 8) + PairIds.CI * (nV cs + k * cs.length + 1) + 24) := by
  have hl0 := layout_eqs g cs k
  have hSI : bPI g cs k ≤ S := by omega
  have h0 : HTB S (.seq (.seq (alloc gPU gKT) (alloc gPV gKT)) (.const ZeroCost.sBase 0))
      (DictPost g cs k) (fun c => (EInv g cs k (0 * k) c ∧ c.reg ZeroCost.sBase = 0 * k) ∧
        c.reg gT = cs.length) 7 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c hP => ?_
    have hga : GA g cs k (run (.seq (.seq (alloc gPU gKT) (alloc gPV gKT))
        (.const ZeroCost.sBase 0)) c) :=
      (show RegIndep [rT, gPU, rFREE, gPV, ZeroCost.sBase] (GA g cs k) by indep [gA_iff]).run_of_sub
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
  have hl := HTB.forUpC (i := ZeroCost.sI) (n := gT) (N := cs.length) (body := edgeRow)
    (fun i c => EInv g cs k (i * k) c ∧ c.reg ZeroCost.sBase = i * k) (k * 36 + 4) (by decide)
    (by decide) (by decide) (fun j => by indep [EInv, gE_iff, gA_iff])
    (fun i hi => edgeRow_spec hcs hSI i hi)
  have h1 : HTB S idsArgs (fun c => (EInv g cs k (cs.length * k) c ∧
        c.reg ZeroCost.sBase = cs.length * k) ∧ c.reg ZeroCost.sI = cs.length ∧
        c.reg gT = cs.length) (IdsPre g cs k) 8 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨⟨hG, hM, ho⟩, _⟩, _, _⟩ => ?_
    rw [Nat.mul_comm] at hM
    have hAg : Agree [rT, PairIds.rPU, PairIds.rPV, PairIds.rPL, PairIds.rPN] c (run idsArgs c) :=
      agree_run (by decide) rfl rfl (by decide) c
    have hpu : (run idsArgs c).reg PairIds.rPU = bPU g cs k := by
      simp +decide [idsArgs, run_mov, hG.rpu]
    have hpv : (run idsArgs c).reg PairIds.rPV = bPV g cs k := by
      simp +decide [idsArgs, run_mov, hG.rpv]
    have hF : (run idsArgs c).reg rFREE = bPI g cs k := (hAg.reg _ (by decide)).trans hG.rfree
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, (show RegIndep [rT, PairIds.rPU, PairIds.rPV, PairIds.rPL,
      PairIds.rPN] (GA g cs k) by indep [gA_iff]).indep c _ hAg hG.ga, hF,
      by rw [hAg.mem]; exact hM.mverts, by rw [hAg.out]; exact ho⟩
    · simp +decide [idsArgs, run_mov, hG.ga.rkt, length_prs hcs]
    · simp +decide [idsArgs, run_mov, hG.rn]
    · rw [hpu, hAg.mem, ← map_fst_prs hcs]; exact hM.mpu.toArr
    · rw [hpv, hAg.mem, ← map_snd_prs hcs]; exact hM.mpv.toArr
    · rw [hpu, hpv, hF, length_prs hcs]; exact ⟨by omega, by omega⟩
    · rw [hF, hAg.mem]; exact hM.mzero
  have h3 : HTB S idsBack (IdsMid g cs k) (EdgesPost g cs k) 6 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide)
      fun c ⟨hga, hid, hct, hne, hF, hV, hE, hC, hZ, ho⟩ => ?_
    have hAg : Agree [rT, gEID, gCNT, gNE] c (run idsBack c) :=
      agree_run (by decide) rfl rfl (by decide) c
    refine ⟨(show RegIndep [rT, gEID, gCNT, gNE] (GA g cs k) by indep [gA_iff]).indep c _ hAg hga,
      ?_, ?_, ?_, (hAg.reg _ (by decide)).trans hF, by rw [hAg.mem]; exact hV,
      by rw [hAg.mem]; exact hE, by rw [hAg.mem]; exact hC, by rw [hAg.mem]; exact hZ,
      by rw [hAg.out]; exact ho⟩
    · simp +decide [idsBack, run_mov, hid]
    · simp +decide [idsBack, run_mov, hct]
    · simp +decide [idsBack, run_mov, hne]
  refine HTB.assoc (HTB.assoc ((h0.seq (hl.seq (h1.seq ((pairIds_flow hcs hS).seq
    h3)))).weaken ?_))
  have : cs.length * (k * 36 + 4 + 4) = cs.length * (k * 36 + 8) := by ring
  omega

/-! ### The edge pass -/

/-- **The edge pass** (phases 1–4), from the input to the identifiers and counts, within
`300 kt + 15t + 160` steps and the addresses below `S ≥ bOFF g cs k`. -/
theorem edgePhase_spec (hcs : ∀ c ∈ cs, IsCycle g k c) (hS : bOFF g cs k ≤ S) :
    HTB S edgePhase (fun c => c = initial (flowInput g cs k)) (EdgesPost g cs k)
      (300 * (k * cs.length) + 15 * cs.length + 160) := by
  have hl := layout_eqs g cs k
  refine ((stepInit_spec hcs (by omega)).seq ((stepMax_spec hcs (by omega)).seq
    ((stepDict_spec hcs (by omega)).seq (stepEdges_spec hcs hS)))).weaken ?_
  have hN := nV_le hcs
  have e1 : cs.length * (k * 36 + 8) = 36 * (k * cs.length) + 8 * cs.length := by ring
  have e2 : k * cs.length * 12 = 12 * (k * cs.length) := by ring
  have e3 : k * cs.length * 16 = 16 * (k * cs.length) := by ring
  simp only [PairIds.CI, PairIds.CL, PairIds.CR]
  omega

/-- **The memory of the edge pass is linear** in `labelBound g + kt + m + 1` (the label
dictionary has `maxV cs + 1 ≤ labelBound g` cells). -/
theorem bOFF_le (hcs : ∀ c ∈ cs, IsCycle g k c) :
    bOFF g cs k ≤ 11 * (labelBound g + k * cs.length + g.length + 1) := by
  have hl := layout_eqs g cs k
  have hN := nV_le hcs
  have hM := maxV_lt_labelBound hcs
  omega

end phase4

end STACS2027.Runtimes.Flow
