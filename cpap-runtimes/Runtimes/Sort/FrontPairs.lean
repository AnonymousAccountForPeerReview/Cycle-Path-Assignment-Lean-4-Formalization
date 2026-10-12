module

public import Runtimes.Sort.FrontProg
import Mathlib.Tactic

/-!
# The sorting front end: the ordered id pairs of the occurrences

Phase 3 of `front` (`fPairs_spec`): for every occurrence `q = ik + j` (in the order of the
cycles), the machine reads the labels `x = verts[q]`, `y = verts[ik + next k j]` of the ends of
its edge `e = occs[q]` and their vertex identifiers `ID[q]`, `ID[ik + next k j]` (phase 2),
orders the two ids by **comparing the labels** (`pOrd`: swap if `y < x`), and stores
`idPr e = (idv e.1, idv e.2)` as `(PU[q], PV[q])` — Corollary 5's id pairs `prs g k`, without a
dictionary indexed by labels.
-/

@[expose] public section

namespace STACS2027.Runtimes.Sort

open STACS2027 STACS2027.RAM STACS2027.RAM.R0 STACS2027.Runtimes.ZeroCost
open scoped List

variable {S : ℕ}

/-! ### The state of the pair pass -/

/-- The registers fixed during the pair pass. -/
@[mk_iff] structure FG (g : Graph) (k F : ℕ) (c : Config) : Prop where
  ga : GA g k c
  rid : c.reg fID = fIDb g k F
  rn : c.reg ZeroCost.gN = nV g k
  rpu : c.reg gPU = fPU g k F
  rpv : c.reg gPV = fPV g k F
  rfree : c.reg rFREE = fPI g k F

theorem FG.regIndep (g : Graph) (k F : ℕ) : RegIndep WE (FG g k F) := by indep [fG_iff, gA_iff]

/-- The memory of the pair pass: the id pairs of the first `q` occurrences are stored. -/
structure FMem (g : Graph) (k F : ℕ) (m₀ : ℕ → ℕ) (q : ℕ) (m : ℕ → ℕ) : Prop where
  mverts : Arr m (bV g) (verts g k)
  mid : Arr m (fIDb g k F) ((verts g k).map (idv g k))
  mpu : Tab m (fPU g k F) q fun q' => idv g k ((occs g k).getD q' (0, 0)).1
  mpv : Tab m (fPV g k F) q fun q' => idv g k ((occs g k).getD q' (0, 0)).2
  mzero : ZeroFrom m (fPI g k F)
  same : SameOn (· < F) m₀ m

/-- The state of the pair pass after `q` occurrences. -/
def FInv (g : Graph) (k F : ℕ) (m₀ : ℕ → ℕ) (q : ℕ) (c : Config) : Prop :=
  FG g k F c ∧ FMem g k F m₀ q c.mem

/-- Recording the id pair of occurrence `q`: two stores. -/
theorem FMem.put {g : Graph} {k F q : ℕ} {m₀ m : ℕ → ℕ} (h : FMem g k F m₀ q m)
    (hvb : bV g + fL g k ≤ F) (hq : q < fL g k) :
    FMem g k F m₀ (q + 1) (upd (upd m (fPU g k F + q) (idv g k ((occs g k).getD q (0, 0)).1))
      (fPV g k F + q) (idv g k ((occs g k).getD q (0, 0)).2)) := by
  have hlv := length_verts' g k
  have e1 : fIDb g k F = F + 3 * fL g k := rfl
  have e2 : fPU g k F = F + 5 * fL g k := rfl
  have e3 : fPV g k F = F + 6 * fL g k := rfl
  have e4 : fPI g k F = F + 7 * fL g k := rfl
  refine ⟨(h.mverts.upd_of_disjoint (by omega)).upd_of_disjoint (by omega),
    (h.mid.upd_of_disjoint (by simp only [List.length_map]; omega)).upd_of_disjoint
      (by simp only [List.length_map]; omega),
    ((h.mpu.upd_of_disjoint (by omega)).snoc (by simp)).upd_of_disjoint (by omega),
    (h.mpv.upd_of_disjoint (by omega)).upd_of_disjoint (by omega) |>.snoc (by simp),
    (h.mzero.upd (by omega)).upd (by omega),
    (h.same.upd_of_ge (by omega) _).upd_of_ge (by omega) _⟩

/-! ### Reading an occurrence -/

/-- The ids of the ends, ordered by their labels `sX`, `sY`. -/
theorem pIdOrd_run (c : Config) :
    (run (.seq pIds pOrd) c).reg sU = (if c.reg sY < c.reg sX then c.mem (c.reg fID + c.reg sP)
      else c.mem (c.reg fID + c.reg sQ)) ∧
    (run (.seq pIds pOrd) c).reg sV = (if c.reg sY < c.reg sX then c.mem (c.reg fID + c.reg sQ)
      else c.mem (c.reg fID + c.reg sP)) ∧
    Agree [sU, sV, rT] c (run (.seq pIds pOrd) c) := by
  refine ⟨?_, ?_, agree_run (by decide) rfl rfl (by decide) c⟩ <;>
  · simp +decide only [pIds, pOrd, run_seq', run_ld, run_ifLt, run_swap (show sU ≠ sV by decide),
      run_skip, setReg_reg, setReg_mem, ↓reduceIte, config_ite_reg]

/-- **Reading occurrence `q = ik + j`**: `sQ = q`, and `sU`, `sV` are the ids of the ends of its
edge, ordered by label (`idPr`); the accesses are in the cycle part of the input and `ID`. -/
theorem pRead_run {g : Graph} {k F i j q' : ℕ} {m₀ : ℕ → ℕ} {c : Config}
    (hS : fPI g k F ≤ S) (hvb : bV g + fL g k ≤ F) (hi : i < (cycles g k).length) (hj : j < k)
    (hG : FG g k F c) (hM : FMem g k F m₀ q' c.mem) (hJ : c.reg sJ = j)
    (hB : c.reg sBase = i * k) :
    (run pRead c).reg sQ = i * k + j ∧
      (run pRead c).reg sU = idv g k ((occs g k).getD (i * k + j) (0, 0)).1 ∧
      (run pRead c).reg sV = idv g k ((occs g k).getD (i * k + j) (0, 0)).2 ∧
      Agree WR c (run pRead c) ∧ AddrOK S pRead c := by
  have hq := occ_lt hi hj
  have hk : 0 < k := by omega
  have hq2 : i * k + next k j < k * (cycles g k).length := occ_lt hi (next_lt hk)
  have hlv := length_verts g k
  have hfl : fL g k = k * (cycles g k).length := rfl
  have e1 : fIDb g k F = F + 3 * fL g k := rfl
  have e4 : fPI g k F = F + 7 * fL g k := rfl
  set x := (verts g k).getD (i * k + j) 0 with hxd
  set y := (verts g k).getD (i * k + next k j) 0 with hyd
  have he : (occs g k).getD (i * k + j) (0, 0) = edge x y := occs_getD hi hj
  have hx : c.mem (bV g + (i * k + j)) = x := hM.mverts.getD (by rw [length_verts]; exact hq)
  have hy : c.mem (bV g + (i * k + next k j)) = y :=
    hM.mverts.getD (by rw [length_verts]; exact hq2)
  have hix : c.mem (fIDb g k F + (i * k + j)) = idv g k x := by
    rw [hM.mid.get (i := i * k + j) (by simp only [List.length_map]; omega), List.getElem_map,
      hxd, getD_eq_getElem' (by omega)]
  have hiy : c.mem (fIDb g k F + (i * k + next k j)) = idv g k y := by
    rw [hM.mid.get (i := i * k + next k j) (by simp only [List.length_map]; omega),
      List.getElem_map, hyd, getD_eq_getElem' (by omega)]
  obtain ⟨h1q, h1x, a1⟩ := edgeA_run c
  obtain ⟨h2p, a2⟩ := nextPos_run (c := run edgeA c) (base := i * k)
    (by rw [a1.reg sJ (by decide), hJ]) (by rw [a1.reg gK (by decide), hG.ga.rk])
    (by rw [h1q, hB, hJ]) (by rw [a1.reg sBase (by decide), hB])
  obtain ⟨h3y, a3⟩ := ldY_run (run nextPos (run edgeA c))
  set c₃ := run (ld sY gV sP) (run nextPos (run edgeA c)) with hc₃
  obtain ⟨h4u, h4v, a4⟩ := pIdOrd_run c₃
  have a13 : Agree WR c c₃ :=
    ((a1.mono (by decide)).trans (a2.mono (by decide))).trans (a3.mono (by decide))
  have e3x : c₃.reg sX = x := by
    rw [hc₃, a3.reg sX (by decide), a2.reg sX (by decide), h1x, hG.ga.rv, hB, hJ, hx]
  have e3y : c₃.reg sY = y := by
    rw [hc₃, h3y, a2.mem, a1.mem, a2.reg gV (by decide), a1.reg gV (by decide), h2p, hG.ga.rv, hy]
  have e3q : c₃.reg sQ = i * k + j := by
    rw [hc₃, a3.reg sQ (by decide), a2.reg sQ (by decide), h1q, hB, hJ]
  have e3p : c₃.reg sP = i * k + next k j := by rw [hc₃, a3.reg sP (by decide), h2p]
  have e3i : c₃.reg fID = fIDb g k F := by rw [a13.reg fID (by decide), hG.rid]
  have e3m : c₃.mem = c.mem := a13.mem
  have hrun : run pRead c = run (.seq pIds pOrd) c₃ := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun, a4.reg sQ (by decide), e3q]
  · rw [hrun, h4u, e3x, e3y, e3q, e3p, e3i, e3m, hix, hiy, he]
    unfold edge
    split_ifs with h
    · simp [Nat.min_eq_right h.le]
    · simp [Nat.min_eq_left (Nat.le_of_not_lt h)]
  · rw [hrun, h4v, e3x, e3y, e3q, e3p, e3i, e3m, hix, hiy, he]
    unfold edge
    split_ifs with h
    · simp [Nat.max_eq_left h.le]
    · simp [Nat.max_eq_right (Nat.le_of_not_lt h)]
  · exact a13.trans (a4.mono (by decide))
  · refine AddrOK.seq (by addr_ok [edgeA, hG.ga.rv, hB, hJ]) (AddrOK.seq (AddrOK.of_memFree rfl)
      (AddrOK.seq ?_ (AddrOK.seq ?_ (AddrOK.of_memFree rfl))))
    · rw [addrOK_ld, a2.reg gV (by decide), a1.reg gV (by decide), h2p, hG.ga.rv]; omega
    · show AddrOK S pIds c₃
      simp +decide only [pIds, addrOK_seq, addrOK_ld, run_ld, setReg_reg, ↓reduceIte, e3q, e3p, e3i]
      constructor <;> omega

/-! ### The pair pass -/

/-- The invariant of the inner loop (cycle `i`) after `j` positions. -/
def PJInv (g : Graph) (k F : ℕ) (m₀ : ℕ → ℕ) (i j : ℕ) (c : Config) : Prop :=
  FInv g k F m₀ (i * k + j) c ∧ c.reg sBase = i * k ∧ c.reg sI = i

/-- One occurrence of the pair pass: its ordered id pair into `PU`, `PV`. -/
theorem pBody_spec (g : Graph) (k F : ℕ) (m₀ : ℕ → ℕ) (hS : fPI g k F ≤ S)
    (hvb : bV g + fL g k ≤ F) (i j : ℕ) (hi : i < (cycles g k).length) (hj : j < k) :
    HTB S pBody (fun c => PJInv g k F m₀ i j c ∧ c.reg sJ = j ∧ c.reg gK = k)
      (fun c => PJInv g k F m₀ i (j + 1) c ∧ c.reg sJ = j ∧ c.reg gK = k) 32 := by
  refine HTB.run_le (by decide) (by decide) fun c hc => ?_
  obtain ⟨⟨⟨hG, hM⟩, hB, hI⟩, hJ, hK⟩ := hc
  have hq := occ_lt hi hj
  have hfl : fL g k = k * (cycles g k).length := rfl
  have e2 : fPU g k F = F + 5 * fL g k := rfl
  have e3 : fPV g k F = F + 6 * fL g k := rfl
  have e4 : fPI g k F = F + 7 * fL g k := rfl
  obtain ⟨r1q, r1u, r1v, a1, A1⟩ := pRead_run (S := S) hS hvb hi hj hG hM hJ hB
  have hG1 : FG g k F (run pRead c) := (FG.regIndep g k F).indep.mono (by decide) c _ a1 hG
  have hfin : run pBody c = run edgePut (run pRead c) := rfl
  have hmem : (run pBody c).mem = upd (upd c.mem (fPU g k F + (i * k + j))
      (idv g k ((occs g k).getD (i * k + j) (0, 0)).1)) (fPV g k F + (i * k + j))
      (idv g k ((occs g k).getD (i * k + j) (0, 0)).2) := by
    rw [hfin]
    simp +decide only [edgePut, run_seq', run_st (show sU ≠ rT by decide),
      run_st (show sV ≠ rT by decide), setReg_mem, setMem_mem_upd, setReg_reg, setMem_reg,
      ↓reduceIte, hG1.rpu, hG1.rpv, r1q, r1u, r1v, a1.mem]
  have hreg : ∀ r, r ∉ [rT, sQ, sX, sP, sY, sU, sV] → (run pBody c).reg r = c.reg r := by
    intro r hr
    rw [hfin, run_reg_of_not_mem (s := edgePut) (by decide) (fun h => hr (by
      have : ∀ x ∈ wregs edgePut, x ∈ [rT, sQ, sX, sP, sY, sU, sV] := by decide
      exact this r h)), a1.reg r (not_mem_of_sub hr (by decide))]
  refine ⟨AddrOK.seq A1 (by addr_ok [edgePut, hG1.rpu, hG1.rpv, r1q]),
    ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩⟩
  · exact ((FG.regIndep g k F).mono (by decide)) _ _ hreg hG
  · rw [hmem, ← Nat.add_assoc]; exact hM.put hvb hq
  · rw [hreg sBase (by decide), hB]
  · rw [hreg sI (by decide), hI]
  · rw [hreg sJ (by decide), hJ]
  · rw [hreg gK (by decide), hK]

/-- One cycle of the pair pass. -/
theorem pRow_spec (g : Graph) (k F : ℕ) (m₀ : ℕ → ℕ) (hS : fPI g k F ≤ S)
    (hvb : bV g + fL g k ≤ F) (i : ℕ) (hi : i < (cycles g k).length) :
    HTB S pRow (fun c => (FInv g k F m₀ (i * k) c ∧ c.reg sBase = i * k) ∧ c.reg sI = i ∧
        c.reg gT = (cycles g k).length)
      (fun c => (FInv g k F m₀ ((i + 1) * k) c ∧ c.reg sBase = (i + 1) * k) ∧ c.reg sI = i ∧
        c.reg gT = (cycles g k).length) (k * 36 + 4) := by
  have hl := HTB.forUpC (i := sJ) (n := gK) (N := k) (body := pBody)
    (fun j c => PJInv g k F m₀ i j c ∧ c.reg gT = (cycles g k).length) 32 (by decide) (by decide)
    (by decide) (fun j => by indep [PJInv, FInv, fG_iff, gA_iff])
    (fun j hj => (pBody_spec g k F m₀ hS hvb i j hi hj).frame
      (F := fun c => c.reg gT = (cycles g k).length)
      (fun c c' hfr h => by rw [hfr.reg gT (by decide), h]) |>.mono
      (fun c ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨⟨h1, h3, h4⟩, h2⟩)
      (fun c ⟨⟨h1, h3, h4⟩, h2⟩ => ⟨⟨h1, h2⟩, h3, h4⟩)
      le_rfl)
  have h2 : HTB S (.add sBase sBase gK)
      (fun c => (PJInv g k F m₀ i k c ∧ c.reg gT = (cycles g k).length) ∧ c.reg sJ = k ∧
        c.reg gK = k)
      (fun c => (FInv g k F m₀ ((i + 1) * k) c ∧ c.reg sBase = (i + 1) * k) ∧ c.reg sI = i ∧
        c.reg gT = (cycles g k).length) 1 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨⟨hE, hB, hI⟩, hT⟩, _, hK⟩ => ?_
    have hE' : FInv g k F m₀ ((i + 1) * k) c := by
      rw [show (i + 1) * k = i * k + k by ring]; exact hE
    refine ⟨⟨(show Indep [sBase] (FInv g k F m₀ ((i + 1) * k)) by
      indep [FInv, fG_iff, gA_iff]).setReg (by decide) _ hE', ?_⟩, ?_, ?_⟩
    · simp +decide [hB, hK]; ring
    · simp +decide [hI]
    · simp +decide [hT]
  refine (hl.seq h2).mono
    (fun c ⟨⟨hE, hB⟩, hI, hT⟩ => ⟨⟨⟨by simpa using hE, hB, hI⟩, hT⟩, hE.1.ga.rk⟩)
    (fun _ h => h) (by omega)

/-- The state after the pair pass. -/
structure PairsPost (g : Graph) (k F : ℕ) (m₀ : ℕ → ℕ) (c : Config) : Prop where
  vb : bV g + fL g k ≤ F
  pin : PairIds.PIn (prs g k) (nV g k) c
  ga : GA g k c
  rfree : c.reg rFREE = fPI g k F
  mverts : Arr c.mem (bV g) (verts g k)
  same : SameOn (· < F) m₀ c.mem

/-- **Phase 3**: the ordered id pairs of the occurrences. -/
theorem fPairs_spec (g : Graph) (k F : ℕ) (m₀ : ℕ → ℕ) (hS : fPI g k F ≤ S) :
    HTB S (.seq fPairs idsArgs) (VidsPost g k F m₀) (PairsPost g k F m₀)
      (7 + ((cycles g k).length * (k * 36 + 4 + 4) + 3) + 8) := by
  refine HTB.pre_fact (p := bV g + fL g k ≤ F) (fun c h => h.vb) fun hvb => ?_
  have hfl : fL g k = k * (cycles g k).length := rfl
  have e2 : fPU g k F = F + 5 * fL g k := rfl
  have e3 : fPV g k F = F + 6 * fL g k := rfl
  have e4 : fPI g k F = F + 7 * fL g k := rfl
  have h0 : HTB S (.seq (.seq (alloc gPU gKT) (alloc gPV gKT)) (.const sBase 0))
      (VidsPost g k F m₀) (fun c => (FInv g k F m₀ (0 * k) c ∧ c.reg sBase = 0 * k) ∧
        c.reg gT = (cycles g k).length) 7 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c hP => ?_
    have hga : GA g k (run (.seq (.seq (alloc gPU gKT) (alloc gPV gKT)) (.const sBase 0)) c) :=
      (show RegIndep [rT, gPU, rFREE, gPV, sBase] (GA g k) by indep [gA_iff]).run_of_sub
        (by decide) (by decide) hP.ga
    simp only [Nat.zero_mul]
    refine ⟨⟨⟨⟨hga, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    all_goals simp +decide only [run_seq',
      run_alloc (show gKT ≠ rT by decide) (show gPU ≠ gKT by decide),
      run_alloc (show gKT ≠ rT by decide) (show gPV ≠ gKT by decide), run_const, setReg_reg,
      setReg_mem, ↓reduceIte, hP.rid, hP.rn, hP.rfree, hP.ga.rkt, hP.ga.rt]
    · simp only [fPU]
    · simp only [fPV, fL]; omega
    · simp only [fPI, fL]; omega
    · exact ⟨hP.mverts, hP.mid, by simp, by simp, hP.zero.mono (by rw [hP.rfree]; omega), hP.same⟩
  have hl := HTB.forUpC (i := sI) (n := gT) (N := (cycles g k).length) (body := pRow)
    (fun i c => FInv g k F m₀ (i * k) c ∧ c.reg sBase = i * k) (k * 36 + 4) (by decide) (by decide)
    (by decide) (fun j => by indep [FInv, fG_iff, gA_iff])
    (fun i hi => pRow_spec g k F m₀ hS hvb i hi)
  have h1 : HTB S idsArgs (fun c => (FInv g k F m₀ ((cycles g k).length * k) c ∧
        c.reg sBase = (cycles g k).length * k) ∧ c.reg sI = (cycles g k).length ∧
        c.reg gT = (cycles g k).length) (PairsPost g k F m₀) 8 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨⟨hG, hM⟩, _⟩, _, _⟩ => ?_
    rw [Nat.mul_comm] at hM
    have hAg : Agree [rT, PairIds.rPU, PairIds.rPV, PairIds.rPL, PairIds.rPN] c (run idsArgs c) :=
      agree_run (by decide) rfl rfl (by decide) c
    have hpu : (run idsArgs c).reg PairIds.rPU = fPU g k F := by
      simp +decide [idsArgs, run_mov, hG.rpu]
    have hpv : (run idsArgs c).reg PairIds.rPV = fPV g k F := by
      simp +decide [idsArgs, run_mov, hG.rpv]
    have hF : (run idsArgs c).reg rFREE = fPI g k F := (hAg.reg _ (by decide)).trans hG.rfree
    refine ⟨hvb, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, (show RegIndep [rT, PairIds.rPU, PairIds.rPV,
      PairIds.rPL, PairIds.rPN] (GA g k) by indep [gA_iff]).indep c _ hAg hG.ga, hF,
      by rw [hAg.mem]; exact hM.mverts, by rw [hAg.mem]; exact hM.same⟩
    · simp +decide [idsArgs, run_mov, hG.ga.rkt, length_prs]
    · simp +decide [idsArgs, run_mov, hG.rn]
    · rw [hpu, hAg.mem, ← map_fst_prs]; exact hM.mpu.toArr
    · rw [hpv, hAg.mem, ← map_snd_prs]; exact hM.mpv.toArr
    · rw [hpu, hpv, hF, length_prs]; exact ⟨by omega, by omega⟩
    · rw [hF, hAg.mem]; exact hM.mzero
  exact ((h0.seq hl).assoc.assoc.seq h1).weaken (by omega)

end STACS2027.Runtimes.Sort
