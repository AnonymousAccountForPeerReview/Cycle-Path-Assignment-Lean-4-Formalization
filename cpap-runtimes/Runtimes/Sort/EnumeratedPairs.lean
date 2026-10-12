module

public import Runtimes.Sort.EnumeratedProg
import Mathlib.Tactic

/-!
# Sorting enumerated cycle lists

The edge-occurrence pair pass for an arbitrary list of simple cycles.
These are the existing sorting-front-end proofs with the canonical cycle enumeration
replaced by a supplied list and an explicit proof that every entry is a simple cycle.
No step of the program depends on the order of that list or on a vertex-label dictionary.
-/

@[expose] public section

namespace STACS2027.Runtimes.EnumeratedSort

open STACS2027 STACS2027.RAM STACS2027.RAM.R0 STACS2027.Runtimes.ZeroCost
open STACS2027.Runtimes.Sort
open scoped List

variable {S : ℕ}

@[mk_iff] structure FG (g : Graph) (cs : List Cycle) (k F : ℕ) (c : Config) : Prop where
  ga : Flow.GA g cs k c
  rid : c.reg fID = fIDb g cs k F
  rn : c.reg ZeroCost.gN = Flow.nV cs
  rpu : c.reg gPU = fPU g cs k F
  rpv : c.reg gPV = fPV g cs k F
  rfree : c.reg rFREE = fPI g cs k F

theorem FG.regIndep (g : Graph) (cs : List Cycle) (k : ℕ) (_hcs : ∀ c ∈ cs, IsCycle g k c) (F : ℕ) : RegIndep WE (FG g cs k F) := by indep [fG_iff, Flow.gA_iff]

structure FMem (g : Graph) (cs : List Cycle) (k F : ℕ) (m₀ : ℕ → ℕ) (q : ℕ) (m : ℕ → ℕ) : Prop where
  mverts : Arr m (bV g) (Flow.verts cs)
  mid : Arr m (fIDb g cs k F) ((Flow.verts cs).map (Flow.idv cs))
  mpu : Tab m (fPU g cs k F) q fun q' => Flow.idv cs ((Flow.occs cs).getD q' (0, 0)).1
  mpv : Tab m (fPV g cs k F) q fun q' => Flow.idv cs ((Flow.occs cs).getD q' (0, 0)).2
  mzero : ZeroFrom m (fPI g cs k F)
  same : SameOn (· < F) m₀ m

def FInv (g : Graph) (cs : List Cycle) (k F : ℕ) (m₀ : ℕ → ℕ) (q : ℕ) (c : Config) : Prop :=
  FG g cs k F c ∧ FMem g cs k F m₀ q c.mem

theorem FMem.put {g : Graph} {cs : List Cycle} {k F q : ℕ} (hcs : ∀ c ∈ cs, IsCycle g k c) {m₀ m : ℕ → ℕ} (h : FMem g cs k F m₀ q m)
    (hvb : bV g + fL g cs k ≤ F) (hq : q < fL g cs k) :
    FMem g cs k F m₀ (q + 1) (upd (upd m (fPU g cs k F + q) (Flow.idv cs ((Flow.occs cs).getD q (0, 0)).1))
      (fPV g cs k F + q) (Flow.idv cs ((Flow.occs cs).getD q (0, 0)).2)) := by
  have hlv := length_verts' g cs k hcs
  have e1 : fIDb g cs k F = F + 3 * fL g cs k := rfl
  have e2 : fPU g cs k F = F + 5 * fL g cs k := rfl
  have e3 : fPV g cs k F = F + 6 * fL g cs k := rfl
  have e4 : fPI g cs k F = F + 7 * fL g cs k := rfl
  refine ⟨(h.mverts.upd_of_disjoint (by omega)).upd_of_disjoint (by omega),
    (h.mid.upd_of_disjoint (by simp only [List.length_map]; omega)).upd_of_disjoint
      (by simp only [List.length_map]; omega),
    ((h.mpu.upd_of_disjoint (by omega)).snoc (by simp)).upd_of_disjoint (by omega),
    (h.mpv.upd_of_disjoint (by omega)).upd_of_disjoint (by omega) |>.snoc (by simp),
    (h.mzero.upd (by omega)).upd (by omega),
    (h.same.upd_of_ge (by omega) _).upd_of_ge (by omega) _⟩

theorem pIdOrd_run (c : Config) :
    (run (.seq pIds pOrd) c).reg sU = (if c.reg sY < c.reg sX then c.mem (c.reg fID + c.reg sP)
      else c.mem (c.reg fID + c.reg sQ)) ∧
    (run (.seq pIds pOrd) c).reg sV = (if c.reg sY < c.reg sX then c.mem (c.reg fID + c.reg sQ)
      else c.mem (c.reg fID + c.reg sP)) ∧
    Agree [sU, sV, rT] c (run (.seq pIds pOrd) c) := by
  refine ⟨?_, ?_, agree_run (by decide) rfl rfl (by decide) c⟩ <;>
  · simp +decide only [pIds, pOrd, run_seq', run_ld, run_ifLt, run_swap (show sU ≠ sV by decide),
      run_skip, setReg_reg, setReg_mem, ↓reduceIte, config_ite_reg]

theorem pRead_run {g : Graph} {cs : List Cycle} {k F i j q' : ℕ} (hcs : ∀ c ∈ cs, IsCycle g k c) {m₀ : ℕ → ℕ} {c : Config}
    (hS : fPI g cs k F ≤ S) (hvb : bV g + fL g cs k ≤ F) (hi : i < (cs).length) (hj : j < k)
    (hG : FG g cs k F c) (hM : FMem g cs k F m₀ q' c.mem) (hJ : c.reg sJ = j)
    (hB : c.reg sBase = i * k) :
    (run pRead c).reg sQ = i * k + j ∧
      (run pRead c).reg sU = Flow.idv cs ((Flow.occs cs).getD (i * k + j) (0, 0)).1 ∧
      (run pRead c).reg sV = Flow.idv cs ((Flow.occs cs).getD (i * k + j) (0, 0)).2 ∧
      Agree WR c (run pRead c) ∧ AddrOK S pRead c := by
  have hbV : Flow.bV g = bV g := rfl
  have hq := occ_lt hi hj
  have hk : 0 < k := by omega
  have hq2 : i * k + next k j < k * (cs).length := occ_lt hi (next_lt hk)
  have hlv := Flow.length_verts hcs
  have hfl : fL g cs k = k * (cs).length := rfl
  have e1 : fIDb g cs k F = F + 3 * fL g cs k := rfl
  have e4 : fPI g cs k F = F + 7 * fL g cs k := rfl
  set x := (Flow.verts cs).getD (i * k + j) 0 with hxd
  set y := (Flow.verts cs).getD (i * k + next k j) 0 with hyd
  have he : (Flow.occs cs).getD (i * k + j) (0, 0) = edge x y := Flow.occs_getD hcs hi hj
  have hx : c.mem (bV g + (i * k + j)) = x := hM.mverts.getD (by rw [(Flow.length_verts hcs)]; exact hq)
  have hy : c.mem (bV g + (i * k + next k j)) = y :=
    hM.mverts.getD (by rw [(Flow.length_verts hcs)]; exact hq2)
  have hix : c.mem (fIDb g cs k F + (i * k + j)) = Flow.idv cs x := by
    rw [hM.mid.get (i := i * k + j) (by simp only [List.length_map]; omega), List.getElem_map,
      hxd, getD_eq_getElem' (by omega)]
  have hiy : c.mem (fIDb g cs k F + (i * k + next k j)) = Flow.idv cs y := by
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
    rw [hc₃, a3.reg sX (by decide), a2.reg sX (by decide), h1x, hG.ga.rv, hbV, hB, hJ, hx]
  have e3y : c₃.reg sY = y := by
    rw [hc₃, h3y, a2.mem, a1.mem, a2.reg gV (by decide), a1.reg gV (by decide), h2p, hG.ga.rv, hbV, hy]
  have e3q : c₃.reg sQ = i * k + j := by
    rw [hc₃, a3.reg sQ (by decide), a2.reg sQ (by decide), h1q, hB, hJ]
  have e3p : c₃.reg sP = i * k + next k j := by rw [hc₃, a3.reg sP (by decide), h2p]
  have e3i : c₃.reg fID = fIDb g cs k F := by rw [a13.reg fID (by decide), hG.rid]
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
  · refine AddrOK.seq (by addr_ok [edgeA, hG.ga.rv, hbV, hB, hJ]) (AddrOK.seq (AddrOK.of_memFree rfl)
      (AddrOK.seq ?_ (AddrOK.seq ?_ (AddrOK.of_memFree rfl))))
    · rw [addrOK_ld, a2.reg gV (by decide), a1.reg gV (by decide), h2p, hG.ga.rv, hbV]; omega
    · show AddrOK S pIds c₃
      simp +decide only [pIds, addrOK_seq, addrOK_ld, run_ld, setReg_reg, ↓reduceIte, e3q, e3p, e3i]
      constructor <;> omega

def PJInv (g : Graph) (cs : List Cycle) (k F : ℕ) (m₀ : ℕ → ℕ) (i j : ℕ) (c : Config) : Prop :=
  FInv g cs k F m₀ (i * k + j) c ∧ c.reg sBase = i * k ∧ c.reg sI = i

theorem pBody_spec (g : Graph) (cs : List Cycle) (k : ℕ) (hcs : ∀ c ∈ cs, IsCycle g k c) (F : ℕ) (m₀ : ℕ → ℕ) (hS : fPI g cs k F ≤ S)
    (hvb : bV g + fL g cs k ≤ F) (i j : ℕ) (hi : i < (cs).length) (hj : j < k) :
    HTB S pBody (fun c => PJInv g cs k F m₀ i j c ∧ c.reg sJ = j ∧ c.reg gK = k)
      (fun c => PJInv g cs k F m₀ i (j + 1) c ∧ c.reg sJ = j ∧ c.reg gK = k) 32 := by
  refine HTB.run_le (by decide) (by decide) fun c hc => ?_
  obtain ⟨⟨⟨hG, hM⟩, hB, hI⟩, hJ, hK⟩ := hc
  have hq := occ_lt hi hj
  have hfl : fL g cs k = k * (cs).length := rfl
  have e2 : fPU g cs k F = F + 5 * fL g cs k := rfl
  have e3 : fPV g cs k F = F + 6 * fL g cs k := rfl
  have e4 : fPI g cs k F = F + 7 * fL g cs k := rfl
  obtain ⟨r1q, r1u, r1v, a1, A1⟩ := pRead_run (S := S) hcs hS hvb hi hj hG hM hJ hB
  have hG1 : FG g cs k F (run pRead c) := (FG.regIndep g cs k hcs F).indep.mono (by decide) c _ a1 hG
  have hfin : run pBody c = run edgePut (run pRead c) := rfl
  have hmem : (run pBody c).mem = upd (upd c.mem (fPU g cs k F + (i * k + j))
      (Flow.idv cs ((Flow.occs cs).getD (i * k + j) (0, 0)).1)) (fPV g cs k F + (i * k + j))
      (Flow.idv cs ((Flow.occs cs).getD (i * k + j) (0, 0)).2) := by
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
  · exact ((FG.regIndep g cs k hcs F).mono (by decide)) _ _ hreg hG
  · rw [hmem, ← Nat.add_assoc]; exact hM.put hcs hvb hq
  · rw [hreg sBase (by decide), hB]
  · rw [hreg sI (by decide), hI]
  · rw [hreg sJ (by decide), hJ]
  · rw [hreg gK (by decide), hK]

theorem pRow_spec (g : Graph) (cs : List Cycle) (k : ℕ) (hcs : ∀ c ∈ cs, IsCycle g k c) (F : ℕ) (m₀ : ℕ → ℕ) (hS : fPI g cs k F ≤ S)
    (hvb : bV g + fL g cs k ≤ F) (i : ℕ) (hi : i < (cs).length) :
    HTB S pRow (fun c => (FInv g cs k F m₀ (i * k) c ∧ c.reg sBase = i * k) ∧ c.reg sI = i ∧
        c.reg gT = (cs).length)
      (fun c => (FInv g cs k F m₀ ((i + 1) * k) c ∧ c.reg sBase = (i + 1) * k) ∧ c.reg sI = i ∧
        c.reg gT = (cs).length) (k * 36 + 4) := by
  have hl := HTB.forUpC (i := sJ) (n := gK) (N := k) (body := pBody)
    (fun j c => PJInv g cs k F m₀ i j c ∧ c.reg gT = (cs).length) 32 (by decide) (by decide)
    (by decide) (fun j => by indep [PJInv, FInv, fG_iff, Flow.gA_iff])
    (fun j hj => (pBody_spec g cs k hcs F m₀ hS hvb i j hi hj).frame
      (F := fun c => c.reg gT = (cs).length)
      (fun c c' hfr h => by rw [hfr.reg gT (by decide), h]) |>.mono
      (fun c ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨⟨h1, h3, h4⟩, h2⟩)
      (fun c ⟨⟨h1, h3, h4⟩, h2⟩ => ⟨⟨h1, h2⟩, h3, h4⟩)
      le_rfl)
  have h2 : HTB S (.add sBase sBase gK)
      (fun c => (PJInv g cs k F m₀ i k c ∧ c.reg gT = (cs).length) ∧ c.reg sJ = k ∧
        c.reg gK = k)
      (fun c => (FInv g cs k F m₀ ((i + 1) * k) c ∧ c.reg sBase = (i + 1) * k) ∧ c.reg sI = i ∧
        c.reg gT = (cs).length) 1 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨⟨hE, hB, hI⟩, hT⟩, _, hK⟩ => ?_
    have hE' : FInv g cs k F m₀ ((i + 1) * k) c := by
      rw [show (i + 1) * k = i * k + k by ring]; exact hE
    refine ⟨⟨(show Indep [sBase] (FInv g cs k F m₀ ((i + 1) * k)) by
      indep [FInv, fG_iff, Flow.gA_iff]).setReg (by decide) _ hE', ?_⟩, ?_, ?_⟩
    · simp +decide [hB, hK]; ring
    · simp +decide [hI]
    · simp +decide [hT]
  refine (hl.seq h2).mono
    (fun c ⟨⟨hE, hB⟩, hI, hT⟩ => ⟨⟨⟨by simpa using hE, hB, hI⟩, hT⟩, hE.1.ga.rk⟩)
    (fun _ h => h) (by omega)

structure PairsPost (g : Graph) (cs : List Cycle) (k F : ℕ) (m₀ : ℕ → ℕ) (c : Config) : Prop where
  vb : bV g + fL g cs k ≤ F
  pin : PairIds.PIn (Flow.prs cs) (Flow.nV cs) c
  ga : Flow.GA g cs k c
  rfree : c.reg rFREE = fPI g cs k F
  mverts : Arr c.mem (bV g) (Flow.verts cs)
  same : SameOn (· < F) m₀ c.mem

theorem fPairs_spec (g : Graph) (cs : List Cycle) (k : ℕ) (hcs : ∀ c ∈ cs, IsCycle g k c) (F : ℕ) (m₀ : ℕ → ℕ) (hS : fPI g cs k F ≤ S) :
    HTB S (.seq fPairs idsArgs) (VidsPost g cs k F m₀) (PairsPost g cs k F m₀)
      (7 + ((cs).length * (k * 36 + 4 + 4) + 3) + 8) := by
  refine HTB.pre_fact (p := bV g + fL g cs k ≤ F) (fun c h => h.vb) fun hvb => ?_
  have hfl : fL g cs k = k * (cs).length := rfl
  have e2 : fPU g cs k F = F + 5 * fL g cs k := rfl
  have e3 : fPV g cs k F = F + 6 * fL g cs k := rfl
  have e4 : fPI g cs k F = F + 7 * fL g cs k := rfl
  have h0 : HTB S (.seq (.seq (alloc gPU gKT) (alloc gPV gKT)) (.const sBase 0))
      (VidsPost g cs k F m₀) (fun c => (FInv g cs k F m₀ (0 * k) c ∧ c.reg sBase = 0 * k) ∧
        c.reg gT = (cs).length) 7 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c hP => ?_
    have hga : Flow.GA g cs k (run (.seq (.seq (alloc gPU gKT) (alloc gPV gKT)) (.const sBase 0)) c) :=
      (show RegIndep [rT, gPU, rFREE, gPV, sBase] (Flow.GA g cs k) by indep [Flow.gA_iff]).run_of_sub
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
  have hl := HTB.forUpC (i := sI) (n := gT) (N := (cs).length) (body := pRow)
    (fun i c => FInv g cs k F m₀ (i * k) c ∧ c.reg sBase = i * k) (k * 36 + 4) (by decide) (by decide)
    (by decide) (fun j => by indep [FInv, fG_iff, Flow.gA_iff])
    (fun i hi => pRow_spec g cs k hcs F m₀ hS hvb i hi)
  have h1 : HTB S idsArgs (fun c => (FInv g cs k F m₀ ((cs).length * k) c ∧
        c.reg sBase = (cs).length * k) ∧ c.reg sI = (cs).length ∧
        c.reg gT = (cs).length) (PairsPost g cs k F m₀) 8 := HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨⟨hG, hM⟩, _⟩, _, _⟩ => ?_
    rw [Nat.mul_comm] at hM
    have hAg : Agree [rT, PairIds.rPU, PairIds.rPV, PairIds.rPL, PairIds.rPN] c (run idsArgs c) :=
      agree_run (by decide) rfl rfl (by decide) c
    have hpu : (run idsArgs c).reg PairIds.rPU = fPU g cs k F := by
      simp +decide [idsArgs, run_mov, hG.rpu]
    have hpv : (run idsArgs c).reg PairIds.rPV = fPV g cs k F := by
      simp +decide [idsArgs, run_mov, hG.rpv]
    have hF : (run idsArgs c).reg rFREE = fPI g cs k F := (hAg.reg _ (by decide)).trans hG.rfree
    refine ⟨hvb, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, (show RegIndep [rT, PairIds.rPU, PairIds.rPV,
      PairIds.rPL, PairIds.rPN] (Flow.GA g cs k) by indep [Flow.gA_iff]).indep c _ hAg hG.ga, hF,
      by rw [hAg.mem]; exact hM.mverts, by rw [hAg.mem]; exact hM.same⟩
    · simp +decide [idsArgs, run_mov, hG.ga.rkt, (Flow.length_prs hcs)]
    · simp +decide [idsArgs, run_mov, hG.rn]
    · rw [hpu, hAg.mem, ← (Flow.map_fst_prs hcs)]; exact hM.mpu.toArr
    · rw [hpv, hAg.mem, ← (Flow.map_snd_prs hcs)]; exact hM.mpv.toArr
    · rw [hpu, hpv, hF, (Flow.length_prs hcs)]; exact ⟨by omega, by omega⟩
    · rw [hF, hAg.mem]; exact hM.mzero
  exact ((h0.seq hl).assoc.assoc.seq h1).weaken (by omega)

end STACS2027.Runtimes.EnumeratedSort
