module

public import Outerplanar.RAM.Poly3Total
public import Outerplanar.RAM.Poly3Odo
import Mathlib.Tactic

/-!
# Phase P3 of the polygon solver: the states of the main pass

The main pass fills the tables segment by segment. Its states are described by

* `Glob mR T`: the registers constant during the main pass (`k`, `n`, the interface arrays,
  the table offsets `TOFF`), whose arrays are stored in the ghost memory
  `mR` below the tables `T = gTAB` (the memory below `T` agrees with `mR`: `SameOn (· < T)`);
* `SegR j`: the registers of the current segment `j` (its ends, face offset, numbers of
  boundary and top cycles and their powers of `k`, the table offset);
* `SSt mR T A R V j`: both, with the addresses of `TAB = T`, `ARG = A`, `REL = R`, `VAL = V`
  (all register-only, so they survive every store);
* `AMem mR T A R V j a vals m`: the memory: below `T` as `mR`; the tables of the first `j`
  segments and the first `a` entries of the segment `j` at `T` and `A`; the relevant cycles
  at `R`, the digits `vals` at `V`; zero from `V + |rel s|` on. Stores into the digits
  (`AMem.updV`) and of the next entries (`AMem.store`) keep it.

From these the data `Rd S` read by the computation of a configuration follows (`rd_of`), for a
bound `S` at or above the end `V + |rel s|` of the digits.
-/

@[expose] public section

namespace STACS2027.RAM.P3

open STACS2027.Poly STACS2027.RAM.P1

variable {pg : Graph} {n k : ℕ}

/-! ### The states -/

/-- The registers constant during the main pass, with their arrays in the ghost memory `mR`
below `T`. -/
@[mk_iff] structure Glob (pg : Graph) (n k : ℕ) (mR : ℕ → ℕ) (T : ℕ) (c : Config) : Prop where
  kk : c.reg rK = k
  pn : c.reg gPN = n
  ns : c.reg gNS = (segOrder pg n).length
  sa : Arr mR (c.reg gSA) ((segOrder pg n).map Prod.fst)
  sb : Arr mR (c.reg gSB) ((segOrder pg n).map Prod.snd)
  fsid : Arr mR (c.reg gFSID) (fsidCat pg n)
  foff : Arr mR (c.reg gFOFF) (faceOffs pg n)
  fv : Arr mR (c.reg gFV) (faceCat pg n)
  pl : Arr mR (c.reg gPOOL) (pool pg n k).flatten
  tst : Arr mR (c.reg gTST) (topStarts pg n k)
  boff : Arr mR (c.reg gBOFF) (bndOffs pg n k)
  bidx : Arr mR (c.reg gBIDX) (bndCat pg n k)
  toff : Arr mR (c.reg gTOFF) (tabOffs pg n k)
  bsa : c.reg gSA + (segOrder pg n).length ≤ T
  bsb : c.reg gSB + (segOrder pg n).length ≤ T
  bfsid : c.reg gFSID + (fsidCat pg n).length ≤ T
  bfoff : c.reg gFOFF + ((segOrder pg n).length + 1) ≤ T
  bfv : c.reg gFV + (faceCat pg n).length ≤ T
  bpl : c.reg gPOOL + (pool pg n k).flatten.length ≤ T
  btst : c.reg gTST + ((segOrder pg n).length + 1) ≤ T
  bboff : c.reg gBOFF + ((segOrder pg n).length + 1) ≤ T
  bbidx : c.reg gBIDX + (bndCat pg n k).length ≤ T
  btoff : c.reg gTOFF + ((segOrder pg n).length + 1) ≤ T
  tab : c.reg gTAB = T

/-- The registers of the segment `j`. -/
@[mk_iff] structure SegR (pg : Graph) (n k j : ℕ) (c : Config) : Prop where
  jj : c.reg rJ = j
  sa : c.reg rSA = (sg pg n j).1
  sb : c.reg rSB = (sg pg n j).2
  fo : c.reg rFO = fOff pg n j
  fl : c.reg rFL = (faceVerts pg n (sg pg n j)).length - 1
  nb : c.reg rNB = (bnd pg n k (sg pg n j)).length
  nc : c.reg rNC = (topIdx pg n k (sg pg n j)).length
  nr : c.reg rNR = (rel pg n k (sg pg n j)).length
  pb : c.reg rPB = k ^ (bnd pg n k (sg pg n j)).length
  pc : c.reg rPC = k ^ (topIdx pg n k (sg pg n j)).length
  tO : c.reg rTO = toffAt pg n k j

/-- The registers inside the segment `j`, with the addresses of the arrays. -/
@[mk_iff] structure SSt (pg : Graph) (n k : ℕ) (mR : ℕ → ℕ) (T A R V j : ℕ) (c : Config) : Prop where
  glob : Glob pg n k mR T c
  seg : SegR pg n k j c
  arg : c.reg gARG = A
  rr : c.reg rREL = R
  vv : c.reg rVAL = V
  vb : c.reg rVB = V + (bnd pg n k (sg pg n j)).length
  free : c.reg rFREE = V + (rel pg n k (sg pg n j)).length

/-- The layout of the arrays of the main pass. -/
structure Lay (pg : Graph) (n k : ℕ) (T A R V j : ℕ) : Prop where
  ta : T + toffAt pg n k (segOrder pg n).length = A
  ar : A + toffAt pg n k (segOrder pg n).length ≤ R
  rv : R + (rel pg n k (sg pg n j)).length = V

/-- The tables of the first `j` segments and the first `a` entries of the segment `j`. -/
def tabPre (pg : Graph) (n k j a : ℕ) : List ℕ :=
  tabDone pg n k j ++ (List.range a).map (table pg n k (sg pg n j))

/-- The minimizing configurations of the first `j` segments and of the first `a` entries of
the segment `j`. -/
def argPre (pg : Graph) (n k j a : ℕ) : List ℕ :=
  argDone pg n k j ++ (List.range a).map (argTab pg n k (sg pg n j))

/-- The memory inside the segment `j`, at its entry `a`, with the digits `vals`. -/
structure AMem (pg : Graph) (n k : ℕ) (mR : ℕ → ℕ) (T A R V j a : ℕ) (vals : List ℕ)
    (m : ℕ → ℕ) : Prop where
  same : SameOn (· < T) mR m
  tb : Arr m T (tabPre pg n k j a)
  ag : Arr m A (argPre pg n k j a)
  rl : Arr m R (rel pg n k (sg pg n j))
  vl : Arr m V vals
  free : ZeroFrom m (V + (rel pg n k (sg pg n j)).length)

/-! ### Lengths -/

theorem length_tabPre (j a : ℕ) : (tabPre pg n k j a).length = toffAt pg n k j + a := by
  simp [tabPre, length_tabDone]

theorem length_argPre (j a : ℕ) : (argPre pg n k j a).length = toffAt pg n k j + a := by
  simp [argPre, length_argDone]

theorem toffAt_le_full {j a : ℕ} (hj : j < (segOrder pg n).length)
    (ha : a ≤ k ^ (bnd pg n k (sg pg n j)).length) :
    toffAt pg n k j + a ≤ toffAt pg n k (segOrder pg n).length := by
  have h1 := toffAt_succ (pg := pg) (n := n) (k := k) hj
  have h2 := toffAt_mono (pg := pg) (n := n) (k := k) (show j + 1 ≤ (segOrder pg n).length by omega)
  rw [← sg_eq hj] at h1
  omega

/-! ### Stores -/

/-- A store into the digits. -/
theorem AMem.updV {mR : ℕ → ℕ} {T A R V j a : ℕ} {vals : List ℕ} {m : ℕ → ℕ}
    (h : AMem pg n k mR T A R V j a vals m) (hlay : Lay pg n k T A R V j)
    (hj : j < (segOrder pg n).length) (ha : a ≤ k ^ (bnd pg n k (sg pg n j)).length)
    (hvl : vals.length = (rel pg n k (sg pg n j)).length) {t : ℕ} (ht : t < vals.length) (v : ℕ) :
    AMem pg n k mR T A R V j a (vals.set t v) (upd m (V + t) v) := by
  have hl := toffAt_le_full hj ha
  have h1 := hlay.ta
  have h2 := hlay.ar
  have h3 := hlay.rv
  refine ⟨h.same.upd_of_ge (by omega) _, h.tb.upd_of_disjoint (by rw [length_tabPre]; omega),
    h.ag.upd_of_disjoint (by rw [length_argPre]; omega), h.rl.upd_of_disjoint (by omega),
    h.vl.upd_set rfl, h.free.upd (by omega)⟩

/-- Storing the entry `a` of the segment `j` (table and minimizing configuration). -/
theorem AMem.store {mR : ℕ → ℕ} {T A R V j a : ℕ} {vals : List ℕ} {m : ℕ → ℕ}
    (h : AMem pg n k mR T A R V j a vals m) (hlay : Lay pg n k T A R V j)
    (hj : j < (segOrder pg n).length) (ha : a < k ^ (bnd pg n k (sg pg n j)).length) :
    AMem pg n k mR T A R V j (a + 1) vals
      (upd (upd m (T + (toffAt pg n k j + a)) (table pg n k (sg pg n j) a))
        (A + (toffAt pg n k j + a)) (argTab pg n k (sg pg n j) a)) := by
  have hl := toffAt_le_full hj ha
  have h1 := hlay.ta
  have h2 := hlay.ar
  have h3 := hlay.rv
  have htp : tabPre pg n k j (a + 1) = tabPre pg n k j a ++ [table pg n k (sg pg n j) a] := by
    simp [tabPre, List.range_succ]
  have hap : argPre pg n k j (a + 1) = argPre pg n k j a ++ [argTab pg n k (sg pg n j) a] := by
    simp [argPre, List.range_succ]
  refine ⟨(h.same.upd_of_ge (by omega) _).upd_of_ge (by omega) _, ?_, ?_,
    (h.rl.upd_of_disjoint (by omega)).upd_of_disjoint (by omega),
    (h.vl.upd_of_disjoint (by omega)).upd_of_disjoint (by omega),
    (h.free.upd (by omega)).upd (by omega)⟩
  · rw [htp]
    refine (h.tb.upd_snoc (by rw [length_tabPre])).upd_of_disjoint ?_
    rw [List.length_append, length_tabPre, List.length_singleton]; omega
  · rw [hap]
    refine (h.ag.upd_of_disjoint (by rw [length_argPre]; omega)).upd_snoc ?_
    rw [length_argPre]

/-! ### Reading -/

theorem Glob.rd {mR : ℕ → ℕ} {T : ℕ} {c : Config} (hg : Glob pg n k mR T c)
    (hs : SameOn (· < T) mR c.mem) :
    Arr c.mem (c.reg gSA) ((segOrder pg n).map Prod.fst) ∧
    Arr c.mem (c.reg gSB) ((segOrder pg n).map Prod.snd) ∧
    Arr c.mem (c.reg gFSID) (fsidCat pg n) ∧
    Arr c.mem (c.reg gFOFF) (faceOffs pg n) ∧
    Arr c.mem (c.reg gFV) (faceCat pg n) ∧
    Arr c.mem (c.reg gPOOL) (pool pg n k).flatten ∧
    Arr c.mem (c.reg gTST) (topStarts pg n k) ∧
    Arr c.mem (c.reg gBOFF) (bndOffs pg n k) ∧
    Arr c.mem (c.reg gBIDX) (bndCat pg n k) ∧
    Arr c.mem (c.reg gTOFF) (tabOffs pg n k) := by
  have hfo : (faceOffs pg n).length = (segOrder pg n).length + 1 := by
    rw [faceOffs, length_prefixSums, List.length_map]
  have hts : (topStarts pg n k).length = (segOrder pg n).length + 1 := by
    rw [topStarts, length_prefixSums, List.length_map]
  have hbo : (bndOffs pg n k).length = (segOrder pg n).length + 1 := by
    rw [bndOffs, length_prefixSums, List.length_map]
  refine ⟨hg.sa.of_below hs (by simpa using hg.bsa), hg.sb.of_below hs (by simpa using hg.bsb),
    hg.fsid.of_below hs hg.bfsid, hg.foff.of_below hs (by rw [hfo]; exact hg.bfoff),
    hg.fv.of_below hs hg.bfv, hg.pl.of_below hs hg.bpl, hg.tst.of_below hs (by rw [hts]; exact hg.btst),
    hg.boff.of_below hs (by rw [hbo]; exact hg.bboff), hg.bidx.of_below hs hg.bbidx,
    hg.toff.of_below hs (by rw [length_tabOffs]; exact hg.btoff)⟩

/-- **The data of a configuration** from the state of the segment `j`. -/
theorem rd_of {S : ℕ} {mR : ℕ → ℕ} {T A R V j a : ℕ} {vals : List ℕ} {c : Config}
    (hS : SSt pg n k mR T A R V j c) (hM : AMem pg n k mR T A R V j a vals c.mem)
    (hlay : Lay pg n k T A R V j) (hj : j ≤ (segOrder pg n).length)
    (hvl : vals.length = (rel pg n k (sg pg n j)).length)
    (hSz : V + (rel pg n k (sg pg n j)).length ≤ S) :
    Rd S pg n k j vals c := by
  obtain ⟨-, -, hfsid, -, hfv, hpl, -, hboff, hbidx, htoff⟩ := hS.glob.rd hM.same
  have htb : Arr c.mem (c.reg gTAB) (tabDone pg n k j) := by
    rw [hS.glob.tab]; exact hM.tb.prefix
  have hbo : (bndOffs pg n k).length = (segOrder pg n).length + 1 := by
    rw [bndOffs, length_prefixSums, List.length_map]
  have hg := hS.glob
  have h1 := hlay.ta
  have h2 := hlay.ar
  have h3 := hlay.rv
  have hm := toffAt_mono (pg := pg) (n := n) (k := k) hj
  have hT : T ≤ S := by omega
  exact ⟨hS.glob.kk, hS.glob.pn, hpl, hfsid, hfv, hboff, hbidx, htoff, htb,
    by rw [hS.rr]; exact hM.rl, by rw [hS.vv]; exact hM.vl, hS.seg.nr, hS.seg.fo, hS.seg.fl,
    hS.seg.sa, hS.seg.sb, by have := hg.bpl; omega, by have := hg.bfsid; omega,
    by have := hg.bfv; omega, by rw [hbo]; have := hg.bboff; omega, by have := hg.bbidx; omega,
    by rw [length_tabOffs]; have := hg.btoff; omega,
    by rw [hg.tab, length_tabDone]; omega, by rw [hS.rr]; omega, by rw [hS.vv, hvl]; omega⟩

end STACS2027.RAM.P3
