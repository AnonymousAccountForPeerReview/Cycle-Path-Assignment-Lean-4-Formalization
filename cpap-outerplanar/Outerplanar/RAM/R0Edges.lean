module

public import Outerplanar.RAM.R0Prog
import Mathlib.Tactic

/-!
# Phase R0 (parsing): the id pairs and the distinct edges (steps 4–6)

* `stepIds_spec`: the id pass; after `j` input pairs the arrays `PU`, `PV` hold the id pairs
  `pairsPre g j` of the proper pairs among them (`IdsMem`), ordered smaller first (`edgeIds`);
* `pairLeads_r0`: the leaders `LEAD[q] = (idPairs g).idxOf (idPairs g)[q]`, by the module
  `PairIds.pairLeads` (a stable counting sort of the pairs by first id and a timestamped
  scan; no `N × N` table);
* `stepKeep_spec`: the keep pass; after `q` indices the edge arrays hold
  `((idPairs g).take q).eraseDups` (`KeepMem`): an index is appended iff it is the first of
  its pair (`LEAD[q] = q`, `PairIds.eraseDups_take_succ`). At the end they hold
  `(idPairs g).eraseDups = idEdges g`.
-/

@[expose] public section

namespace STACS2027.RAM.R0

open STACS2027.Algo

variable {S : ℕ}

/-! ### Memory fixed after the label pass -/

/-- The input, the dictionary and the label array, fixed from step 3 on. -/
structure StaticMem (g : Graph) (m : ℕ → ℕ) : Prop where
  input : Arr m 0 (graphInput g)
  dict : Tab m (baseD g) (maxLab g + 1) (dictOf (labels g))
  lab : Arr m (baseLB g) (labels g ++ List.replicate (2 * g.length - numV g) 0)

theorem StaticMem.upd {g : Graph} {m : ℕ → ℕ} (h : StaticMem g m) {a : ℕ} (v : ℕ) (ha : baseEU g ≤ a) :
    StaticMem g (RAM.upd m a v) := by
  have hL := layout_eqs g
  have hn := numV_le g
  exact ⟨h.input.upd_of_disjoint (by simp; omega), h.dict.upd_of_disjoint (by omega),
    h.lab.upd_of_disjoint (by simp [numV] at hn ⊢; omega)⟩

theorem StaticMem.of_below {g : Graph} {m m' : ℕ → ℕ} (h : StaticMem g m)
    (hs : SameOn (· < baseEU g) m m') : StaticMem g m' := by
  have hL := layout_eqs g
  have hn := numV_le g
  exact ⟨h.input.of_below hs (by simp; omega), h.dict.of_below hs (by omega),
    h.lab.of_below hs (by simp [numV] at hn ⊢; omega)⟩

/-! ### Step 4: the id pairs -/

/-- The memory during the id pass, after the id pairs `Q`. -/
structure IdsMem (g : Graph) (Q : List Edge) (m : ℕ → ℕ) : Prop where
  static : StaticMem g m
  pu : Arr m (basePU g) (Q.map Prod.fst)
  pv : Arr m (basePV g) (Q.map Prod.snd)
  zero : ZeroFrom m (baseB2 g)

/-- The state of the id pass after the id pairs `Q`. -/
@[mk_iff] structure IdsRep (g : Graph) (Q : List Edge) (c : Config) : Prop where
  glob : Glob g c
  n : c.reg gN = numV g
  free : c.reg rFREE = baseB2 g
  pl : c.reg PairIds.rPL = Q.length
  pn : c.reg PairIds.rPN = numV g
  mem : IdsMem g Q c.mem

theorem IdsRep.indep (g : Graph) (Q : List Edge) :
    Indep [rT, rI, rP, rA, rB, rU, rV] (IdsRep g Q) := by
  indep [idsRep_iff, glob_iff]

/-- The invariant of the id pass after `j` input pairs. -/
def IdsInv (g : Graph) (j : ℕ) (c : Config) : Prop :=
  IdsRep g (pairsPre g j) c ∧ c.reg rP = 2 * j + 1

/-- Appending an id pair: two stores. -/
theorem IdsMem.snoc {g : Graph} {Q : List Edge} {m : ℕ → ℕ} (h : IdsMem g Q m)
    (hlen : Q.length + 1 ≤ g.length) (u v : ℕ) :
    IdsMem g (Q ++ [(u, v)]) (upd (upd m (basePU g + Q.length) u) (basePV g + Q.length) v) := by
  have hL := layout_eqs g
  refine ⟨(h.static.upd _ (by omega)).upd _ (by omega), ?_, ?_, (h.zero.upd (by omega)).upd (by omega)⟩
  · simpa using (h.pu.upd_snoc (x := u) (by simp)).upd_of_disjoint (a := basePV g + Q.length)
      (v := v) (by simp; omega)
  · simpa using (h.pv.upd_of_disjoint (a := basePU g + Q.length) (v := u) (by simp; omega)).upd_snoc
      (x := v) (by simp)

/-- **Step 4, initialization** (memory-free). -/
theorem idsInit_spec (g : Graph) :
    HTB S idsInit (fun c => LabInv g g.length c ∧ c.reg rI = g.length ∧ c.reg gM = g.length)
      (fun c => IdsInv g 0 c ∧ c.reg gM = g.length) 4 := HTB.of_HT rfl <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨hR, _⟩, _, hm⟩ => ?_
  rw [labels_take_length] at hR
  have hL := layout_eqs g
  have hnv : numV g = (labels g).length := rfl
  simp only [idsInit, run_seq', run_const, run_mov (show gN ≠ rT by decide)]
  unfold IdsInv
  rw [pairsPre_zero]
  refine ⟨⟨⟨(Glob.regIndep g).setReg (by decide) _ ((Glob.regIndep g).setReg (by decide) _
    ((Glob.regIndep g).setReg (by decide) _ ((Glob.regIndep g).setReg (by decide) _ hR.glob))),
    ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  all_goals simp +decide only [setReg_reg, setReg_mem, ↓reduceIte, List.length_nil]
  · rw [hR.n, hnv]
  · exact hR.free
  · rw [hR.n, hnv]
  · exact ⟨⟨hR.mem.input, hR.mem.dict, hR.mem.lab⟩, arr_nil _ _, arr_nil _ _,
      hR.mem.zero.mono (by omega)⟩
  · exact hm

theorem loopFree_edgeIds : LoopFree edgeIds := by decide

/-- The ids of the ends, ordered. -/
theorem edgeIds_run {g : Graph} {c : Config} {a b : ℕ} (hG : Glob g c) (hS : StaticMem g c.mem)
    (ha : a ∈ labels g) (hb : b ∈ labels g) (hA : c.reg rA = a) (hB : c.reg rB = b) :
    (run edgeIds c).reg rU = (edge (idOf g a) (idOf g b)).1 ∧
      (run edgeIds c).reg rV = (edge (idOf g a) (idOf g b)).2 ∧ Agree [rU, rV, rT] c (run edgeIds c) := by
  have hda : c.mem (baseD g + a) = idOf g a + 1 := by
    rw [hS.dict.get (by have := labels_le_maxLab ha; omega), dictOf_labels ha]
  have hdb : c.mem (baseD g + b) = idOf g b + 1 := by
    rw [hS.dict.get (by have := labels_le_maxLab hb; omega), dictOf_labels hb]
  refine ⟨?_, ?_, agree_run loopFree_edgeIds rfl rfl (by decide) c⟩ <;>
  · simp +decide only [edgeIds, run_seq', run_ld, run_dec, run_ifLt, run_swap, setReg_reg, ↓reduceIte,
      setReg_mem, hG.d, hA, hB, hda, hdb, Nat.add_sub_cancel, edge, run_skip]
    split_ifs <;> simp +decide <;> omega

/-- **Appending the id pair of two labels**: the accesses are in the dictionary and `PU`, `PV`. -/
theorem idsIns_run {g : Graph} {Q : List Edge} {c : Config} {a b : ℕ} (hR : IdsRep g Q c)
    (ha : a ∈ labels g) (hb : b ∈ labels g) (hA : c.reg rA = a) (hB : c.reg rB = b)
    (hlen : Q.length + 1 ≤ g.length) (hS : endR0 g ≤ S) :
    IdsRep g (Q ++ [edge (idOf g a) (idOf g b)]) (run idsIns c) ∧ AddrOK S idsIns c ∧
      ∀ r ∈ [gN, rFREE, PairIds.rPN, rP, rI, gM], (run idsIns c).reg r = c.reg r := by
  obtain ⟨hU, hV, hAg⟩ := edgeIds_run hR.glob hR.mem.static ha hb hA hB
  have hR₁ : IdsRep g Q (run edgeIds c) := ((IdsRep.indep g Q).mono (by decide)) c _ hAg hR
  have hfit := fits g hS
  have hla := labels_le_maxLab ha
  have hlb := labels_le_maxLab hb
  have hreg : ∀ r ∈ [gN, rFREE, PairIds.rPN, rP, rI, gM], (run idsIns c).reg r = c.reg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact run_reg_of_not_mem (by decide) (by decide) c
  have hmem := hR₁.mem.snoc hlen (edge (idOf g a) (idOf g b)).1 (edge (idOf g a) (idOf g b)).2
  refine ⟨⟨(Glob.regIndep g).run_of_sub (by decide) (by decide) hR.glob, ?_, ?_, ?_, ?_, ?_⟩,
    AddrOK.seq (by addr_ok [edgeIds, hR.glob.d, hA, hB])
      (by addr_ok [hR₁.glob.pu, hR₁.glob.pv, hR₁.pl]), hreg⟩
  · rw [hreg gN (by decide)]; exact hR.n
  · rw [hreg rFREE (by decide)]; exact hR.free
  · simp +decide only [idsIns, run_seq', run_st (show rU ≠ rT by decide),
      run_st (show rV ≠ rT by decide), run_inc (show PairIds.rPL ≠ rT by decide), setReg_reg,
      setMem_reg, ↓reduceIte, hR₁.pl, List.length_append, List.length_singleton]
  · rw [hreg PairIds.rPN (by decide)]; exact hR.pn
  · simpa +decide only [idsIns, run_seq', run_st (show rU ≠ rT by decide),
      run_st (show rV ≠ rT by decide), run_inc (show PairIds.rPL ≠ rT by decide), setReg_reg,
      setReg_mem, setMem_reg, setMem_mem_upd, ↓reduceIte, hR₁.pl, hR₁.glob.pu, hR₁.glob.pv, hU, hV,
      Prod.mk.eta] using hmem

theorem idsBody_spec (g : Graph) (hS : endR0 g ≤ S) (j : ℕ) (hj : j < g.length) :
    HTB S idsBody (fun c => IdsInv g j c ∧ c.reg rI = j ∧ c.reg gM = g.length)
      (fun c => IdsInv g (j + 1) c ∧ c.reg rI = j ∧ c.reg gM = g.length) 29 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hR, hp⟩, hi, hm⟩ => ?_
  have hA₀ := readPair_addrOK hp hj hS
  obtain ⟨ha, hb⟩ := input_pair hR.mem.static.input hj
  obtain ⟨hA, hB, hP, hAg⟩ := readPair_run c
  rw [hp, ha] at hA
  rw [hp, show 2 * j + 1 + 1 = 2 * j + 2 by omega, hb] at hB
  rw [hp] at hP
  have hR₁ : IdsRep g (pairsPre g j) (run readPair c) :=
    ((IdsRep.indep g _).mono (by decide)) c _ hAg hR
  have hi₁ : (run readPair c).reg rI = j := (hAg.reg rI (by decide)).trans hi
  have hm₁ : (run readPair c).reg gM = g.length := (hAg.reg gM (by decide)).trans hm
  have hlen := length_pairsPre_le g (j + 1)
  unfold IdsInv
  rw [pairsPre_succ g j hj] at hlen ⊢
  by_cases hab : g[j].1 < g[j].2
  · simp only [hab, ↓reduceIte, List.length_append, List.length_singleton] at hlen ⊢
    have hpr : g[j] ∈ proper g := Comb.mem_proper.mpr ⟨List.getElem_mem hj, hab⟩
    have hlab := Comb.mem_labels_of_proper hpr
    have hR₂ := (IdsRep.indep g _).setReg (d := rT) (by decide) (g[j].2 - g[j].1) hR₁
    obtain ⟨h3, a3, hr3⟩ := idsIns_run hR₂ hlab.1 hlab.2 (by simp +decide [hA]) (by simp +decide [hB])
      (by omega) hS
    refine ⟨hA₀.seq (AddrOK.ifLt (fun _ => ?_) (fun _ => by simp)), ?_⟩
    · rw [hA, hB]; exact a3
    simp only [idsBody, run_seq', run_ifLt, hA, hB, hab, ↓reduceIte]
    refine ⟨⟨h3, ?_⟩, ?_, ?_⟩ <;> rw [hr3 _ (by simp)]
    · simp +decide [hP]; omega
    · simp +decide [hi₁]
    · simp +decide [hm₁]
  · simp only [hab, ↓reduceIte, List.append_nil]
    refine ⟨hA₀.seq (AddrOK.ifLt (fun h => by rw [hA, hB] at h; exact absurd h hab)
      (fun _ => by simp)), ?_⟩
    simp only [idsBody, run_seq', run_ifLt, hA, hB, hab, ↓reduceIte]
    refine ⟨⟨(IdsRep.indep g _).setReg (d := rT) (by decide) _ hR₁, ?_⟩, ?_, ?_⟩
    · simp +decide [hP]; omega
    · simp +decide [hi₁]
    · simp +decide [hm₁]

/-- **Step 4**: the id pass. -/
theorem stepIds_spec (g : Graph) (hS : endR0 g ≤ S) :
    HTB S stepIds (fun c => LabInv g g.length c ∧ c.reg rI = g.length ∧ c.reg gM = g.length)
      (fun c => IdsInv g g.length c ∧ c.reg rI = g.length ∧ c.reg gM = g.length)
      (4 + (g.length * 33 + 3)) :=
  (idsInit_spec g).seq (HTB.forUpC (i := rI) (n := gM) (N := g.length) (body := idsBody) (IdsInv g)
    29 (by decide) (by decide) (by decide) (fun j => by indep [IdsInv, idsRep_iff, glob_iff])
    (fun j hj => idsBody_spec g hS j hj))

/-! ### Step 5: the leaders of the id pairs -/

/-- After the id pass: the input of `PairIds.pairLeads`. -/
theorem IdsRep.pIn {g : Graph} {c : Config} (h : IdsRep g (idPairs g) c) :
    PairIds.PIn (idPairs g) (numV g) c := by
  have hL := layout_eqs g
  have hl := length_idPairs_le g
  exact ⟨h.pl, h.pn, by rw [h.glob.pu]; exact h.mem.pu, by rw [h.glob.pv]; exact h.mem.pv,
    ⟨by rw [h.glob.pu, h.free]; omega, by rw [h.glob.pv, h.free]; omega⟩,
    by rw [h.free]; exact h.mem.zero⟩

/-- The memory during the keep pass, after `q` indices. -/
structure KeepMem (g : Graph) (q : ℕ) (m : ℕ → ℕ) : Prop where
  static : StaticMem g m
  pu : Arr m (basePU g) ((idPairs g).map Prod.fst)
  pv : Arr m (basePV g) ((idPairs g).map Prod.snd)
  ld : Arr m (PairIds.bLD (numV g) (idPairs g).length (baseB2 g))
    ((idPairs g).map ((idPairs g).idxOf ·))
  eu : Arr m (baseEU g) ((((idPairs g).take q).eraseDups).map Prod.fst)
  ev : Arr m (baseEV g) ((((idPairs g).take q).eraseDups).map Prod.snd)
  zero : ZeroFrom m (endR0 g)

/-- The registers fixed during the keep pass. -/
@[mk_iff] structure KGlob (g : Graph) (c : Config) : Prop where
  glob : Glob g c
  n : c.reg gN = numV g
  free : c.reg rFREE = endR0 g
  pl : c.reg PairIds.rPL = (idPairs g).length
  ld : c.reg PairIds.rLD = PairIds.bLD (numV g) (idPairs g).length (baseB2 g)

/-- **Step 5**: the leaders of the id pairs (the module `PairIds.pairLeads`). -/
theorem pairLeads_r0 (g : Graph) (hS : endR0 g ≤ S) :
    HTB S PairIds.pairLeads (fun c => IdsInv g g.length c ∧ c.reg rI = g.length ∧ c.reg gM = g.length)
      (fun c => KGlob g c ∧ KeepMem g 0 c.mem)
      (PairIds.CL * (numV g + (idPairs g).length + 1)) := by
  refine HTB.of_forall fun c₀ ⟨⟨hR, _⟩, _, _⟩ => ?_
  rw [pairsPre_length] at hR
  have hF : c₀.reg rFREE = baseB2 g := hR.free
  have hS' : PairIds.leadsEnd (numV g) (idPairs g).length (c₀.reg rFREE) ≤ S := by rw [hF]; exact hS
  refine (PairIds.pairLeads_spec (idPairs g) (numV g) (idPairs_below g) c₀ hS').mono
    (fun c hc => ⟨hc ▸ hR.pIn, hc⟩) (fun c ⟨hL, hfr⟩ => ?_) le_rfl
  have hk : ∀ r, r ≠ rT → r ≠ rFREE → r < 100 ∨ (120 ≤ r ∧ r < 124) → c.reg r = c₀.reg r :=
    fun r h1 h2 h3 => hfr.reg r (PairIds.not_mem_wregs_pairLeads h1 h2 h3)
  have hG := hR.glob
  have hL' := layout_eqs g
  have hl := length_idPairs_le g
  obtain ⟨hld, hrld, hfree, hzero, hs⟩ := hL
  rw [hF] at hrld hfree hs
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩,
    ⟨hR.mem.static.of_below (hs.mono fun a (ha : a < _) => show a < _ by omega),
      hR.mem.pu.of_below hs (by simp; omega), hR.mem.pv.of_below hs (by simp; omega),
      by rw [← hrld]; exact hld, by simp, by simp, by rw [hL'.2.2.2.2.2.2.2, ← hfree]; exact hzero⟩⟩
  · rw [hk _ (by decide) (by decide) (by decide)]; exact hG.one
  · rw [hk _ (by decide) (by decide) (by decide)]; exact hG.m
  · rw [hk _ (by decide) (by decide) (by decide)]; exact hG.mx
  · rw [hk _ (by decide) (by decide) (by decide)]; exact hG.d
  · rw [hk _ (by decide) (by decide) (by decide)]; exact hG.lb
  · rw [hk _ (by decide) (by decide) (by decide)]; exact hG.eu
  · rw [hk _ (by decide) (by decide) (by decide)]; exact hG.ev
  · rw [hk _ (by decide) (by decide) (by decide)]; exact hG.pu
  · rw [hk _ (by decide) (by decide) (by decide)]; exact hG.pv
  · rw [hk _ (by decide) (by decide) (by decide)]; exact hR.n
  · rw [hfree]; exact hL'.2.2.2.2.2.2.2.symm
  · rw [hk _ (by decide) (by decide) (by decide)]; exact hR.pl
  · exact hrld

/-! ### Step 6: the distinct edges -/

/-- The invariant of the keep pass after `q` indices. -/
def KeepInv (g : Graph) (q : ℕ) (c : Config) : Prop :=
  KGlob g c ∧ c.reg gNE = ((idPairs g).take q).eraseDups.length ∧ KeepMem g q c.mem

/-- A first occurrence: two stores. -/
theorem KeepMem.add {g : Graph} {q : ℕ} {m : ℕ → ℕ} (h : KeepMem g q m)
    (hq : q < (idPairs g).length) (hfirst : (idPairs g).idxOf (idPairs g)[q] = q) :
    KeepMem g (q + 1) (upd (upd m (baseEU g + ((idPairs g).take q).eraseDups.length)
      (idPairs g)[q].1) (baseEV g + ((idPairs g).take q).eraseDups.length) (idPairs g)[q].2) := by
  have hL := layout_eqs g
  have hl := length_idPairs_le g
  have hn : ((idPairs g).take q).eraseDups.length ≤ q :=
    (length_eraseDups_le _).trans (by simp)
  have hle := PairIds.leads_eqs (numV g) (idPairs g).length (baseB2 g)
  have hsucc := PairIds.eraseDups_take_succ (idPairs g) hq
  simp only [hfirst, ↓reduceIte] at hsucc
  refine ⟨(h.static.upd _ (by omega)).upd _ (by omega),
    (h.pu.upd_of_disjoint (by simp; omega)).upd_of_disjoint (by simp; omega),
    (h.pv.upd_of_disjoint (by simp; omega)).upd_of_disjoint (by simp; omega),
    (h.ld.upd_of_disjoint (by simp; omega)).upd_of_disjoint (by simp; omega), ?_, ?_,
    (h.zero.upd (by omega)).upd (by omega)⟩
  · rw [hsucc, List.map_append, List.map_singleton]
    exact (h.eu.upd_snoc (by simp)).upd_of_disjoint (by simp; omega)
  · rw [hsucc, List.map_append, List.map_singleton]
    exact (h.ev.upd_of_disjoint (by simp; omega)).upd_snoc (by simp)

/-- A later occurrence: nothing changes. -/
theorem KeepMem.skip {g : Graph} {q : ℕ} {m : ℕ → ℕ} (h : KeepMem g q m)
    (hq : q < (idPairs g).length) (hnot : ¬ (idPairs g).idxOf (idPairs g)[q] = q) :
    KeepMem g (q + 1) m := by
  have hsucc := PairIds.eraseDups_take_succ (idPairs g) hq
  simp only [hnot, ↓reduceIte] at hsucc
  exact ⟨h.static, h.pu, h.pv, h.ld, by rw [hsucc]; exact h.eu, by rw [hsucc]; exact h.ev, h.zero⟩

theorem keepBody_spec (g : Graph) (hS : endR0 g ≤ S) (q : ℕ) (hq : q < (idPairs g).length) :
    HTB S keepBody (fun c => KeepInv g q c ∧ c.reg rI = q ∧ c.reg PairIds.rPL = (idPairs g).length)
      (fun c => KeepInv g (q + 1) c ∧ c.reg rI = q ∧ c.reg PairIds.rPL = (idPairs g).length) 18 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hK, hne, hM⟩, hi, hl⟩ => ?_
  have hq' : q < ((idPairs g).map Prod.fst).length := by simpa using hq
  have hx : c.mem (PairIds.bLD (numV g) (idPairs g).length (baseB2 g) + q) =
      (idPairs g).idxOf (idPairs g)[q] := by
    rw [hM.ld.get (by simpa using hq), List.getElem_map]
  have hu : c.mem (basePU g + q) = (idPairs g)[q].1 := by
    rw [hM.pu.get hq', List.getElem_map]
  have hv : c.mem (basePV g + q) = (idPairs g)[q].2 := by
    rw [hM.pv.get (by simpa using hq), List.getElem_map]
  have hn : ((idPairs g).take q).eraseDups.length ≤ q :=
    (length_eraseDups_le _).trans (by simp)
  have hlL := length_idPairs_le g
  have := fits g hS
  have hfl := PairIds.fits (numV g) (idPairs g).length (baseB2 g) hS
  have hG := hK.glob
  refine ⟨by addr_ok [keepBody, keepAdd, hK.ld, hG.pu, hG.pv, hG.eu, hG.ev, hi, hne, hx], ?_⟩
  have hreg : ∀ r ∈ [gN, rFREE, PairIds.rPL, PairIds.rLD, rI], (run keepBody c).reg r = c.reg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact run_reg_of_not_mem (by decide) (by decide) c
  refine ⟨⟨⟨(Glob.regIndep g).run_of_sub (by decide) (by decide) hG, by rw [hreg _ (by simp)]; exact hK.n,
    by rw [hreg _ (by simp)]; exact hK.free, by rw [hreg _ (by simp)]; exact hK.pl,
    by rw [hreg _ (by simp)]; exact hK.ld⟩, ?_, ?_⟩, by rw [hreg _ (by simp)]; exact hi,
    by rw [hreg _ (by simp)]; exact hl⟩
  all_goals
    simp +decide only [keepBody, keepAdd, run_seq', run_ld, run_ifEq (show rX ≠ rT by decide)
      (show rI ≠ rT by decide), run_st (show rU ≠ rT by decide), run_st (show rV ≠ rT by decide),
      run_inc (show gNE ≠ rT by decide), run_skip, setReg_reg, setReg_mem, setMem_reg,
      ↓reduceIte, hK.ld, hG.pu, hG.pv, hG.eu, hG.ev, hi, hne, hx, hu, hv]
  · have hsucc := PairIds.eraseDups_take_succ (idPairs g) hq
    by_cases hfirst : (idPairs g).idxOf (idPairs g)[q] = q
    · simp only [hfirst, ↓reduceIte] at hsucc ⊢
      simp +decide only [setReg_reg, ↓reduceIte]
      rw [hsucc, List.length_append, List.length_singleton]
    · simp only [hfirst, ↓reduceIte] at hsucc ⊢
      simp +decide only [setReg_reg, ↓reduceIte]
      rw [hsucc, hne]
  · by_cases hfirst : (idPairs g).idxOf (idPairs g)[q] = q
    · simp only [hfirst, ↓reduceIte]
      exact hM.add hq hfirst
    · simp only [hfirst, ↓reduceIte]
      exact hM.skip hq hfirst

/-- **Step 6**: the keep pass. -/
theorem stepKeep_spec (g : Graph) (hS : endR0 g ≤ S) :
    HTB S stepKeep (fun c => KGlob g c ∧ KeepMem g 0 c.mem)
      (fun c => KeepInv g (idPairs g).length c ∧ c.reg rI = (idPairs g).length ∧
        c.reg PairIds.rPL = (idPairs g).length)
      (1 + ((idPairs g).length * 22 + 3)) := by
  have h0 : HTB S (.const gNE 0) (fun c => KGlob g c ∧ KeepMem g 0 c.mem)
      (fun c => KeepInv g 0 c ∧ c.reg PairIds.rPL = (idPairs g).length) 1 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨hK, hM⟩ => by
      simp only [run_const]
      refine ⟨⟨(show RegIndep [gNE] (KGlob g) by indep [kGlob_iff, glob_iff]).setReg (by decide) _ hK,
        by simp, hM⟩, by simp +decide [hK.pl]⟩
  exact h0.seq (HTB.forUpC (i := rI) (n := PairIds.rPL) (N := (idPairs g).length) (body := keepBody)
    (KeepInv g) 18 (by decide) (by decide) (by decide) (fun j => by indep [KeepInv, kGlob_iff, glob_iff])
    (fun j hj => keepBody_spec g hS j hj))

end STACS2027.RAM.R0
