module

public import ApproximationHardness.Embed.DFSMemory
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-! # Exact refinement of a cached forest-search step -/

@[expose] public section

namespace STACS2027.Embed.DFSRAM

open RAM

attribute [local simp] dartCount scan current inner height postLength remaining
  baseRegister widthRegister address pointer degree nextDart opposite nextVertex
  parent value needHeight test otherTest repValue

theorem Bases.run_aux {L : Layout} {G : DG} {c : Config} {p : Stmt}
    (h : Bases L G c)
    (hp : ∀ r, r ∈ regsW p → (141 ≤ r ∧ r ≤ 145) ∨ (180 ≤ r ∧ r ≤ 191)) :
    Bases L G (run p c) := by
  apply h.frame
  intro r hr
  apply run_reg_frame
  intro hn
  have := hp r hn
  simp only [dartCount, baseRegister, widthRegister] at hr
  rcases hr with hr | hr | hr | hr | hr | hr <;> omega

theorem Tables.mem_congr {L : Layout} {G : DG} {c d : Config}
    (h : Tables L G c) (hm : d.mem = c.mem) : Tables L G d := by
  cases h
  constructor <;> simpa only [hm]

theorem MemoryRep.congr {L : Layout} {G : DG} {m : Nat → Nat} {s t : DS}
    (h : MemoryRep L G m s) (hp : t.par = s.par) (hd : t.depth = s.depth)
    (ht : t.ptr = s.ptr) (hs : t.st = s.st) (hl : t.post = s.post) : MemoryRep L G m t := by
  constructor
  · simpa only [dsArray, hp, hd, ht, hs] using h.arrays
  · simpa only [hl] using h.post

theorem Rep.setGhosts {L : Layout} {G : DG} {c : Config} {s : DS}
    (h : Rep L G c s) (vs es : List Nat) : Rep L G c {s with vl := vs, ex := es} := by
  exact ⟨h.bases, h.scan, h.current, h.inner, h.height, h.postLength,
    h.parents, h.depths, h.pointers, h.states, h.post⟩

theorem Rep.run_readOnly {L : Layout} {G : DG} {c : Config} {s : DS} {p : Stmt}
    (h : Rep L G c s) (hs : hasStore p = false)
    (hp : ∀ r, r ∈ regsW p → 180 ≤ r ∧ r ≤ 191) : Rep L G (run p c) s := by
  have hf (r : Nat) (hr : r < 180) : (run p c).reg r = c.reg r := by
    apply run_reg_frame
    intro hn
    have := hp r hn
    omega
  apply h.memory.of_regs (run_mem_frame p c hs)
    (h.bases.run_aux (fun r hr => Or.inr (hp r hr)))
  · rw [hf _ (by decide)]; exact h.scan
  · rw [hf _ (by decide)]; exact h.current
  · rw [hf _ (by decide)]; exact h.inner
  · rw [hf _ (by decide)]; exact h.height
  · rw [hf _ (by decide)]; exact h.postLength

theorem Tables.run_readOnly {L : Layout} {G : DG} {c : Config} {p : Stmt}
    (h : Tables L G c) (hs : hasStore p = false) : Tables L G (run p c) :=
  h.mem_congr (run_mem_frame p c hs)

theorem loadCell_addrOK {L : Layout} {G : DG} {c : Config}
    (hb : Bases L G c) (dst j i : Nat) (hj : j < 11) (hi : c.reg i < L.width) :
    AddrOK L.limit (loadCell dst j i) c := by
  have hcell := Layout.cell_lt (L := L) hj hi
  simpa [loadCell, seqs, AddrOK, run, hb.2.2.2.2.2 j hj, Layout.cell] using hcell

theorem storeCell_addrOK {L : Layout} {G : DG} {c : Config}
    (hb : Bases L G c) (j i src : Nat) (hj : j < 11) (hi : c.reg i < L.width) :
    AddrOK L.limit (storeCell j i src) c := by
  have hcell := Layout.cell_lt (L := L) hj hi
  simpa [storeCell, seqs, AddrOK, run, hb.2.2.2.2.2 j hj, Layout.cell] using hcell

theorem insideRead_values {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (ht : Tables L G c) (hv : s.cur < 2 * G.E) :
    (run insideRead c).reg pointer = s.ptr s.cur ∧
    (run insideRead c).reg degree = (G.darts s.cur).length ∧
    (run insideRead c).reg test = (G.darts s.cur).length - s.ptr s.cur := by
  have hcell (j : Nat) (hj : j < 11) : c.reg (160 + j) = L.block j := hr.bases.2.2.2.2.2 j hj
  have hp := hr.pointers s.cur hv
  have hd := ht.degrees s.cur hv
  simp only [Layout.cell] at hp hd
  simp [insideRead, loadCell, seqs, run, hcell 8 (by decide), hcell 2 (by decide),
    hr.current, hp, hd]

theorem outsideRead_values {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (ht : Tables L G c) (hv : s.r < 2 * G.E) :
    (run outsideRead c).reg repValue = G.rep s.r ∧
    (run outsideRead c).reg value = s.st s.r ∧
    (run outsideRead c).reg test = G.rep s.r - s.r ∧
    (run outsideRead c).reg otherTest = s.r - G.rep s.r := by
  have hcell (j : Nat) (hj : j < 11) : c.reg (160 + j) = L.block j := hr.bases.2.2.2.2.2 j hj
  have hp := ht.representatives s.r hv
  have hd := hr.states s.r hv
  simp only [Layout.cell] at hp hd
  simp [outsideRead, loadCell, seqs, run, hcell 0 (by decide), hcell 9 (by decide),
    hr.scan, hp, hd]

theorem readNext_value {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (ht : Tables L G c) (hv : s.cur < 2 * G.E)
    (hp : c.reg pointer = s.ptr s.cur) (hk : s.ptr s.cur < 3) :
    (run readNext c).reg nextDart = G.nd s := by
  have hcell (j : Nat) (hj : j < 11) : c.reg (160 + j) = L.block j := hr.bases.2.2.2.2.2 j hj
  have ha (k : Nat) (hk : k < 3) := ht.adjacent k hk s.cur hv
  simp only [Layout.cell] at ha
  have hk' : s.ptr s.cur = 0 ∨ s.ptr s.cur = 1 ∨ s.ptr s.cur = 2 := by omega
  rcases hk' with hk' | hk' | hk'
  all_goals simp [readNext, loadCell, seqs, run, hr.current, hp, hk',
    hr.bases.2.1, hcell 3 (by decide), hcell 4 (by decide), hcell 5 (by decide),
    ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), DG.nd]

theorem exploreRead_values {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (ht : Tables L G c) (hG : G.Ok)
    (hv : s.cur < 2 * G.E) (hp : c.reg pointer = s.ptr s.cur)
    (hk : s.ptr s.cur < (G.darts s.cur).length) :
    (run exploreRead c).reg nextDart = G.nd s ∧
    (run exploreRead c).reg opposite = STACS2027.Embed.pair (G.nd s) ∧
    (run exploreRead c).reg nextVertex = G.nw s ∧
    (run exploreRead c).reg value = s.st (G.nw s) ∧
    (run exploreRead c).reg pointer = s.ptr s.cur := by
  have hn := readNext_value hr ht hv hp (by have := hG.deg s.cur; omega)
  have hmem : (run readNext c).mem = c.mem := run_mem_frame _ _ (by decide)
  have hf (r : Nat) (hr : r ≠ 180 ∧ r ≠ 183 ∧ r ≠ 189) :
      (run readNext c).reg r = c.reg r := by
    apply run_reg_frame
    simp [readNext, loadCell, seqs, regsW]
    omega
  obtain ⟨hnd, _, hnw, _, _⟩ := DG.nw_facts hG hk
  have hpair := ht.partners _ hnd
  have hrep := ht.representatives _ (pair_lt hnd)
  have hstate := hr.states _ hnw
  have hcell (j : Nat) (hj : j < 11) : c.reg (160 + j) = L.block j := hr.bases.2.2.2.2.2 j hj
  simp only [Layout.cell, DG.nw] at hpair hrep hstate
  simp [exploreRead, loadCell, seqs, run_seq, run, hn, hmem,
    hf 160 (by decide), hf 161 (by decide), hf 169 (by decide), hf 181 (by decide),
    hcell 0 (by decide), hcell 1 (by decide), hcell 9 (by decide), hp,
    hpair, hrep, hstate, DG.nw]

theorem explorePrefix_refines {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (ht : Tables L G c) (hG : G.Ok)
    (hv : s.cur < 2 * G.E) (hp : c.reg pointer = s.ptr s.cur)
    (hk : s.ptr s.cur < (G.darts s.cur).length)
    (hw : 2 * G.E ≤ L.width) (hpost : s.post.length ≤ L.width) :
    Rep L G (run explorePrefix c) {s with ptr := upd s.ptr s.cur (s.ptr s.cur + 1)} ∧
    (run explorePrefix c).reg opposite = STACS2027.Embed.pair (G.nd s) ∧
    (run explorePrefix c).reg nextVertex = G.nw s ∧
    (run explorePrefix c).reg value = s.st (G.nw s) := by
  obtain ⟨hd, hpair, hnw, hstate, hptr⟩ := exploreRead_values hr ht hG hv hp hk
  have hrr : Rep L G (run exploreRead c) s := by
    apply hr.run_readOnly (by decide)
    intro r h
    simp [exploreRead, readNext, loadCell, seqs, regsW] at h
    omega
  have hmem := hr.memory.update (j := 8) (value := s.ptr s.cur + 1)
    (by decide) (by decide) hv hw hpost
  have hmem' : MemoryRep L G (upd c.mem (L.cell 8 s.cur) (s.ptr s.cur + 1))
      {s with ptr := upd s.ptr s.cur (s.ptr s.cur + 1)} := by
    apply hmem.congr <;> rfl
  have hm : (run explorePrefix c).mem = upd c.mem (L.cell 8 s.cur) (s.ptr s.cur + 1) := by
    have hmf : (run exploreRead c).mem = c.mem := run_mem_frame _ _ (by decide)
    simp [explorePrefix, storeCell, seqs, run_seq, run, hptr, hrr.current,
      hrr.bases.2.1, hrr.bases.2.2.2.2.2 8 (by decide), hmf, Layout.cell,
      Config.setMem, Config.setReg, upd]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply hmem'.of_regs hm
    · apply hr.bases.run_aux
      intro r h
      simp [explorePrefix, exploreRead, readNext, storeCell, loadCell, seqs, regsW] at h
      omega
    all_goals
      have hf : ∀ r, r < 180 → (run explorePrefix c).reg r = c.reg r := by
        intro r hr
        apply run_reg_frame
        simp [explorePrefix, exploreRead, readNext, storeCell, loadCell, seqs, regsW]
        omega
      rw [hf _ (by decide)]
    · exact hr.scan
    · exact hr.current
    · exact hr.inner
    · exact hr.height
    · exact hr.postLength
  all_goals simp [explorePrefix, storeCell, seqs, run_seq, run, hpair, hnw, hstate]

theorem startRoot_refines {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (hv : s.r < 2 * G.E) (hw : 2 * G.E ≤ L.width)
    (hpost : s.post.length ≤ L.width) :
    Rep L G (run startRoot c) {s with
      st := upd s.st s.r 1,
      par := upd s.par s.r (2 * G.E), depth := upd s.depth s.r 0,
      cur := s.r, inner := true, vl := s.vl ++ [s.r], H := max s.H 1} := by
  let s' := {s with
      st := upd s.st s.r 1,
      par := upd s.par s.r (2 * G.E), depth := upd s.depth s.r 0,
      cur := s.r, inner := true, vl := s.vl ++ [s.r], H := max s.H 1}
  have hmem := ((hr.memory.update (j := 9) (value := 1) (by decide) (by decide) hv hw hpost).update
    (j := 6) (value := 2 * G.E) (by decide) (by decide) hv hw hpost).update
    (j := 7) (value := 0) (by decide) (by decide) hv hw hpost
  have hmem' : MemoryRep L G
      (upd (upd (upd c.mem (L.cell 9 s.r) 1) (L.cell 6 s.r) (2 * G.E))
        (L.cell 7 s.r) 0) s' := by
    apply hmem.congr <;> rfl
  obtain ⟨hscan, hcur, hi, hH, hp, hm⟩ := startRoot_raw c hr.bases.1 hr.bases.2.1
  have hcell (j : Nat) (hj : j < 11) : c.reg (160 + j) = L.block j := hr.bases.2.2.2.2.2 j hj
  apply hmem'.of_regs
  · simpa only [hr.scan, hr.bases.2.2.1, hcell 9 (by decide), hcell 6 (by decide),
      hcell 7 (by decide), Layout.cell] using hm
  · apply hr.bases.run_aux
    intro r h
    simp [startRoot, storeCell, seqs, regsW] at h
    rcases h with h | h | h | h | h | h | h | h <;> omega
  · simpa only [s'] using hscan.trans hr.scan
  · simpa only [s'] using hcur.trans hr.scan
  · simpa only [s', Bool.true_eq_false, ↓reduceIte] using hi
  · simpa only [s', hr.height] using hH
  · simpa only [s'] using hp.trans hr.postLength

theorem exploreNew_raw (c : Config) (hz : c.reg 0 = 0) (h1 : c.reg 1 = 1) :
    let m := upd (upd c.mem (c.reg 169 + c.reg nextVertex) 1)
      (c.reg 166 + c.reg nextVertex) (c.reg opposite)
    let dep := m (c.reg 167 + c.reg current)
    let d := run exploreNew c
    d.reg scan = c.reg scan ∧ d.reg current = c.reg nextVertex ∧
    d.reg inner = c.reg inner ∧ d.reg height = max (c.reg height) (dep + 2) ∧
    d.reg postLength = c.reg postLength ∧
    d.mem = upd m (c.reg 167 + c.reg nextVertex) (dep + 1) := by
  dsimp only
  simp [exploreNew, storeCell, loadCell, seqs, run, hz, h1, Nat.sub_eq_zero_iff_le,
    Config.setMem, Config.setReg, upd, Nat.add_assoc]
  split_ifs <;> constructor
  all_goals first | omega | rfl

theorem exploreNew_refines {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) {w p : Nat} (hv : s.cur < 2 * G.E)
    (hwv : w < 2 * G.E) (hw : 2 * G.E ≤ L.width)
    (hpost : s.post.length ≤ L.width)
    (hnext : c.reg nextVertex = w) (hopp : c.reg opposite = p) :
    Rep L G (run exploreNew c) {s with
      st := upd s.st w 1, par := upd s.par w p,
      depth := upd s.depth w (s.depth s.cur + 1),
      H := max s.H (s.depth s.cur + 2), cur := w} := by
  let m := upd (upd c.mem (L.cell 9 w) 1) (L.cell 6 w) p
  have hm2 := (hr.memory.update (j := 9) (value := 1) (by decide) (by decide) hwv hw hpost).update
    (j := 6) (value := p) (by decide) (by decide) hwv hw hpost
  have hdep : m (L.cell 7 s.cur) = s.depth s.cur := by
    simpa [dsArray, setArray] using hm2.arrays 7 (by decide) (by decide) s.cur hv
  have hm3 := hm2.update (j := 7) (value := s.depth s.cur + 1) (by decide) (by decide) hwv hw hpost
  have hm3' : MemoryRep L G (upd m (L.cell 7 w) (s.depth s.cur + 1))
      {s with
        st := upd s.st w 1, par := upd s.par w p,
        depth := upd s.depth w (s.depth s.cur + 1),
        H := max s.H (s.depth s.cur + 2), cur := w} := by
    apply hm3.congr <;> rfl
  have hcell (j : Nat) (hj : j < 11) : c.reg (160 + j) = L.block j := hr.bases.2.2.2.2.2 j hj
  simp only [m, Layout.cell] at hdep
  obtain ⟨hr', hc', hi', hh', hp', hm'⟩ := exploreNew_raw c hr.bases.1 hr.bases.2.1
  simp only [hcell 9 (by decide), hcell 6 (by decide), hcell 7 (by decide),
    hnext, hopp, hr.current, hdep] at hr' hc' hi' hh' hp' hm'
  apply hm3'.of_regs hm'
  · apply hr.bases.run_aux
    intro r hn
    simp [exploreNew, storeCell, loadCell, seqs, regsW] at hn
    omega
  · exact hr'.trans hr.scan
  · exact hc'
  · exact hi'.trans hr.inner
  · simpa only [hr.height] using hh'
  · exact hp'.trans hr.postLength

theorem finishStep_refines {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (ht : Tables L G c) (hG : G.Ok)
    (hv : s.cur < 2 * G.E) (hw : 4 * G.E + 2 ≤ L.width)
    (hpost : s.post.length ≤ 4 * G.E) :
    Rep L G (run finishStep c)
      (if 2 * G.E ≤ s.par s.cur then
        {s with
          st := upd s.st s.cur 2, post := s.post ++ [s.cur, 2 * G.E + s.cur],
          inner := false, r := s.r + 1}
      else {s with
        st := upd s.st s.cur 2, post := s.post ++ [s.cur],
        cur := G.rep (STACS2027.Embed.pair (s.par s.cur))}) := by
  let m := upd (upd c.mem (L.cell 9 s.cur) 2) (L.cell 10 s.post.length) s.cur
  have hmem := (hr.memory.update (j := 9) (value := 2) (by decide) (by decide)
    hv (by omega) (by omega)).push s.cur (by omega) (by simpa only [setArray] using (show s.post.length < L.width by omega))
  have hmem' : MemoryRep L G m {s with
      st := upd s.st s.cur 2, post := s.post ++ [s.cur]} := by
    apply hmem.congr <;> rfl
  have ht1 : Tables L G {c with mem := upd c.mem (L.cell 9 s.cur) 2} :=
    ht.update 9 s.cur 2 (by decide) (by decide) (by omega) (by omega) rfl
  have ht2 : Tables L G {c with mem := m} :=
    ht1.update 10 s.post.length s.cur (by decide) (by decide) (by omega) (by omega) rfl
  have hparent : m (L.cell 6 s.cur) = s.par s.cur := by
    simpa [dsArray] using hmem'.arrays 6 (by decide) (by decide) s.cur hv
  simp only [m, Layout.cell] at hparent
  have hcell (j : Nat) (hj : j < 11) : c.reg (160 + j) = L.block j := hr.bases.2.2.2.2.2 j hj
  obtain ⟨hr', hc', hi', hh', hp', hm'⟩ := finishStep_raw c hr.bases.1 hr.bases.2.1
  simp only [hcell 9 (by decide), hcell 10 (by decide), hcell 6 (by decide),
    hcell 0 (by decide), hcell 1 (by decide), hr.current, hr.postLength,
    hr.bases.2.2.1, show L.block 10 + s.post.length + 1 = L.cell 10 (s.post.length + 1) by rfl,
    hparent] at hr' hc' hi' hp' hm'
  have hb : Bases L G (run finishStep c) := by
    apply hr.bases.run_aux
    intro r hn
    simp [finishStep, finishRoot, finishChild, pushPost, advanceScan,
      storeCell, loadCell, seqs, regsW] at hn
    omega
  by_cases hroot : 2 * G.E ≤ s.par s.cur
  · have hmemroot := hmem'.push (2 * G.E + s.cur) (by omega)
      (by simp only [List.length_append, List.length_singleton]; omega)
    have hmemroot' : MemoryRep L G (upd m (L.cell 10 (s.post.length + 1)) (2 * G.E + s.cur))
        {s with
          st := upd s.st s.cur 2, post := s.post ++ [s.cur, 2 * G.E + s.cur],
          inner := false, r := s.r + 1} := by
      have hcongr := hmemroot.congr (t := {s with
        st := upd s.st s.cur 2, post := s.post ++ [s.cur, 2 * G.E + s.cur],
        inner := false, r := s.r + 1}) rfl rfl rfl rfl (by simp [List.append_assoc])
      simpa only [List.length_append, List.length_singleton] using hcongr
    simp only [hparent, hroot, ↓reduceIte] at hr' hc' hi' hp' hm' ⊢
    apply hmemroot'.of_regs hm' hb
    · simpa only [hr.scan] using hr'
    · simpa only [hr.current] using hc'
    · simpa using hi'
    · simpa only [hr.height] using hh'
    · simpa using hp'
  · have hp : s.par s.cur < 2 * G.E := by omega
    have hpair := ht2.partners _ hp
    have hrep := ht2.representatives _ (pair_lt hp)
    simp only [m, Layout.cell] at hpair hrep
    simp only [hparent, hroot, ↓reduceIte] at hr' hc' hi' hp' hm' ⊢
    have hmemchild := hmem'.congr (t := {s with
      st := upd s.st s.cur 2, post := s.post ++ [s.cur],
      cur := G.rep (STACS2027.Embed.pair (s.par s.cur))}) rfl rfl rfl rfl rfl
    apply hmemchild.of_regs hm' hb
    · simpa only [hr.scan] using hr'
    · simpa only [hpair, hrep] using hc'
    · simpa only [hr.inner] using hi'
    · simpa only [hr.height] using hh'
    · simpa using hp'

theorem exploreStep_refines {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (ht : Tables L G c) (hG : G.Ok)
    (hv : s.cur < 2 * G.E) (hp : c.reg pointer = s.ptr s.cur)
    (hi : s.inner = true) (hk : s.ptr s.cur < (G.darts s.cur).length)
    (hw : 2 * G.E ≤ L.width) (hpost : s.post.length ≤ L.width) :
    Rep L G (run exploreStep c) (G.step s) := by
  obtain ⟨hpre, hop, hnw, hval⟩ := explorePrefix_refines hr ht hG hv hp hk hw hpost
  obtain ⟨_, _, hwv, _, _⟩ := DG.nw_facts hG hk
  by_cases hnew : s.st (G.nw s) = 0
  · have href := exploreNew_refines hpre hv hwv hw hpost hnw hop
    have hout := href.setGhosts (s.vl ++ [G.nw s]) (s.ex ++ [G.nd s])
    simpa only [exploreStep, run_seq, run_ifz, hval, hnew, ↓reduceIte,
      DG.step, hi, hk, ↓reduceIte] using hout
  · have hout := hpre.setGhosts s.vl (s.ex ++ [G.nd s])
    simpa only [exploreStep, run_seq, run_ifz, hval, hnew, ↓reduceIte,
      run, DG.step, hi, hk, ↓reduceIte] using hout

theorem insideStep_refines {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (ht : Tables L G c) (hG : G.Ok)
    (hi : s.inner = true) (hv : s.cur < 2 * G.E)
    (hw : 4 * G.E + 2 ≤ L.width) (hpost : s.post.length ≤ 4 * G.E) :
    Rep L G (run insideStep c) (G.step s) := by
  have hrr : Rep L G (run insideRead c) s := by
    apply hr.run_readOnly (by decide)
    intro r hn
    simp [insideRead, loadCell, seqs, regsW] at hn
    omega
  have htt := ht.run_readOnly (p := insideRead) (by decide)
  obtain ⟨hp, _, htest⟩ := insideRead_values hr ht hv
  by_cases hk : s.ptr s.cur < (G.darts s.cur).length
  · have hne : (G.darts s.cur).length - s.ptr s.cur ≠ 0 := by omega
    have he := exploreStep_refines hrr htt hG hv hp hi hk (by omega) (by omega)
    simpa only [insideStep, run_seq, run_ifz, htest, hne, ↓reduceIte] using he
  · have he := finishStep_refines hrr htt hG hv hw hpost
    have hz : (G.darts s.cur).length - s.ptr s.cur = 0 := by omega
    simpa only [insideStep, run_seq, run_ifz, htest, hz, ↓reduceIte, DG.step, hi,
      hk, ↓reduceIte] using he

theorem advanceScan_refines {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) : Rep L G (run advanceScan c) {s with r := s.r + 1} := by
  have hm : MemoryRep L G c.mem {s with r := s.r + 1} := by
    apply hr.memory.congr <;> rfl
  apply hm.of_regs (by rfl)
  · apply hr.bases.run_aux
    intro r hn
    simp [advanceScan, regsW] at hn
    omega
  · simp [advanceScan, run, hr.scan, hr.bases.2.1]
  · simpa [advanceScan, run] using hr.current
  · simpa [advanceScan, run] using hr.inner
  · simpa [advanceScan, run] using hr.height
  · simpa [advanceScan, run] using hr.postLength

theorem outsideStep_refines {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (ht : Tables L G c) (hi : s.inner = false)
    (hw : 2 * G.E ≤ L.width) (hpost : s.post.length ≤ L.width) :
    Rep L G (run outsideStep c) (G.step s) := by
  let c0 := run (.sub test dartCount scan) c
  have hr0 : Rep L G c0 s := by
    apply hr.run_readOnly (by decide)
    intro r hn
    simp [regsW] at hn
    omega
  have ht0 : Tables L G c0 := ht.run_readOnly (by decide)
  have htest0 : c0.reg test = 2 * G.E - s.r := by
    simp [c0, run, hr.bases.2.2.1, hr.scan]
  by_cases hv : s.r < 2 * G.E
  · have hnz : 2 * G.E - s.r ≠ 0 := by omega
    let c1 := run outsideRead c0
    have hr1 : Rep L G c1 s := by
      apply hr0.run_readOnly (by decide)
      intro r hn
      simp [outsideRead, loadCell, seqs, regsW] at hn
      omega
    have ht1 : Tables L G c1 := ht0.run_readOnly (by decide)
    obtain ⟨_, hval, htst, hother⟩ := outsideRead_values hr0 ht0 hv
    change c1.reg value = s.st s.r at hval
    change c1.reg test = G.rep s.r - s.r at htst
    change c1.reg otherTest = s.r - G.rep s.r at hother
    have hrun : run outsideStep c =
        run (.ifz test (.ifz otherTest (.ifz value startRoot advanceScan) advanceScan)
          advanceScan) c1 := by
      simp only [outsideStep, seqs, run_seq, run_ifz]
      change (if c0.reg test = 0 then c0 else _) = _
      simp only [htest0, hnz, ↓reduceIte]
      rfl
    by_cases heq : G.rep s.r = s.r
    · have hz : G.rep s.r - s.r = 0 := by omega
      have hz' : s.r - G.rep s.r = 0 := by omega
      by_cases hnew : s.st s.r = 0
      · have he := startRoot_refines hr1 hv hw hpost
        simpa only [hrun, run_ifz, htst, hother, hval, hz, hz', hnew, ↓reduceIte,
          DG.step, hi, Bool.false_eq_true, ↓reduceIte, hv, heq, hnew, Nat.sub_self, and_self] using he
      · have he := advanceScan_refines hr1
        simpa only [hrun, run_ifz, htst, hother, hval, hz, hz', hnew, ↓reduceIte,
          DG.step, hi, Bool.false_eq_true, ↓reduceIte, hv, heq, hnew, Nat.sub_self, and_false] using he
    · have hfailed : G.rep s.r - s.r ≠ 0 ∨ s.r - G.rep s.r ≠ 0 := by omega
      have he := advanceScan_refines hr1
      rcases hfailed with hfail | hfail
      · simpa only [hrun, run_ifz, htst, hfail, ↓reduceIte, DG.step, hi,
          Bool.false_eq_true, ↓reduceIte, hv, heq, false_and] using he
      · by_cases hz : G.rep s.r - s.r = 0
        · simpa only [hrun, run_ifz, htst, hz, hother, hfail, ↓reduceIte, DG.step, hi,
            Bool.false_eq_true, ↓reduceIte, hv, heq, false_and] using he
        · simpa only [hrun, run_ifz, htst, hz, ↓reduceIte, DG.step, hi,
            Bool.false_eq_true, ↓reduceIte, hv, heq, false_and] using he
  · have hz : 2 * G.E - s.r = 0 := by omega
    have hrun : run outsideStep c = c0 := by
      simp only [outsideStep, seqs, run_seq, run_ifz]
      change (if c0.reg test = 0 then c0 else _) = _
      simp only [htest0, hz, ↓reduceIte]
    simpa only [hrun, DG.step, hi, Bool.false_eq_true, ↓reduceIte, hv] using hr0

theorem stepProgram_refines {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (ht : Tables L G c) (hG : G.Ok) (hI : G.Inv s)
    (hw : 4 * G.E + 2 ≤ L.width) : Rep L G (run stepProgram c) (G.step s) := by
  have hp := (DG.bounds hI).2.2
  cases hi : s.inner
  · have he := outsideStep_refines hr ht hi (by omega) (by omega)
    simpa only [stepProgram, run_ifz, hr.inner, hi, Bool.false_eq_true, ↓reduceIte] using he
  · have hv := (hI.vert s.cur (by have := (hI.path hi).1; omega)).1
    have he := insideStep_refines hr ht hG hi hv hw hp
    simpa only [stepProgram, run_ifz, hr.inner, hi, ↓reduceIte, Nat.one_ne_zero] using he

end STACS2027.Embed.DFSRAM
