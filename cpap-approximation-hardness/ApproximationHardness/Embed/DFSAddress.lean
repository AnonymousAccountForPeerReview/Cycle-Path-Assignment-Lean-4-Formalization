module

public import ApproximationHardness.Embed.DFSFrame
import Lean.Elab.Tactic.Omega

/-! # Address bounds for the concrete cached forest search -/

@[expose] public section

namespace STACS2027.Embed.DFSRAM

open RAM

attribute [local simp] dartCount scan current inner height postLength remaining
  baseRegister widthRegister address pointer degree nextDart opposite nextVertex
  parent value needHeight test otherTest repValue

theorem startRoot_addrOK {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (hv : s.r < 2 * G.E) (hw : 2 * G.E ≤ L.width) :
    AddrOK L.limit startRoot c := by
  have hb (j : Nat) (hj : j < 11) := hr.bases.2.2.2.2.2 j hj
  have h9 := Layout.cell_lt (L := L) (j := 9) (by decide) (i := s.r) (by omega)
  have h6 := Layout.cell_lt (L := L) (j := 6) (by decide) (i := s.r) (by omega)
  have h7 := Layout.cell_lt (L := L) (j := 7) (by decide) (i := s.r) (by omega)
  simp only [Layout.cell] at h9 h6 h7
  simp [startRoot, storeCell, seqs, AddrOK, run, hr.scan,
    hb 9 (by decide), hb 6 (by decide), hb 7 (by decide), h9, h6, h7]

theorem exploreNew_addrOK {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (hv : s.cur < 2 * G.E)
    (hnw : c.reg nextVertex < 2 * G.E) (hw : 2 * G.E ≤ L.width) :
    AddrOK L.limit exploreNew c := by
  have hb (j : Nat) (hj : j < 11) := hr.bases.2.2.2.2.2 j hj
  have h9 := Layout.cell_lt (L := L) (j := 9) (by decide) (i := c.reg nextVertex) (by omega)
  have h6 := Layout.cell_lt (L := L) (j := 6) (by decide) (i := c.reg nextVertex) (by omega)
  have h7 := Layout.cell_lt (L := L) (j := 7) (by decide) (i := c.reg nextVertex) (by omega)
  have h7c := Layout.cell_lt (L := L) (j := 7) (by decide) (i := s.cur) (by omega)
  simp only [Layout.cell] at h9 h6 h7 h7c
  simp [exploreNew, storeCell, loadCell, seqs, AddrOK, run, hr.current,
    hb 9 (by decide), hb 6 (by decide), hb 7 (by decide), h9, h6, h7, h7c]

theorem insideRead_addrOK {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (hv : s.cur < 2 * G.E) (hw : 2 * G.E ≤ L.width) :
    AddrOK L.limit insideRead c := by
  have hb (j : Nat) (hj : j < 11) := hr.bases.2.2.2.2.2 j hj
  have h8 := Layout.cell_lt (L := L) (j := 8) (by decide) (i := s.cur) (by omega)
  have h2 := Layout.cell_lt (L := L) (j := 2) (by decide) (i := s.cur) (by omega)
  simp only [Layout.cell] at h8 h2
  simp [insideRead, loadCell, seqs, AddrOK, run, hr.current,
    hb 8 (by decide), hb 2 (by decide), h8, h2]

theorem outsideRead_addrOK {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (hv : s.r < 2 * G.E) (hw : 2 * G.E ≤ L.width) :
    AddrOK L.limit outsideRead c := by
  have hb (j : Nat) (hj : j < 11) := hr.bases.2.2.2.2.2 j hj
  have h0 := Layout.cell_lt (L := L) (j := 0) (by decide) (i := s.r) (by omega)
  have h9 := Layout.cell_lt (L := L) (j := 9) (by decide) (i := s.r) (by omega)
  simp only [Layout.cell] at h0 h9
  simp [outsideRead, loadCell, seqs, AddrOK, run, hr.scan,
    hb 0 (by decide), hb 9 (by decide), h0, h9]

theorem readNext_addrOK {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (hv : s.cur < 2 * G.E) (hw : 2 * G.E ≤ L.width) :
    AddrOK L.limit readNext c := by
  have hb (j : Nat) (hj : j < 11) := hr.bases.2.2.2.2.2 j hj
  have h3 := Layout.cell_lt (L := L) (j := 3) (by decide) (i := s.cur) (by omega)
  have h4 := Layout.cell_lt (L := L) (j := 4) (by decide) (i := s.cur) (by omega)
  have h5 := Layout.cell_lt (L := L) (j := 5) (by decide) (i := s.cur) (by omega)
  simp only [Layout.cell] at h3 h4 h5
  simp [readNext, loadCell, seqs, AddrOK, run, hr.current,
    hb 3 (by decide), hb 4 (by decide), hb 5 (by decide), h3, h4, h5]

theorem outsideStep_addrOK {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (hw : 2 * G.E ≤ L.width) :
    AddrOK L.limit outsideStep c := by
  let c0 := run (.sub test dartCount scan) c
  have hr0 : Rep L G c0 s := by
    apply hr.run_readOnly (by decide)
    intro r hn
    simp [regsW] at hn
    omega
  have htest : c0.reg test = 2 * G.E - s.r := by
    simp [c0, run, hr.bases.2.2.1, hr.scan]
  simp only [outsideStep, seqs, addrOK_seq, addrOK_sub, addrOK_skip,
    true_and, and_true, addrOK_ifz]
  refine ⟨fun _ => trivial, fun hn => ?_⟩
  change c0.reg test ≠ 0 at hn
  have hv : s.r < 2 * G.E := by rw [htest] at hn; omega
  have hr1 : Rep L G (run outsideRead c0) s := by
    apply hr0.run_readOnly (by decide)
    intro r hn
    simp [outsideRead, loadCell, seqs, regsW] at hn
    omega
  refine ⟨outsideRead_addrOK hr0 hv hw, ?_⟩
  refine ⟨fun _ => ⟨fun _ => ⟨fun _ => startRoot_addrOK hr1 hv hw,
    fun _ => AddrOK.of_memFree (by decide)⟩,
    fun _ => AddrOK.of_memFree (by decide)⟩,
    fun _ => AddrOK.of_memFree (by decide)⟩


/-- The finishing prefix commits the vertex and reads its parent before dispatching. -/
def finishPrefixProgram : Stmt := seqs [.const value 2, storeCell 9 current value,
  pushPost current, loadCell parent 6 current, .sub test dartCount parent]

/-- All accesses of the finishing prefix lie in the vertex and post-order blocks. -/
theorem finishPrefix_addrOK {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (hv : s.cur < 2 * G.E)
    (hw : 4 * G.E + 2 ≤ L.width) (hp : s.post.length ≤ 4 * G.E) :
    AddrOK L.limit finishPrefixProgram c := by
  have hb (j : Nat) (hj : j < 11) := hr.bases.2.2.2.2.2 j hj
  have h9 := Layout.cell_lt (L := L) (j := 9) (by decide) (i := s.cur) (by omega)
  have h6 := Layout.cell_lt (L := L) (j := 6) (by decide) (i := s.cur) (by omega)
  have h10 := Layout.cell_lt (L := L) (j := 10) (by decide) (i := s.post.length) (by omega)
  simp only [Layout.cell] at h9 h6 h10
  simp [finishPrefixProgram, pushPost, loadCell, storeCell, AddrOK, run, seqs,
    hr.current, hr.postLength, hb 9 (by decide), hb 6 (by decide), hb 10 (by decide), h9, h6, h10]

/-- Finishing uses bounded parent and post-order accesses in both the root and child cases. -/
theorem finishStep_addrOK {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (ht : Tables L G c) (hv : s.cur < 2 * G.E)
    (hw : 4 * G.E + 2 ≤ L.width) (hpost : s.post.length ≤ 4 * G.E) :
    AddrOK L.limit finishStep c := by
  let c₁ := run finishPrefixProgram c
  let m := upd (upd c.mem (L.cell 9 s.cur) 2) (L.cell 10 s.post.length) s.cur
  have hmem := (hr.memory.update (j := 9) (value := 2) (by decide) (by decide)
    hv (by omega) (by omega)).push s.cur (by omega)
      (by simpa only [setArray] using (show s.post.length < L.width by omega))
  have hmem' : MemoryRep L G m {s with st := upd s.st s.cur 2, post := s.post ++ [s.cur]} := by
    apply hmem.congr <;> rfl
  have ht₁ : Tables L G {c with mem := upd c.mem (L.cell 9 s.cur) 2} :=
    ht.update 9 s.cur 2 (by decide) (by decide) (by omega) (by omega) rfl
  have ht₂ : Tables L G {c with mem := m} :=
    ht₁.update 10 s.post.length s.cur (by decide) (by decide) (by omega) (by omega) rfl
  have hparent : m (L.cell 6 s.cur) = s.par s.cur := by
    simpa [dsArray] using hmem'.arrays 6 (by decide) (by decide) s.cur hv
  have hbase (j : Nat) (hj : j < 11) := hr.bases.2.2.2.2.2 j hj
  have hm₁ : c₁.mem = m := by
    funext a
    simp [c₁, finishPrefixProgram, pushPost, storeCell, loadCell, seqs, run,
      hr.current, hr.postLength, hbase 9 (by decide), hbase 10 (by decide),
      m, Layout.cell, Config.setMem, upd]
  have hb₁ : Bases L G c₁ := hr.bases.run_aux (by
    intro r hn; simp [finishPrefixProgram, pushPost, loadCell, storeCell, seqs, regsW] at hn; omega)
  have hparent₁ : c₁.reg parent = s.par s.cur := by
    have hx : c₁.reg parent = m (L.cell 6 s.cur) := by
      simp [c₁, finishPrefixProgram, pushPost, storeCell, loadCell, seqs, run,
        hr.current, hr.postLength, hbase 9 (by decide), hbase 10 (by decide), hbase 6 (by decide),
        m, Layout.cell, Config.setMem, upd]
    exact hx.trans hparent
  have htest₁ : c₁.reg test = 2 * G.E - s.par s.cur := by
    have hx : c₁.reg test = c.reg dartCount - c₁.reg parent := by
      simp [c₁, finishPrefixProgram, pushPost, storeCell, loadCell, seqs, run]
    rw [hx, hr.bases.2.2.1, hparent₁]
  have hpost₁ : c₁.reg postLength = s.post.length + 1 := by
    simp [c₁, finishPrefixProgram, pushPost, storeCell, loadCell, seqs, run, hr.postLength, hr.bases.2.1]
  have htable₁ : Tables L G c₁ := ht₂.mem_congr hm₁
  change AddrOK L.limit (seqs ([.const value 2, storeCell 9 current value,
    pushPost current, loadCell parent 6 current, .sub test dartCount parent] ++
    [.ifz test finishRoot finishChild])) c
  rw [addrOK_seqs_append]
  refine ⟨finishPrefix_addrOK hr hv hw hpost, ?_⟩
  change AddrOK L.limit (seqs [.ifz test finishRoot finishChild]) c₁
  simp only [addrOK_seqs_cons, addrOK_seqs_nil, and_true]
  apply AddrOK.ifz
  · intro _
    have ha : c₁.reg 170 + c₁.reg postLength < L.limit := by
      rw [hb₁.2.2.2.2.2 10 (by decide), hpost₁]
      exact Layout.cell_lt (by decide) (by omega)
    simp [finishRoot, pushPost, advanceScan, storeCell, AddrOK, run, seqs, ha]
  · intro hn
    have hp : s.par s.cur < 2 * G.E := by rw [htest₁] at hn; omega
    have ha : AddrOK L.limit (loadCell opposite 1 parent) c₁ :=
      loadCell_addrOK hb₁ _ _ _ (by decide) (by rw [hparent₁]; omega)
    let c₂ := run (loadCell opposite 1 parent) c₁
    have hb₂ : Bases L G c₂ := hb₁.run_aux (by
      intro r hn; simp [loadCell, seqs, regsW] at hn; omega)
    have hopp : c₂.reg opposite = STACS2027.Embed.pair (s.par s.cur) := by
      have hx := htable₁.partners _ hp
      simpa [c₂, loadCell, run, seqs, hparent₁, hb₁.2.2.2.2.2 1 (by decide), Layout.cell] using hx
    have ha₂ : AddrOK L.limit (loadCell current 0 opposite) c₂ :=
      loadCell_addrOK hb₂ _ _ _ (by decide) (by rw [hopp]; have := pair_lt hp; omega)
    exact AddrOK.seq ha ha₂


/-- Exploration reads only the selected bounded dart, its partner, and the neighbour state. -/
theorem exploreRead_addrOK {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (ht : Tables L G c) (hG : G.Ok)
    (hv : s.cur < 2 * G.E) (hp : c.reg pointer = s.ptr s.cur)
    (hk : s.ptr s.cur < (G.darts s.cur).length) (hw : 2 * G.E ≤ L.width) :
    AddrOK L.limit exploreRead c := by
  obtain ⟨hnd, _, hnw, _, _⟩ := DG.nw_facts hG hk
  let c₁ := run readNext c
  have hr₁ : Rep L G c₁ s := hr.run_readOnly (by decide) (by
    intro r hn; simp [readNext, loadCell, seqs, regsW] at hn; omega)
  have ht₁ : Tables L G c₁ := ht.run_readOnly (by decide)
  have hnext₁ : c₁.reg nextDart = G.nd s := readNext_value hr ht hv hp (by have := hG.deg s.cur; omega)
  have ha₁ := readNext_addrOK hr hv hw
  have ha₂ : AddrOK L.limit (loadCell opposite 1 nextDart) c₁ :=
    loadCell_addrOK hr₁.bases _ _ _ (by decide) (by rw [hnext₁]; omega)
  let c₂ := run (loadCell opposite 1 nextDart) c₁
  have hr₂ : Rep L G c₂ s := hr₁.run_readOnly (by decide) (by
    intro r hn; simp [loadCell, seqs, regsW] at hn; omega)
  have ht₂ : Tables L G c₂ := ht₁.run_readOnly (by decide)
  have hopp₂ : c₂.reg opposite = STACS2027.Embed.pair (G.nd s) := by
    have hx := ht₁.partners _ hnd
    simpa [c₂, loadCell, run, seqs, hnext₁, hr₁.bases.2.2.2.2.2 1 (by decide), Layout.cell] using hx
  have ha₃ : AddrOK L.limit (loadCell nextVertex 0 opposite) c₂ :=
    loadCell_addrOK hr₂.bases _ _ _ (by decide) (by rw [hopp₂]; have := pair_lt hnd; omega)
  let c₃ := run (loadCell nextVertex 0 opposite) c₂
  have hr₃ : Rep L G c₃ s := hr₂.run_readOnly (by decide) (by
    intro r hn; simp [loadCell, seqs, regsW] at hn; omega)
  have hvertex₃ : c₃.reg nextVertex = G.nw s := by
    have hx := ht₂.representatives _ (pair_lt hnd)
    simpa [c₃, loadCell, run, seqs, hopp₂, hr₂.bases.2.2.2.2.2 0 (by decide), Layout.cell, DG.nw] using hx
  have ha₄ : AddrOK L.limit (loadCell value 9 nextVertex) c₃ :=
    loadCell_addrOK hr₃.bases _ _ _ (by decide) (by rw [hvertex₃]; omega)
  simp only [exploreRead, addrOK_seqs_cons, addrOK_seqs_nil, run_seqs_cons, run_seqs_nil]
  exact ⟨ha₁, ha₂, ha₃, ha₄, trivial⟩

/-- Advancing the adjacency pointer writes only the bounded current-vertex cell. -/
theorem explorePrefix_addrOK {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (ht : Tables L G c) (hG : G.Ok)
    (hv : s.cur < 2 * G.E) (hp : c.reg pointer = s.ptr s.cur)
    (hk : s.ptr s.cur < (G.darts s.cur).length) (hw : 2 * G.E ≤ L.width) :
    AddrOK L.limit explorePrefix c := by
  let c₁ := run exploreRead c
  let c₂ := run (.add pointer pointer 1) c₁
  have hr₁ : Rep L G c₁ s := hr.run_readOnly (by decide) (by
    intro r hn; simp [exploreRead, readNext, loadCell, seqs, regsW] at hn; omega)
  have hr₂ : Rep L G c₂ s := hr₁.run_readOnly (by decide) (by
    intro r hn; simp [regsW] at hn; omega)
  have ha₁ := exploreRead_addrOK hr ht hG hv hp hk hw
  have ha₂ : AddrOK L.limit (storeCell 8 current pointer) c₂ :=
    storeCell_addrOK hr₂.bases _ _ _ (by decide) (by rw [hr₂.current]; omega)
  simp only [explorePrefix, addrOK_seqs_cons, addrOK_seqs_nil, addrOK_add,
    addrOK_skip, run_seqs_cons, run_seqs_nil]
  exact ⟨ha₁, trivial, ha₂, trivial, trivial⟩

/-- Exploring either a new or an already visited neighbour has bounded memory accesses. -/
theorem exploreStep_addrOK {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (ht : Tables L G c) (hG : G.Ok)
    (hv : s.cur < 2 * G.E) (hp : c.reg pointer = s.ptr s.cur)
    (hk : s.ptr s.cur < (G.darts s.cur).length) (hw : 2 * G.E ≤ L.width)
    (hpost : s.post.length ≤ L.width) : AddrOK L.limit exploreStep c := by
  obtain ⟨hr₁, _, hnw, _⟩ := explorePrefix_refines hr ht hG hv hp hk hw hpost
  have hnwbound : (run explorePrefix c).reg nextVertex < 2 * G.E := by
    rw [hnw]; exact (DG.nw_facts hG hk).2.2.1
  refine AddrOK.seq (explorePrefix_addrOK hr ht hG hv hp hk hw) ?_
  apply AddrOK.ifz
  · intro _; exact exploreNew_addrOK hr₁ hv hnwbound hw
  · intro _; trivial

/-- The inside step chooses between bounded finishing and bounded adjacency exploration. -/
theorem insideStep_addrOK {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (ht : Tables L G c) (hG : G.Ok) (hI : G.Inv s)
    (hi : s.inner = true) (hw : 4 * G.E + 2 ≤ L.width) : AddrOK L.limit insideStep c := by
  have hv : s.cur < 2 * G.E := (hI.vert s.cur (by rw [(hI.path hi).1]; decide)).1
  have hpost : s.post.length ≤ 4 * G.E := (DG.bounds hI).2.2
  let c₁ := run insideRead c
  have hr₁ : Rep L G c₁ s := hr.run_readOnly (by decide) (by
    intro r hn; simp [insideRead, loadCell, seqs, regsW] at hn; omega)
  have ht₁ : Tables L G c₁ := ht.run_readOnly (by decide)
  obtain ⟨hptr, _, htest⟩ := insideRead_values hr ht hv
  refine AddrOK.seq (insideRead_addrOK hr hv (by omega)) ?_
  apply AddrOK.ifz
  · intro _; exact finishStep_addrOK hr₁ ht₁ hv hw hpost
  · intro hn
    have hk : s.ptr s.cur < (G.darts s.cur).length := by
      change c₁.reg test ≠ 0 at hn
      rw [htest] at hn
      omega
    exact exploreStep_addrOK hr₁ ht₁ hG hv hptr hk (by omega) (by omega)

/-- Every actual cached forest-search step stays inside the finite eleven-block layout. -/
theorem stepProgram_addrOK {L : Layout} {G : DG} {c : Config} {s : DS}
    (hr : Rep L G c s) (ht : Tables L G c) (hG : G.Ok) (hI : G.Inv s)
    (hw : 4 * G.E + 2 ≤ L.width) : AddrOK L.limit stepProgram c := by
  apply AddrOK.ifz
  · intro _; exact outsideStep_addrOK hr (by omega)
  · intro hn
    have hi : s.inner = true := by
      rw [hr.inner] at hn
      cases hs : s.inner <;> simp_all
    exact insideStep_addrOK hr ht hG hI hi hw

end STACS2027.Embed.DFSRAM
