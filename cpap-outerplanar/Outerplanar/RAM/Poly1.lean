module

public import Outerplanar.RAM.Poly1Slot
import Mathlib.Tactic

/-!
# Phase P1 of the polygon solver (structure): the main triple

`poly1` runs the stages

* A (`Poly1Csr`): the sorted neighbour lists `nbP pg n p` (two stable counting sorts of the
  arcs);
* B (`Poly1Enum`): the segments in the order `segEnum`, with the face vertex after their first
  end (`predNb`) and their sizes; the largest neighbours `lastNb` and the enumeration ids of the
  pairs `(x, lastNb x)`;
* C (`Poly1Order`): the segments in the order `segOrder` (a stable counting sort by size), the
  interface arrays `gSA`, `gSB`, `gNS`;
* D (`Poly1Order`): the segment ids of the enumerated segments (`posId`, the inverse
  permutation of the sort);
* E (`Poly1Face`): the face vertices `gFV` (`faceCat`, by walking the faces) and their offsets
  `gFOFF` (`faceOffs`);
* F (`Poly1Slot`): the slot ids `gFSID` (`fsidCat`), parallel to `gFV`.

Every array has `O(n + |pg|)` cells; no table is indexed by pairs of positions.

`poly1_specB`: from `PolyIn pg n omap`, `poly1` reaches `Poly1Post pg n omap` within
`CP1 * (n + |pg| + 1)` steps (`CP1 = 450`), allocating at most `MP1 pg n = 27 |pg| + 8 n + 5`
fresh cells (`poly1_HG`, a bounded growth triple `HGMB S`), without output, every load and
store below any bound `S` leaving room for these cells (`PolyPhaseB`);
`poly1_wregs`: it writes only `rT`, `rFREE` and registers `≥ gP0` (in fact only `gNS … gFV`,
`84 … 99` and scratch registers); `poly1_writes`: no output instruction.
-/

@[expose] public section

namespace STACS2027.RAM.P1

open STACS2027.Poly

/-- **Phase P1** of the polygon solver. -/
def poly1 : Stmt := .seq stageA (.seq stageB (.seq stageC (.seq stageD (.seq stageE stageF))))

/-- The constant of the running time of P1. -/
def CP1 : ℕ := 450

/-- The registers written by P1. -/
abbrev W1 : List ℕ := wregs poly1

theorem W1_eq : W1 = WA ++ (WB ++ (WC ++ (WD ++ (WE ++ WF)))) := rfl

theorem mem_W1 {r : ℕ} :
    r ∈ W1 ↔ r ∈ WA ∨ r ∈ WB ∨ r ∈ WC ∨ r ∈ WD ∨ r ∈ WE ∨ r ∈ WF := by
  rw [W1_eq]; simp only [List.mem_append]

theorem not_mem_W1 {r : ℕ} (hA : r ∉ WA) (hB : r ∉ WB) (hC : r ∉ WC) (hD : r ∉ WD)
    (hE : r ∉ WE) (hF : r ∉ WF) : r ∉ W1 := by
  rw [mem_W1]; simp only [not_or]; exact ⟨hA, hB, hC, hD, hE, hF⟩

/-- The registers P1 may write: `rT`, `rFREE`, its interface registers `gNS … gFV`, its own
registers `gPx … 99` and scratch registers. -/
def Allowed (r : ℕ) : Prop :=
  r = rT ∨ r = rFREE ∨ (gNS ≤ r ∧ r ≤ gFV) ∨ (gPx ≤ r ∧ r ≤ 99) ∨ rS ≤ r

instance (r : ℕ) : Decidable (Allowed r) := by unfold Allowed; infer_instance

/-- P1 writes only the registers allowed to it. -/
theorem poly1_wregs' : ∀ r ∈ wregs poly1, Allowed r := by
  have hA : ∀ r ∈ WA, Allowed r := by
    simp only [WA, stageA, wregs_seq, List.forall_mem_append]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
  have hB : ∀ r ∈ WB, Allowed r := by
    simp only [WB, stageB, enOuter, wregs_seq, List.forall_mem_append]
    refine ⟨?_, ?_⟩ <;> decide
  have hC : ∀ r ∈ WC, Allowed r := by
    simp only [WC, stageC, wregs_seq, List.forall_mem_append]
    refine ⟨?_, ?_, ?_⟩ <;> decide
  have hD : ∀ r ∈ WD, Allowed r := by decide
  have hE : ∀ r ∈ WE, Allowed r := by
    simp only [WE, stageE, wregs_seq, List.forall_mem_append]
    refine ⟨?_, ?_, ?_⟩ <;> decide
  have hF : ∀ r ∈ WF, Allowed r := by
    simp only [WF, stageF, wregs_seq, List.forall_mem_append]
    refine ⟨?_, ?_⟩ <;> decide
  intro r hr
  rcases mem_W1.mp hr with h | h | h | h | h | h
  exacts [hA r h, hB r h, hC r h, hD r h, hE r h, hF r h]

/-- **P1 writes only `rT`, `rFREE` and registers at or above `gP0`.** -/
theorem poly1_wregs : ∀ r ∈ wregs poly1, r = rT ∨ r = rFREE ∨ gP0 ≤ r := by
  intro r hr
  rcases poly1_wregs' r hr with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (by have := h.1; simp only [gNS, gP0] at this ⊢; omega))
  · exact Or.inr (Or.inr (by have := h.1; simp only [gPx, gP0] at this ⊢; omega))
  · exact Or.inr (Or.inr (by simp only [rS, gP0] at h ⊢; omega))

/-- **P1 does not write output.** -/
theorem poly1_writes : writes poly1 = false := by decide

variable {pg : Graph} {n : ℕ}

/-- The fresh cells of P1. -/
def MP1 (pg : Graph) (n : ℕ) : ℕ := 27 * pg.length + 8 * n + 5

/-- The growth triple of P1 in bounded space, with the growth of the free pointer. -/
theorem poly1_HG {S : ℕ} (omap : List ℕ) (hP : IsPolygon pg n) (hlt : ∀ e ∈ pg, e.1 < e.2)
    (hnd : pg.Nodup) :
    HGMB S poly1 W1 (fun c => PolyIn pg n omap c ∧ c.reg gPE = pg.length)
      (fun c => (SlotSt pg n c ∧ Zf c) ∧ FaceSt pg n c ∧ OrdSt pg n c ∧ EnumSt pg n c)
      (408 * pg.length + 73 * n + 225) (MP1 pg n) := by
  have hA := ((stageA_spec (S := S) omap hP hlt hnd).frame (F := fun c => c.reg gPE = pg.length)
    (Stable.regEq (by decide) _)).mono (W' := W1) (fun _ h => mem_W1.mpr (Or.inl h))
    (fun _ h => h) (fun _ h => h) le_rfl le_rfl
  have hB := ((stageB_spec (S := S) hP hlt hnd).frame (F := fun c => c.reg gPN = n)
    (Stable.regEq (by decide) _)).mono (W' := W1) (fun _ h => mem_W1.mpr (Or.inr (Or.inl h)))
    (P' := fun c => ((Csr pg n c ∧ Zf c) ∧ ArcSt pg n c) ∧ c.reg gPE = pg.length)
    (fun _ h => ⟨⟨h.1.1, h.1.2.1, h.2⟩, h.1.2.1⟩) (fun _ h => h) le_rfl le_rfl
  have hC := (stageC_spec (S := S) (pg := pg) (n := n)).mono (W' := W1)
    (fun _ h => mem_W1.mpr (Or.inr (Or.inr (Or.inl h))))
    (P' := fun c => (EnumSt pg n c ∧ Zf c) ∧ c.reg gPN = n) (fun _ h => h) (fun _ h => h) le_rfl
    le_rfl
  have hD := ((stageD_spec (S := S) (pg := pg) (n := n)).frame
    (F := fun c => OrdSt pg n c ∧ EnumSt pg n c)
    ((stable_ordSt (by decide)).and (stable_enumSt (by decide)))).mono (W' := W1)
    (fun _ h => mem_W1.mpr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    (P' := fun c => (OrdSt pg n c ∧ Zf c) ∧ (EnumSt pg n c ∧ c.reg gPN = n))
    (fun _ h => ⟨h, h.1.1, h.2.1⟩) (fun _ h => h) le_rfl le_rfl
  have hE := ((stageE_spec (S := S) (pg := pg) (n := n) hP).frame
    (F := fun c => PosSt pg n c ∧ OrdSt pg n c ∧ EnumSt pg n c)
    ((Stable.tabAt (by decide) _).and ((stable_ordSt (by decide)).and
      (stable_enumSt (by decide))))).mono (W' := W1)
    (fun _ h => mem_W1.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    (P' := fun c => (PosSt pg n c ∧ Zf c) ∧ (OrdSt pg n c ∧ EnumSt pg n c))
    (fun _ h => ⟨⟨h.1.2, h.2.1, h.2.2⟩, h.1.1, h.2.1, h.2.2⟩) (fun _ h => h) le_rfl le_rfl
  have hF := ((stageF_spec (S := S) (pg := pg) (n := n) hP).frame
    (F := fun c => FaceSt pg n c ∧ OrdSt pg n c ∧ EnumSt pg n c)
    ((stable_faceSt (by decide)).and ((stable_ordSt (by decide)).and
      (stable_enumSt (by decide))))).mono (W' := W1)
    (fun _ h => mem_W1.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
    (P' := fun c => (FaceSt pg n c ∧ Zf c) ∧ (PosSt pg n c ∧ OrdSt pg n c ∧ EnumSt pg n c))
    (fun _ h => ⟨⟨h.1, h.2.2.1, h.2.2.2, h.2.1⟩, h.1.1, h.2.2.1, h.2.2.2⟩) (fun _ h => h) le_rfl
    le_rfl
  exact (hA.seq (hB.seq (hC.seq (hD.seq (hE.seq hF))))).weaken (by omega) (by unfold MP1; omega)

/-- **Phase P1** (structure), in bounded space: from `PolyIn pg n omap`, `poly1` reaches
`Poly1Post pg n omap` within `CP1 * (n + |pg| + 1)` steps by a run touching only addresses below
any bound `S ≥ F + CP1 * (n + |pg| + 1)` (`F` the initial free pointer), allocating at most
`MP1 pg n ≤ CP1 * (n + |pg| + 1)` fresh cells, without output. -/
theorem poly1_specB (pg : Graph) (n : ℕ) (omap : List ℕ) (hP : IsPolygon pg n)
    (hlt : ∀ e ∈ pg, e.1 < e.2) (hnd : pg.Nodup) :
    PolyPhaseB poly1 pg n (PolyIn pg n omap) (Poly1Post pg n omap) CP1 := by
  intro S c₀ hS
  refine HTB.of_forall fun c₁ ⟨hc, h1⟩ => ?_
  subst h1
  have hthree := hP.three_le
  have hC : MP1 pg n ≤ CP1 * (n + pg.length + 1) := by unfold MP1 CP1; omega
  refine ((poly1_HG omap hP hlt hnd).bound c₁ (by omega)).mono
    (fun c hc' => ⟨⟨hc' ▸ hc, hc' ▸ hc.pe⟩, hc'⟩) ?_ ?_
  · rintro c ⟨⟨⟨hS, hZ⟩, hF, hO, hE⟩, hg, hfree⟩
    have hb := hc.below
    have hlen := length_segOrder (pg := pg) (n := n)
    have hn : ∀ {r}, r ∉ WA → r ∉ WB → r ∉ WC → r ∉ WD → r ∉ WE → r ∉ WF → c.reg r = c₁.reg r :=
      fun hA hB hC hD hE hF => hg.reg _ (not_mem_W1 hA hB hC hD hE hF)
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hc.omap_len, hZ, ?_⟩, ?_, hO.2.1.1, hO.2.2.1, hS.1,
      hF.1.1, hF.2.1, ?_⟩, hg.out, hg.mem, hg.free, by omega⟩
    · rw [hn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hc.zero
    · rw [hn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hc.one
    · rw [hn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hc.pn
    · rw [hn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hc.pe
    · exact hg.arr (not_mem_W1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hc.pu (by simpa using hb.1)
    · exact hg.arr (not_mem_W1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hc.pv (by simpa using hb.2.1)
    · exact hg.arr (not_mem_W1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hc.om (by rw [hc.omap_len]; exact hb.2.2)
    · exact ⟨hg.le (not_mem_W1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hb.1,
        hg.le (not_mem_W1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hb.2.1,
        hg.le (not_mem_W1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hb.2.2⟩
    · rw [hE.1, hlen]
    · have h1 := hO.2.1.2
      have h2 := hO.2.2.2
      have h3 := hF.1.2
      have h4 := hF.2.2
      have h5 := hS.2
      simp only [List.length_map, faceOffs, prefixSums, List.length_range] at h1 h2 h3 h4
      exact ⟨h1, h2, h5, h3, h4⟩
  · simp only [CP1]
    nlinarith

end STACS2027.RAM.P1
