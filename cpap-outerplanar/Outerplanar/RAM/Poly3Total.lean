module

public import Outerplanar.RAM.Poly3Child
import Mathlib.Tactic

/-!
# Phase P3 of the polygon solver: the total of a configuration

`total` computes `totV s vals` (the local cost of the segment `s` plus the table entries of
its children, `totV_eq`) into `rTOT` (`total_spec`): the load cost of `s` itself, then the
slots `(x, y)` of the face of `s` (`slotBody_spec`): a side `y = x + 1` adds its load cost
(`loadCost_spec`), a child its table entry (`childCost_spec`).
-/

@[expose] public section

namespace STACS2027.RAM.P3

open STACS2027.Poly STACS2027.RAM.P1

variable {pg : Graph} {n k : ℕ}

theorem fOff_eq (j : ℕ) :
    fOff pg n j = (((segOrder pg n).take j).map fun t => (faceVerts pg n t).length).sum := by
  rw [fOff, List.length_flatMap]

/-- The slot `q` of the face of `s`. -/
def slotAt (pg : Graph) (n : ℕ) (s : ℕ × ℕ) (q : ℕ) : ℕ × ℕ :=
  ((faceVerts pg n s).getD q 0, (faceVerts pg n s).getD (q + 1) 0)

/-- The total after `q` slots. -/
def totQ (pg : Graph) (n k j : ℕ) (vals : List ℕ) (q : ℕ) : ℕ :=
  pairCount (loadAt pg n k (sg pg n j) vals (sg pg n j)) +
    ((List.range q).map fun q' => slotCost pg n k (sg pg n j) vals (slotAt pg n (sg pg n j) q')).sum

theorem slotAt_mem {s : ℕ × ℕ} {q : ℕ} (hq : q < (faceVerts pg n s).length - 1) :
    slotAt pg n s q ∈ slots pg n s := by
  rw [slots, pairs_eq_map]
  exact List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩

theorem totQ_full (j : ℕ) (vals : List ℕ) :
    totQ pg n k j vals ((faceVerts pg n (sg pg n j)).length - 1) = totV pg n k (sg pg n j) vals := by
  rw [totV_eq, totQ, slots, pairs_eq_map, List.map_map]
  rfl

/-- The bound of one slot. -/
def tSlot (k : ℕ) : ℕ := tLC k + tCC k + 25

theorem slotBody_spec {S j : ℕ} {vals : List ℕ} (G : Config → Prop)
    (hG : Indep (wregs (forUp rQ rFL slotBody)) G) (hGr : ∀ c, G c → Rd S pg n k j vals c)
    (hP : IsPolygon pg n) (hj : j < (segOrder pg n).length) (hk : 0 < k)
    (hvk : ∀ x ∈ vals, x < k) (hvl : vals.length = (rel pg n k (sg pg n j)).length)
    (q : ℕ) (hq : q < (faceVerts pg n (sg pg n j)).length - 1) :
    HTB S slotBody (fun c => (G c ∧ c.reg rTOT = totQ pg n k j vals q) ∧ c.reg rQ = q ∧
        c.reg rFL = (faceVerts pg n (sg pg n j)).length - 1)
      (fun c => (G c ∧ c.reg rTOT = totQ pg n k j vals (q + 1)) ∧ c.reg rQ = q ∧
        c.reg rFL = (faceVerts pg n (sg pg n j)).length - 1) (tSlot k) := by
  obtain ⟨x, y, hxyd⟩ : ∃ x y, slotAt pg n (sg pg n j) q = (x, y) := ⟨_, _, rfl⟩
  have hxy : x < y := by
    have := pairs_lt faceVerts_pairwise _ (slotAt_mem hq); rw [hxyd] at this; exact this
  have hsucc : totQ pg n k j vals (q + 1) =
      totQ pg n k j vals q + slotCost pg n k (sg pg n j) vals (x, y) := by
    rw [totQ, totQ, List.sum_range_succ, Nat.add_assoc, hxyd]
  have hx : (faceVerts pg n (segOrder pg n)[j]).getD q 0 = x := by
    rw [← sg_eq hj]; exact congrArg Prod.fst hxyd
  have hy : (faceVerts pg n (segOrder pg n)[j]).getD (q + 1) 0 = y := by
    rw [← sg_eq hj]; exact congrArg Prod.snd hxyd
  have hql : q + 1 < (faceVerts pg n (segOrder pg n)[j]).length := by rw [← sg_eq hj]; omega
  -- the frame of the branches
  let F : Config → Prop := fun c => (G c ∧ c.reg rQ = q ∧ c.reg rFL = (faceVerts pg n (sg pg n j)).length - 1) ∧ c.reg rX = x ∧ c.reg rY = y
  have hfl : fOff pg n j + (q + 1) < (faceCat pg n).length := by
    have := fOff_succ (pg := pg) (n := n) hj
    have := fOff_le_faceCat (pg := pg) (n := n) (j + 1)
    omega
  have h₁ : HTB S slotRd (fun c => (G c ∧ c.reg rTOT = totQ pg n k j vals q) ∧ c.reg rQ = q ∧
        c.reg rFL = (faceVerts pg n (sg pg n j)).length - 1)
      (fun c => (F c ∧ c.reg rTOT = totQ pg n k j vals q) ∧ c.reg rU = x + 1) 9 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hg, ht⟩, hq', hn⟩ => ?_
    have hR := hGr c hg
    have := hR.bfv
    refine ⟨by addr_ok [slotRd, hq', hR.fo], ?_⟩
    have hag : Agree (wregs (forUp rQ rFL slotBody)) c (RAM.run slotRd c) :=
      agree_run (by decide) rfl rfl (by decide) c
    have hfx : c.mem (c.reg gFV + (fOff pg n j + q)) = x := by
      rw [fOff_eq, arr_flatMap_seg_read _ hR.fv hj (by omega), hx]
    have hfy : c.mem (c.reg gFV + (fOff pg n j + q + 1)) = y := by
      rw [fOff_eq, Nat.add_assoc, arr_flatMap_seg_read _ hR.fv hj hql, hy]
    refine ⟨⟨⟨⟨hG c _ hag hg, ?_, ?_⟩, ?_, ?_⟩, ?_⟩, ?_⟩
    all_goals simp +decide only [slotRd, run_seq', run_add, run_ld, run_inc, run_addc, setReg_reg,
      ↓reduceIte, setReg_mem, hq', hn, hR.fo, hfx, hfy, ht]
  have hside : y = x + 1 → HTB S sideCost (fun c => (F c ∧ c.reg rTOT = totQ pg n k j vals q) ∧
      c.reg rY = c.reg rU)
      (fun c => (G c ∧ c.reg rTOT = totQ pg n k j vals (q + 1)) ∧ c.reg rQ = q ∧ c.reg rFL = (faceVerts pg n (sg pg n j)).length - 1)
      (tLC k + tCC k + 4) := by
    intro hyx
    have hm : HTB S (.seq (mov rEX rX) (mov rEY rY))
        (fun c => (F c ∧ c.reg rTOT = totQ pg n k j vals q) ∧ c.reg rY = c.reg rU)
        (fun c => (F c ∧ c.reg rEX = x ∧ c.reg rEY = y) ∧ c.reg rTOT = totQ pg n k j vals q) 4 := by
      refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨hf, ht⟩, _⟩ => ?_
      have hag : Agree (wregs (forUp rQ rFL slotBody)) c (RAM.run (.seq (mov rEX rX) (mov rEY rY)) c) :=
        agree_run (by decide) rfl rfl (by decide) c
      obtain ⟨⟨hg, hq', hn⟩, hx', hy'⟩ := hf
      refine ⟨⟨⟨⟨hG c _ hag hg, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
      all_goals simp +decide only [run_seq', run_mov, setReg_reg, ↓reduceIte, hq', hn, hx', hy', ht]
    have hl := loadCost_spec (pg := pg) (n := n) (k := k) (j := j) (vals := vals) (ex := x) (ey := y)
      (t0 := totQ pg n k j vals q) (fun c => F c ∧ c.reg rEX = x ∧ c.reg rEY = y) (by indepG hG)
      (fun c hc => ⟨hGr c hc.1.1.1, hc.2.1, hc.2.2⟩) hP hj hvk hvl hxy hk
    refine (hm.seq hl).mono (fun _ h => h) ?_ (by omega)
    rintro c ⟨⟨⟨⟨hg, hq', hn⟩, -, -⟩, -, -⟩, ht⟩
    refine ⟨⟨hg, ?_⟩, hq', hn⟩
    rw [ht, hsucc, slotCost]
    simp only [hyx, ↓reduceIte]
  have hchild : ¬ y = x + 1 → HTB S childCost (fun c => (F c ∧ c.reg rTOT = totQ pg n k j vals q) ∧
      c.reg rY ≠ c.reg rU)
      (fun c => (G c ∧ c.reg rTOT = totQ pg n k j vals (q + 1)) ∧ c.reg rQ = q ∧
        c.reg rFL = (faceVerts pg n (sg pg n j)).length - 1)
      (tLC k + tCC k + 4) := by
    intro hyx
    have hw : (x, y) ∈ childSegs pg n (sg pg n j) := by
      rw [childSegs, List.mem_filter, ← hxyd]
      exact ⟨slotAt_mem hq, by rw [hxyd]; simp only [decide_eq_true_eq]; omega⟩
    have hc := childCost_spec (pg := pg) (n := n) (k := k) (j := j) (vals := vals) (x := x) (y := y)
      (q := q) (t0 := totQ pg n k j vals q) F (by indepG hG)
      (fun c hc => ⟨hGr c hc.1.1, hc.1.2.1⟩) hP hj hk hvk hvl (by omega)
      (congrArg Prod.fst hxyd) (congrArg Prod.snd hxyd) hw
    refine hc.mono (fun c h => h.1) ?_ (by omega)
    rintro c ⟨⟨⟨hg, hq', hn⟩, -, -⟩, ht⟩
    refine ⟨⟨hg, ?_⟩, hq', hn⟩
    rw [ht, hsucc, slotCost]
    simp only [hyx, ↓reduceIte]
  have hP₁ : Indep [rT] (fun c => (F c ∧ c.reg rTOT = totQ pg n k j vals q) ∧ c.reg rU = x + 1) := by
    indepG hG
  have hif : HTB S (ifEq rY rU sideCost childCost)
      (fun c => (F c ∧ c.reg rTOT = totQ pg n k j vals q) ∧ c.reg rU = x + 1)
      (fun c => (G c ∧ c.reg rTOT = totQ pg n k j vals (q + 1)) ∧ c.reg rQ = q ∧
        c.reg rFL = (faceVerts pg n (sg pg n j)).length - 1) (tLC k + tCC k + 4 + 4) := by
    by_cases hyx : y = x + 1
    · refine HTB.ifEq (by decide) (by decide) hP₁ ((hside hyx).pre fun c h => ⟨h.1.1, h.2⟩) ?_
      intro c ⟨⟨⟨⟨_, _, hy'⟩, _⟩, hu⟩, hne⟩
      exact absurd (by rw [hy', hu, hyx]) hne
    · refine HTB.ifEq (by decide) (by decide) hP₁ ?_ ((hchild hyx).pre fun c h => ⟨h.1.1, h.2⟩)
      intro c ⟨⟨⟨⟨_, _, hy'⟩, _⟩, hu⟩, he⟩
      exact absurd (by rw [← hy', he, hu]) hyx
  exact (h₁.seq hif).weaken (by unfold tSlot; omega)

/-- The bound of `total` (per face vertex). -/
def tTot (k : ℕ) : ℕ := tSlot k + 12

/-- **The total of a configuration**: `total` computes `totV s vals` into `rTOT`. -/
theorem total_spec {S j : ℕ} {vals : List ℕ} (G : Config → Prop) (hG : Indep (wregs total) G)
    (hGr : ∀ c, G c → Rd S pg n k j vals c) (hP : IsPolygon pg n) (hj : j < (segOrder pg n).length)
    (hk : 0 < k) (hvk : ∀ x ∈ vals, x < k) (hvl : vals.length = (rel pg n k (sg pg n j)).length) :
    HTB S total G (fun c => G c ∧ c.reg rTOT = totV pg n k (sg pg n j) vals)
      (tTot k * ((faceVerts pg n (sg pg n j)).length + 1)) := by
  have hs := (of_mem_segs (sg_mem hj)).2
  have h₁ : HTB S totInit G (fun c => (G c ∧ c.reg rEX = (sg pg n j).1 ∧
      c.reg rEY = (sg pg n j).2) ∧ c.reg rTOT = 0) 5 := by
    refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c hg => ?_
    have hR := hGr c hg
    have hag : Agree (wregs total) c (RAM.run totInit c) := agree_run (by decide) rfl rfl (by decide) c
    refine ⟨⟨hG c _ hag hg, ?_, ?_⟩, ?_⟩
    all_goals simp +decide only [totInit, run_seq', run_const, run_mov, setReg_reg, ↓reduceIte,
      hR.sa, hR.sb]
  have h₂ := loadCost_spec (pg := pg) (n := n) (k := k) (j := j) (vals := vals)
    (ex := (sg pg n j).1) (ey := (sg pg n j).2) (t0 := 0)
    (fun c => G c ∧ c.reg rEX = (sg pg n j).1 ∧ c.reg rEY = (sg pg n j).2) (by indepG hG)
    (fun c hc => ⟨hGr c hc.1, hc.2.1, hc.2.2⟩) hP hj hvk hvl (by omega) hk
  have h₃ := HTB.forUpC (S := S) (i := rQ) (n := rFL) (N := (faceVerts pg n (sg pg n j)).length - 1)
    (body := slotBody) (fun q c => G c ∧ c.reg rTOT = totQ pg n k j vals q) (tSlot k)
    (by decide) (by decide) (by decide) (fun q => by indepG hG)
    (fun q hq => slotBody_spec G (hG.mono (by decide +kernel)) hGr hP hj hk hvk hvl q hq)
  have h₃' := h₃.pre (P' := fun c => (G c ∧ c.reg rEX = (sg pg n j).1 ∧ c.reg rEY = (sg pg n j).2) ∧
      c.reg rTOT = 0 + pairCount (loadAt pg n k (sg pg n j) vals ((sg pg n j).1, (sg pg n j).2)))
    (fun c h => ⟨⟨h.1.1, by rw [h.2, totQ]; simp⟩, (hGr c h.1.1).fl⟩)
  refine (h₁.seq (h₂.seq h₃')).mono (fun _ h => h) ?_ ?_
  · exact fun c ⟨⟨hg, ht⟩, _, _⟩ => ⟨hg, by rw [ht, totQ_full]⟩
  · have h1 : ((faceVerts pg n (sg pg n j)).length - 1) * (tSlot k + 4) ≤
        (faceVerts pg n (sg pg n j)).length * tTot k :=
      Nat.mul_le_mul (Nat.sub_le _ _) (by unfold tTot; omega)
    have h2 : tTot k * ((faceVerts pg n (sg pg n j)).length + 1) =
        (faceVerts pg n (sg pg n j)).length * tTot k + tTot k := by ring
    have htt : tTot k = tSlot k + 12 := rfl
    have hts : tSlot k = tLC k + tCC k + 25 := rfl
    rw [h2]; omega

end STACS2027.RAM.P3
