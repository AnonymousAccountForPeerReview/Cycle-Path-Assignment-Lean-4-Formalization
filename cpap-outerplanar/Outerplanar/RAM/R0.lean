module

public import Outerplanar.RAM.R0Edges
import Mathlib.Tactic

/-!
# Phase R0 (parsing): the main triple

`r0_spec`: started on `initial (graphInput g)`, the program `r0` halts within
`C0 * (g.length + 1)` steps (`C0 = 300`), accessing only the addresses below any
`S ≥ endR0 g` (`endR0_le`: `endR0 g ≤ 20 * (labelBound g + g.length + 1)`), in a configuration
satisfying `R0Post g`:

* `rZERO = 0`, `rONE = 1`, `gM = m`, `gN = numV g`, `gNE = (idEdges g).length`,
  `gMX = maxLab g` (every label is at most `gMX`), the output is empty;
* the arrays `labels g` at `gLB`, the edge ends `(idEdges g).map Prod.fst` at `gEU` and
  `(idEdges g).map Prod.snd` at `gEV`;
* the dictionary `Tab c.mem gD (gMX + 1) (dictOf (labels g))` (so `mem[gD + x] = idOf g x + 1`
  for a label `x`, `dictOf_labels`, and `0` for other `x ≤ gMX`), the input itself;
* the layout: these regions are disjoint, in this order, below `rFREE = endR0 g`, and
  `ZeroFrom c.mem (c.reg rFREE)`.

There is no adjacency matrix any more: the edges are deduplicated by the module
`PairIds.pairLeads`, so the memory is linear in `labelBound g + g.length`.
-/

@[expose] public section

namespace STACS2027.RAM.R0

open STACS2027.Algo

variable {S : ℕ}

/-- The state after phase R0 (the interface for the later phases). -/
structure R0Post (g : Graph) (c : Config) : Prop where
  zero : c.reg rZERO = 0
  one : c.reg rONE = 1
  m : c.reg gM = g.length
  mx : c.reg gMX = maxLab g
  n : c.reg gN = numV g
  ne : c.reg gNE = (idEdges g).length
  out : c.out = []
  input : Arr c.mem 0 (graphInput g)
  lb : Arr c.mem (c.reg gLB) (labels g)
  eu : Arr c.mem (c.reg gEU) ((idEdges g).map Prod.fst)
  ev : Arr c.mem (c.reg gEV) ((idEdges g).map Prod.snd)
  dict : Tab c.mem (c.reg gD) (c.reg gMX + 1) (dictOf (labels g))
  free : ZeroFrom c.mem (c.reg rFREE)
  layout : c.reg gD = 2 * g.length + 1 ∧ c.reg gD + c.reg gMX < c.reg gLB ∧
    c.reg gLB + 2 * g.length ≤ c.reg gEU ∧ c.reg gEU + g.length ≤ c.reg gEV ∧
    c.reg gEV + g.length ≤ c.reg rFREE
  fin : c.reg rFREE = endR0 g

/-- Every label is at most `gMX`. -/
theorem R0Post.labels_le {g : Graph} {c : Config} (h : R0Post g c) {x : ℕ} (hx : x ∈ labels g) :
    x ≤ c.reg gMX := h.mx ▸ labels_le_maxLab hx

/-- The dictionary entry of a label. -/
theorem R0Post.dict_label {g : Graph} {c : Config} (h : R0Post g c) {x : ℕ} (hx : x ∈ labels g) :
    c.mem (c.reg gD + x) = idOf g x + 1 := by
  rw [h.dict.get (by have := h.labels_le hx; omega), dictOf_labels hx]

/-- The constant of the running time of R0. -/
def C0 : ℕ := 300

theorem labels_take_zero (g : Graph) : labels (g.take 0) = [] := by simp [labels, proper]

/-- R0 without the frame facts (register `0`, output). -/
theorem r0_core (g : Graph) (hS : endR0 g ≤ S) :
    HTB S r0 (fun c => c = initial (graphInput g)) (fun c => KeepInv g (idPairs g).length c)
      (24 * g.length + 7 + (22 + (g.length * 31 + 3 + ((4 + (g.length * 33 + 3)) +
        (PairIds.CL * (numV g + (idPairs g).length + 1) + (1 + ((idPairs g).length * 22 + 3))))))) := by
  have h₂ := (stepLayout_spec (S := S) g).post (Q' := fun c => LabInv g 0 c ∧ c.reg gM = g.length)
    fun c ⟨hR, hp⟩ => ⟨⟨by rw [labels_take_zero]; exact hR, hp⟩, hR.glob.m⟩
  have h₄ := (stepIds_spec g hS)
  have h₆ := (stepKeep_spec g hS).post (Q' := fun c => KeepInv g (idPairs g).length c) fun c h => h.1
  exact (stepMax_spec g hS).seq (h₂.seq ((stepLabels_spec g hS).seq (h₄.seq
    ((pairLeads_r0 g hS).seq h₆))))

theorem keepInv_post {g : Graph} {c : Config} (h : KeepInv g (idPairs g).length c)
    (h0 : c.reg rZERO = 0) (ho : c.out = []) : R0Post g c := by
  obtain ⟨hK, hne, hM⟩ := h
  rw [List.take_length, ← idEdges_eq] at hne
  have hL := layout_eqs g
  have hG := hK.glob
  have hlen := length_idEdges_le g
  have hn := numV_le g
  have hle := PairIds.leads_eqs (numV g) (idPairs g).length (baseB2 g)
  refine ⟨h0, hG.one, hG.m, hG.mx, hK.n, hne, ho, hM.static.input, ?_, ?_, ?_, ?_, ?_, ?_,
    hK.free⟩
  · rw [hG.lb]; exact hM.static.lab.prefix
  · rw [hG.eu]; have := hM.eu; rwa [List.take_length, ← idEdges_eq] at this
  · rw [hG.ev]; have := hM.ev; rwa [List.take_length, ← idEdges_eq] at this
  · rw [hG.d, hG.mx]; exact hM.static.dict
  · rw [hK.free]; exact hM.zero
  · rw [hG.d, hG.mx, hG.lb, hG.eu, hG.ev, hK.free, hL.2.2.2.2.2.2.2]
    omega

/-- The register `0` is not written by `r0`. -/
theorem r0_zero : rZERO ∉ wregs r0 := by
  simp only [r0, wregs_seq, List.mem_append, not_or]
  exact ⟨by decide, by decide, by decide, by decide,
    PairIds.not_mem_wregs_pairLeads (by decide) (by decide) (by decide), by decide⟩

/-- `r0` does not write output. -/
theorem r0_writes : writes r0 = false := by
  simp only [r0, writes_seq, PairIds.pairLeads_writes]; decide

/-- **Phase R0 within linear space**: from the initial configuration on `graphInput g`, the
program `r0` halts within `C0 * (g.length + 1)` steps, accessing only the addresses below any
`S ≥ endR0 g` (`endR0 g ≤ 20 * (labelBound g + g.length + 1)`, `endR0_le`), in a configuration
satisfying `R0Post g` (whose first free address is `endR0 g`). -/
theorem r0_spec (g : Graph) (hS : endR0 g ≤ S) :
    HTB S r0 (fun c => c = initial (graphInput g)) (R0Post g) (C0 * (g.length + 1)) := by
  have h := (r0_core g hS).frame (F := fun c => c.reg rZERO = 0 ∧ c.out = [])
    fun c c' hfr ⟨h0, ho⟩ => ⟨(hfr.reg 0 r0_zero).trans h0, (hfr.out r0_writes).trans ho⟩
  have hn := numV_le g
  have hl := length_idPairs_le g
  refine h.mono (fun c hc => ⟨hc, by subst hc; simp, by subst hc; simp⟩)
    (fun c ⟨hE, h0, ho⟩ => keepInv_post hE h0 ho) ?_
  simp only [C0, PairIds.CL]
  omega

end STACS2027.RAM.R0
