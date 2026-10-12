module

public import ApproximationHardness.Embed.DFSRun
public import ApproximationHardness.RAM.SpecB
public import ApproximationHardness.RAM.Pass
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-! # Bounded RAM depth-first search with cached adjacency

All adjacency lists have length at most three and are supplied in ascending dart
order. Each machine step realizes exactly one step of the existing forest
search. Artifact date: 2026-10-12.
-/

@[expose] public section

namespace STACS2027.Embed.DFSRAM

open RAM

structure Layout where
  base : Nat
  width : Nat

def Layout.block (L : Layout) (j : Nat) := L.base + j * L.width
def Layout.cell (L : Layout) (j i : Nat) := L.block j + i
def Layout.limit (L : Layout) := L.base + 11 * L.width

abbrev dartCount := 140
abbrev scan := 141
abbrev current := 142
abbrev inner := 143
abbrev height := 144
abbrev postLength := 145
abbrev remaining := 146
abbrev baseRegister := 147
abbrev widthRegister := 148
abbrev address := 180
abbrev pointer := 181
abbrev degree := 182
abbrev nextDart := 183
abbrev opposite := 184
abbrev nextVertex := 185
abbrev parent := 186
abbrev value := 187
abbrev needHeight := 188
abbrev test := 189
abbrev otherTest := 190
abbrev repValue := 191

attribute [local simp] dartCount scan current inner height postLength remaining
  baseRegister widthRegister address pointer degree nextDart opposite nextVertex
  parent value needHeight test otherTest repValue

def Bases (L : Layout) (G : DG) (c : Config) : Prop :=
  c.reg 0 = 0 ∧ c.reg 1 = 1 ∧ c.reg dartCount = 2 * G.E ∧
    c.reg baseRegister = L.base ∧ c.reg widthRegister = L.width ∧
    ∀ j, j < 11 → c.reg (160 + j) = L.block j

structure Tables (L : Layout) (G : DG) (c : Config) : Prop where
  representatives : ∀ d, d < 2 * G.E → c.mem (L.cell 0 d) = G.rep d
  partners : ∀ d, d < 2 * G.E → c.mem (L.cell 1 d) = STACS2027.Embed.pair d
  degrees : ∀ v, v < 2 * G.E → c.mem (L.cell 2 v) = (G.darts v).length
  adjacent : ∀ k, k < 3 → ∀ v, v < 2 * G.E →
    c.mem (L.cell (3 + k) v) = (G.darts v).getD k 0

structure Rep (L : Layout) (G : DG) (c : Config) (s : DS) : Prop where
  bases : Bases L G c
  scan : c.reg DFSRAM.scan = s.r
  current : c.reg DFSRAM.current = s.cur
  inner : c.reg DFSRAM.inner = if s.inner then 1 else 0
  height : c.reg DFSRAM.height = s.H
  postLength : c.reg DFSRAM.postLength = s.post.length
  parents : ∀ v, v < 2 * G.E → c.mem (L.cell 6 v) = s.par v
  depths : ∀ v, v < 2 * G.E → c.mem (L.cell 7 v) = s.depth v
  pointers : ∀ v, v < 2 * G.E → c.mem (L.cell 8 v) = s.ptr v
  states : ∀ v, v < 2 * G.E → c.mem (L.cell 9 v) = s.st v
  post : ∀ i, i < s.post.length → c.mem (L.cell 10 i) = s.post.getD i 0

def loadCell (dst block index : Nat) : Stmt := seqs [
  .add address (160 + block) index, .load dst address]

def storeCell (block index src : Nat) : Stmt := seqs [
  .add address (160 + block) index, .store address src]

def pushPost (src : Nat) : Stmt := .seq (storeCell 10 postLength src)
  (.add postLength postLength 1)

def advanceScan : Stmt := .add scan scan 1

def startRoot : Stmt := seqs [
  storeCell 9 scan 1, storeCell 6 scan dartCount, storeCell 7 scan 0,
  .add current scan 0, .const inner 1, .ifz height (.const height 1) .skip]

def outsideRead : Stmt := seqs [loadCell repValue 0 scan,
  .sub test repValue scan, .sub otherTest scan repValue, loadCell value 9 scan]

def outsideStep : Stmt := seqs [
  .sub test dartCount scan,
  .ifz test .skip (.seq outsideRead (
    .ifz test (.ifz otherTest
      (.ifz value startRoot advanceScan) advanceScan)
      advanceScan))]

def readNext : Stmt := .ifz pointer (loadCell nextDart 3 current)
  (.seq (.sub test pointer 1)
    (.ifz test (loadCell nextDart 4 current) (loadCell nextDart 5 current)))

def exploreNew : Stmt := seqs [
  storeCell 9 nextVertex 1, storeCell 6 nextVertex opposite,
  loadCell value 7 current, .add value value 1, storeCell 7 nextVertex value,
  .add needHeight value 1, .sub test needHeight height,
  .ifz test .skip (.add height needHeight 0), .add current nextVertex 0]

def exploreRead : Stmt := seqs [
  readNext, loadCell opposite 1 nextDart, loadCell nextVertex 0 opposite,
  loadCell value 9 nextVertex]

def explorePrefix : Stmt := seqs [exploreRead,
  .add pointer pointer 1, storeCell 8 current pointer,
  .skip]

def exploreStep : Stmt := .seq explorePrefix (.ifz value exploreNew .skip)

def finishRoot : Stmt := seqs [
  .add value dartCount current, pushPost value, .const inner 0, advanceScan]

def finishChild : Stmt := .seq (loadCell opposite 1 parent) (loadCell current 0 opposite)

def finishStep : Stmt := seqs [
  .const value 2, storeCell 9 current value, pushPost current,
  loadCell parent 6 current, .sub test dartCount parent,
  .ifz test finishRoot finishChild]

def insideRead : Stmt := seqs [loadCell pointer 8 current,
  loadCell degree 2 current, .sub test degree pointer]

def insideStep : Stmt := .seq insideRead (.ifz test finishStep exploreStep)

def stepProgram : Stmt := .ifz inner outsideStep insideStep

def loopBody : Stmt := .seq stepProgram (.sub remaining remaining 1)
def program : Stmt := .loop remaining loopBody

theorem stepProgram_loopFree : LoopFree stepProgram := by
  simp [stepProgram, outsideStep, outsideRead, insideStep, insideRead, startRoot,
    exploreStep, explorePrefix, exploreRead, exploreNew,
    finishStep, finishRoot, finishChild, advanceScan, readNext, pushPost,
    loadCell, storeCell, LoopFree, seqs]

theorem stepProgram_size : size stepProgram ≤ 250 := by decide

theorem Layout.cell_lt {L : Layout} {j i : Nat} (hj : j < 11) (hi : i < L.width) :
    L.cell j i < L.limit := by
  dsimp [Layout.cell, Layout.block, Layout.limit]
  have := Nat.mul_le_mul_right L.width (show j + 1 ≤ 11 by omega)
  rw [Nat.add_mul] at this
  omega

theorem Layout.cell_injective {L : Layout} {j k i a : Nat}
    (hi : i < L.width) (ha : a < L.width) (h : L.cell j i = L.cell k a) :
    j = k ∧ i = a := by
  dsimp [Layout.cell, Layout.block] at h
  have : j = k := by
    apply Classical.byContradiction
    intro hn
    rcases Nat.lt_or_gt_of_ne hn with hjk | hkj
    · have hm := Nat.mul_le_mul_right L.width (show j + 1 ≤ k by omega)
      rw [Nat.add_mul] at hm
      omega
    · have hm := Nat.mul_le_mul_right L.width (show k + 1 ≤ j by omega)
      rw [Nat.add_mul] at hm
      omega
  exact ⟨this, by subst this; omega⟩

theorem update_cell (L : Layout) (m : Nat → Nat) (j k i a x : Nat)
    (hi : i < L.width) (ha : a < L.width) :
    upd m (L.cell k a) x (L.cell j i) =
      if j = k ∧ i = a then x else m (L.cell j i) := by
  simp only [upd]
  have hiff : L.cell j i = L.cell k a ↔ j = k ∧ i = a :=
    ⟨Layout.cell_injective hi ha, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [hiff]

theorem Bases.frame {L : Layout} {G : DG} {c d : Config} (h : Bases L G c)
    (hf : ∀ r, r = 0 ∨ r = 1 ∨ r = dartCount ∨ r = baseRegister ∨
      r = widthRegister ∨ (160 ≤ r ∧ r < 171) → d.reg r = c.reg r) : Bases L G d := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hf 0 (by simp)]; exact h.1
  · rw [hf 1 (by simp)]; exact h.2.1
  · rw [hf dartCount (by simp)]; exact h.2.2.1
  · rw [hf baseRegister (by simp)]; exact h.2.2.2.1
  · rw [hf widthRegister (by simp)]; exact h.2.2.2.2.1
  · intro j hj
    rw [hf (160 + j) (by omega)]
    exact h.2.2.2.2.2 j hj

theorem Bases.run_step {L : Layout} {G : DG} {c : Config} (h : Bases L G c) :
    Bases L G (run stepProgram c) := by
  apply h.frame
  intro r hr
  simp only [dartCount, baseRegister, widthRegister] at hr
  apply run_reg_frame
  simp [stepProgram, outsideStep, outsideRead, insideStep, insideRead, startRoot,
    exploreStep, explorePrefix, exploreRead, exploreNew,
    finishStep, finishRoot, finishChild, advanceScan, readNext, pushPost,
    loadCell, storeCell, regsW, seqs]
  rcases hr with hr | hr | hr | hr | hr | hr <;> omega

theorem stepProgram_remaining (c : Config) :
    (run stepProgram c).reg remaining = c.reg remaining := by
  apply run_reg_frame
  decide

theorem stepProgram_out (c : Config) : (run stepProgram c).out = c.out := by
  apply run_out_frame
  decide

theorem startRoot_raw (c : Config) (hz : c.reg 0 = 0) (h1 : c.reg 1 = 1) :
    let d := run startRoot c
    d.reg scan = c.reg scan ∧ d.reg current = c.reg scan ∧ d.reg inner = 1 ∧
      d.reg height = max (c.reg height) 1 ∧ d.reg postLength = c.reg postLength ∧
      d.mem = upd (upd (upd c.mem (c.reg 169 + c.reg scan) 1)
        (c.reg 166 + c.reg scan) (c.reg dartCount)) (c.reg 167 + c.reg scan) 0 := by
  dsimp only
  by_cases hH : c.reg height = 0
  · simp [startRoot, storeCell, seqs, run, hz, h1, hH] <;> rfl
  · have hH' : 1 ≤ c.reg height := by omega
    simp [startRoot, storeCell, seqs, run, hz, h1, hH, Nat.max_eq_left hH'] <;> rfl

theorem finishStep_raw (c : Config) (hz : c.reg 0 = 0) (h1 : c.reg 1 = 1) :
    let m := upd (upd c.mem (c.reg 169 + c.reg current) 2)
      (c.reg 170 + c.reg postLength) (c.reg current)
    let p := m (c.reg 166 + c.reg current)
    let d := run finishStep c
    d.reg scan = (if c.reg dartCount ≤ p then c.reg scan + 1 else c.reg scan) ∧
    d.reg current = (if c.reg dartCount ≤ p then c.reg current
      else m (c.reg 160 + m (c.reg 161 + p))) ∧
    d.reg inner = (if c.reg dartCount ≤ p then 0 else c.reg inner) ∧
    d.reg height = c.reg height ∧
    d.reg postLength = c.reg postLength + (if c.reg dartCount ≤ p then 2 else 1) ∧
    d.mem = if c.reg dartCount ≤ p then
      upd (upd (upd c.mem (c.reg 169 + c.reg current) 2)
        (c.reg 170 + c.reg postLength) (c.reg current))
        (c.reg 170 + c.reg postLength + 1) (c.reg dartCount + c.reg current)
    else upd (upd c.mem (c.reg 169 + c.reg current) 2)
      (c.reg 170 + c.reg postLength) (c.reg current) := by
  dsimp only
  simp [finishStep, finishRoot, finishChild, advanceScan, pushPost, storeCell,
    loadCell, seqs, run, hz, h1, Nat.sub_eq_zero_iff_le, upd, Nat.add_assoc,
    Config.setMem, Config.setReg]
  split_ifs <;> exact ⟨rfl, rfl⟩

end STACS2027.Embed.DFSRAM
