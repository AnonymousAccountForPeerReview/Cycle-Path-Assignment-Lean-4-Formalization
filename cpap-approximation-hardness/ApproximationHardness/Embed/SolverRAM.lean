module

public import ApproximationHardness.Embed.Frontier
public import ApproximationHardness.Embed.LinkedRAM
import Lean.Elab.Tactic.Omega

/-!
# RAM layout of the embedding solver

The solver uses twenty-two equal-width blocks. Its first twelve blocks hold
the mutable linked machine arrays; the remaining ten hold the plan and DFS
tables. Every block has a fixed base register, so indirect accesses use addition.
-/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

/-- The common width and the first address of the solver's contiguous blocks. -/
structure Layout where
  base : Nat
  width : Nat

def Layout.block (L : Layout) (j : Nat) : Nat := L.base + j * L.width
def Layout.cell (L : Layout) (j i : Nat) : Nat := L.block j + i
def Layout.limit (L : Layout) : Nat := L.base + 22 * L.width

theorem Layout.cell_lt {L : Layout} {j i : Nat} (hj : j < 22) (hi : i < L.width) :
    L.cell j i < L.limit := by
  dsimp [Layout.cell, Layout.block, Layout.limit]
  have := Nat.mul_le_mul_right L.width (show j + 1 ≤ 22 by omega)
  rw [Nat.add_mul] at this
  omega

theorem Layout.cell_injective {L : Layout} {j k i a : Nat}
    (hi : i < L.width) (ha : a < L.width) (h : L.cell j i = L.cell k a) :
    j = k ∧ i = a := by
  dsimp [Layout.cell, Layout.block] at h
  have hw : 0 < L.width := by omega
  have : j = k := by
    by_contra hn
    rcases Nat.lt_or_gt_of_ne hn with hjk | hkj
    · have hm := Nat.mul_le_mul_right L.width (show j + 1 ≤ k by omega)
      rw [Nat.add_mul] at hm
      omega
    · have hm := Nat.mul_le_mul_right L.width (show k + 1 ≤ j by omega)
      rw [Nat.add_mul] at hm
      omega
  exact ⟨this, by subst this; omega⟩

/-- The twelve mutable blocks in their fixed layout order. -/
def memField (m : SMem) : Nat → Nat → Nat
  | 0 => m.nx
  | 1 => m.ph
  | 2 => m.pt
  | 3 => m.mh
  | 4 => m.mt
  | 5 => m.gn
  | 6 => m.rs
  | 7 => m.rl
  | 8 => m.gp
  | 9 => m.gf
  | 10 => m.inf
  | 11 => m.ia
  | _ => fun _ => 0

/-- Every block base is held in its fixed register. -/
def Bases (L : Layout) (c : Config) : Prop :=
  c.reg 0 = 0 ∧ c.reg 1 = 1 ∧ c.reg 2 = L.base ∧ c.reg 3 = L.width ∧
    ∀ j, j < 22 → c.reg (50 + j) = L.block j

/-- The mutable arrays and the actual scalar state; the consumed list is ghost data. -/
structure Rep (L : Layout) (c : Config) (s : SMS) : Prop where
  bases : Bases L c
  arrays : ∀ j, j < 12 → ∀ i, i < L.width → c.mem (L.cell j i) = memField s.m j i
  index : c.reg 6 = s.k
  mode : c.reg 7 = s.mode
  node : c.reg 8 = s.v
  group : c.reg 9 = s.G
  upperLow : c.reg 10 = s.lh
  resultLow : c.reg 11 = s.lx
  upperHead : c.reg 12 = s.rxp
  lowerHead : c.reg 13 = s.ryp
  positiveHead : c.reg 14 = s.ah
  positiveTail : c.reg 15 = s.at'
  negativeHead : c.reg 16 = s.bh
  negativeTail : c.reg 17 = s.bt
  lowerClassHead : c.reg 18 = s.ch
  lowerClassTail : c.reg 19 = s.ct

def itemType : Item → Nat
  | .node _ => 0
  | .dart _ => 1

def itemValue : Item → Nat
  | .node v => v
  | .dart e => e

/-- The read-only plan tables supplied by formula preprocessing and DFS. -/
structure Tables (L : Layout) (c : Config) (S : Sol) (post : List Nat)
    (vertexBound dartBound : Nat) : Prop where
  vertices : vertexBound ≤ L.width
  darts : dartBound ≤ L.width
  length : c.reg 4 = post.length
  infinity : c.reg 5 = S.INF
  keys : ∀ e, e < dartBound → c.mem (L.cell 12 e) = S.key e
  partners : ∀ e, e < dartBound → c.mem (L.cell 13 e) = S.α e
  target : ∀ e, e < dartBound → c.mem (L.cell 14 e) = if S.isIn e then 1 else 0
  groupIds : ∀ v, v < vertexBound → c.mem (L.cell 15 v) = S.gid v
  counts : ∀ v, v < vertexBound → c.mem (L.cell 16 v) = (S.P.parts v).length
  leftType : ∀ v, v < vertexBound →
    c.mem (L.cell 17 v) = itemType ((S.P.parts v).getD 0 (.node 0))
  leftValue : ∀ v, v < vertexBound →
    c.mem (L.cell 18 v) = itemValue ((S.P.parts v).getD 0 (.node 0))
  rightType : ∀ v, v < vertexBound →
    c.mem (L.cell 19 v) = itemType ((S.P.parts v).getD 1 (.node 0))
  rightValue : ∀ v, v < vertexBound →
    c.mem (L.cell 20 v) = itemValue ((S.P.parts v).getD 1 (.node 0))
  order : ∀ i (hi : i < post.length), c.mem (L.cell 21 i) = post[i]'hi
  orderBound : post.length ≤ L.width
  nodeBound : ∀ v ∈ post, v < vertexBound
  partsBound : ∀ v, v < vertexBound → (S.P.parts v).length ≤ 2
  children : ∀ v, v < vertexBound → ∀ it ∈ S.P.parts v,
    match it with
    | .node w => w < vertexBound
    | .dart e => e < dartBound
  partnersBound : ∀ e, e < dartBound → S.α e < dartBound
  groupsBound : ∀ v, v < vertexBound → S.gid v < L.width

/-- Read one indexed block cell, using the fixed address scratch register. -/
def loadCell (dst block index : Nat) : Stmt :=
  seqs [.add 40 (50 + block) index, .load dst 40]

/-- Write one indexed block cell. -/
def storeCell (block index src : Nat) : Stmt :=
  seqs [.add 40 (50 + block) index, .store 40 src]

/-- Concatenate a class into a scalar head/tail pair. Operands are snapshotted first. -/
def appendInto (head tail otherHead otherTail : Nat) : Stmt := seqs [
  .add 32 head 0, .add 33 tail 0, .add 34 otherHead 0, .add 35 otherTail 0,
  .ifz 32 (seqs [.add head 34 0, .add tail 35 0])
    (.ifz 34 .skip (seqs [.sub 40 33 1, .add 40 50 40, .store 40 34, .add tail 35 0]))]

theorem appendInto_loopFree (head tail otherHead otherTail : Nat) :
    LoopFree (appendInto head tail otherHead otherTail) := by
  simp [appendInto, LoopFree, seqs]

theorem appendInto_size (head tail otherHead otherTail : Nat) :
    size (appendInto head tail otherHead otherTail) = 16 := by rfl

/-- This in-place primitive has exactly the linked-array append semantics. -/
theorem appendInto_spec (c : Config) {head tail otherHead otherTail : Nat}
    (hh : head < 30) (ht : tail < 30) (hu : otherHead < 30) (hv : otherTail < 30)
    (hhz : head ≠ 0) (htz : tail ≠ 0) (hne : head ≠ tail)
    (hz : c.reg 0 = 0) (ho : c.reg 1 = 1) :
    let nx := fun i => c.mem (c.reg 50 + i)
    let r := appL nx (c.reg head) (c.reg tail) (c.reg otherHead) (c.reg otherTail)
    let c' := run (appendInto head tail otherHead otherTail) c
    c'.reg head = r.1 ∧ c'.reg tail = r.2.1 ∧
      (∀ i, c'.mem (c.reg 50 + i) = r.2.2 i) ∧ c'.out = c.out := by
  dsimp only
  have haux : head ≠ 32 ∧ head ≠ 33 ∧ head ≠ 34 ∧ head ≠ 35 ∧ head ≠ 40 ∧
      tail ≠ 32 ∧ tail ≠ 33 ∧ tail ≠ 34 ∧ tail ≠ 35 ∧ tail ≠ 40 ∧
      otherHead ≠ 32 ∧ otherHead ≠ 33 ∧ otherHead ≠ 34 ∧ otherHead ≠ 35 ∧
      otherTail ≠ 32 ∧ otherTail ≠ 33 ∧ otherTail ≠ 34 ∧ otherTail ≠ 35 := by omega
  rcases haux with ⟨ha, hb, hc, hd, he, hf, hg, hi, hj, hk, hl, hm, hn, hp, hq, hr, hs, ht'⟩
  by_cases h₁ : c.reg head = 0
  · simp [appendInto, seqs, run, appL, Ne.symm hd, Ne.symm hhz, *]
  · by_cases h₂ : c.reg otherHead = 0
    · simp [appendInto, seqs, run, appL, *]
    · simp [appendInto, seqs, run, appL, upd, *]

end STACS2027.Embed.RAMSolver
