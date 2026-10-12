module

public import ApproximationHardness.Embed.SolverNodeRAM
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Bounded-address execution of child-result reads and singleton initialization. -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

/-- Every possibly used block cell of an item-result instruction. -/
def ItemAddressOK (bound : Nat) (c : Config) (typ value : Nat) : Prop :=
  (c.reg typ = 0 → ∀ j ∈ [6, 7], c.reg (50 + j) + c.reg value < bound) ∧
  (c.reg typ ≠ 0 → ∀ j ∈ [1, 2, 3, 5, 12], c.reg (50 + j) + c.reg value < bound)

/-- Item-result instructions have only the stated indexed memory accesses. -/
theorem itemResultInto_addrOK {bound : Nat} {c : Config} {typ value head low : Nat}
    (hh : 20 ≤ head ∧ head < 30) (hl : 20 ≤ low ∧ low < 30)
    (hv : value < 30) (hvh : value ≠ head) (hvl : value ≠ low)
    (hz : c.reg 0 = 0) (ho : c.reg 1 = 1) (ha : ItemAddressOK bound c typ value) :
    AddrOK bound (itemResultInto typ value head low) c := by
  have hnh : ∀ i, i ≤ 1 ∨ 40 ≤ i → i ≠ head := by intro i hi; rcases hi with hi | hi <;> omega
  have hnl : ∀ i, i ≤ 1 ∨ 40 ≤ i → i ≠ low := by intro i hi; rcases hi with hi | hi <;> omega
  have hv' : value ≠ 40 := by omega
  by_cases ht : c.reg typ = 0
  · have h₆ := ha.1 ht 6 (by simp)
    have h₇ := ha.1 ht 7 (by simp)
    simp [itemResultInto, loadCell, storeCell, AddrOK, run, seqs, ht, hvh, hvl, hv', hnh, hnl, *]
  · have h₁ := ha.2 ht 1 (by simp)
    have h₂ := ha.2 ht 2 (by simp)
    have h₃ := ha.2 ht 3 (by simp)
    have h₅ := ha.2 ht 5 (by simp)
    have h₁₂ := ha.2 ht 12 (by simp)
    simp [itemResultInto, loadCell, storeCell, AddrOK, run, seqs, ht, hvh, hvl, hv', hnh, hnl, *]

/-- The item program has a fixed instruction bound independent of the formula. -/
theorem itemResultInto_size (typ value head low : Nat) : size (itemResultInto typ value head low) ≤ 50 := by
  norm_num [itemResultInto, size, seqs, loadCell, storeCell]

/-- Item kinds and bounded formula tables supply its actual address bounds. -/
theorem ItemAddressOK.ofRep {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound typ value : Nat} (hr : Rep L c s)
    (ht : Tables L c S post vertexBound dartBound) (it : Item)
    (hit : match it with | .node w => w < vertexBound | .dart e => e < dartBound)
    (htyp : c.reg typ = itemType it) (hval : c.reg value = itemValue it) :
    ItemAddressOK L.limit c typ value := by
  have hbase := hr.bases.2.2.2.2
  cases it with
  | node w =>
    have hw : w < L.width := hit.trans_le ht.vertices
    refine ⟨?_, ?_⟩
    · intro _ j hj
      have hj' : j < 22 := by simp at hj; omega
      rw [hbase j hj', hval]
      exact L.cell_lt hj' hw
    · intro hn
      simp [htyp, itemType] at hn
  | dart e =>
    have he : e < L.width := hit.trans_le ht.darts
    refine ⟨?_, ?_⟩
    · intro hn
      simp [htyp, itemType] at hn
    · intro _ j hj
      have hj' : j < 22 := by simp at hj; omega
      rw [hbase j hj', hval]
      exact L.cell_lt hj' he

/-- An item instruction executes under the common finite layout in at most 50 steps. -/
theorem itemResultInto_exec {L : Layout} {c : Config} {s : SMS} {S : Sol} {post : List Nat}
    {vertexBound dartBound typ value head low : Nat} (hr : Rep L c s)
    (ht : Tables L c S post vertexBound dartBound) (it : Item)
    (hit : match it with | .node w => w < vertexBound | .dart e => e < dartBound)
    (hh : 20 ≤ head ∧ head < 30) (hl : 20 ≤ low ∧ low < 30)
    (hv : value < 30) (hvh : value ≠ head) (hvl : value ≠ low)
    (htyp : c.reg typ = itemType it) (hval : c.reg value = itemValue it) :
    ∃ t, ExecB L.limit (itemResultInto typ value head low) c t
      (run (itemResultInto typ value head low) c) ∧ t ≤ 50 := by
  have ha := itemResultInto_addrOK hh hl hv hvh hvl hr.bases.1 hr.bases.2.1
    (ItemAddressOK.ofRep hr ht it hit htyp hval)
  exact ⟨_, execB_run _ (itemResultInto_loopFree _ _ _ _) c ha,
    Nat.le_trans (cost_le_size _ _) (itemResultInto_size _ _ _ _)⟩

end STACS2027.Embed.RAMSolver
