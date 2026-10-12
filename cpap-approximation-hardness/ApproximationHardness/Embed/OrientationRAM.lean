module

public import ApproximationHardness.Embed.SolverRAM
public import ApproximationHardness.Embed.Orient
import Lean.Elab.Tactic.Omega

/-!
# The RAM orientation pass

The orientation array starts immediately after the solver's twenty-two blocks.
Its entries encode Booleans by zero and one. All temporary registers are at
least one hundred, preserving the solver's scalar and base registers.
-/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

def boolWord (b : Bool) : Nat := if b then 1 else 0

namespace ORam
abbrev base : Nat := 100
abbrev group : Nat := 101
abbrev parent : Nat := 102
abbrev flip : Nat := 103
abbrev address : Nat := 104
abbrev value : Nat := 105
abbrev diff : Nat := 106
abbrev otherDiff : Nat := 107
end ORam

attribute [local simp] ORam.base ORam.group ORam.parent ORam.flip ORam.address
  ORam.value ORam.diff ORam.otherDiff

/-- Compute and store the orientation of the group in register `group`. -/
def orientGroup : Stmt := seqs [
  .add ORam.address 58 ORam.group,
  .load ORam.parent ORam.address,
  .ifz ORam.parent (.const ORam.value 0) (seqs [
    .sub ORam.parent ORam.parent 1,
    .add ORam.address ORam.base ORam.parent,
    .load ORam.value ORam.address,
    .add ORam.address 59 ORam.group,
    .load ORam.flip ORam.address,
    .sub ORam.diff ORam.flip 1,
    .sub ORam.otherDiff 1 ORam.flip,
    .add ORam.diff ORam.diff ORam.otherDiff,
    .ifz ORam.diff
      (.ifz ORam.value (.const ORam.value 1) (.const ORam.value 0)) .skip]),
  .add ORam.address ORam.base ORam.group,
  .store ORam.address ORam.value]

theorem orientGroup_loopFree : LoopFree orientGroup := by
  simp [orientGroup, LoopFree, seqs]

theorem orientGroup_size : size orientGroup = 21 := by decide

/-- The abstract value of the new group orientation. -/
def groupOrientation (parA flpA : Nat → Nat) (o : Nat → Bool) (g : Nat) : Bool :=
  ForestData.oval parA flpA o g

theorem orientGroup_value (c : Config) (parA flpA : Nat → Nat) (o : Nat → Bool)
    (hone : c.reg 1 = 1)
    (hpar : c.mem (c.reg 58 + c.reg ORam.group) = parA (c.reg ORam.group))
    (hflip : c.mem (c.reg 59 + c.reg ORam.group) = flpA (c.reg ORam.group))
    (hor : c.mem (c.reg ORam.base + (parA (c.reg ORam.group) - 1)) =
      boolWord (o (parA (c.reg ORam.group) - 1))) :
    (run orientGroup c).reg ORam.value =
      boolWord (groupOrientation parA flpA o (c.reg ORam.group)) := by
  simp only [ORam.group, ORam.base] at hpar hflip hor
  by_cases hp : parA (c.reg 101) = 0
  · simp [orientGroup, seqs, run, hpar, hp, groupOrientation,
      ForestData.oval, boolWord]
  · by_cases hf : flpA (c.reg 101) = 1
    · cases ho : o (parA (c.reg 101) - 1) <;>
        simp [orientGroup, seqs, run, hone, hpar, hflip, hor, hp, hf, ho,
          groupOrientation, ForestData.oval, boolWord]
    · cases ho : o (parA (c.reg 101) - 1) <;>
        simp [orientGroup, seqs, run, hone, hpar, hflip, hor, hp, hf, ho,
          groupOrientation, ForestData.oval, boolWord] <;> omega

theorem orientGroup_frame (c : Config) :
    (∀ r, r < 100 → (run orientGroup c).reg r = c.reg r) ∧
    (run orientGroup c).reg ORam.base = c.reg ORam.base ∧
    (run orientGroup c).reg ORam.group = c.reg ORam.group ∧
    (run orientGroup c).out = c.out ∧
    (∀ a, a ≠ c.reg ORam.base + c.reg ORam.group →
      (run orientGroup c).mem a = c.mem a) := by
  have hr : ∀ r, r < 100 →
      r ≠ ORam.parent ∧ r ≠ ORam.flip ∧ r ≠ ORam.address ∧ r ≠ ORam.value ∧
      r ≠ ORam.diff ∧ r ≠ ORam.otherDiff := by
    intro r hr; dsimp [ORam.parent, ORam.flip, ORam.address, ORam.value,
      ORam.diff, ORam.otherDiff]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r h
    rcases hr r h with ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩
    simp [orientGroup, seqs, run, h₁,h₂,h₃,h₄,h₅,h₆]
  · simp [orientGroup, seqs, run]
  · simp [orientGroup, seqs, run]
  · simp [orientGroup, seqs, run]
  · intro a ha
    simp [orientGroup, seqs, run, ha]

theorem orientGroup_reg (c : Config) (r : Nat)
    (hr : r ≠ ORam.parent ∧ r ≠ ORam.flip ∧ r ≠ ORam.address ∧
      r ≠ ORam.value ∧ r ≠ ORam.diff ∧ r ≠ ORam.otherDiff) :
    (run orientGroup c).reg r = c.reg r := by
  rcases hr with ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩
  simp [orientGroup, seqs, run, h₁,h₂,h₃,h₄,h₅,h₆]

theorem orientGroup_store (c : Config) :
    (run orientGroup c).mem (c.reg ORam.base + c.reg ORam.group) =
      (run orientGroup c).reg ORam.value := by
  simp [orientGroup, seqs, run]

theorem orientGroup_addrOK {S : Nat} (c : Config) (hone : c.reg 1 = 1)
    (hpar : c.reg 58 + c.reg ORam.group < S)
    (hflp : c.reg 59 + c.reg ORam.group < S)
    (hor : c.reg ORam.base + c.reg ORam.group < S)
    (hparent : c.mem (c.reg 58 + c.reg ORam.group) ≠ 0 →
      c.reg ORam.base + (c.mem (c.reg 58 + c.reg ORam.group) - 1) < S) :
    AddrOK S orientGroup c := by
  by_cases hp : c.mem (c.reg 58 + c.reg 101) = 0
  · simp [orientGroup, AddrOK, seqs, run, hone, hp, hpar, hor]
  · have h := hparent hp
    simp [orientGroup, AddrOK, seqs, run, hone, hp, hpar, hflp, hor, h]

/-- A group update takes a bounded constant number of actual RAM steps. -/
theorem orientGroup_exec {S : Nat} (c : Config) (hone : c.reg 1 = 1)
    (hpar : c.reg 58 + c.reg ORam.group < S)
    (hflp : c.reg 59 + c.reg ORam.group < S)
    (hor : c.reg ORam.base + c.reg ORam.group < S)
    (hparent : c.mem (c.reg 58 + c.reg ORam.group) ≠ 0 →
      c.reg ORam.base + (c.mem (c.reg 58 + c.reg ORam.group) - 1) < S) :
    ∃ t, ExecB S orientGroup c t (run orientGroup c) ∧ t ≤ 21 :=
  ⟨_, execB_run orientGroup orientGroup_loopFree c
    (orientGroup_addrOK c hone hpar hflp hor hparent), by
      simpa [orientGroup_size] using cost_le_size orientGroup c⟩

/-- Every entry other than the updated group is preserved. -/
theorem orientGroup_array (c : Config) (parA flpA : Nat → Nat) (o : Nat → Bool)
    (hone : c.reg 1 = 1)
    (hpar : c.mem (c.reg 58 + c.reg ORam.group) = parA (c.reg ORam.group))
    (hflip : c.mem (c.reg 59 + c.reg ORam.group) = flpA (c.reg ORam.group))
    (hor : ∀ i, c.mem (c.reg ORam.base + i) = boolWord (o i)) :
    ∀ i, (run orientGroup c).mem (c.reg ORam.base + i) =
      boolWord (upd o (c.reg ORam.group)
        (groupOrientation parA flpA o (c.reg ORam.group)) i) := by
  intro i
  by_cases hi : i = c.reg ORam.group
  · subst i
    rw [orientGroup_store, orientGroup_value c parA flpA o hone hpar hflip (hor _)]
    simp [upd]
  · rw [(orientGroup_frame c).2.2.2.2 _ (by omega), hor i]
    simp [upd, hi]

theorem orientGroup_boundedArray (width : Nat) (c : Config)
    (parA flpA : Nat → Nat) (o : Nat → Bool) (hone : c.reg 1 = 1)
    (hpar : c.mem (c.reg 58 + c.reg ORam.group) = parA (c.reg ORam.group))
    (hflip : c.mem (c.reg 59 + c.reg ORam.group) = flpA (c.reg ORam.group))
    (hparent : parA (c.reg ORam.group) ≠ 0 →
      parA (c.reg ORam.group) - 1 < width)
    (hor : ∀ i, i < width → c.mem (c.reg ORam.base + i) = boolWord (o i)) :
    ∀ i, i < width → (run orientGroup c).mem (c.reg ORam.base + i) =
      boolWord (upd o (c.reg ORam.group)
        (groupOrientation parA flpA o (c.reg ORam.group)) i) := by
  intro i hi
  by_cases hg : i = c.reg ORam.group
  · subst i
    rw [orientGroup_store]
    by_cases hp : parA (c.reg ORam.group) = 0
    · simp [orientGroup, seqs, run, hpar, hp, groupOrientation,
        ForestData.oval, boolWord, upd]
    · rw [orientGroup_value c parA flpA o hone hpar hflip (hor _ (hparent hp))]
      simp [upd]
  · rw [(orientGroup_frame c).2.2.2.2 _ (by omega), hor i hi]
    simp [upd, hg]

/-- Solver records bound every nonzero orientation parent by a linear identifier range. -/
theorem records_parentBound {F : ForestData} {hF : F.Valid} {post : List Nat}
    {parA flpA : Nat → Nat} (hR : ForestData.Records F hF parA flpA)
    (hP : ForestData.PostOrder F hF post) (g : Nat) (hg : parA g ≠ 0) :
    parA g - 1 < 8 * F.E := by
  obtain ⟨v, x, hx, he⟩ := hR.zero g hg
  have hp := hR.par v x hx
  have hb := hP.lt v (hP.mem v x hx)
  rw [he] at hp
  simp only [ForestData.gid] at hp
  omega

/-- The group identifiers visited by the orientation pass, in their execution order. -/
def orientationKeys (F : ForestData) (post : List Nat) : List Nat :=
  (ForestData.oitems F post).map (ForestData.okey F)

theorem orientationKeys_bound {F : ForestData} {hF : F.Valid} {post : List Nat}
    (hP : ForestData.PostOrder F hF post) :
    ∀ g ∈ orientationKeys F post, g < 8 * F.E := by
  intro g hg
  simp only [orientationKeys, ForestData.oitems, List.map_append, List.map_map,
    List.mem_append, List.mem_map, Function.comp, ForestData.okey] at hg
  rcases hg with ⟨v, hv, rfl⟩ | ⟨d, hd, rfl⟩
  · have h := hP.lt v (List.mem_reverse.mp hv)
    simp only [ForestData.gid]
    omega
  · have h := List.mem_range.mp hd
    omega

theorem orientationKeys_length {F : ForestData} {hF : F.Valid} {post : List Nat}
    (hP : ForestData.PostOrder F hF post) :
    (orientationKeys F post).length ≤ 6 * F.E := by
  have hp := length_le_of_nodup_lt (4 * F.E) post hP.nodup hP.lt
  simp only [orientationKeys, ForestData.oitems, List.length_map, List.length_append,
    List.length_reverse, List.length_range]
  omega

theorem orientationKeys_fold (F : ForestData) (post : List Nat)
    (parA flpA : Nat → Nat) :
    (orientationKeys F post).foldl
        (fun o g => upd o g (groupOrientation parA flpA o g)) (fun _ => false) =
      ForestData.orient F post parA flpA := by
  simp [orientationKeys, ForestData.orient, List.foldl_map, groupOrientation]

end STACS2027.Embed.RAMSolver
