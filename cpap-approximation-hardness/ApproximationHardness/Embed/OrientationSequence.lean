module

public import ApproximationHardness.Embed.OrientationRAM
import Lean.Elab.Tactic.Omega

/-! # Counted RAM execution of the orientation fold -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

attribute [local simp] ORam.base ORam.group ORam.parent ORam.flip ORam.address
  ORam.value ORam.diff ORam.otherDiff

/-- Disjoint parent, flip, orientation, and visit-stream storage. -/
structure OrientationLayout where
  width : Nat
  parents : Nat
  flips : Nat
  orientation : Nat
  keys : Nat
  capacity : Nat
  space : Nat
  parentsBelow : parents + width ≤ orientation
  flipsBelow : flips + width ≤ orientation
  keysAbove : orientation + width ≤ keys
  keysBelow : keys + capacity ≤ space

structure OrientationState (D : OrientationLayout) (parA flpA : Nat → Nat)
    (o : Nat → Bool) (c : Config) (todo : List Nat) : Prop where
  one : c.reg 1 = 1
  parentBase : c.reg 58 = D.parents
  flipBase : c.reg 59 = D.flips
  orientationBase : c.reg 100 = D.orientation
  keyBase : c.reg 113 = D.keys
  count : c.reg 109 = todo.length
  position : c.reg 110 + todo.length ≤ D.capacity
  parents : ∀ g, g < D.width → c.mem (D.parents + g) = parA g
  flips : ∀ g, g < D.width → c.mem (D.flips + g) = flpA g
  orientation : ∀ g, g < D.width → c.mem (D.orientation + g) = boolWord (o g)
  keys : ∀ j, j < todo.length → c.mem (D.keys + c.reg 110 + j) = todo.getD j 0

def sequenceRead : Stmt := seqs [.add 111 113 110, .load 101 111]
def sequenceAdvance : Stmt := seqs [.add 110 110 1, .sub 109 109 1]
def orientationBody : Stmt := .seq sequenceRead (.seq orientGroup sequenceAdvance)
def orientationLoop : Stmt := .loop 109 orientationBody

theorem sequenceRead_reg (c : Config) (r : Nat) (hr : r ≠ 111 ∧ r ≠ 101) :
    (run sequenceRead c).reg r = c.reg r := by
  simp [sequenceRead, seqs, run, hr.1, hr.2]

theorem sequenceRead_group (c : Config) :
    (run sequenceRead c).reg 101 = c.mem (c.reg 113 + c.reg 110) := by
  simp [sequenceRead, seqs, run]

theorem sequenceRead_mem (c : Config) : (run sequenceRead c).mem = c.mem := by
  simp [sequenceRead, seqs, run]

theorem sequenceRead_out (c : Config) : (run sequenceRead c).out = c.out := by
  simp [sequenceRead, seqs, run]

theorem sequenceAdvance_reg (c : Config) (r : Nat) (hr : r ≠ 110 ∧ r ≠ 109) :
    (run sequenceAdvance c).reg r = c.reg r := by
  simp [sequenceAdvance, seqs, run, hr.1, hr.2]

theorem sequenceAdvance_mem (c : Config) : (run sequenceAdvance c).mem = c.mem := by
  simp [sequenceAdvance, seqs, run]

theorem sequenceAdvance_out (c : Config) : (run sequenceAdvance c).out = c.out := by
  simp [sequenceAdvance, seqs, run]

theorem OrientationState.read {D : OrientationLayout} {parA flpA : Nat → Nat}
    {o : Nat → Bool} {c : Config} {todo : List Nat}
    (h : OrientationState D parA flpA o c todo) :
    OrientationState D parA flpA o (run sequenceRead c) todo := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [sequenceRead, seqs, run] using h.one
  · simpa [sequenceRead, seqs, run] using h.parentBase
  · simpa [sequenceRead, seqs, run] using h.flipBase
  · simpa [sequenceRead, seqs, run] using h.orientationBase
  · simpa [sequenceRead, seqs, run] using h.keyBase
  · simpa [sequenceRead, seqs, run] using h.count
  · simpa [sequenceRead, seqs, run] using h.position
  · simpa only [sequenceRead_mem] using h.parents
  · simpa only [sequenceRead_mem] using h.flips
  · simpa only [sequenceRead_mem] using h.orientation
  · simpa [sequenceRead, seqs, run] using h.keys

theorem OrientationState.orient {D : OrientationLayout} {parA flpA : Nat → Nat}
    {o : Nat → Bool} {c : Config} {todo : List Nat}
    (h : OrientationState D parA flpA o c todo)
    (hg : c.reg ORam.group < D.width)
    (hp : ∀ g, parA g ≠ 0 → parA g - 1 < D.width) :
    OrientationState D parA flpA
      (upd o (c.reg ORam.group) (groupOrientation parA flpA o (c.reg ORam.group)))
      (run orientGroup c) todo := by
  have hf := orientGroup_frame c
  have hreg (r : Nat) (hr : r = 1 ∨ r = 58 ∨ r = 59 ∨ r = 100 ∨
      r = 113 ∨ r = 109 ∨ r = 110) : (run orientGroup c).reg r = c.reg r := by
    apply orientGroup_reg
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have hpar : c.mem (c.reg 58 + c.reg ORam.group) = parA (c.reg ORam.group) := by
    rw [h.parentBase]; exact h.parents _ hg
  have hflp : c.mem (c.reg 59 + c.reg ORam.group) = flpA (c.reg ORam.group) := by
    rw [h.flipBase]; exact h.flips _ hg
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hreg 1 (by simp)]; exact h.one
  · rw [hreg 58 (by simp)]; exact h.parentBase
  · rw [hreg 59 (by simp)]; exact h.flipBase
  · rw [hreg 100 (by simp)]; exact h.orientationBase
  · rw [hreg 113 (by simp)]; exact h.keyBase
  · rw [hreg 109 (by simp)]; exact h.count
  · rw [hreg 110 (by simp)]; exact h.position
  · intro g hgg
    rw [hf.2.2.2.2 _ (by rw [h.orientationBase]; have := D.parentsBelow; omega)]
    exact h.parents g hgg
  · intro g hgg
    rw [hf.2.2.2.2 _ (by rw [h.orientationBase]; have := D.flipsBelow; omega)]
    exact h.flips g hgg
  · intro g hgg
    have ho := orientGroup_boundedArray D.width c parA flpA o h.one hpar hflp
      (hp _) (by rw [h.orientationBase]; exact h.orientation) g hgg
    simpa only [h.orientationBase] using ho
  · intro j hj
    rw [hreg 110 (by simp), hf.2.2.2.2 _ (by
      rw [h.orientationBase]; have := D.keysAbove; omega)]
    exact h.keys j hj

theorem OrientationState.advance {D : OrientationLayout} {parA flpA : Nat → Nat}
    {o : Nat → Bool} {c : Config} {g : Nat} {todo : List Nat}
    (h : OrientationState D parA flpA o c (g :: todo)) :
    OrientationState D parA flpA o (run sequenceAdvance c) todo := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [sequenceAdvance_reg _ _ (by decide)]; exact h.one
  · rw [sequenceAdvance_reg _ _ (by decide)]; exact h.parentBase
  · rw [sequenceAdvance_reg _ _ (by decide)]; exact h.flipBase
  · rw [sequenceAdvance_reg _ _ (by decide)]; exact h.orientationBase
  · rw [sequenceAdvance_reg _ _ (by decide)]; exact h.keyBase
  · simp [sequenceAdvance, seqs, run, h.one, h.count]
  · have hb := h.position
    simpa [sequenceAdvance, seqs, run, h.one, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hb
  · simpa only [sequenceAdvance_mem] using h.parents
  · simpa only [sequenceAdvance_mem] using h.flips
  · simpa only [sequenceAdvance_mem] using h.orientation
  · intro j hj
    have hk := h.keys (j + 1) (by simp; omega)
    simpa [sequenceAdvance, seqs, run, h.one, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hk

theorem orientationBody_loopFree : LoopFree orientationBody := by
  simp [orientationBody, sequenceRead, sequenceAdvance, orientGroup_loopFree,
    LoopFree, seqs]

theorem orientationBody_size : size orientationBody = 27 := by decide

theorem orientationBody_state {D : OrientationLayout} {parA flpA : Nat → Nat}
    {o : Nat → Bool} {c : Config} {g : Nat} {todo : List Nat}
    (h : OrientationState D parA flpA o c (g :: todo)) (hg : g < D.width)
    (hp : ∀ g, parA g ≠ 0 → parA g - 1 < D.width) :
    OrientationState D parA flpA (upd o g (groupOrientation parA flpA o g))
      (run orientationBody c) todo := by
  have hk := h.keys 0 (by simp)
  have he : (run sequenceRead c).reg ORam.group = g := by
    simpa [sequenceRead_group, h.keyBase] using hk
  have hr := h.read
  have ho := hr.orient (by rw [he]; exact hg) hp
  rw [he] at ho
  exact ho.advance

theorem orientationBody_out (c : Config) : (run orientationBody c).out = c.out := by
  simp only [orientationBody, run, sequenceAdvance_out,
    (orientGroup_frame _).2.2.2.1, sequenceRead_out]

theorem orientationBody_addrOK {D : OrientationLayout} {parA flpA : Nat → Nat}
    {o : Nat → Bool} {c : Config} {g : Nat} {todo : List Nat}
    (h : OrientationState D parA flpA o c (g :: todo)) (hg : g < D.width)
    (hp : ∀ g, parA g ≠ 0 → parA g - 1 < D.width) :
    AddrOK D.space orientationBody c := by
  have hk := h.keys 0 (by simp)
  have he : (run sequenceRead c).reg ORam.group = g := by
    simpa [sequenceRead_group, h.keyBase] using hk
  have hr := h.read
  have hOS : D.orientation + D.width ≤ D.space :=
    le_trans D.keysAbove (by have := D.keysBelow; omega)
  have hread : AddrOK D.space sequenceRead c := by
    have hpos := h.position
    simp only [List.length_cons] at hpos
    have hb := D.keysBelow
    simp [sequenceRead, seqs, AddrOK, run, h.keyBase]
    omega
  have hgroup : AddrOK D.space orientGroup (run sequenceRead c) := by
    apply orientGroup_addrOK _ hr.one
    · rw [hr.parentBase, he]
      have := D.parentsBelow
      omega
    · rw [hr.flipBase, he]
      have := D.flipsBelow
      omega
    · rw [hr.orientationBase, he]
      omega
    · intro hn
      rw [hr.parentBase, he, hr.parents g hg] at hn ⊢
      rw [hr.orientationBase]
      have := hp g hn
      omega
  exact .seq hread (.seq hgroup (AddrOK.of_memFree (by
    simp [sequenceAdvance, seqs, memFree])))

/-- The actual counted loop realizes the complete orientation fold in linear time. -/
theorem orientationLoop_spec {D : OrientationLayout} {parA flpA : Nat → Nat}
    (hp : ∀ g, parA g ≠ 0 → parA g - 1 < D.width) :
    ∀ (todo : List Nat) (o : Nat → Bool) (c : Config),
      OrientationState D parA flpA o c todo →
      (∀ g ∈ todo, g < D.width) →
      ∃ t c', ExecB D.space orientationLoop c t c' ∧
        t ≤ 28 * todo.length + 1 ∧
        OrientationState D parA flpA
          (todo.foldl (fun o g => upd o g (groupOrientation parA flpA o g)) o) c' [] ∧
        c'.out = c.out := by
  intro todo
  induction todo with
  | nil =>
    intro o c hc _
    exact ⟨1, c, .loopDone (by simpa using hc.count), by simp, hc, rfl⟩
  | cons g todo ih =>
    intro o c hc hg
    have hgb : g < D.width := hg g (by simp)
    have hn : c.reg 109 ≠ 0 := by have := hc.count; simp at this; omega
    have hA := orientationBody_addrOK hc hgb hp
    have he := execB_run orientationBody orientationBody_loopFree c hA
    have hb : RAM.cost orientationBody c ≤ 27 := by
      simpa [orientationBody_size] using cost_le_size orientationBody c
    have hs := orientationBody_state hc hgb hp
    obtain ⟨t, c', ht, htime, hfinal, hout⟩ :=
      ih _ _ hs (fun a ha => hg a (List.mem_cons_of_mem g ha))
    refine ⟨RAM.cost orientationBody c + t + 1, c', .loopNext hn he ht,
      ?_, hfinal, ?_⟩
    · simp only [List.length_cons]; omega
    · exact hout.trans (orientationBody_out c)

/-- Solver records and the post-order make the executed orientation consistent. -/
theorem orientationLoop_consistent {D : OrientationLayout} {F : ForestData} {hF : F.Valid}
    {post : List Nat} {parA flpA : Nat → Nat} {c : Config}
    (hR : ForestData.Records F hF parA flpA)
    (hP : ForestData.PostOrder F hF post) (hw : 8 * F.E ≤ D.width)
    (hc : OrientationState D parA flpA (fun _ => false) c (orientationKeys F post)) :
    ∃ t c' o, ExecB D.space orientationLoop c t c' ∧ t ≤ 168 * F.E + 1 ∧
      OrientationState D parA flpA o c' [] ∧ (F.sol hF).Consistent o ∧ c'.out = c.out := by
  obtain ⟨t, c', ht, hb, hfinal, hout⟩ := orientationLoop_spec
    (fun g hg => lt_of_lt_of_le (records_parentBound hR hP g hg) hw)
    (orientationKeys F post) (fun _ => false) c hc
    (fun g hg => lt_of_lt_of_le (orientationKeys_bound hP g hg) hw)
  rw [orientationKeys_fold] at hfinal
  refine ⟨t, c', ForestData.orient F post parA flpA, ht, ?_, hfinal,
    ForestData.orient_consistent hF hR hP, hout⟩
  have := orientationKeys_length hP
  omega

end STACS2027.Embed.RAMSolver
