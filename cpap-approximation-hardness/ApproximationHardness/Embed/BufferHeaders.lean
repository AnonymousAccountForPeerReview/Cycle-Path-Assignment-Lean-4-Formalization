module

public import ApproximationHardness.Embed.PlanHeader
public import ApproximationHardness.Embed.RotationOutput
public import ApproximationHardness.Embed.OrientationFrame
import Lean.Elab.Tactic.Omega

/-! # Uniform setup of orientation, keys, both local rotations, and output registers -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

def orientationBase (L : Layout) := L.limit+L.width
def keyBase (L : Layout) := orientationBase L+L.width
def nextBase (L : Layout) := keyBase L+L.width
def predBase (L : Layout) := nextBase L+L.width
def bufferLimit (L : Layout) := predBase L+L.width

def bufferHeaders : Stmt := seqs [
  .add 100 280 3,.add 113 100 3,.add 261 113 3,.add 262 261 3]

def orientationLayout (L : Layout) : OrientationLayout where
  width:=L.width
  parents:=L.block 8
  flips:=L.block 9
  orientation:=orientationBase L
  keys:=keyBase L
  capacity:=L.width
  space:=bufferLimit L
  parentsBelow:=by dsimp [Layout.block,orientationBase,Layout.limit];omega
  flipsBelow:=by dsimp [Layout.block,orientationBase,Layout.limit];omega
  keysAbove:=by rfl
  keysBelow:=by dsimp [keyBase,nextBase,predBase,bufferLimit];omega

theorem bufferHeaders_values (L : Layout) (c : Config)
    (hz : c.reg 280=L.limit) (hw : c.reg 3=L.width) :
    (run bufferHeaders c).reg 100=orientationBase L ∧
    (run bufferHeaders c).reg 113=keyBase L ∧
    (run bufferHeaders c).reg 261=nextBase L ∧
    (run bufferHeaders c).reg 262=predBase L := by
  simp [bufferHeaders,seqs,run,hz,hw,orientationBase,keyBase,nextBase,predBase]

theorem bufferHeaders_frame (c : Config) :
    (run bufferHeaders c).mem=c.mem ∧ (run bufferHeaders c).out=c.out ∧
    ∀ r,r≠100 → r≠113 → r≠261 → r≠262 → (run bufferHeaders c).reg r=c.reg r := by
  refine ⟨by simp [bufferHeaders,seqs,run],by simp [bufferHeaders,seqs,run],?_⟩
  intro r h1 h2 h3 h4
  simp [bufferHeaders,seqs,run,h1,h2,h3,h4]

theorem bufferHeaders_spec (S : Nat) (c : Config) :
    ∃ t,ExecB S bufferHeaders c t (run bufferHeaders c) ∧ t≤5 := by
  exact ⟨_,execB_run _ (by simp [bufferHeaders,seqs,LoopFree]) c
    (AddrOK.of_memFree (by rfl)),cost_le_size _ _⟩

/-- Prepare the final read-only rotation scan after the default caches and orientation. -/
def readoutHeader : Stmt := seqs [
  .add 125 140 0,.const 126 0,.add 127 160 0,
  .add 128 261 0,.add 129 262 0,.add 130 100 0]

theorem readoutHeader_values (c : Config) (hz : c.reg 0=0) :
    (run readoutHeader c).reg 125=c.reg 140 ∧ (run readoutHeader c).reg 126=0 ∧
    (run readoutHeader c).reg 127=c.reg 160 ∧ (run readoutHeader c).reg 128=c.reg 261 ∧
    (run readoutHeader c).reg 129=c.reg 262 ∧ (run readoutHeader c).reg 130=c.reg 100 := by
  simp [readoutHeader,seqs,run,hz]

theorem readoutHeader_frame (c : Config) :
    (run readoutHeader c).mem=c.mem ∧ (run readoutHeader c).out=c.out ∧
    ∀ r,r<125 ∨ 130<r → (run readoutHeader c).reg r=c.reg r := by
  refine ⟨by simp [readoutHeader,seqs,run],by simp [readoutHeader,seqs,run],?_⟩
  intro r hr
  apply run_reg_frame
  simp only [readoutHeader,seqs,regsW,List.mem_append,List.mem_cons,List.mem_nil_iff,
    or_false,not_or]
  repeat' constructor
  all_goals omega

theorem readoutHeader_spec (S : Nat) (c : Config) :
    ∃ t,ExecB S readoutHeader c t (run readoutHeader c) ∧ t≤7 := by
  exact ⟨_,execB_run _ (by simp [readoutHeader,seqs,LoopFree]) c
    (AddrOK.of_memFree (by rfl)),cost_le_size _ _⟩

end STACS2027.Embed.RAMSolver
