module

public import ApproximationHardness.Embed.DefaultCycle
public import ApproximationHardness.Embed.DFSRAM
public import ApproximationHardness.RAM.FrameB
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.SplitIfs

/-! # Constant local rotation cache construction from two encoded plan parts -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

/-- Decode a part at vertex242; scratch249..251. -/
def decodePart (dst kindBase valueBase : Nat) : Stmt := seqs [
  .add 251 kindBase 242,.load 249 251,
  .add 251 valueBase 242,.load 250 251,
  .ifz 249 (seqs [.add 251 166 250,.load 250 251,.add 251 161 250,.load dst 251])
    (.add dst 250 0)]

def readLeftPart : Stmt := decodePart 246 67 68
def readRightPart : Stmt := decodePart 247 69 70

theorem decodePart_loopFree (dst kindBase valueBase : Nat) :
    LoopFree (decodePart dst kindBase valueBase) := by simp [decodePart,seqs,LoopFree]

theorem readLeftPart_size : size readLeftPart≤14 := by decide
theorem readRightPart_size : size readRightPart≤14 := by decide

theorem decodePart_mem (dst kindBase valueBase : Nat) (c : Config) :
    (run (decodePart dst kindBase valueBase) c).mem=c.mem := by
  simp [decodePart,seqs,run]

theorem decodePart_out (dst kindBase valueBase : Nat) (c : Config) :
    (run (decodePart dst kindBase valueBase) c).out=c.out := by
  simp [decodePart,seqs,run]

theorem readLeftPart_value (F : ForestData) (it : Item) (c : Config)
    (hz : c.reg 0=0)
    (ht : c.mem (c.reg 67+c.reg 242)=itemType it)
    (hv : c.mem (c.reg 68+c.reg 242)=itemValue it)
    (hp : ∀ v,it=.node v → c.mem (c.reg 166+v)=F.par v)
    (hq : ∀ v,it=.node v → c.mem (c.reg 161+F.par v)=STACS2027.Embed.pair (F.par v)) :
    (run readLeftPart c).reg 246=F.itemDart it := by
  cases it with
  | node v => simp [readLeftPart,decodePart,seqs,run,itemType,itemValue,ForestData.itemDart,
      ht,hv,hp v rfl,hq v rfl]
  | dart e => simp [readLeftPart,decodePart,seqs,run,itemType,itemValue,ForestData.itemDart,hz,ht,hv]

theorem readRightPart_value (F : ForestData) (it : Item) (c : Config)
    (hz : c.reg 0=0)
    (ht : c.mem (c.reg 69+c.reg 242)=itemType it)
    (hv : c.mem (c.reg 70+c.reg 242)=itemValue it)
    (hp : ∀ v,it=.node v → c.mem (c.reg 166+v)=F.par v)
    (hq : ∀ v,it=.node v → c.mem (c.reg 161+F.par v)=STACS2027.Embed.pair (F.par v)) :
    (run readRightPart c).reg 247=F.itemDart it := by
  cases it with
  | node v => simp [readRightPart,decodePart,seqs,run,itemType,itemValue,ForestData.itemDart,
      ht,hv,hp v rfl,hq v rfl]
  | dart e => simp [readRightPart,decodePart,seqs,run,itemType,itemValue,ForestData.itemDart,hz,ht,hv]


/-- Equality branch for natural labels, using both truncated differences. -/
def rotationIfEq (a b : Nat) (yes no : Stmt) : Stmt := seqs [
  .sub 263 a b,.sub 264 b a,.ifz 263 (.ifz 264 yes no) no]

def nextPredValues (next pred : Nat) : Stmt := seqs [.add 254 next 0,.add 255 pred 0]

/-- Degree244, dart240, and three cycle entries258..260. -/
def nextPredCode : Stmt := rotationIfEq 244 1 (nextPredValues 258 258)
  (rotationIfEq 244 265
    (rotationIfEq 240 258 (nextPredValues 259 259) (nextPredValues 258 258))
    (rotationIfEq 240 258 (nextPredValues 259 260)
      (rotationIfEq 240 259 (nextPredValues 260 258) (nextPredValues 258 259))))

def nextLabel (n d a b e : Nat) : Nat :=
  if n=1 then a else if n=2 then (if d=a then b else a)
  else if d=a then b else if d=b then e else a

def predLabel (n d a b e : Nat) : Nat :=
  if n=1 then a else if n=2 then (if d=a then b else a)
  else if d=a then e else if d=b then a else b

theorem nextPredCode_loopFree : LoopFree nextPredCode := by
  simp [nextPredCode,rotationIfEq,nextPredValues,seqs,LoopFree]

theorem nextPredCode_mem (c : Config) : (run nextPredCode c).mem=c.mem := by
  simp [nextPredCode,rotationIfEq,nextPredValues,seqs,run]

theorem nextPredCode_out (c : Config) : (run nextPredCode c).out=c.out := by
  simp [nextPredCode,rotationIfEq,nextPredValues,seqs,run]

theorem nextPredCode_size : size nextPredCode≤1000 := by decide

theorem both_zero_iff (a b : Nat) : a-b=0 ∧ b-a=0 ↔ a=b := by omega

theorem run_rotationIfEq (a b : Nat) (yes no : Stmt) (c : Config)
    (ha : a≠263) (hb : b≠263) :
    run (rotationIfEq a b yes no) c =
      if c.reg a=c.reg b then
        run yes ((c.setReg 263 (c.reg a-c.reg b)).setReg 264 (c.reg b-c.reg a)) else
        run no ((c.setReg 263 (c.reg a-c.reg b)).setReg 264 (c.reg b-c.reg a)) := by
  by_cases he : c.reg a=c.reg b
  · simp [rotationIfEq,seqs,run,setReg_reg,ha,hb,he]
  · have hd : c.reg a-c.reg b≠0 ∨ c.reg b-c.reg a≠0 := by omega
    rcases hd with hd|hd
    · simp [rotationIfEq,seqs,run,setReg_reg,ha,hb,he,hd]
    · by_cases hz : c.reg a-c.reg b=0 <;>
        simp [rotationIfEq,seqs,run,setReg_reg,ha,hb,he,hd,hz]

theorem nextPredCode_values (c : Config) (hz : c.reg 0=0) (ho : c.reg 1=1)
    (ht : c.reg 265=2) :
    (run nextPredCode c).reg 254=nextLabel (c.reg 244) (c.reg 240)
      (c.reg 258) (c.reg 259) (c.reg 260) ∧
    (run nextPredCode c).reg 255=predLabel (c.reg 244) (c.reg 240)
      (c.reg 258) (c.reg 259) (c.reg 260) := by
  simp only [nextPredCode,run_rotationIfEq 244 1 _ _ _ (by decide) (by decide),
    run_rotationIfEq 244 265 _ _ _ (by decide) (by decide),
    run_rotationIfEq 240 258 _ _ _ (by decide) (by decide),
    run_rotationIfEq 240 259 _ _ _ (by decide) (by decide),reg_ite,
    nextPredValues,seqs,run,setReg_reg,hz,ho,ht,reduceCtorEq,ite_false,ite_true]
  simp [nextLabel,predLabel]


def readBothParts : Stmt := seqs [.const 246 0,.const 247 0,
  .ifz 245 .skip (.seq readLeftPart
    (.seq (.sub 252 245 1) (.ifz 252 .skip readRightPart)))]

/-- Read a dart's vertex, default cyclic slots, and degree. -/
def rotationRead : Stmt := seqs [
  .add 251 160 240,.load 242 251,
  .add 251 166 242,.load 243 251,
  .add 251 162 242,.load 244 251,
  .add 251 66 242,.load 245 251,
  readBothParts,.sub 256 140 243,
  .ifz 256 (seqs [.add 258 246 0,.add 259 247 0,.add 251 280 242,.load 260 251])
    (seqs [.add 258 243 0,.add 259 246 0,.add 260 247 0]),
  .const 265 2]

def cycleSlots (F : ForestData) (v : Nat) : Nat × Nat × Nat :=
  let ps := (F.parts v).map F.itemDart
  if F.IsRoot v then (ps.getD 0 0,ps.getD 1 0,F.zOf v)
  else (F.par v,ps.getD 0 0,ps.getD 1 0)

theorem rotationRead_loopFree : LoopFree rotationRead := by
  simp [rotationRead,readBothParts,readLeftPart,readRightPart,decodePart_loopFree,seqs,LoopFree]

theorem rotationRead_size : size rotationRead≤100 := by decide

theorem rotationRead_mem (c : Config) : (run rotationRead c).mem=c.mem := by
  simp [rotationRead,readBothParts,readLeftPart,readRightPart,decodePart,seqs,run]

theorem rotationRead_out (c : Config) : (run rotationRead c).out=c.out := by
  simp [rotationRead,readBothParts,readLeftPart,readRightPart,decodePart,seqs,run]

theorem rotationRead_reg (c : Config) (r : Nat)
    (hr : r<240 ∨ r=240 ∨ r=241 ∨ r=261 ∨ r=262 ∨ 265<r) :
    (run rotationRead c).reg r=c.reg r := by
  apply run_reg_frame
  simp only [rotationRead,readBothParts,readLeftPart,readRightPart,decodePart,seqs,regsW,
    List.mem_append,List.mem_cons,List.mem_nil_iff,or_false,not_or,not_false_eq_true]
  repeat' constructor
  all_goals omega

end STACS2027.Embed.RAMSolver
