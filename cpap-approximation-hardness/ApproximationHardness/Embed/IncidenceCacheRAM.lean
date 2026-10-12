module

public import ApproximationHardness.Embed.FirstOccurrenceRAM
public import ApproximationHardness.Embed.AdjacencyCache
import Lean.Elab.Tactic.Omega

/-! # Literal and clause passes for the incidence representative cache -/

@[expose] public section

namespace STACS2027.Embed.IncidenceRAM

open RAM Complexity.SAT

/-- Formula input cursor220, clause counter221, literal counter208. -/
def CacheAt (c : Config) (w : List Nat) : Prop :=
  ∀ i, i < w.length → c.mem (c.reg 220+i) = w.getD i 0

theorem CacheAt.head {c : Config} {x : Nat} {w : List Nat} (h : CacheAt c (x::w)) :
    c.mem (c.reg 220) = x := by
  simpa using h 0 (by simp)

theorem CacheAt.of_mem {c c' : Config} {w : List Nat} (h : CacheAt c w)
    (hp : c'.reg 220 = c.reg 220)
    (hm : ∀ i, i < w.length → c'.mem (c.reg 220+i) = c.mem (c.reg 220+i)) :
    CacheAt c' w := by
  intro i hi; rw [hp,hm i hi]; exact h i hi

theorem CacheAt.drop {c c' : Config} {w u : List Nat} (h : CacheAt c (w++u))
    (hp : c'.reg 220 = c.reg 220+w.length)
    (hm : ∀ i, i < u.length → c'.mem (c.reg 220+w.length+i) =
      c.mem (c.reg 220+w.length+i)) : CacheAt c' u := by
  intro i hi
  rw [hp,hm i hi]
  have he := h (w.length+i) (by simp;omega)
  rw [Nat.add_assoc,he,List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega)]
  simp

/-- Insert both darts of one literal, with the clause representative in210. -/
def cacheLiteral : Stmt := .seq (.load 211 220) (.seq firstLookup (seqs [
  .add 215 160 209, .store 215 214,
  .add 216 209 1, .add 215 160 216, .store 215 210,
  .add 215 161 209, .store 215 216,
  .add 215 161 216, .store 215 209,
  .add 209 209 1, .add 209 209 1,
  .add 220 220 1, .add 220 220 1, .sub 208 208 1]))

def cacheClausePre : Stmt := seqs [
  .load 208 220, .add 220 220 1, .add 210 209 1, .sub 221 221 1]

def cacheClause : Stmt := .seq cacheClausePre (.loop 208 cacheLiteral)
def cacheFormula : Stmt := .loop 221 cacheClause

theorem cacheLiteral_loopFree : LoopFree cacheLiteral := by
  simp [cacheLiteral,firstLookup_loopFree,LoopFree,seqs]

theorem cacheLiteral_size : size cacheLiteral ≤ 30 := by decide

theorem cacheLiteral_out (c : Config) : (run cacheLiteral c).out = c.out := by
  simp [cacheLiteral,firstLookup,seqs,run]

theorem cacheLiteral_reg (c : Config) (r : Nat)
    (hr : r ≠ 208 ∧ r ≠ 209 ∧ r ≠ 211 ∧ r ≠ 212 ∧ r ≠ 213 ∧
      r ≠ 214 ∧ r ≠ 215 ∧ r ≠ 216 ∧ r ≠ 220) :
    (run cacheLiteral c).reg r = c.reg r := by
  rcases hr with ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉⟩
  simp [cacheLiteral,firstLookup,seqs,run,h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉]

theorem cacheLiteral_advance (c : Config) (hone : c.reg 1 = 1) :
    (run cacheLiteral c).reg 209 = c.reg 209+2 ∧
    (run cacheLiteral c).reg 220 = c.reg 220+2 ∧
    (run cacheLiteral c).reg 208 = c.reg 208-1 := by
  simp [cacheLiteral,firstLookup,seqs,run,hone,Nat.add_assoc]

/-- Four cache stores follow the dictionary insertion. -/
theorem cacheLiteral_mem (c : Config) (hone : c.reg 1 = 1) (a : Nat) :
    (run cacheLiteral c).mem a =
      if a = c.reg 161+(c.reg 209+1) then c.reg 209 else
      if a = c.reg 161+c.reg 209 then c.reg 209+1 else
      if a = c.reg 160+(c.reg 209+1) then c.reg 210 else
      if a = c.reg 160+c.reg 209 then
        (if c.mem (c.reg 205+c.mem (c.reg 220)) = 0 then c.reg 209
         else c.mem (c.reg 205+c.mem (c.reg 220))-1) else
      if a = c.reg 205+c.mem (c.reg 220) ∧ c.mem (c.reg 205+c.mem (c.reg 220)) = 0
        then c.reg 209+1 else c.mem a := by
  by_cases h : c.mem (c.reg 205+c.mem (c.reg 220)) = 0 <;>
    simp [cacheLiteral,firstLookup,seqs,run,hone,h]


theorem cacheLiteral_addrOK {S : Nat} (c : Config) (hone : c.reg 1 = 1)
    (hp : c.reg 220 < S) (hd : c.reg 205+c.mem (c.reg 220) < S)
    (hr : c.reg 160+(c.reg 209+1) < S) (hq : c.reg 161+(c.reg 209+1) < S) :
    AddrOK S cacheLiteral c := by
  have hr' : c.reg 160+c.reg 209 < S := by omega
  have hq' : c.reg 161+c.reg 209 < S := by omega
  by_cases hz : c.mem (c.reg 205+c.mem (c.reg 220)) = 0 <;>
    simp [cacheLiteral,firstLookup,seqs,run,AddrOK,hone,hp,hd,hr,hq,hr',hq',hz]

theorem cacheClausePre_loopFree : LoopFree cacheClausePre := by
  simp [cacheClausePre,seqs,LoopFree]

theorem cacheClausePre_size : size cacheClausePre ≤ 6 := by decide

theorem cacheClausePre_mem (c : Config) : (run cacheClausePre c).mem = c.mem := by
  simp [cacheClausePre,seqs,run]

theorem cacheClausePre_out (c : Config) : (run cacheClausePre c).out = c.out := by
  simp [cacheClausePre,seqs,run]

theorem cacheClausePre_reg (c : Config) (r : Nat)
    (hr : r ≠ 208 ∧ r ≠ 220 ∧ r ≠ 210 ∧ r ≠ 221) :
    (run cacheClausePre c).reg r = c.reg r := by
  rcases hr with ⟨h₁,h₂,h₃,h₄⟩
  simp [cacheClausePre,seqs,run,h₁,h₂,h₃,h₄]

theorem cacheClausePre_read (c : Config) (hone : c.reg 1 = 1) :
    (run cacheClausePre c).reg 208 = c.mem (c.reg 220) ∧
    (run cacheClausePre c).reg 220 = c.reg 220+1 ∧
    (run cacheClausePre c).reg 210 = c.reg 209+1 ∧
    (run cacheClausePre c).reg 221 = c.reg 221-1 := by
  simp [cacheClausePre,seqs,run,hone]

theorem cacheClausePre_addrOK {S : Nat} (c : Config) (hp : c.reg 220 < S) :
    AddrOK S cacheClausePre c := by
  simp [cacheClausePre,seqs,AddrOK,hp]

end STACS2027.Embed.IncidenceRAM
