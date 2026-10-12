module

public import NPHardness.EmitterThreeCNF
public import Complexity.CookLevinEmitter
public import Complexity.StackTableauMachineBounds

/-! Compiled fresh-variable normalization. Every transformed program remains
in the foundation's finite emitter syntax, so its polynomial bound counts
actual instructions of the original one-tape machine. -/

@[expose] public section
namespace STACS2027
open Complexity Complexity.SAT Complexity.ChainThreeSAT Complexity.StackTableauEmitter

def transformAllocated
    (replace : {n : Nat} → List (LiteralExpr n) → NumExpr n → NumExpr n → ClauseProgram n) :
    {n : Nat} → ClauseProgram n → NumExpr n → NumExpr n → ClauseProgram n
  | _, .clause ls, C, base => replace ls C base
  | _, .seq p q, C, base => .seq
      (transformAllocated replace p C (.add base (emitterSlotsExpr q C)))
      (transformAllocated replace q C base)
  | _, .forDown bound p, C, base => .forDown bound
      (transformAllocated replace p C.lift
        (.add base.lift (.mul (.var 0) (emitterSlotsExpr p C.lift))))
  | _, .ifLe l r p q, C, base => .ifLe l r
      (transformAllocated replace p C base) (transformAllocated replace q C base)
  | _, .ifInput i p q r, C, base => .ifInput i
      (transformAllocated replace p C base) (transformAllocated replace q C base)
      (transformAllocated replace r C base)

theorem transformAllocated_emit
    (replace : {n : Nat} → List (LiteralExpr n) → NumExpr n → NumExpr n → ClauseProgram n)
    (sem : Nat → Nat → Clause → CNF)
    (hreplace : ∀ {n} (ls : List (LiteralExpr n)) (C base : NumExpr n) (input : SAT.Word) (env : Env n),
      (replace ls C base).emit input env = sem (C.eval env) (base.eval env) (ls.map (fun l => l.eval env)))
    {n : Nat} (p : ClauseProgram n) (C base : NumExpr n) (input : SAT.Word) (env : Env n) :
    (transformAllocated replace p C base).emit input env =
      (allocatedEmit p input env (C.eval env) (base.eval env)).flatMap
        (fun x => sem (C.eval env) x.1 x.2) := by
  induction p with
  | clause ls => simp [transformAllocated,allocatedEmit,hreplace]
  | seq p q ihp ihq =>
    simp only [transformAllocated,ClauseProgram.emit,ihp,ihq,allocatedEmit,List.flatMap_append,
      NumExpr.eval,emitterSlotsExpr_eval]
  | forDown bound p ih =>
    simp only [transformAllocated,ClauseProgram.emit,allocatedEmit,List.flatMap_assoc]
    apply congrArg (List.flatMap · (List.range (bound.eval env)).reverse)
    funext i
    simpa only [NumExpr.eval,NumExpr.eval_lift,extend_zero,emitterSlotsExpr_eval] using
      ih C.lift (.add base.lift (.mul (.var 0) (emitterSlotsExpr p C.lift))) (extend i env)
  | ifLe l r p q ihp ihq =>
    simp only [transformAllocated,ClauseProgram.emit,allocatedEmit]
    split <;> simp [ihp,ihq]
  | ifInput i p q r ihp ihq ihr =>
    simp only [transformAllocated,ClauseProgram.emit,allocatedEmit]
    split
    · next h => simp only [h,ihp]
    · next h => simp only [h,ihq]
    · next h => simp only [h,ihr]

def chainEndExpr {n : Nat} (base : NumExpr n) : List (LiteralExpr n) → ClauseProgram n
  | [] => .clause [⟨base,false⟩,⟨base,false⟩]
  | l :: ls => .seq (chainEndExpr (.add base (.const 1)) ls)
      (.clause [⟨.add base (.const 1),true⟩,l,⟨base,false⟩])

def chainChunkExpr {n : Nat} (base : NumExpr n) (ls : List (LiteralExpr n)) : ClauseProgram n :=
  .seq (chainEndExpr base ls) (.clause [⟨base,true⟩,⟨base,true⟩])

theorem chainEndExpr_emit {n : Nat} (base : NumExpr n) (ls : List (LiteralExpr n))
    (input : SAT.Word) (env : Env n) :
    (chainEndExpr base ls).emit input env =
      (chainEnd (base.eval env) (ls.map (fun l => l.eval env))).map expandSourceUnit := by
  induction ls generalizing base with
  | nil => rfl
  | cons l ls ih =>
    simp only [chainEndExpr,ClauseProgram.emit,ih,List.map_cons,chainEnd,List.map_append,
      NumExpr.eval,LiteralExpr.eval,List.map_nil]
    rfl

theorem chainChunkExpr_emit {n : Nat} (base : NumExpr n) (ls : List (LiteralExpr n))
    (input : SAT.Word) (env : Env n) :
    (chainChunkExpr base ls).emit input env =
      sourceChainChunk (base.eval env) (ls.map (fun l => l.eval env)) := by
  simp only [chainChunkExpr,ClauseProgram.emit,chainEndExpr_emit,sourceChainChunk,chainClause,List.map_append]
  rfl

def normalizeTemplate {n : Nat} (ls : List (LiteralExpr n)) (C slot : NumExpr n) : ClauseProgram n :=
  chainChunkExpr (.add (.add C (.const 1)) (.mul slot (.add C (.const 1)))) ls

def normalizedEmitter {n : Nat} (p : ClauseProgram n) (C : NumExpr n) : ClauseProgram n :=
  transformAllocated normalizeTemplate p C (.const 0)

theorem normalizedEmitter_emit {n : Nat} (p : ClauseProgram n) (C : NumExpr n)
    (input : SAT.Word) (env : Env n) :
    (normalizedEmitter p C).emit input env =
      allocatedThree (C.eval env) (allocatedEmit p input env (C.eval env) 0) := by
  exact transformAllocated_emit normalizeTemplate
    (fun C slot c => sourceChainChunk (C+1+slot*(C+1)) c)
    (fun ls C base input env => chainChunkExpr_emit _ ls input env) p C (.const 0) input env

theorem normalizedEmitter_correct {n : Nat} (p : ClauseProgram n) (C : NumExpr n)
    (input : SAT.Word) (env : Env n) (hf : p.Fits input env (C.eval env)) :
    Satisfiable ((normalizedEmitter p C).emit input env) ↔ Satisfiable (p.emit input env) := by
  rw [normalizedEmitter_emit]
  exact allocatedThree_satisfiable p input env _ 0 hf

theorem normalizedEmitter_sizes {n : Nat} (p : ClauseProgram n) (C : NumExpr n)
    (input : SAT.Word) (env : Env n) :
    ∀ c ∈ (normalizedEmitter p C).emit input env, c.length = 2 ∨ c.length = 3 := by
  rw [normalizedEmitter_emit]
  exact allocatedThree_sizes _ _

/-- Every machine-defined NP language has a polynomial-time emitter whose
clauses have exactly two or three entries. No external hardness theorem is used. -/
theorem inNP_twoThreeEmitter {L : Language} (hL : InNP L) :
    ∃ p : ClauseProgram 1, (∀ input,
      L input ↔ Satisfiable (p.emit input (fun _ => input.length))) ∧
      ∀ input c, c ∈ p.emit input (fun _ => input.length) → c.length = 2 ∨ c.length = 3 := by
  obtain ⟨p,hp⟩ := CookLevinEmitter.inNP_emitter hL
  obtain ⟨coefficient,exponent,hbound⟩ := p.envelope_polynomial
  let C := CookLevinEmitter.boundExpr coefficient exponent
  refine ⟨normalizedEmitter p C,?_,?_⟩
  · intro input
    have hf : p.Fits input (fun _ => input.length) (C.eval (fun _ => input.length)) := by
      apply p.fits_of_envelope input _ input.length _ (fun _ => Nat.le_refl _)
      simpa [C] using hbound input.length
    have hs := normalizedEmitter_correct p C input (fun _ => input.length) hf
    exact (hp input).trans ((SAT.SAT_encode_iff _).trans hs.symm)
  · intro input c hc
    exact normalizedEmitter_sizes p C input _ c hc

end STACS2027
