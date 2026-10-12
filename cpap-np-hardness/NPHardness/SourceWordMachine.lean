module

public import NPHardness.WordPipelineHeader
public import NPHardness.PlanarSourceDimensions
public import NPHardness.PlanarSourceEndpointChoices

/-! A charged source-sign scan for occurrence-ring inputs. The sole supplied
header is the input clause count. A full literal scan computes the variable
bound, subtraction computes the copied-clause count, and the implication
suffix supplies one signed-literal record for each source-sign RAM cell.

The graph stage reads that Boolean RAM cell and compares it with a literal's
sign whenever an endpoint bit is needed. No endpoint-choice table is supplied.
This is a record/pointer word machine with zero-initial RAM and read-only
fixed-k gadget tables, not a compilation to a primitive instruction set. -/

@[expose] public section
namespace STACS2027.SourceWord
open Complexity.SAT WordPipeline PlanarSource

abbrev SignMemory := Nat → Bool

def writeSign (s : SignMemory) (v : Nat) (b : Bool) : SignMemory :=
  fun i => if i=v then b else s i

inductive State where
  | header (scan : Header.State)
  | skip (dimension count : Nat) (remaining : CNF)
  | signs (dimension : Nat) (remaining : CNF) (memory : SignMemory)
  | graph (dimension : Nat) (signs : SignMemory) (config : WordConstructor.Config)
  | rejected

def headerState (input : CNF) (budget : Nat) : Header.State → State
  | .done n => .skip n (budget-n) input
  | s => .header s

def step (k budget : Nat) (input : CNF) : State → State
  | .header s => headerState input budget (Header.step s)
  | .skip n 0 f => .signs n f (fun _ => false)
  | .skip _ (_+1) [] => .rejected
  | .skip n (r+1) (_::f) => .skip n r f
  | .signs n [] s => .graph n s (WordConstructor.initial n)
  | .signs _ ([]::_) _ => .rejected
  | .signs n ((l::_)::f) s => .signs n f (writeSign s l.var l.positive)
  | .graph n signs cfg => .graph n signs
      (WordConstructor.step (sourceEndpointChoices signs) k n input cfg)
  | .rejected => .rejected

def initial (input : CNF) : State := .header (.formula input 0)

theorem run_header (k budget : Nat) (input : CNF) :
    ∃t,t≤input.flatten.length+2*input.length+1 ∧
      Runs (step k budget input) t (initial input)
        (.skip (variableBound input) (budget-variableBound input) input) := by
  apply Runs.simulate (headerState input budget) ?_ (Header.computes_bound input)
  intro s
  cases s with
  | done n => exact Or.inl rfl
  | formula f n => exact Or.inr rfl
  | clause c f n => exact Or.inr rfl

theorem run_skip (k budget n : Nat) (input copied suffix : CNF) :
    Runs (step k budget input) (copied.length+1)
      (.skip n copied.length (copied++suffix)) (.signs n suffix (fun _ => false)) := by
  induction copied with
  | nil => exact Runs.next (Runs.refl _)
  | cons c f ih => exact Runs.next ih

def intervalSigns (base count : Nat) (values old : SignMemory) : SignMemory :=
  fun i => if base≤i ∧ i<base+count then values i else old i

theorem intervalSigns_succ (base count : Nat) (values old : SignMemory) :
    intervalSigns (base+1) count values (writeSign old base (values base)) =
      intervalSigns base (count+1) values old := by
  funext i
  simp only [intervalSigns,writeSign]
  by_cases h : i=base
  · subst i
    simp
  · by_cases hlt : base<i
    · have hn : base+1≤i := by omega
      have he : (i<base+1+count)=(i<base+(count+1)) := by congr 1 <;> omega
      simp only [hn,he,true_and,ite_eq_right h,show base≤i by omega]
    · have hn : ¬base≤i := by omega
      have hn' : ¬base+1≤i := by omega
      simp only [hn,hn',false_and,↓reduceIte,ite_eq_right h]

def ringSuffix (base count : Nat) (next : Nat→Nat) (values : SignMemory) : CNF :=
  (List.range' base count).map fun i => [⟨i,values i⟩,⟨next i,!(values (next i))⟩]

theorem run_signs (k budget n base count : Nat) (input : CNF)
    (next : Nat→Nat) (values old : SignMemory) :
    Runs (step k budget input) (count+1)
      (.signs n (ringSuffix base count next values) old)
      (.graph n (intervalSigns base count values old) (WordConstructor.initial n)) := by
  induction count generalizing base old with
  | zero =>
    have hz : intervalSigns base 0 values old=old := by
      funext i
      simp only [intervalSigns,Nat.add_zero,show ¬(base≤i ∧ i<base) from by omega,↓reduceIte]
    rw [hz]
    exact Runs.next (Runs.refl _)
  | succ count ih =>
    have h := Runs.next (s := State.signs n (ringSuffix base (count+1) next values) old)
      (ih (base+1) (writeSign old base (values base)))
    simpa only [ringSuffix,List.range'_succ,List.map_cons,step,intervalSigns_succ] using h

theorem interval_sourceSigns (f : CNF) :
    intervalSigns 0 f.flatten.length (Formula.sourceSigns f) (fun _ => false)=Formula.sourceSigns f := by
  funext i
  by_cases hi : i<f.flatten.length
  · simp only [intervalSigns,Nat.zero_le,true_and,Nat.zero_add,ite_eq_left hi]
  · simp only [intervalSigns,Nat.zero_le,true_and,Nat.zero_add,ite_eq_right hi,Formula.sourceSigns,List.getElem?_eq_none (by omega : f.flatten.length≤i),Option.getD_none]

theorem graph_runs {k budget n t : Nat} {input : CNF} {signs : SignMemory}
    {a b : WordConstructor.Config}
    (h : WordConstructor.Executes (sourceEndpointChoices signs) k n input t a b) :
    Runs (step k budget input) t (.graph n signs a) (.graph n signs b) := by
  induction h with
  | refl => exact Runs.refl _
  | next h ih => exact Runs.next ih

/-- The sign table is reconstructed exactly, including its false out-of-range
cells, from the input's actual implication suffix. -/
theorem extracts_sourceSigns (k : Nat) (f : CNF) (next : Nat→Nat)
    (hn : ∀i,i<f.flatten.length→next i<f.flatten.length) :
    let input := Formula.ringFormula f next (Formula.sourceSigns f)
    ∃t,t≤input.flatten.length+2*input.length+f.length+f.flatten.length+3 ∧
      Runs (step k input.length input) t (initial input)
        (.graph f.flatten.length (Formula.sourceSigns f) (WordConstructor.initial f.flatten.length)) := by
  dsimp only
  let input := Formula.ringFormula f next (Formula.sourceSigns f)
  have hv : variableBound input=f.flatten.length := Formula.ringFormula_variableBound_of_bounded f next _ hn
  obtain ⟨t,ht,hr⟩ := run_header k input.length input
  have hsub : input.length-f.flatten.length=f.length := by
    dsimp only [input]
    rw [Formula.ringFormula_length,Nat.add_sub_cancel]
  rw [hv,hsub] at hr
  have hs := run_skip k input.length f.flatten.length input (Formula.copyFormula f)
    (Formula.ringClauses f.flatten.length next (Formula.sourceSigns f))
  rw [Formula.copyFormula_length] at hs
  have hb := run_signs k input.length f.flatten.length 0 f.flatten.length input next
    (Formula.sourceSigns f) (fun _ => false)
  rw [interval_sourceSigns] at hb
  have he : ringSuffix 0 f.flatten.length next (Formula.sourceSigns f)=
      Formula.ringClauses f.flatten.length next (Formula.sourceSigns f) := by
    simp only [ringSuffix,Formula.ringClauses,←List.range_eq_range']
  rw [he] at hb
  refine ⟨t+(f.length+1)+(f.flatten.length+1),?_,(hr.trans hs).trans hb⟩
  change t+(f.length+1)+(f.flatten.length+1)≤input.flatten.length+2*input.length+f.length+f.flatten.length+3
  omega

end STACS2027.SourceWord
