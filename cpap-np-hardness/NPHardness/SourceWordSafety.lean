module

public import NPHardness.SourceWordConstruction
public import NPHardness.WordPipelineSafety

/-! Uniform logarithmic numeric payload bounds for every prefix of the
source-sign extraction and graph constructor. This includes sign-table write
addresses, all scalar registers and stored literals, occurrence counters and
edge endpoints. Linked-list pointers remain abstract references; no concrete
pointer-address encoding or primitive-ISA compiler is claimed. -/

@[expose] public section
namespace STACS2027.SourceWord
open Complexity.SAT WordPipeline WordPipeline.Payload LinearPreprocessPayload PlanarSource

def SignBound (b : Nat) (memory : SignMemory) : Prop := ∀i,b<i→memory i=false

theorem SignBound.mono {b d : Nat} {memory : SignMemory} (h : SignBound b memory) (hb : b≤d) :
    SignBound d memory := fun i hi => h i (by omega)

theorem writeSign_bound {b v : Nat} {memory : SignMemory} (h : SignBound b memory)
    (hv : v≤b) (value : Bool) : SignBound b (writeSign memory v value) := by
  intro i hi
  simp only [writeSign,ite_eq_right (show i≠v from by omega),h i hi]

def DataBound (k b : Nat) (input : CNF) : State → Prop
  | .header s => HeaderStateBound b s
  | .skip n r f => n≤b ∧ r≤b ∧ FormulaBound b f
  | .signs n f bits => n≤b ∧ FormulaBound b f ∧ SignBound b bits
  | .graph n bits cfg => SignBound b bits ∧ GraphStateBound k n b input cfg
  | .rejected => True

def StateBound (k b : Nat) (input : CNF) (s : State) : Prop :=
  FormulaBound b input ∧ DataBound k b input s

theorem StateBound.mono {k b d : Nat} {input : CNF} {s : State}
    (h : StateBound k b input s) (hb : b≤d) : StateBound k d input s := by
  refine ⟨h.1.mono hb,?_⟩
  have hs := h.2
  cases s with
  | header s => exact hs.mono hb
  | skip n r f => exact ⟨Nat.le_trans hs.1 hb,Nat.le_trans hs.2.1 hb,hs.2.2.mono hb⟩
  | signs n f bits => exact ⟨Nat.le_trans hs.1 hb,hs.2.1.mono hb,hs.2.2.mono hb⟩
  | graph n bits cfg => exact ⟨hs.1.mono hb,hs.2.mono hb⟩
  | rejected => trivial

theorem header_state_bound {k b budget : Nat} {input : CNF} {s : Header.State}
    (hb : budget≤b) (hi : FormulaBound b input) (hs : HeaderStateBound b s) :
    DataBound k b input (headerState input budget s) := by
  cases s with
  | formula f n => exact hs
  | clause c f n => exact hs
  | done n => exact ⟨hs,Nat.le_trans (Nat.sub_le budget n) hb,hi⟩

theorem step_bound {k budget b : Nat} {input : CNF} {s : State}
    (hb : budget≤b) (h : StateBound k b input s) :
    StateBound k (b+2) input (step k budget input s) := by
  refine ⟨h.1.mono (by omega),?_⟩
  have hs := h.2
  cases s with
  | header s => exact header_state_bound (by omega) (h.1.mono (by omega)) (header_step_bound s hs)
  | skip n r f =>
    cases r with
    | zero => exact ⟨by have := hs.1; omega,hs.2.2.mono (by omega),fun i _ => rfl⟩
    | succ r =>
      cases f with
      | nil => trivial
      | cons c f => exact ⟨by have := hs.1; omega,by have := hs.2.1; omega,
          (formula_tail hs.2.2).mono (by omega)⟩
  | signs n f bits =>
    cases f with
    | nil => exact ⟨hs.2.2.mono (by omega),graph_initial_bound (by have := hs.1; omega) (h.1.mono (by omega))⟩
    | cons c f =>
      cases c with
      | nil => trivial
      | cons l ls =>
        have hl := hs.2.1 (l::ls) (by simp) l (by simp)
        exact ⟨by have := hs.1; omega,(formula_tail hs.2.1).mono (by omega),
          (writeSign_bound hs.2.2 hl l.positive).mono (by omega)⟩
  | graph n bits cfg => exact ⟨hs.1.mono (by omega),
      (graph_step_bound (sourceEndpointChoices bits) hs.2).mono (by omega)⟩
  | rejected => trivial

theorem Runs.bounded {k budget b t : Nat} {input : CNF} {s q : State}
    (h : Runs (step k budget input) t s q) (hb : budget≤b) (hs : StateBound k b input s) :
    StateBound k (b+2*t) input q := by
  induction h generalizing b with
  | refl => simpa using hs
  | next h ih =>
    have hh := ih (show budget≤b+2 by omega) (step_bound hb hs)
    simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem initial_bound (k budget : Nat) (input : CNF) :
    StateBound k (variableBound input+budget+1) input (initial input) := by
  have hi : FormulaBound (variableBound input+budget+1) input := by
    intro c hc l hl
    have hh := literal_lt_variableBound hc hl
    omega
  exact ⟨hi,hi,by omega⟩

def wordWidth (k b t : Nat) : Nat := ((2*(b+2*t)+1)*(gadgetWidth k+1)).log2+1

def WordsFit (k w : Nat) (input : CNF) (s : State) : Prop :=
  StateBound k (2^w-1) input s ∧ gadgetWidth k<2^w ∧
    match s with
    | .graph _ _ cfg => VerticesBelow cfg.output (2^w)
    | _ => True

theorem bounded_words {k b t : Nat} {input : CNF} {s : State}
    (h : StateBound k (b+2*t) input s) : WordsFit k (wordWidth k b t) input s := by
  have hp : (2*(b+2*t)+1)*(gadgetWidth k+1)<2^wordWidth k b t := Nat.lt_log2_self
  have hb : b+2*t≤(2*(b+2*t)+1)*(gadgetWidth k+1) := by
    have hm := Nat.mul_le_mul_left (2*(b+2*t)+1) (show 1≤gadgetWidth k+1 by omega)
    simp only [Nat.mul_one] at hm
    omega
  have hw : gadgetWidth k<(2*(b+2*t)+1)*(gadgetWidth k+1) := by
    have hm := Nat.mul_le_mul_right (gadgetWidth k+1) (show 1≤2*(b+2*t)+1 by omega)
    simp only [Nat.one_mul] at hm
    omega
  have hv : (2*(b+2*t)+1)*gadgetWidth k≤2^wordWidth k b t := by
    have hm := Nat.mul_le_mul_left (2*(b+2*t)+1) (show gadgetWidth k≤gadgetWidth k+1 by omega)
    omega
  refine ⟨h.mono (by omega),Nat.lt_trans hw hp,?_⟩
  cases s with
  | graph n bits cfg => exact VerticesBelow.mono h.2.2.2.2.2.2 hv
  | header s => trivial
  | skip n r f => trivial
  | signs n f bits => trivial
  | rejected => trivial

theorem wordWidth_logarithmic (k n m t : Nat) (hm : m≤3*n)
    (ht : t≤(n+1)*linearCoefficient k) :
    wordWidth k (n+m+1) t≤(n+1).log2+
      ((4*linearCoefficient k+11)*(gadgetWidth k+1)).log2+2 := by
  let A := (4*linearCoefficient k+11)*(gadgetWidth k+1)
  have hA : 0<A := Nat.mul_pos (by omega) (by omega)
  have hnum : 2*(n+m+1+2*t)+1≤(n+1)*(4*linearCoefficient k+11) := by
    simp only [Nat.mul_add]
    rw [Nat.mul_left_comm (n+1) 4 (linearCoefficient k)]
    omega
  have hp : (2*(n+m+1+2*t)+1)*(gadgetWidth k+1)≤(n+1)*A := by
    exact (Nat.mul_assoc _ _ _).symm ▸ Nat.mul_le_mul_right (gadgetWidth k+1) hnum
  have hn : n+1<2^((n+1).log2+1) := Nat.lt_log2_self
  have ha : A<2^(A.log2+1) := Nat.lt_log2_self
  have hprod : (n+1)*A<2^((n+1).log2+A.log2+2) := by
    have h1 := Nat.mul_lt_mul_of_pos_right hn hA
    have h2 := Nat.mul_le_mul_left (2^((n+1).log2+1)) (Nat.le_of_lt ha)
    have he : (n+1).log2+A.log2+2=((n+1).log2+1)+(A.log2+1) := by omega
    rw [he,Nat.pow_add]
    exact Nat.lt_of_lt_of_le h1 h2
  have hz : (2*(n+m+1+2*t)+1)*(gadgetWidth k+1)≠0 :=
    Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))
  have hl := (Nat.log2_lt hz).mpr (Nat.lt_of_le_of_lt hp hprod)
  change ((2*(n+m+1+2*t)+1)*(gadgetWidth k+1)).log2+1≤(n+1).log2+A.log2+2
  omega

/-- Linear execution and one logarithmic payload-word width valid for every
prefix, with the orientation table computed from the input itself. -/
theorem linear_word_construction {k : Nat} (hk : 5≤k) (f : CNF) (next : Nat→Nat)
    (hn : ∀i,i<f.flatten.length→next i<f.flatten.length)
    (hf : BoundedOccurrence (Formula.ringFormula f next (Formula.sourceSigns f)))
    (hd : ClauseVariablesDistinct (Formula.ringFormula f next (Formula.sourceSigns f))) :
    let input := Formula.ringFormula f next (Formula.sourceSigns f)
    ∃t w, Runs (step k input.length input) t (initial input)
        (.graph f.flatten.length (Formula.sourceSigns f)
          ⟨.done,historyMemory input.flatten,
            (orientedFormulaGraph (sourceEndpointChoices (Formula.sourceSigns f)) k input).reverse⟩) ∧
      t≤(f.flatten.length+1)*linearCoefficient k ∧
      w≤(f.flatten.length+1).log2+((4*linearCoefficient k+11)*(gadgetWidth k+1)).log2+2 ∧
      (Satisfiable input ↔ HasAssignment
        (orientedFormulaGraph (sourceEndpointChoices (Formula.sourceSigns f)) k input).reverse k input.length) ∧
      ∀u s,u≤t→Runs (step k input.length input) u (initial input) s→WordsFit k w input s := by
  dsimp only
  let input := Formula.ringFormula f next (Formula.sourceSigns f)
  let n := f.flatten.length
  have hv : variableBound input=n := Formula.ringFormula_variableBound_of_bounded f next _ hn
  obtain ⟨t,hr,ht,hs⟩ := linear_construction hk f next hn hf hd
  have hm : input.length≤3*n := by
    have hh := hf.clause_count_variableBound
    rw [hv] at hh
    change 2*input.length≤3*n at hh
    omega
  refine ⟨t,wordWidth k (n+input.length+1) t,hr,ht,
    wordWidth_logarithmic k n input.length t hm ht,hs,?_⟩
  intro u s hu hrun
  change Runs (step k input.length input) u (initial input) s at hrun
  apply bounded_words
  have hi := initial_bound k input.length input
  rw [hv] at hi
  exact (Runs.bounded hrun (by omega) hi).mono (by omega)

end STACS2027.SourceWord
