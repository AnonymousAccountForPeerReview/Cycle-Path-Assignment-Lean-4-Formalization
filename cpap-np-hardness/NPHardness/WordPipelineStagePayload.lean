module

public import NPHardness.WordPipelineCorrect
public import NPHardness.LinearPreprocessPayload

/-! Natural-number payload bounds for the four list-scanning stages. -/

@[expose] public section
namespace STACS2027.WordPipeline.Payload
open Complexity.SAT
open LinearPreprocessPayload

theorem formula_cons {b : Nat} {c : Clause} {f : CNF} (hc : ClauseBound b c) (hf : FormulaBound b f) :
    FormulaBound b (c::f) := by
  intro d hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact hc
  · exact hf d hd

theorem formula_tail {b : Nat} {c : Clause} {f : CNF} (h : FormulaBound b (c::f)) : FormulaBound b f :=
  fun d hd => h d (by simp [hd])

theorem clause_tail {b : Nat} {l : Literal} {c : Clause} (h : ClauseBound b (l::c)) : ClauseBound b c :=
  fun r hr => h r (by simp [hr])

theorem smallDistinct_sublist (c : Clause) : (LinearPreprocessNormalize.smallDistinct c).Sublist c := by
  by_cases hc : c.length ≤ 3
  · rw [LinearPreprocessNormalize.smallDistinct_eq hc]
    exact distinctLiterals_sublist c
  · cases c with
    | nil => simp at hc
    | cons a c => cases c with
      | nil => simp at hc
      | cons b c => cases c with
        | nil => simp at hc
        | cons d c => cases c with
          | nil => simp at hc
          | cons e c => simp [LinearPreprocessNormalize.smallDistinct]

theorem normalizeOne_bound {b : Nat} {c d : Clause} (hc : ClauseBound b c)
    (h : LinearPreprocessNormalize.normalizeOne c = some d) : ClauseBound b d := by
  dsimp only [LinearPreprocessNormalize.normalizeOne] at h
  split at h
  · cases h
  · have he := Option.some.inj h
    subst d
    intro l hl
    exact hc l ((smallDistinct_sublist c).subset hl)

def NormStateBound (b : Nat) : LinearPreprocessNormalize.State → Prop
  | .scan f acc => FormulaBound b f ∧ FormulaBound b acc
  | .reverse f acc => FormulaBound b f ∧ FormulaBound b acc
  | .done f => FormulaBound b f

theorem NormStateBound.mono {b d : Nat} {s : LinearPreprocessNormalize.State}
    (h : NormStateBound b s) (hb : b ≤ d) : NormStateBound d s := by
  cases s with
  | scan f acc => exact ⟨h.1.mono hb,h.2.mono hb⟩
  | reverse f acc => exact ⟨h.1.mono hb,h.2.mono hb⟩
  | done f => exact FormulaBound.mono h hb

theorem norm_step_bound {b : Nat} (s : LinearPreprocessNormalize.State) (h : NormStateBound b s) :
    NormStateBound (b+2) (LinearPreprocessNormalize.step s) := by
  apply NormStateBound.mono (b := b) _ (by omega)
  cases s with
  | done f => exact h
  | scan f acc => cases f with
    | nil => exact ⟨h.2,by simp [FormulaBound]⟩
    | cons c f =>
      have ht := formula_tail h.1
      cases he : LinearPreprocessNormalize.normalizeOne c with
      | none => simpa [LinearPreprocessNormalize.step,he,NormStateBound] using And.intro ht h.2
      | some d =>
        have hd := normalizeOne_bound (h.1 c (by simp)) he
        simpa [LinearPreprocessNormalize.step,he,NormStateBound] using And.intro ht (formula_cons hd h.2)
  | reverse f acc => cases f with
    | nil => exact h.2
    | cons c f => exact ⟨formula_tail h.1,formula_cons (h.1 c (by simp)) h.2⟩

def ExtractStateBound (b : Nat) : LinearPreprocessExtract.State → Prop
  | .scan j r acc count => j ≤ b ∧ r ≤ b ∧ FormulaBound b acc ∧ count ≤ b
  | .reverse f acc count => FormulaBound b f ∧ FormulaBound b acc ∧ count ≤ b
  | .done f count => FormulaBound b f ∧ count ≤ b

theorem ExtractStateBound.mono {b d : Nat} {s : LinearPreprocessExtract.State}
    (h : ExtractStateBound b s) (hb : b ≤ d) : ExtractStateBound d s := by
  cases s with
  | scan j r acc count => exact ⟨Nat.le_trans h.1 hb,Nat.le_trans h.2.1 hb,h.2.2.1.mono hb,Nat.le_trans h.2.2.2 hb⟩
  | reverse f acc count => exact ⟨h.1.mono hb,h.2.1.mono hb,Nat.le_trans h.2.2 hb⟩
  | done f count => exact ⟨h.1.mono hb,Nat.le_trans h.2 hb⟩

theorem extract_step_bound {b : Nat} (mem : LinearPreprocessUnits.Memory) (hm : MemoryBound b mem)
    (s : LinearPreprocessExtract.State) (h : ExtractStateBound b s) :
    ExtractStateBound (b+2) (LinearPreprocessExtract.step mem s) := by
  cases s with
  | done f count => exact h.mono (by omega)
  | scan j r acc count =>
    have hj := h.1
    have hr := h.2.1
    have hc := h.2.2.2
    cases r with
    | zero => exact ⟨h.2.2.1.mono (by omega),by simp [FormulaBound],by omega⟩
    | succ r =>
      cases he : mem j with
      | none =>
        simp only [LinearPreprocessExtract.step,he,ExtractStateBound]
        exact ⟨by omega,by omega,h.2.2.1.mono (by omega),by omega⟩
      | some c =>
        simp only [LinearPreprocessExtract.step,he,ExtractStateBound]
        exact ⟨by omega,by omega,(formula_cons (hm j c he).2 h.2.2.1).mono (by omega),by omega⟩
  | reverse f acc count =>
    have hc := h.2.2
    cases f with
    | nil => exact ⟨h.2.1.mono (by omega),by omega⟩
    | cons c f => exact ⟨(formula_tail h.1).mono (by omega),
        (formula_cons (h.1 c (by simp)) h.2.1).mono (by omega),by omega⟩

def PaddingStateBound (b : Nat) : LinearPreprocessPadding.State → Prop
  | .scanFormula f n acc => FormulaBound b f ∧ n ≤ b ∧ FormulaBound b acc
  | .scanClause c f n acc => ClauseBound b c ∧ FormulaBound b f ∧ n ≤ b ∧ FormulaBound b acc
  | .pad remaining next acc => remaining ≤ b ∧ next ≤ b ∧ FormulaBound b acc
  | .reverse f acc => FormulaBound b f ∧ FormulaBound b acc
  | .done f => FormulaBound b f

theorem PaddingStateBound.mono {b d : Nat} {s : LinearPreprocessPadding.State}
    (h : PaddingStateBound b s) (hb : b ≤ d) : PaddingStateBound d s := by
  cases s with
  | scanFormula f n acc => exact ⟨h.1.mono hb,Nat.le_trans h.2.1 hb,h.2.2.mono hb⟩
  | scanClause c f n acc => exact ⟨h.1.mono hb,h.2.1.mono hb,Nat.le_trans h.2.2.1 hb,h.2.2.2.mono hb⟩
  | pad remaining next acc => exact ⟨Nat.le_trans h.1 hb,Nat.le_trans h.2.1 hb,h.2.2.mono hb⟩
  | reverse f acc => exact ⟨h.1.mono hb,h.2.mono hb⟩
  | done f => exact FormulaBound.mono h hb

theorem padding_step_bound {b count : Nat} (hc : count ≤ b)
    (s : LinearPreprocessPadding.State) (h : PaddingStateBound b s) :
    PaddingStateBound (b+2) (LinearPreprocessPadding.step count s) := by
  cases s with
  | done f => exact FormulaBound.mono h (by omega)
  | scanFormula f n acc =>
    have hn := h.2.1
    cases f with
    | nil => exact ⟨by omega,by omega,h.2.2.mono (by omega)⟩
    | cons c f => exact ⟨(h.1 c (by simp)).mono (by omega),(formula_tail h.1).mono (by omega),
        by omega,(formula_cons (h.1 c (by simp)) h.2.2).mono (by omega)⟩
  | scanClause c f n acc =>
    have hn := h.2.2.1
    cases c with
    | nil => exact ⟨h.2.1.mono (by omega),by omega,h.2.2.2.mono (by omega)⟩
    | cons l c =>
      have hl := h.1 l (by simp)
      exact ⟨(clause_tail h.1).mono (by omega),h.2.1.mono (by omega),by omega,h.2.2.2.mono (by omega)⟩
  | pad remaining next acc =>
    have hr := h.1
    have hn := h.2.1
    cases remaining with
    | zero => exact ⟨h.2.2.mono (by omega),by simp [FormulaBound]⟩
    | succ r =>
      refine ⟨by omega,by omega,formula_cons ?_ (h.2.2.mono (by omega))⟩
      intro l hl
      simp only [paddingClause,List.mem_cons,List.not_mem_nil,or_false] at hl
      rcases hl with rfl | rfl <;> simp only <;> omega
  | reverse f acc =>
    cases f with
    | nil => exact h.2.mono (by omega)
    | cons c f => exact ⟨(formula_tail h.1).mono (by omega),(formula_cons (h.1 c (by simp)) h.2).mono (by omega)⟩

def HeaderStateBound (b : Nat) : Header.State → Prop
  | .formula f n => FormulaBound b f ∧ n ≤ b
  | .clause c f n => ClauseBound b c ∧ FormulaBound b f ∧ n ≤ b
  | .done n => n ≤ b

theorem HeaderStateBound.mono {b d : Nat} {s : Header.State}
    (h : HeaderStateBound b s) (hb : b ≤ d) : HeaderStateBound d s := by
  cases s with
  | formula f n => exact ⟨h.1.mono hb,Nat.le_trans h.2 hb⟩
  | clause c f n => exact ⟨h.1.mono hb,h.2.1.mono hb,Nat.le_trans h.2.2 hb⟩
  | done n => exact Nat.le_trans h hb

theorem header_step_bound {b : Nat} (s : Header.State) (h : HeaderStateBound b s) :
    HeaderStateBound (b+2) (Header.step s) := by
  cases s with
  | done n => exact h.mono (by omega)
  | formula f n =>
    have hn := h.2
    cases f with
    | nil => change n ≤ b+2; omega
    | cons c f => exact ⟨(h.1 c (by simp)).mono (by omega),(formula_tail h.1).mono (by omega),by omega⟩
  | clause c f n =>
    have hn := h.2.2
    cases c with
    | nil => exact ⟨h.2.1.mono (by omega),by omega⟩
    | cons l c =>
      have hl := h.1 l (by simp)
      exact ⟨(clause_tail h.1).mono (by omega),h.2.1.mono (by omega),by omega⟩

end STACS2027.WordPipeline.Payload
