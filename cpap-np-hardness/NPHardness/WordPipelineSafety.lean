module

public import NPHardness.WordPipelineGraphPayload
public import NPHardness.WordPipelineStagePayload

/-! Uniform word-payload bounds for every prefix of the full deterministic
pipeline. This covers preprocessing tables, clause and variable IDs, counters,
input/output literal records, local gadget labels, and emitted endpoints.
Linked-list pointers remain abstract cell references; a concrete primitive
RAM instruction-set compiler or pointer-address encoding is not asserted. -/

@[expose] public section
namespace STACS2027.WordPipeline
open Complexity.SAT LinearPreprocessPayload Payload

def StateBound (k b : Nat) : State → Prop
  | .normalize s => NormStateBound b s
  | .initialize s => InitStateBound b s
  | .units size adj s => size ≤ b ∧ AdjacencyBound b adj ∧ UnitsStateBound b s
  | .extract mem s => MemoryBound b mem ∧ ExtractStateBound b s
  | .padding count s => count ≤ b ∧ PaddingStateBound b s
  | .header f s => FormulaBound b f ∧ HeaderStateBound b s
  | .graph n f s => GraphStateBound k n b f s
  | .done out => VerticesBelow out ((2*b+1)*gadgetWidth k)

theorem StateBound.mono {k b d : Nat} {s : State}
    (h : StateBound k b s) (hb : b ≤ d) : StateBound k d s := by
  cases s with
  | normalize s => exact NormStateBound.mono h hb
  | «initialize» s => exact InitStateBound.mono h hb
  | units size adj s => exact ⟨Nat.le_trans h.1 hb,h.2.1.mono hb,h.2.2.mono hb⟩
  | extract mem s => exact ⟨h.1.mono hb,h.2.mono hb⟩
  | padding count s => exact ⟨Nat.le_trans h.1 hb,h.2.mono hb⟩
  | header f s => exact ⟨h.1.mono hb,h.2.mono hb⟩
  | graph n f s => exact GraphStateBound.mono h hb
  | done out => exact VerticesBelow.mono h (Nat.mul_le_mul_right _ (by omega))

theorem normalize_state_bound {k b : Nat} {s : LinearPreprocessNormalize.State}
    (h : NormStateBound b s) : StateBound k b (normalizeState s) := by
  cases s with
  | scan f acc => exact h
  | reverse f acc => exact h
  | done f => exact init_start_bound h

theorem initialize_state_bound {k b : Nat} {s : LinearPreprocessInit.State}
    (h : InitStateBound b s) : StateBound k b (initializeState s) := by
  cases s with
  | scanFormula j f mem adj => exact h
  | scanClause j c f mem adj => exact h
  | queue r size mem adj out => exact h
  | done size mem adj queue => exact ⟨h.1,h.2.2.1,h.2.1,h.2.2.2⟩

theorem units_state_bound {k b budget size : Nat} {adj : LinearPreprocessUnits.Incidences}
    {s : LinearPreprocessUnits.State} (hb : budget+1 ≤ b) (hsize : size ≤ b)
    (ha : AdjacencyBound b adj) (h : UnitsStateBound b s) :
    StateBound k b (unitsState budget size adj s) := by
  cases s with
  | running mem queue => exact ⟨hsize,ha,h⟩
  | done mem => exact ⟨h,by simp [ExtractStateBound,FormulaBound]; exact hsize⟩
  | rejected => exact ⟨hb,by simp [PaddingStateBound,FormulaBound]⟩

theorem extract_state_bound {k b budget : Nat} {mem : LinearPreprocessUnits.Memory}
    {s : LinearPreprocessExtract.State} (hb : budget ≤ b) (hm : MemoryBound b mem)
    (h : ExtractStateBound b s) : StateBound k b (extractState budget mem s) := by
  cases s with
  | scan j r acc count => exact ⟨hm,h⟩
  | reverse f acc count => exact ⟨hm,h⟩
  | done f count => exact ⟨by omega,h.1,Nat.zero_le _,by simp [FormulaBound]⟩

theorem padding_state_bound {k b count : Nat} {s : LinearPreprocessPadding.State}
    (hc : count ≤ b) (h : PaddingStateBound b s) : StateBound k b (paddingState count s) := by
  cases s with
  | scanFormula f n acc => exact ⟨hc,h⟩
  | scanClause c f n acc => exact ⟨hc,h⟩
  | pad r n acc => exact ⟨hc,h⟩
  | reverse f acc => exact ⟨hc,h⟩
  | done f => exact ⟨h,h,Nat.zero_le _⟩

theorem header_state_bound {k b : Nat} {f : CNF} {s : Header.State}
    (hf : FormulaBound b f) (h : HeaderStateBound b s) : StateBound k b (headerState f s) := by
  cases s with
  | formula g n => exact ⟨hf,h⟩
  | clause c g n => exact ⟨hf,h⟩
  | done n => exact graph_initial_bound h hf

theorem graph_state_bound {k n b : Nat} {f : CNF} {s : WordConstructor.Config}
    (h : GraphStateBound k n b f s) : StateBound k b (graphState n f s) := by
  rcases s with ⟨phase,mem,out⟩
  cases phase <;> first | exact h | exact h.2.2.2.2

/-- A global transition increases the numeric envelope by at most two. -/
theorem step_bound (flips : EndpointChoices) {k budget b : Nat} {s : State}
    (hb : budget ≤ b) (h : StateBound k b s) : StateBound k (b+2) (step flips k budget s) := by
  cases s with
  | normalize s => exact normalize_state_bound (norm_step_bound s h)
  | «initialize» s => exact initialize_state_bound ((init_step_bound s h).mono (by omega))
  | units size adj s =>
    exact units_state_bound (by omega) (by have := h.1; omega)
      (h.2.1.mono (by omega)) ((units_step_bound adj h.2.1 s h.2.2).mono (by omega))
  | extract mem s =>
    exact extract_state_bound (by omega) (h.1.mono (by omega)) (extract_step_bound mem h.1 s h.2)
  | padding count s =>
    exact padding_state_bound (by have := h.1; omega) (padding_step_bound h.1 s h.2)
  | header f s => exact header_state_bound (h.1.mono (by omega)) (header_step_bound s h.2)
  | graph n f s => exact graph_state_bound ((graph_step_bound flips h).mono (by omega))
  | done out => exact StateBound.mono h (by omega)

theorem Runs.bounded {flips : EndpointChoices} {k budget b t : Nat} {s q : State}
    (h : Runs (step flips k budget) t s q) (hb : budget ≤ b) (hs : StateBound k b s) :
    StateBound k (b+2*t) q := by
  induction h generalizing b with
  | refl => simpa using hs
  | next h ih =>
    have hh := ih (show budget ≤ b+2 by omega) (step_bound flips hb hs)
    simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem initial_bound (k : Nat) (f : CNF) :
    StateBound k (variableBound f+f.length+1) (initial f) := by
  refine ⟨?_,by simp [FormulaBound]⟩
  intro c hc l hl
  have h := literal_lt_variableBound hc hl
  omega

def wordWidth (k b t : Nat) : Nat := ((2*(b+2*t)+1)*(gadgetWidth k+1)).log2+1

/-- All non-vertex natural fields fit `w` bits, as do local gadget labels and
all emitted endpoints. The `StateBound` predicate spells out the fields of
each phase, including every live preprocessing cell and queue entry. -/
def WordsFit (k w : Nat) (s : State) : Prop :=
  StateBound k (2^w-1) s ∧ gadgetWidth k < 2^w ∧
    match s with
    | .graph _ _ cfg => VerticesBelow cfg.output (2^w)
    | .done out => VerticesBelow out (2^w)
    | _ => True

theorem bounded_words {k b t : Nat} {s : State} (h : StateBound k (b+2*t) s) :
    WordsFit k (wordWidth k b t) s := by
  have hp : (2*(b+2*t)+1)*(gadgetWidth k+1) < 2^wordWidth k b t := Nat.lt_log2_self
  have hb : b+2*t ≤ (2*(b+2*t)+1)*(gadgetWidth k+1) := by
    have hm := Nat.mul_le_mul_left (2*(b+2*t)+1) (show 1 ≤ gadgetWidth k+1 by omega)
    simp only [Nat.mul_one] at hm
    omega
  have hw : gadgetWidth k < (2*(b+2*t)+1)*(gadgetWidth k+1) := by
    have hm := Nat.mul_le_mul_right (gadgetWidth k+1) (show 1 ≤ 2*(b+2*t)+1 by omega)
    simp only [Nat.one_mul] at hm
    omega
  have hv : (2*(b+2*t)+1)*gadgetWidth k ≤ 2^wordWidth k b t := by
    have hm := Nat.mul_le_mul_left (2*(b+2*t)+1) (show gadgetWidth k ≤ gadgetWidth k+1 by omega)
    omega
  refine ⟨h.mono (by omega),Nat.lt_trans hw hp,?_⟩
  cases s with
  | graph n f cfg => exact VerticesBelow.mono h.2.2.2.2 hv
  | done out => exact VerticesBelow.mono h hv
  | normalize s => trivial
  | «initialize» s => trivial
  | units size adj s => trivial
  | extract mem s => trivial
  | padding count s => trivial
  | header f s => trivial

theorem wordWidth_logarithmic (k n m t : Nat)
    (hm : m ≤ 3*n) (ht : t ≤ (n+1)*linearCoefficient k) :
    wordWidth k (n+m+1) t ≤ (n+1).log2 +
      ((4*linearCoefficient k+11)*(gadgetWidth k+1)).log2 + 2 := by
  let A := (4*linearCoefficient k+11)*(gadgetWidth k+1)
  have hA : 0 < A := Nat.mul_pos (by omega) (by omega)
  have hnum : 2*(n+m+1+2*t)+1 ≤ (n+1)*(4*linearCoefficient k+11) := by
    simp only [Nat.mul_add]
    rw [Nat.mul_left_comm (n+1) 4 (linearCoefficient k)]
    omega
  have hp : (2*(n+m+1+2*t)+1)*(gadgetWidth k+1) ≤ (n+1)*A := by
    exact (Nat.mul_assoc _ _ _).symm ▸ Nat.mul_le_mul_right (gadgetWidth k+1) hnum
  have hn : n+1 < 2^((n+1).log2+1) := Nat.lt_log2_self
  have ha : A < 2^(A.log2+1) := Nat.lt_log2_self
  have hprod : (n+1)*A < 2^((n+1).log2+A.log2+2) := by
    have h1 := Nat.mul_lt_mul_of_pos_right hn hA
    have h2 := Nat.mul_le_mul_left (2^((n+1).log2+1)) (Nat.le_of_lt ha)
    have he : (n+1).log2+A.log2+2 = ((n+1).log2+1)+(A.log2+1) := by omega
    rw [he,Nat.pow_add]
    exact Nat.lt_of_lt_of_le h1 h2
  have hz : (2*(n+m+1+2*t)+1)*(gadgetWidth k+1) ≠ 0 :=
    Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))
  have hl := (Nat.log2_lt hz).mpr (Nat.lt_of_le_of_lt hp hprod)
  change ((2*(n+m+1+2*t)+1)*(gadgetWidth k+1)).log2+1 ≤ (n+1).log2+A.log2+2
  omega

/-- Full-domain linear construction, with one logarithmic payload-word size
valid throughout every execution prefix. All preprocessing is charged. -/
theorem full_domain_linear_words (flips : EndpointChoices) {k : Nat} (hk : 5 ≤ k)
    {f : CNF} (hf : BoundedOccurrence f) :
    ∃ t out w, Runs (step flips k f.length) t (initial f) (.done out) ∧
      t ≤ (variableBound f+1)*linearCoefficient k ∧
      w ≤ (variableBound f+1).log2 +
        ((4*linearCoefficient k+11)*(gadgetWidth k+1)).log2 + 2 ∧
      (Satisfiable f ↔ HasAssignment out k f.length) ∧
      ∀ u s, u ≤ t → Runs (step flips k f.length) u (initial f) s → WordsFit k w s := by
  obtain ⟨t,out,hr,ht,hs⟩ := full_domain_linear flips hk hf
  have hm : f.length ≤ 3*variableBound f := by have := hf.clause_count_variableBound; omega
  refine ⟨t,out,wordWidth k (variableBound f+f.length+1) t,hr,ht,
    wordWidth_logarithmic k (variableBound f) f.length t hm ht,hs,?_⟩
  intro u s hu hrun
  apply bounded_words
  exact (hrun.bounded (by omega) (initial_bound k f)).mono (by omega)

end STACS2027.WordPipeline
