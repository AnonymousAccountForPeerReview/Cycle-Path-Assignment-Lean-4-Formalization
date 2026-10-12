module

public import NPHardness.WordPipelineCorrect
public import NPHardness.LinearPreprocessPayload

/-! Numeric payload invariants for graph emission, independent of the semantic
cleanliness invariant. They are used to bound all pipeline phases uniformly. -/

@[expose] public section
namespace STACS2027.WordPipeline.Payload
open Complexity.SAT LinearPreprocessPayload

def PlacedBound (b : Nat) (c : List PlacedLiteral) : Prop :=
  ∀ p ∈ c, p.literal.var ≤ b ∧ p.earlier ≤ b

def GraphPhaseBound (k b : Nat) : WordConstructor.Phase → Prop
  | .variables v r => v ≤ b ∧ r ≤ b
  | .variableEdges v r es => v ≤ b ∧ r ≤ b ∧ VerticesBelow es (gadgetWidth k)
  | .clauses j f => j ≤ b ∧ FormulaBound b f
  | .literals j ls f rev => j ≤ b ∧ ClauseBound b ls ∧ FormulaBound b f ∧ PlacedBound b rev
  | .clauseEdges j f c es => j ≤ b ∧ FormulaBound b f ∧ PlacedBound b c ∧ VerticesBelow es (gadgetWidth k)
  | .done => True
  | .rejected => True

def GraphStateBound (k n b : Nat) (input : CNF) (s : WordConstructor.Config) : Prop :=
  n ≤ b ∧ FormulaBound b input ∧ GraphPhaseBound k b s.phase ∧
    (∀ l, s.memory l ≤ b) ∧ VerticesBelow s.output ((2*b+1)*gadgetWidth k)

theorem PlacedBound.mono {b d : Nat} {c : List PlacedLiteral}
    (h : PlacedBound b c) (hb : b ≤ d) : PlacedBound d c :=
  fun p hp => ⟨Nat.le_trans (h p hp).1 hb,Nat.le_trans (h p hp).2 hb⟩

theorem GraphPhaseBound.mono {k b d : Nat} {p : WordConstructor.Phase}
    (h : GraphPhaseBound k b p) (hb : b ≤ d) : GraphPhaseBound k d p := by
  cases p with
  | variables v r => exact ⟨Nat.le_trans h.1 hb,Nat.le_trans h.2 hb⟩
  | variableEdges v r es => exact ⟨Nat.le_trans h.1 hb,Nat.le_trans h.2.1 hb,h.2.2⟩
  | clauses j f => exact ⟨Nat.le_trans h.1 hb,h.2.mono hb⟩
  | literals j ls f rev => exact ⟨Nat.le_trans h.1 hb,h.2.1.mono hb,h.2.2.1.mono hb,h.2.2.2.mono hb⟩
  | clauseEdges j f c es => exact ⟨Nat.le_trans h.1 hb,h.2.1.mono hb,h.2.2.1.mono hb,h.2.2.2⟩
  | done => trivial
  | rejected => trivial

theorem GraphStateBound.mono {k n b d : Nat} {f : CNF} {s : WordConstructor.Config}
    (h : GraphStateBound k n b f s) (hb : b ≤ d) : GraphStateBound k n d f s :=
  ⟨Nat.le_trans h.1 hb,h.2.1.mono hb,h.2.2.1.mono hb,
    fun l => Nat.le_trans (h.2.2.2.1 l) hb,
    h.2.2.2.2.mono (Nat.mul_le_mul_right _ (by omega))⟩

theorem block_bound {k b v u : Nat} (hv : v ≤ 2*b) (hu : u < gadgetWidth k) :
    blockVertex (gadgetWidth k) v u < (2*b+1)*gadgetWidth k := by
  have h := WordConstructor.block_payload (n := b) (b := b) (by omega : v ≤ b+b) hu
  simpa [Nat.two_mul] using h

theorem clause_vertex_bound (flips : EndpointChoices) {k n b j : Nat} {c : List PlacedLiteral}
    (hn : n ≤ b) (hj : j ≤ b) (hc : PlacedBound b c) {u : Nat} (hu : u < gadgetWidth k) :
    orientedClauseVertex flips (gadgetWidth k) n j c u < (2*b+1)*gadgetWidth k := by
  unfold orientedClauseVertex Oriented.clauseVertex
  cases he : attachmentAt c u with
  | none => exact block_bound (by omega) hu
  | some ps =>
    obtain ⟨p,side⟩ := ps
    obtain ⟨i,_,hip,_⟩ := attachmentAt_spec.mp he
    have hp := hc p (List.mem_of_getElem? hip)
    exact block_bound (by omega)
      (Nat.lt_of_lt_of_le (variableEndpoint_bound _ _) (by have := gadgetWidth_ge k; omega))

theorem graph_step_bound (flips : EndpointChoices) {k n b : Nat} {input : CNF} {s : WordConstructor.Config}
    (h : GraphStateBound k n b input s) :
    GraphStateBound k n (b+1) input (WordConstructor.step flips k n input s) := by
  have hm : ∀ l, s.memory l ≤ b+1 := fun l => by have := h.2.2.2.1 l; omega
  have ho : VerticesBelow s.output ((2*(b+1)+1)*gadgetWidth k) :=
    h.2.2.2.2.mono (Nat.mul_le_mul_right _ (by omega))
  have hn : n ≤ b := h.1
  have hi := h.2.1
  have hp := h.2.2.1
  have hmem := h.2.2.2.1
  refine ⟨by omega,hi.mono (by omega),?_⟩
  rcases s with ⟨phase,m,out⟩
  cases phase with
  | variables v r =>
    cases r with
    | zero => exact ⟨⟨by omega,hi.mono (by omega)⟩,hm,ho⟩
    | succ r => exact ⟨⟨by have := hp.1; omega,by have := hp.2; omega,variableGraph_below k⟩,hm,ho⟩
  | variableEdges v r es =>
    cases es with
    | nil => exact ⟨⟨by have := hp.1; omega,by have := hp.2.1; omega⟩,hm,ho⟩
    | cons e es =>
      refine ⟨⟨by have := hp.1; omega,by have := hp.2.1; omega,
        fun a ha => hp.2.2 a (by simp [ha])⟩,hm,?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact WordConstructor.mapEdge_payload hp.2.2
          (fun u hu => block_bound (by have := hp.1; omega) hu) (by simp)
      · exact ho a ha
  | clauses j f =>
    cases f with
    | nil => exact ⟨True.intro,hm,ho⟩
    | cons c f =>
      have hc := hp.2 c (by simp)
      have hf : FormulaBound b f := fun d hd => hp.2 d (by simp [hd])
      exact ⟨⟨by have := hp.1; omega,hc.mono (by omega),hf.mono (by omega),
        by simp [PlacedBound]⟩,hm,ho⟩
  | literals j ls f rev =>
    cases ls with
    | nil =>
      cases hr : WordConstructor.ready rev with
      | none => simpa [WordConstructor.step,hr,GraphPhaseBound] using And.intro hm ho
      | some c =>
        obtain ⟨he,_⟩ := WordConstructor.ready_spec hr
        have hc : PlacedBound b c := by
          intro p hpc
          apply hp.2.2.2 p
          simp [he,hpc]
        simpa [WordConstructor.step,hr,GraphPhaseBound] using
          And.intro (And.intro (show j ≤ b+1 from by have := hp.1; omega)
            (And.intro (hp.2.2.1.mono (show b ≤ b+1 from by omega))
              (And.intro (hc.mono (by omega)) (clauseGraph_below k c)))) (And.intro hm ho)
    | cons l ls =>
      have hls : ClauseBound b ls := fun q hq => hp.2.1 q (by simp [hq])
      refine ⟨⟨by have := hp.1; omega,hls.mono (by omega),hp.2.2.1.mono (by omega),?_⟩,?_,ho⟩
      · intro p hpc
        rcases List.mem_cons.mp hpc with rfl | hpc
        · refine ⟨?_,?_⟩
          · have hh := hp.2.1 l (by simp)
            change l.var ≤ b+1
            omega
          · have hh := hmem l
            change m l ≤ b at hh
            change m l ≤ b+1
            omega
        · exact hp.2.2.2.mono (by omega) p hpc
      · intro q
        simp only [WordConstructor.step,incrementCounter]
        split
        · have hh := hmem l; change m l ≤ b at hh; omega
        · exact hm q
  | clauseEdges j f c es =>
    cases es with
    | nil => exact ⟨⟨by have := hp.1; omega,hp.2.1.mono (by omega)⟩,hm,ho⟩
    | cons e es =>
      refine ⟨⟨by have := hp.1; omega,hp.2.1.mono (by omega),hp.2.2.1.mono (by omega),
        fun a ha => hp.2.2.2 a (by simp [ha])⟩,hm,?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact WordConstructor.mapEdge_payload hp.2.2.2
          (fun u hu => clause_vertex_bound flips (by omega) (by have := hp.1; omega)
            (hp.2.2.1.mono (show b ≤ b+1 from by omega)) hu) (by simp)
      · exact ho a ha
  | done => exact ⟨hp.mono (by omega),hm,ho⟩
  | rejected => exact ⟨hp.mono (by omega),hm,ho⟩

theorem graph_initial_bound {k n b : Nat} {f : CNF} (hn : n ≤ b) (hf : FormulaBound b f) :
    GraphStateBound k n b f (WordConstructor.initial n) := by
  refine ⟨hn,hf,⟨Nat.zero_le _,hn⟩,?_,?_⟩
  · simp [WordConstructor.initial,historyMemory]
  · simp [WordConstructor.initial,VerticesBelow]

end STACS2027.WordPipeline.Payload
