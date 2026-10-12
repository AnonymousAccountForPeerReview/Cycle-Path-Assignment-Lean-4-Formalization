module

public import NPHardness.PlanarSourceRotationTable
public import NPHardness.PlanarSourcePackedSuccessor

/-! The checked finite arithmetic guard implements the registered angular
successor whenever the concrete descriptor table covers the incident
occurrences and evaluates to their registered page/key values. -/

@[expose] public section
namespace STACS2027.PlanarSource.RotationTable
open Complexity Complexity.SAT Complexity.Planar Comb

/-- Geometric fields of a live descriptor agree with one actual occurrence. -/
def EntryCorrect (f : CNF) (p : Packed.Entry) : Prop :=
  p.live = true → p.index < nM f ∧
    p.variable = vr f (oj f p.index) (ot f p.index) ∧
    p.top = isTop f (oj f p.index) ∧ p.key = key f p.index

def activeIndices (p : Packed.Entry) (xs : List Packed.Entry) : List Nat :=
  (xs.filter (fun q => q.live && q.variable == p.variable)).map Packed.Entry.index

theorem mem_activeIndices (p : Packed.Entry) (xs : List Packed.Entry) (e : Nat) :
    e ∈ activeIndices p xs ↔ ∃ q ∈ xs, Packed.Active p q ∧ q.index = e := by
  simp only [activeIndices, List.mem_map, List.mem_filter, Bool.and_eq_true,
    beq_iff_eq, Packed.Active]
  constructor
  · rintro ⟨q,⟨hq,ha⟩,he⟩; exact ⟨q,hq,ha,he⟩
  · rintro ⟨q,hq,ha,he⟩; exact ⟨q,⟨hq,ha⟩,he⟩

theorem before_entries {f : CNF} {p q : Packed.Entry}
    (hp : EntryCorrect f p) (hq : EntryCorrect f q)
    (hlp : p.live = true) (hlq : q.live = true) :
    Packed.Before p q ↔ Before f p.index q.index := by
  have hp' := hp hlp
  have hq' := hq hlq
  simp only [Packed.Before, Before, hp'.2.2.1, hq'.2.2.1, hp'.2.2.2, hq'.2.2.2]

theorem nextIn_entries {f : CNF} {p q : Packed.Entry} {xs : List Packed.Entry}
    (hp : EntryCorrect f p) (hq : EntryCorrect f q)
    (hx : ∀ r ∈ xs, EntryCorrect f r)
    (hlp : p.live = true) (haq : Packed.Active p q) :
    Packed.NextIn p q xs ↔ NextIn (Before f) (activeIndices p xs) p.index q.index := by
  have hpq := before_entries hp hq hlp haq.1
  constructor
  · rintro ⟨_,_,h⟩
    rcases h with ⟨hab,hn⟩ | ⟨hmax,hmin⟩
    · refine Or.inl ⟨hpq.mp hab, ?_⟩
      intro e he hbetween
      obtain ⟨r,hr,har,rfl⟩ := (mem_activeIndices p xs e).mp he
      exact hn r hr har ⟨(before_entries hp (hx r hr) hlp har.1).mpr hbetween.1,
        (before_entries (hx r hr) hq har.1 haq.1).mpr hbetween.2⟩
    · apply Or.inr
      constructor
      · intro e he hlt
        obtain ⟨r,hr,har,rfl⟩ := (mem_activeIndices p xs e).mp he
        exact hmax r hr har ((before_entries hp (hx r hr) hlp har.1).mpr hlt)
      · intro e he hlt
        obtain ⟨r,hr,har,rfl⟩ := (mem_activeIndices p xs e).mp he
        exact hmin r hr har ((before_entries (hx r hr) hq har.1 haq.1).mpr hlt)
  · intro h
    refine ⟨hlp,haq,?_⟩
    rcases h with ⟨hab,hn⟩ | ⟨hmax,hmin⟩
    · refine Or.inl ⟨hpq.mpr hab, ?_⟩
      intro r hr har hbetween
      exact hn r.index ((mem_activeIndices p xs r.index).mpr ⟨r,hr,har,rfl⟩)
        ⟨(before_entries hp (hx r hr) hlp har.1).mp hbetween.1,
          (before_entries (hx r hr) hq har.1 haq.1).mp hbetween.2⟩
    · apply Or.inr
      constructor
      · intro r hr har hlt
        exact hmax r.index ((mem_activeIndices p xs r.index).mpr ⟨r,hr,har,rfl⟩)
          ((before_entries hp (hx r hr) hlp har.1).mp hlt)
      · intro r hr har hlt
        exact hmin r.index ((mem_activeIndices p xs r.index).mpr ⟨r,hr,har,rfl⟩)
          ((before_entries (hx r hr) hq har.1 haq.1).mp hlt)

/-- Correctness of the *compiled* guard relative to the registered angular
rotation. Every premise is a source descriptor identity or local occurrence
coverage; the desired successor is the conclusion. -/
theorem successorTest_iff_registered {n : Nat} {f : CNF} (hf : CombOK f)
    (p q : Packed.Occurrence n) (xs : List (Packed.Occurrence n))
    (w : SAT.Word) (env : StackTableauEmitter.Env n)
    (hp : EntryCorrect f (p.eval w env))
    (hq : EntryCorrect f (q.eval w env))
    (hx : ∀ r ∈ xs, EntryCorrect f (r.eval w env))
    (hlp : (p.eval w env).live = true)
    (haq : Packed.Active (p.eval w env) (q.eval w env))
    (hcover : ∀ e, e ∈ activeIndices (p.eval w env) (xs.map (fun r => r.eval w env)) ↔
      e < nM f ∧ vr f (oj f e) (ot f e) = (p.eval w env).variable) :
    (Packed.successorTest p q xs).eval w env = true ↔
      rnext (incidenceOrder f (p.eval w env).variable) (p.eval w env).index = (q.eval w env).index := by
  have hp' := hp hlp
  have hq' := hq haq.1
  have hv : (p.eval w env).variable < nK f := by
    rw [hp'.2.1]
    have ho := occ_spec f _ hp'.1
    exact vr_lt _ _ ho.1 ho.2.1
  rw [Packed.successorTest_eval,
    nextIn_entries hp hq (by
      intro r hr
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
      exact hx s hs) hlp haq]
  apply variable_next_iff hf hv _ hcover
  · exact (hcover _).mpr ⟨hp'.1,hp'.2.1.symm⟩
  · exact (hcover _).mpr ⟨hq'.1,hq'.2.1.symm.trans haq.2⟩

end STACS2027.PlanarSource.RotationTable
