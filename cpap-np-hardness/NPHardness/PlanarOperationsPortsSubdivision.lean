module

public import NPHardness.PlanarOperationsPorts

/-! Nonport subdivisions preserve actual cofacial attachment darts. -/

@[expose] public section
namespace STACS2027.PlanarOperations.Ports
open Complexity Complexity.Planar Subdivision
open Complexity.Planar.Subdiv (gN halfEdgeEnd_mem iterate_gN_val)

/-- The explicit four-dart subdivision hypermap, with its graph-sized index type. -/
def splitMap {V : Type} {es ts : List (V×V)} (c : Nat → V)
    (G : Hypermap (2*(es++ts).length)) : Hypermap (2*(es++splitEdges ts c).length) :=
  G' G (A := 2*es.length) (T := ts.length) (by simp only [List.length_append]; omega)
    (by simp only [List.length_append,splitEdges_length]; omega) (by omega)

/-- The explicit transformed hypermap satisfies the registered embedding
conditions. This exposes the witness needed for face-orbit transport. -/
theorem embedding_subdivide {V : Type} (es ts : List (V×V)) (c : Nat → V)
    (hc : ∀ u, u < ts.length → ∀ u', u' < ts.length → c u = c u' → u = u')
    (hfresh : ∀ e ∈ es++ts, ∀ u, u<ts.length → e.1 ≠ c u ∧ e.2 ≠ c u)
    {G : Hypermap (2*(es++ts).length)} (h : IsGraphEmbedding (es++ts) G) :
    IsGraphEmbedding (es++splitEdges ts c) (splitMap c G) := by
  obtain ⟨hedge,hnode,hP⟩ := h
  have hn : 2*(es++ts).length = 2*es.length+2*ts.length := by
    simp only [List.length_append]; omega
  have hN : 2*(es++splitEdges ts c).length = 2*es.length+4*ts.length := by
    simp only [List.length_append,splitEdges_length]; omega
  have hA : (2*es.length)%2 = 0 := by omega
  change IsGraphEmbedding (es++splitEdges ts c) (G' G hn hN hA)
  refine ⟨graphEdge_new G hn hN hA,?_,newMap_planar G hn hN hA hedge hP⟩
  have endOld : ∀ x, x < 2*es.length+4*ts.length → IsOld (2*es.length) x →
      halfEdgeEnd (es++splitEdges ts c) x = halfEdgeEnd (es++ts) (sig (2*es.length) x) :=
    fun x hx ho => end_old hx ho
  have nodeEnd : ∀ y : Fin (2*(es++ts).length),
      halfEdgeEnd (es++ts) (gN G y.val) = halfEdgeEnd (es++ts) y.val := by
    intro y
    have := (hnode y (G.node y)).mp ⟨1,rfl⟩
    unfold gN; rw [dite_eq_left y.isLt]
    exact this.symm
  have inv : ∀ x, x < 2*es.length+4*ts.length →
      halfEdgeEnd (es++splitEdges ts c) (nd G (2*es.length) x) =
        halfEdgeEnd (es++splitEdges ts c) x := by
    intro x hx
    by_cases ho : IsOld (2*es.length) x
    · rw [nd_old G ho, endOld _ (by have := nd_lt (G := G) hn hx; rw [nd_old G ho] at this; exact this)
        (isOld_iota _ _),sig_iota,endOld x hx ho]
      have hs := sig_lt (2*es.length) hx
      exact nodeEnd ⟨sig (2*es.length) x,by omega⟩
    · obtain ⟨u,r,rfl,hu,hr⟩ : ∃ u r, x = 2*es.length+4*u+r ∧ u<ts.length ∧ (r=1 ∨ r=3) :=
        ⟨(x-2*es.length)/4,(x-2*es.length)%4,by omega,by omega,by omega⟩
      rcases hr with rfl | rfl
      · rw [nd_r1 G (by omega) (by omega),show 2*es.length+4*u+1+2 = 2*es.length+4*u+3 by omega,
          end_c hu (by omega),end_c hu (by omega)]
      · rw [nd_r3 G (by omega) (by omega),show 2*es.length+4*u+3-2 = 2*es.length+4*u+1 by omega,
          end_c hu (by omega),end_c hu (by omega)]
  intro d d'
  have hd : d.val < 2*es.length+4*ts.length := by have := d.isLt; omega
  have hd' : d'.val < 2*es.length+4*ts.length := by have := d'.isLt; omega
  constructor
  · rintro ⟨k,rfl⟩
    rw [iterate_node_val]
    have invk : ∀ k x, x < 2*es.length+4*ts.length →
        halfEdgeEnd (es++splitEdges ts c) (iterate (nd G (2*es.length)) k x) =
          halfEdgeEnd (es++splitEdges ts c) x := by
      intro k
      induction k with
      | zero => intro x _; rfl
      | succ k ih =>
        intro x hx
        simp only [iterate]
        rw [ih _ (nd_lt (G := G) hn hx), inv x hx]
    exact (invk k d.val hd).symm
  · intro he
    have classify : ∀ x, x < 2*es.length+4*ts.length →
        IsOld (2*es.length) x ∨
        (∃ u, u<ts.length ∧ ∃ r, (r=1 ∨ r=3) ∧ x=2*es.length+4*u+r) := by
      intro x hx
      by_cases ho : IsOld (2*es.length) x
      · exact Or.inl ho
      · exact Or.inr ⟨(x-2*es.length)/4,by omega,(x-2*es.length)%4,by omega,by omega⟩
    have oldEnd : ∀ x, x < 2*es.length+4*ts.length → IsOld (2*es.length) x →
        ∀ v, halfEdgeEnd (es++splitEdges ts c) x = some v → ∀ u, u<ts.length → v ≠ c u := by
      intro x hx ho v hv u hu
      rw [endOld x hx ho] at hv
      obtain ⟨e,he,hve⟩ := halfEdgeEnd_mem hv
      rcases hve with rfl | rfl
      · exact (hfresh e he u hu).1
      · exact (hfresh e he u hu).2
    have toFin : ∀ k, iterate (nd G (2*es.length)) k d.val = d'.val →
        ∃ k, iterate (G' G hn hN hA).node k d = d' :=
      fun k hk => ⟨k,Fin.ext (by rw [iterate_node_val]; exact hk)⟩
    rcases classify d.val hd with ho | ⟨u,hu,r,hr,hdr⟩ <;>
      rcases classify d'.val hd' with ho' | ⟨u',hu',r',hr',hdr'⟩
    · rw [endOld _ hd ho,endOld _ hd' ho'] at he
      have hs := sig_lt (2*es.length) hd
      have hs' := sig_lt (2*es.length) hd'
      obtain ⟨k,hk⟩ := (hnode ⟨sig (2*es.length) d.val,by omega⟩
        ⟨sig (2*es.length) d'.val,by omega⟩).mpr he
      apply toFin k
      rw [iterate_nd_old G hn k _ hd ho]
      have := congrArg Fin.val hk
      rw [iterate_gN_val] at this
      have e : iterate (gN G) k (sig (2*es.length) d.val) = sig (2*es.length) d'.val := this
      rw [e,iota_sig _ ho']
    · rw [hdr',end_c hu' hr'] at he
      exact absurd rfl (oldEnd _ hd ho _ he u' hu')
    · rw [hdr,end_c hu hr] at he
      exact absurd rfl (oldEnd _ hd' ho' _ he.symm u hu)
    · rw [hdr,end_c hu hr,hdr',end_c hu' hr'] at he
      have := hc u hu u' hu' (Option.some.inj he)
      subst this
      obtain ⟨k,hk⟩ := reach_c G (A := 2*es.length) (u := u) hr hr'
      exact toFin k (by rw [hdr,hk,hdr'])

end STACS2027.PlanarOperations.Ports
