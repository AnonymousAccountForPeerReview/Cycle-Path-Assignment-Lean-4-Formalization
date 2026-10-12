module

public import NPHardness.PlanarPreprocessDeletionRotation
public import NPHardness.PlanarSourceComputableDelete

/-! Exact cyclic-order preservation in executable graph-prefix deletion. -/

@[expose] public section
namespace STACS2027.PlanarSource.ComputableComb
open Complexity Complexity.SAT Complexity.Planar
open STACS2027.PlanarPreprocess.Deletion

theorem GraphEmbedding.dropLast_rnext {V : Type} (es : List (V×V)) (e : V×V)
    (G : GraphEmbedding (es++[e])) (xs : List Nat) (hn : xs.Nodup)
    (hb : ∀ x ∈ xs, x < 2*(es++[e]).length)
    (hrot : ∀ d : Fin (2*(es++[e]).length), d.val∈xs → (G.map.node d).val=rnext xs d.val)
    (x : Fin (2*es.length)) (hx : x.val∈xs) :
    ((G.dropLast es e).map.node x).val =
      rnext (xs.filter (fun d => decide (d<2*es.length))) x.val := by
  let H := (finalEdgeCast es e).hypermap G.map
  have hb' : ∀ d ∈ xs, d<2*es.length+2 := by simpa [Nat.mul_add] using hb
  have hrot' : ∀ d : Fin (2*es.length+2), d.val∈xs → (H.node d).val=rnext xs d.val :=
    fun d hd => hrot ((finalEdgeCast es e).invFun d) hd
  exact removePair_rnext H.node (hm_node_inj H) xs hn hb' hrot' x hx

/-- Removing an arbitrary trailing edge list retains the exact cyclic order
of every surviving source rotation. -/
theorem GraphEmbedding.prefix_rnext {V : Type} (es ts : List (V×V))
    (G : GraphEmbedding (es++ts)) (xs : List Nat) (hn : xs.Nodup)
    (hb : ∀ x ∈ xs, x<2*(es++ts).length)
    (hrot : ∀ d : Fin (2*(es++ts).length), d.val∈xs → (G.map.node d).val=rnext xs d.val)
    (x : Fin (2*es.length)) (hx : x.val∈xs) :
    ((G.prefix es ts).map.node x).val =
      rnext (xs.filter (fun d => decide (d<2*es.length))) x.val := by
  induction ts generalizing es with
  | nil =>
    have hf : xs.filter (fun d => decide (d<2*es.length))=xs := by
      apply List.filter_eq_self.mpr
      intro d hd
      apply decide_eq_true
      simpa only [List.append_nil] using hb d hd
    rw [hf]
    exact hrot ⟨x.val,by simpa only [List.append_nil] using x.isLt⟩ hx
  | cons e ts ih =>
    let H := G.reindex (show es++e::ts=(es++[e])++ts by simp)
    have hb' : ∀ d∈xs, d<2*((es++[e])++ts).length := by
      simpa only [List.append_assoc,List.singleton_append] using hb
    have hrot' : ∀ d : Fin (2*((es++[e])++ts).length),
        d.val∈xs → (H.map.node d).val=rnext xs d.val := by
      intro d hd
      exact hrot ⟨d.val,by simpa only [List.append_assoc,List.singleton_append] using d.isLt⟩ hd
    have hstep := GraphEmbedding.dropLast_rnext es e (H.prefix (es++[e]) ts)
      (xs.filter (fun d => decide (d<2*(es++[e]).length))) (hn.filter _)
      (by intro d hd; exact of_decide_eq_true (List.mem_filter.mp hd).2)
      (fun d hd => ih (es++[e]) H hb' hrot' d (List.mem_filter.mp hd).1) x
      (List.mem_filter.mpr ⟨hx,by
        apply decide_eq_true
        have := x.isLt
        simp only [List.length_append,List.length_cons,List.length_nil]
        omega⟩)
    rw [filter_lt_filter_lt xs (by simp; omega)] at hstep
    exact hstep

end STACS2027.PlanarSource.ComputableComb
