module

public import NPHardness.PlanarSourceCombRotation

/-! Exact clause-slot rotation survives executable deletion of the comb spine. -/

@[expose] public section
namespace STACS2027.PlanarSource.ComputableComb
open Complexity Complexity.SAT Complexity.Planar Comb
open STACS2027.PlanarGluing STACS2027.PlanarPreprocess.Deletion
open STACS2027.PlanarSource.Embedding STACS2027.PlanarSource.Formula

theorem GraphEmbedding.dropLast_node_of_lt {V : Type} (es : List (V×V)) (e : V×V)
    (G : GraphEmbedding (es++[e])) (x : Fin (2*es.length))
    (hx : (G.map.node ⟨x.val,by have := x.isLt; simp; omega⟩).val<2*es.length) :
    ((G.dropLast es e).map.node x).val=
      (G.map.node ⟨x.val,by have := x.isLt; simp; omega⟩).val := by
  let H := (finalEdgeCast es e).hypermap G.map
  have hH : (H.node (embedPair x)).val<2*es.length := hx
  have ha : H.node (embedPair x)≠penultimate (2*es.length) := by
    intro he
    have := congrArg Fin.val he
    change (H.node (embedPair x)).val=2*es.length at this
    omega
  have hb : H.node (embedPair x)≠last (2*es.length+1) := by
    intro he
    have := congrArg Fin.val he
    change (H.node (embedPair x)).val=2*es.length+1 at this
    omega
  exact congrArg Fin.val (embed_removePair_of_avoids (hm_node_inj H) x ha hb)

theorem GraphEmbedding.prefix_node_of_lt {V : Type} (es ts : List (V×V))
    (G : GraphEmbedding (es++ts)) (x : Fin (2*es.length))
    (hx : (G.map.node ⟨x.val,by have := x.isLt; simp; omega⟩).val<2*es.length) :
    ((G.prefix es ts).map.node x).val=
      (G.map.node ⟨x.val,by have := x.isLt; simp; omega⟩).val := by
  induction ts generalizing es with
  | nil => rfl
  | cons e ts ih =>
    let H := G.reindex (show es++e::ts=(es++[e])++ts by simp)
    let y : Fin (2*(es++[e]).length) := ⟨x.val,by have := x.isLt; simp; omega⟩
    have hy : (H.map.node ⟨y.val,by have hy0 := y.isLt; simp only [List.length_append] at *; omega⟩).val<2*(es++[e]).length := by
      have hval : (H.map.node ⟨y.val,by have hy0 := y.isLt; simp only [List.length_append] at *; omega⟩).val=
          (G.map.node ⟨x.val,by have := x.isLt; simp; omega⟩).val := rfl
      rw [hval]
      simp
      omega
    have hi := ih (es++[e]) H y hy
    have hsmall : ((H.prefix (es++[e]) ts).map.node y).val<2*es.length := by
      rw [hi]
      exact hx
    exact (GraphEmbedding.dropLast_node_of_lt es e (H.prefix (es++[e]) ts) x hsmall).trans hi

theorem incidenceEmbedding_clause_node {f : CNF} (h : CombOK f)
    (j t : Nat) (hj : j<f.length) (ht : t<kl f j) :
    (((embedding h).prefix (incidenceGraph f) (variableCycle f)).map.node
      ⟨2*(off f j+t)+1,by rw [incidence_length_nM]; have := off_add_lt f j t hj ht; omega⟩).val =
      2*(off f j+(t+1)%kl f j)+1 := by
  let x : Fin (2*(incidenceGraph f).length) :=
    ⟨2*(off f j+t)+1,by rw [incidence_length_nM]; have := off_add_lt f j t hj ht; omega⟩
  have hstep : ((embedding h).map.node ⟨x.val,by have := x.isLt; simp; omega⟩).val=
      2*(off f j+(t+1)%kl f j)+1 := by
    rw [embedding_node,next_eq]
    exact nxt_cl h hj ht
  have hsmall : ((embedding h).map.node ⟨x.val,by have := x.isLt; simp; omega⟩).val<2*(incidenceGraph f).length := by
    rw [hstep,incidence_length_nM]
    have := off_add_lt f j ((t+1)%kl f j) hj (Nat.mod_lt _ (by omega))
    omega
  exact (GraphEmbedding.prefix_node_of_lt (incidenceGraph f) (variableCycle f) (embedding h) x hsmall).trans hstep

theorem edgeData_clause_next (f : CNF) (G : GraphEmbedding (incidenceGraph f))
    (i : Fin (incidenceGraph f).length) :
    ((ComputableFormula.edgeData f G).rotation.clause.toFun i).val=(G.map.node (d2 i 1)).val/2 := rfl

theorem rotationData_cast_clause {f : CNF} {n m : Nat} (h : n=m)
    (D : ComputableFormula.RotationData f n) (i : Fin m) :
    (((h ▸ D) : ComputableFormula.RotationData f m).rotation.clause.toFun i).val =
      (D.rotation.clause.toFun ⟨i.val,by have := i.isLt; omega⟩).val := by
  cases h
  rfl

theorem incidenceEmbedding_formulaData_clause {f : CNF} (h : CombOK f)
    (j t : Nat) (hj : j<f.length) (ht : t<kl f j) :
    ((ComputableFormula.formulaData f ((embedding h).prefix (incidenceGraph f) (variableCycle f))).rotation.clause.toFun
      ⟨off f j+t,by rw [←incidenceGraph_length_flatten,incidence_length_nM]; exact off_add_lt f j t hj ht⟩).val=
      off f j+(t+1)%kl f j := by
  rw [ComputableFormula.formulaData,rotationData_cast_clause,edgeData_clause_next]
  have hs := incidenceEmbedding_clause_node h j t hj ht
  change (((embedding h).prefix (incidenceGraph f) (variableCycle f)).map.node
      ⟨2*(off f j+t)+1,_⟩).val/2=_
  rw [hs]
  omega

/-- The inverse clause rotation is the previous literal slot of the same clause. -/
theorem incidenceEmbedding_formulaData_clause_prev {f : CNF} (h : CombOK f)
    (i : Fin f.flatten.length) :
    ((ComputableFormula.formulaData f ((embedding h).prefix (incidenceGraph f) (variableCycle f))).rotation.clause.invFun i).val=
      off f (oj f i.val)+(ot f i.val+kl f (oj f i.val)-1)%kl f (oj f i.val) := by
  have hi : i.val<nM f := by
    rw [←incidence_length_nM,Formula.incidenceGraph_length_flatten]
    exact i.isLt
  obtain ⟨hj,ht,hoff⟩ := occ_spec f i.val hi
  let p : Fin f.flatten.length :=
    ⟨off f (oj f i.val)+(ot f i.val+kl f (oj f i.val)-1)%kl f (oj f i.val),by
      have hnM : nM f=f.flatten.length := (incidence_length_nM f).symm.trans (Formula.incidenceGraph_length_flatten f)
      have hh := off_add_lt f (oj f i.val) ((ot f i.val+kl f (oj f i.val)-1)%kl f (oj f i.val)) hj (Nat.mod_lt _ (by omega))
      omega⟩
  have hp := incidenceEmbedding_formulaData_clause h (oj f i.val)
    ((ot f i.val+kl f (oj f i.val)-1)%kl f (oj f i.val)) hj (Nat.mod_lt _ (by omega))
  rw [(mod_succ_pred (by omega) ht).1,hoff] at hp
  have he : (ComputableFormula.formulaData f ((embedding h).prefix (incidenceGraph f) (variableCycle f))).rotation.clause.toFun p=i := Fin.ext hp
  have hh := congrArg (ComputableFormula.formulaData f ((embedding h).prefix (incidenceGraph f) (variableCycle f))).rotation.clause.invFun he
  rw [DartEquiv.left_inv] at hh
  exact congrArg Fin.val hh.symm

theorem gridIncidenceEmbedding_formulaData_clause_prev (W m : Nat)
    (bits : Nat→Nat→Bool×Bool) (hm : 1≤m) (i : Fin (Grid.gridCNF W m bits).flatten.length) :
    ((ComputableFormula.formulaData (Grid.gridCNF W m bits) (gridIncidenceEmbedding W m bits hm)).rotation.clause.invFun i).val=
      off (Grid.gridCNF W m bits) (oj (Grid.gridCNF W m bits) i.val)+
        (ot (Grid.gridCNF W m bits) i.val+kl (Grid.gridCNF W m bits) (oj (Grid.gridCNF W m bits) i.val)-1)%
          kl (Grid.gridCNF W m bits) (oj (Grid.gridCNF W m bits) i.val) :=
  incidenceEmbedding_formulaData_clause_prev (Grid.gridCNF_combOK hm bits) i

end STACS2027.PlanarSource.ComputableComb
