module

public import Outerplanar.Transfer
public import Outerplanar.Minors
import Mathlib.Tactic

/-!
# Outerplanar blocks have a degree-two elimination order

Algorithm 4 deletes, from an outerplanar graph, a vertex of degree at most two at a time
(Appendix E: "every nonempty outerplanar graph has a vertex of degree at most two, and
deleting a vertex preserves outerplanarity"). Here:

* in a polygon with non-crossing chords, every nonempty set `U` of positions has a vertex
  with at most two neighbours in `U` (`polygon_degenerate`): a vertex all of whose edges
  into `U` have no vertex of `U` strictly inside has at most one neighbour in `U` on either
  side, and such a vertex exists — any vertex if no edge into `U` spans a vertex of `U`,
  otherwise the first vertex of `U` inside a shortest such edge;
* hence in a graph with an outerplanar Hamiltonian cycle (`outerplanarHam_degenerate`);
* a graph all of whose nonempty vertex sets have such a vertex has a degree-two
  elimination order in the sense of Section 8 (`eliminationOrder_of_degenerate`).
-/

@[expose] public section

namespace STACS2027

/-- `u` has at most two neighbours in `U`. -/
def AtMostTwo (g : Graph) (U : List ℕ) (u : ℕ) : Prop :=
  ∀ a b c, a ∈ U → b ∈ U → c ∈ U → Adj g u a → Adj g u b → Adj g u c → a = b ∨ a = c ∨ b = c

/-- No vertex of `U` lies strictly between `u` and `y`. -/
def Gap (U : List ℕ) (u y : ℕ) : Prop := ∀ z ∈ U, ¬ (min u y < z ∧ z < max u y)

theorem atMostTwo_of_gaps {g : Graph} {U : List ℕ} {u : ℕ}
    (h : ∀ y ∈ U, Adj g u y → Gap U u y) : AtMostTwo g U u := by
  intro a b c ha hb hc hua hub huc
  have hga := h a ha hua
  have hgb := h b hb hub
  have hgc := h c hc huc
  have key : ∀ p q, p ∈ U → q ∈ U → Gap U u p → Gap U u q → Adj g u p → Adj g u q →
      (u < p ∧ u < q ∨ p < u ∧ q < u) → p = q := by
    intro p q hp hq hgp hgq hup huq hside
    by_contra hpq
    rcases Nat.lt_or_gt_of_ne hpq with hlt | hlt
    · rcases hside with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hgq p hp (by omega)
      · exact hgp q hq (by omega)
    · rcases hside with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hgp q hq (by omega)
      · exact hgq p hp (by omega)
  have hna := hua.1
  have hnb := hub.1
  have hnc := huc.1
  by_cases h1 : u < a <;> by_cases h2 : u < b <;> by_cases h3 : u < c
  · exact Or.inl (key a b ha hb hga hgb hua hub (Or.inl ⟨h1, h2⟩))
  · exact Or.inl (key a b ha hb hga hgb hua hub (Or.inl ⟨h1, h2⟩))
  · exact Or.inr (Or.inl (key a c ha hc hga hgc hua huc (Or.inl ⟨h1, h3⟩)))
  · exact Or.inr (Or.inr (key b c hb hc hgb hgc hub huc (Or.inr ⟨by omega, by omega⟩)))
  · exact Or.inr (Or.inr (key b c hb hc hgb hgc hub huc (Or.inl ⟨h2, h3⟩)))
  · exact Or.inr (Or.inl (key a c ha hc hga hgc hua huc (Or.inr ⟨by omega, by omega⟩)))
  · exact Or.inl (key a b ha hb hga hgb hua hub (Or.inr ⟨by omega, by omega⟩))
  · exact Or.inl (key a b ha hb hga hgb hua hub (Or.inr ⟨by omega, by omega⟩))

namespace IsPolygon

variable {g : Graph} {n : ℕ}

/-- **Polygons are 2-degenerate**: every nonempty set of positions has a vertex with at most
two neighbours in it. -/
theorem polygon_degenerate (hP : IsPolygon g n) {U : List ℕ} (hU : U ≠ []) :
    ∃ u ∈ U, AtMostTwo g U u := by
  classical
  -- the edges into `U` spanning a vertex of `U`
  let S : Finset (ℕ × ℕ) := (U.toFinset ×ˢ U.toFinset).filter fun e =>
    e.1 < e.2 ∧ Adj g e.1 e.2 ∧ ∃ z ∈ U, e.1 < z ∧ z < e.2
  by_cases hS : S.Nonempty
  · obtain ⟨⟨a, b⟩, hab, hmin⟩ := S.exists_min_image (fun e => e.2 - e.1) hS
    simp only [S, Finset.mem_filter, Finset.mem_product, List.mem_toFinset] at hab
    obtain ⟨⟨haU, hbU⟩, hlt, hadj, hz⟩ := hab
    let I : Finset ℕ := U.toFinset.filter fun z => a < z ∧ z < b
    have hI : I.Nonempty := by
      obtain ⟨z, hzU, hz1, hz2⟩ := hz
      exact ⟨z, by simp [I, hzU, hz1, hz2]⟩
    let x := I.min' hI
    have hxI : x ∈ I := I.min'_mem hI
    simp only [I, Finset.mem_filter, List.mem_toFinset] at hxI
    have hxmin : ∀ z ∈ U, a < z → z < b → x ≤ z := by
      intro z hzU h1 h2
      exact I.min'_le z (by simp [I, hzU, h1, h2])
    refine ⟨x, hxI.1, atMostTwo_of_gaps ?_⟩
    intro y hyU hxy z hzU hz
    have hyab : a ≤ y ∧ y ≤ b := by
      by_contra hc
      rcases (show y < a ∨ b < y by omega) with h | h
      · exact hP.noncross h hxI.2.1 hxI.2.2 hxy.symm hadj
      · exact hP.noncross hxI.2.1 hxI.2.2 h hadj hxy
    rcases Nat.lt_or_gt_of_ne hxy.1 with h | h
    · -- `y > x`: a shorter spanning edge `xy` would contradict the choice of `ab`
      have hmem : (x, y) ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_product, List.mem_toFinset]
        exact ⟨⟨hxI.1, hyU⟩, h, hxy, z, hzU, by omega, by omega⟩
      have := hmin _ hmem
      simp only at this
      omega
    · -- `y < x`: a vertex of `U` between `y` and `x` would precede `x` inside `ab`
      have := hxmin z hzU (by omega) (by omega)
      omega
  · -- no spanning edge: every vertex will do
    obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil U hU
    refine ⟨u, hu, atMostTwo_of_gaps ?_⟩
    intro y hyU huy z hzU hz
    apply hS
    rcases Nat.lt_or_gt_of_ne huy.1 with h | h
    · refine ⟨(u, y), ?_⟩
      simp only [S, Finset.mem_filter, Finset.mem_product, List.mem_toFinset]
      exact ⟨⟨hu, hyU⟩, h, huy, z, hzU, by omega, by omega⟩
    · refine ⟨(y, u), ?_⟩
      simp only [S, Finset.mem_filter, Finset.mem_product, List.mem_toFinset]
      exact ⟨⟨hyU, hu⟩, h, huy.symm, z, hzU, by omega, by omega⟩

end IsPolygon

/-- A graph with an outerplanar Hamiltonian cycle is 2-degenerate. -/
theorem outerplanarHam_degenerate {g : Graph} {ham : List ℕ} (h : OuterplanarHam g ham)
    {U : List ℕ} (hU : U ≠ []) (hUv : ∀ u ∈ U, u ∈ ham) : ∃ u ∈ U, AtMostTwo g U u := by
  have hP := isPolygon_posGraph h
  have hnd := h.1.2.2.1
  let pos : ℕ → ℕ := fun v => ham.idxOf v
  have hpos : ∀ v ∈ ham, ham.getD (pos v) 0 = v ∧ pos v < ham.length := by
    intro v hv
    have hlt : ham.idxOf v < ham.length := List.idxOf_lt_length_iff.mpr hv
    refine ⟨?_, hlt⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    exact List.getElem_idxOf hlt
  have hadj : ∀ u ∈ ham, ∀ v ∈ ham, (Adj (posGraph g ham) (pos u) (pos v) ↔ Adj g u v) := by
    intro u hu v hv
    rw [adj_posGraph, (hpos u hu).1, (hpos v hv).1]
    exact ⟨fun h => h.2.2, fun h' => ⟨(hpos u hu).2, (hpos v hv).2, h'⟩⟩
  obtain ⟨u', hu', hmax⟩ := hP.polygon_degenerate (U := U.map pos) (by simpa using hU)
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hu'
  refine ⟨u, hu, ?_⟩
  intro a b c ha hb hc hua hub huc
  have hu' := hUv u hu
  have ha' := hUv a ha
  have hb' := hUv b hb
  have hc' := hUv c hc
  have hinj : ∀ x ∈ ham, ∀ y ∈ ham, pos x = pos y → x = y := by
    intro x hx y hy he
    rw [← (hpos x hx).1, ← (hpos y hy).1, he]
  rcases hmax (pos a) (pos b) (pos c) (List.mem_map_of_mem ha) (List.mem_map_of_mem hb)
    (List.mem_map_of_mem hc) ((hadj u hu' a ha').mpr hua) ((hadj u hu' b hb').mpr hub)
    ((hadj u hu' c hc').mpr huc) with e | e | e
  · exact Or.inl (hinj a ha' b hb' e)
  · exact Or.inr (Or.inl (hinj a ha' c hc' e))
  · exact Or.inr (Or.inr (hinj b hb' c hc' e))

/-! ### Elimination orders -/

/-- An elimination order of the list `ord`: each entry has at most two neighbours among
the entries from it on. -/
def ElimList (g : Graph) : List ℕ → Prop
  | [] => True
  | u :: rest => AtMostTwo g (u :: rest) u ∧ ElimList g rest

theorem exists_elimList {g : Graph}
    (hdeg : ∀ U : List ℕ, U ≠ [] → ∃ u ∈ U, AtMostTwo g U u) :
    ∀ (m : ℕ) (U : List ℕ), U.length ≤ m → U.Nodup →
      ∃ ord : List ℕ, ord.Perm U ∧ ElimList g ord := by
  intro m
  induction m with
  | zero =>
    intro U hU _
    have : U = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨[], List.Perm.refl _, trivial⟩
  | succ m ih =>
    intro U hU hnd
    by_cases hne : U = []
    · subst hne; exact ⟨[], List.Perm.refl _, trivial⟩
    · obtain ⟨u, hu, hmax⟩ := hdeg U hne
      obtain ⟨ord, hp, he⟩ := ih (U.erase u) (by rw [List.length_erase_of_mem hu]; omega)
        (hnd.erase u)
      refine ⟨u :: ord, ?_, ?_, he⟩
      · exact (List.Perm.cons u hp).trans (List.perm_cons_erase hu).symm
      · intro a b c ha hb hc
        have hmem : ∀ x, x ∈ u :: ord → x ∈ U := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hu
          · exact List.mem_of_mem_erase (hp.subset hx)
        exact hmax a b c (hmem a ha) (hmem b hb) (hmem c hc)

theorem elimList_suffix {g : Graph} {v : ℕ} {post : List ℕ} :
    ∀ pre : List ℕ, ElimList g (pre ++ v :: post) → ElimList g (v :: post)
  | [], h => h
  | _ :: pre, h => elimList_suffix pre h.2

/-- **Elimination orders from degeneracy.** -/
theorem eliminationOrder_of_degenerate {g : Graph}
    (hdeg : ∀ U : List ℕ, U ≠ [] → (∀ u ∈ U, IsVertex g u) → ∃ u ∈ U, AtMostTwo g U u) :
    ∃ rank, EliminationOrder g rank := by
  classical
  let V := (vertices g).filter fun v => decide (IsVertex g v)
  have hV : ∀ v, v ∈ V ↔ IsVertex g v := by
    intro v
    simp only [V, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    rintro ⟨u, huv⟩
    exact (endpoints_mem_vertices huv.2).2
  have hVnd : V.Nodup := (List.nodup_range.filter _).filter _
  obtain ⟨ord, hp, he⟩ := exists_elimList (g := g) (fun U hU => by
    by_cases hsub : ∀ u ∈ U, IsVertex g u
    · exact hdeg U hU hsub
    · obtain ⟨u, hu, hnv⟩ : ∃ u ∈ U, ¬ IsVertex g u := by
        by_contra hc
        exact hsub (fun u hu => by by_contra h; exact hc ⟨u, hu, h⟩)
      refine ⟨u, hu, ?_⟩
      intro a b c _ _ _ hua
      exact absurd ⟨a, hua.symm⟩ hnv) V.length V le_rfl hVnd
  have hond : ord.Nodup := hp.nodup_iff.mpr hVnd
  have hmemo : ∀ v, v ∈ ord ↔ IsVertex g v := fun v => hp.mem_iff.trans (hV v)
  let m := ord.length
  let rank : ℕ → ℕ := fun v => if v ∈ ord then ord.idxOf v else m + v
  refine ⟨rank, ?_, ?_⟩
  · intro a b hab
    simp only [rank] at hab
    by_cases ha : a ∈ ord <;> by_cases hb : b ∈ ord <;> simp only [ha, hb, ite_true, ite_false] at hab
    · have h1 := List.idxOf_lt_length_iff.mpr ha
      rw [← List.getElem_idxOf h1, ← List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hb)]
      simp only [hab]
    · have := List.idxOf_lt_length_iff.mpr ha; omega
    · have := List.idxOf_lt_length_iff.mpr hb; omega
    · omega
  · intro v a b c hva hvb hvc ha hb hc
    by_cases hav : a = v
    · simp [hav] at ha
    by_cases hbv : b = v
    · simp [hbv] at hb
    by_cases hcv : c = v
    · simp [hcv] at hc
    have hva' : Adj g v a := ⟨Ne.symm hav, hva⟩
    have hvb' : Adj g v b := ⟨Ne.symm hbv, hvb⟩
    have hvc' : Adj g v c := ⟨Ne.symm hcv, hvc⟩
    have hvo : v ∈ ord := (hmemo v).mpr ⟨a, hva'.symm⟩
    have hao : a ∈ ord := (hmemo a).mpr ⟨v, hva'⟩
    have hbo : b ∈ ord := (hmemo b).mpr ⟨v, hvb'⟩
    have hco : c ∈ ord := (hmemo c).mpr ⟨v, hvc'⟩
    simp only [rank, hvo, hao, hbo, hco, ite_true] at ha hb hc
    -- the entries from `v` on
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hvo
    have hidx : ord.idxOf v = pre.length := by
      rw [hsplit]
      have : v ∉ pre := by
        intro hv
        rw [hsplit] at hond
        exact (List.nodup_append.mp hond).2.2 v hv v (by simp) rfl
      rw [List.idxOf_append_of_notMem this]; simp
    have hafter : ∀ x ∈ ord, ord.idxOf v < ord.idxOf x → x ∈ v :: post := by
      intro x hx hlt
      rw [hsplit] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exfalso
        have : ord.idxOf x < pre.length := by
          rw [hsplit, List.idxOf_append_of_mem hx]
          exact List.idxOf_lt_length_iff.mpr hx
        omega
      · exact hx
    have hel : ElimList g (v :: post) := elimList_suffix pre (hsplit ▸ he)
    exact hel.1 a b c (hafter a hao ha) (hafter b hbo hb) (hafter c hco hc) hva' hvb' hvc'

end STACS2027
