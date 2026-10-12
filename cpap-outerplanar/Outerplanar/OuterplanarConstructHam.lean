module

public import Outerplanar.OuterplanarConstructPoly
public import Outerplanar.OuterplanarSym
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# The polygon embedding of an outerplanar Hamiltonian cycle

For an edge list `es` listing the simple graph of `g` (`RepEdges`, `OuterplanarBasic`):

`OuterplanarHam.sphOuter`: if `g` has a Hamiltonian cycle `ham` with respect to which no two
edges cross (`OuterplanarHam`, the 2-connected case of Lemma 19), then the edge list of `g`
has a spherical outerplanar embedding: renaming every vertex by its position on `ham` gives a
polygon with non-crossing chords (`PolyHyp`), embedded by `PolyHyp.sphOuter`, and the
positions are renamed back (`SphOuter.map_injOn`). Also `sphOuter_single`: a single edge.
-/

@[expose] public section

namespace STACS2027

open Complexity Complexity.Planar PlanarGluing

namespace RepEdges

variable {g : Graph} {es : List Edge} (h : RepEdges g es)
include h

theorem lt {e : Edge} (he : e ∈ es) : e.1 < e.2 := ((h.2 e).mp he).1

theorem adj {e : Edge} (he : e ∈ es) : Adj g e.1 e.2 := ((h.2 e).mp he).2

theorem mem_of_adj {u v : ℕ} (huv : Adj g u v) : (min u v, max u v) ∈ es := by
  apply (h.2 _).mpr
  have hne := huv.1
  refine ⟨by simp only; omega, ?_⟩
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · rw [min_eq_left hlt.le, max_eq_right hlt.le]; exact huv
  · rw [min_eq_right hlt.le, max_eq_left hlt.le]; exact huv.symm

theorem isEnd_iff {v : ℕ} : (∃ e ∈ es, v = e.1 ∨ v = e.2) ↔ IsVertex g v := by
  constructor
  · rintro ⟨e, he, rfl | rfl⟩
    · exact ⟨e.2, (h.adj he).symm⟩
    · exact ⟨e.1, h.adj he⟩
  · rintro ⟨u, huv⟩
    refine ⟨_, h.mem_of_adj huv, ?_⟩
    simp only
    omega

end RepEdges

/-- **The 2-connected case.** A graph with an outerplanar Hamiltonian cycle has a spherical
outerplanar embedding of its simple graph. -/
theorem OuterplanarHam.sphOuter {g : Graph} {ham : List ℕ} {es : List Edge}
    (h : OuterplanarHam g ham) (hes : RepEdges g es) : SphOuter es := by
  obtain ⟨h3, hnd, ⟨hcyc, hwrap⟩, hnc⟩ := h.oham
  have hmem : ∀ v, IsVertex g v → v ∈ ham := h.2.1
  have hends : ∀ e ∈ es, e.1 ∈ ham ∧ e.2 ∈ ham := fun e he =>
    ⟨hmem _ ⟨e.2, (hes.adj he).symm⟩, hmem _ ⟨e.1, hes.adj he⟩⟩
  have hgp : ∀ v ∈ ham, ham.getD (ham.idxOf v) 0 = v := by
    intro v hv
    rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hv)]
    exact List.getElem_idxOf _
  have hpg : ∀ p, p < ham.length → ham.idxOf (ham.getD p 0) = p := by
    intro p hp
    rw [List.getD_eq_getElem _ _ hp]
    exact hnd.idxOf_getElem p hp
  have hposlt : ∀ v ∈ ham, ham.idxOf v < ham.length := fun v hv =>
    List.idxOf_lt_length_of_mem hv
  have hposinj : ∀ u ∈ ham, ∀ v ∈ ham, ham.idxOf u = ham.idxOf v → u = v := by
    intro u hu v hv he
    rw [← hgp u hu, ← hgp v hv, he]
  set es' := es.map fun e => (ham.idxOf e.1, ham.idxOf e.2) with hes'
  have hadj : ∀ p q, p < ham.length → q < ham.length →
      (Adjs es' p q ↔ Adj g (ham.getD p 0) (ham.getD q 0)) := by
    intro p q hp hq
    rw [adjs_iff]
    constructor
    · rintro (hm | hm)
      · obtain ⟨e, he, hee⟩ := List.mem_map.mp hm
        simp only [Prod.mk.injEq] at hee
        rw [← hee.1, ← hee.2, hgp _ (hends e he).1, hgp _ (hends e he).2]
        exact hes.adj he
      · obtain ⟨e, he, hee⟩ := List.mem_map.mp hm
        simp only [Prod.mk.injEq] at hee
        rw [← hee.1, ← hee.2, hgp _ (hends e he).1, hgp _ (hends e he).2]
        exact (hes.adj he).symm
    · intro ha
      have hm := hes.mem_of_adj ha
      have hu : ham.getD p 0 ∈ ham := by
        rw [List.getD_eq_getElem _ _ hp]; exact List.getElem_mem hp
      have hv : ham.getD q 0 ∈ ham := by
        rw [List.getD_eq_getElem _ _ hq]; exact List.getElem_mem hq
      rcases Nat.lt_or_ge (ham.getD p 0) (ham.getD q 0) with hlt | hge
      · left
        refine List.mem_map.mpr ⟨_, hm, ?_⟩
        rw [min_eq_left hlt.le, max_eq_right hlt.le, hpg p hp, hpg q hq]
      · right
        refine List.mem_map.mpr ⟨_, hm, ?_⟩
        rw [min_eq_right hge, max_eq_left hge, hpg p hp, hpg q hq]
  have hlt' : ∀ e ∈ es', e.1 < ham.length ∧ e.2 < ham.length := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    exact ⟨hposlt _ (hends e0 he0).1, hposlt _ (hends e0 he0).2⟩
  have hP : PolyHyp es' ham.length := by
    refine ⟨by omega, hlt', ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
      intro heq
      have := hposinj _ (hends e0 he0).1 _ (hends e0 he0).2 heq
      have := hes.lt he0
      omega
    · intro i j hi hj hij
      have hi' : i < es.length := by simpa [es'] using hi
      have hj' : j < es.length := by simpa [es'] using hj
      have gi : es'.getD i (0, 0) = (ham.idxOf es[i].1, ham.idxOf es[i].2) := by
        rw [List.getD_eq_getElem _ _ hi]; simp [es']
      have gj : es'.getD j (0, 0) = (ham.idxOf es[j].1, ham.idxOf es[j].2) := by
        rw [List.getD_eq_getElem _ _ hj]; simp [es']
      rw [gi, gj] at hij
      have hei := hends _ (List.getElem_mem hi')
      have hej := hends _ (List.getElem_mem hj')
      have hli := hes.lt (List.getElem_mem hi')
      have hlj := hes.lt (List.getElem_mem hj')
      simp only [Prod.mk.injEq] at hij
      rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have e1 := hposinj _ hei.1 _ hej.1 h1
        have e2 := hposinj _ hei.2 _ hej.2 h2
        have : es[i] = es[j] := Prod.ext e1 e2
        exact (hes.1.getElem_inj_iff).mp this
      · have e1 := hposinj _ hei.1 _ hej.2 h1
        have e2 := hposinj _ hei.2 _ hej.1 h2
        omega
    · intro i hi
      exact (hadj i (i + 1) (by omega) hi).mpr (hcyc i hi)
    · exact (hadj 0 (ham.length - 1) (by omega) (by omega)).mpr hwrap.symm
    · intro a b c d hab hbc hcd ⟨hac, hbd⟩
      have hd : d < ham.length := by
        rcases (adjs_iff es' b d).mp hbd with hm | hm
        · exact (hlt' _ hm).2
        · exact (hlt' _ hm).1
      exact hnc a b c d hab hbc hcd hd ⟨(hadj a c (by omega) (by omega)).mp hac,
        (hadj b d (by omega) hd).mp hbd⟩
  have hS := hP.sphOuter.map_injOn (fun i => ham.getD i 0) (by
    intro p q hp hq he
    have hp' : p < ham.length := by
      obtain ⟨e, he', rfl | rfl⟩ := hp
      · exact (hlt' e he').1
      · exact (hlt' e he').2
    have hq' : q < ham.length := by
      obtain ⟨e, he', rfl | rfl⟩ := hq
      · exact (hlt' e he').1
      · exact (hlt' e he').2
    rw [← hpg p hp', ← hpg q hq', he])
  have heq : (es'.map fun e => (ham.getD e.1 0, ham.getD e.2 0)) = es := by
    rw [hes', List.map_map]
    conv => rhs; rw [← List.map_id es]
    apply List.map_congr_left
    intro e he
    simp only [Function.comp_apply, id]
    rw [hgp _ (hends e he).1, hgp _ (hends e he).2]
  rw [heq] at hS
  exact hS

/-- The edge `(0, 1)` is a polygon with two vertices. -/
theorem polyHyp_single : PolyHyp [(0, 1)] 2 := by
  have hadj : Adjs [(0, 1)] 0 1 := (adjs_iff _ _ _).mpr (Or.inl (by simp))
  refine ⟨le_refl _, fun e he => by simp at he; subst he; simp, ⟨?_, ?_⟩, ?_, hadj, ?_⟩
  · intro e he; simp at he; subst he; simp
  · intro i j hi hj _; simp at hi hj; omega
  · intro i hi; rw [show i = 0 by omega]; exact hadj
  · intro a b c d hab hbc hcd ⟨hac, _⟩
    rcases (adjs_iff _ _ _).mp hac with hm | hm <;> simp at hm <;> omega

/-- **A single edge.** -/
theorem sphOuter_single {a b : ℕ} (hab : a ≠ b) : SphOuter [(a, b)] := by
  have h := polyHyp_single.sphOuter.map_injOn (fun i => if i = 0 then a else b) (by
    intro p q hp hq he
    obtain ⟨e, he1, hpe⟩ := hp
    obtain ⟨e', he2, hqe⟩ := hq
    simp at he1 he2
    subst he1 he2
    rcases hpe with rfl | rfl <;> rcases hqe with rfl | rfl <;> simp_all)
  simpa using h

end STACS2027
