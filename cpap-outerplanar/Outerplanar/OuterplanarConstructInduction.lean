module

public import Outerplanar.OuterplanarConstructHam
public import Outerplanar.OuterplanarConstructGlueSph
public import Outerplanar.TwoConnectedK23Structure
public import Outerplanar.Reach
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Dedup
import Mathlib.Tactic

/-!
# Minor-free graphs have spherical outerplanar embeddings

`sphOuter_of_minorFree`: if `g` has neither a `K₄` nor a `K_{2,3}` minor, every edge list
listing its simple graph (`RepEdges`) has a spherical outerplanar embedding. By strong
induction on the number of vertices (`vset g`):

* a 2-connected graph is a `K₄` (excluded) or has an outerplanar Hamiltonian cycle
  (`twoConnectedK23_structure`), embedded as a polygon (`OuterplanarHam.sphOuter`);
* a graph with at most two vertices is empty or one edge (`sphOuter_single`);
* otherwise it is disconnected or has a cut vertex `c`: it splits into two subgraphs with
  fewer vertices whose only common vertex is (at most) `c` (`split_sphOuter`), minor-free as
  subgraphs (`HasMinor.mono`), and their embeddings are glued (`SphOuter.append_cut`).
-/

@[expose] public section

namespace STACS2027

open Complexity Complexity.Planar PlanarGluing

/-- The vertices of `g`: the ends of its entries written smaller end first. -/
def vset (g : Graph) : Finset ℕ :=
  (((g.filter fun e => decide (e.1 < e.2)).map Prod.fst) ++
    ((g.filter fun e => decide (e.1 < e.2)).map Prod.snd)).toFinset

theorem edge_fst_snd_of_lt {e : Edge} (h : e.1 < e.2) : edge e.1 e.2 = e := by
  unfold edge; ext <;> simp <;> omega

theorem edge_snd_fst_of_lt {e : Edge} (h : e.1 < e.2) : edge e.2 e.1 = e := by
  unfold edge; ext <;> simp <;> omega

theorem mem_vset {g : Graph} {v : ℕ} : v ∈ vset g ↔ IsVertex g v := by
  unfold vset
  simp only [List.mem_toFinset, List.mem_append, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro (⟨e, ⟨he, hlt⟩, rfl⟩ | ⟨e, ⟨he, hlt⟩, rfl⟩)
    · exact ⟨e.2, by omega, by rw [edge_snd_fst_of_lt hlt]; exact he⟩
    · exact ⟨e.1, by omega, by rw [edge_fst_snd_of_lt hlt]; exact he⟩
  · rintro ⟨u, hne, hm⟩
    have hlt : (edge u v).1 < (edge u v).2 := by unfold edge; simp only; omega
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · right
      refine ⟨edge u v, ⟨hm, hlt⟩, ?_⟩
      unfold edge; simp only; omega
    · left
      refine ⟨edge u v, ⟨hm, hlt⟩, ?_⟩
      unfold edge; simp only; omega

theorem adj_filter {g : Graph} {P : Edge → Bool} {a b : ℕ} :
    Adj (g.filter P) a b ↔ Adj g a b ∧ P (edge a b) = true := by
  unfold Adj
  rw [List.mem_filter]
  tauto

/-- **Splitting** at a set `S` of vertices closed under adjacency except through `c`: the
entries meeting `S` and the others form two subgraphs with fewer vertices (missing `v`,
resp. `u`) and at most the common vertex `c`. -/
theorem split_sphOuter {g : Graph} {es : List Edge}
    (IH : ∀ (g' : Graph) (es' : List Edge), (vset g').card < (vset g).card → RepEdges g' es' →
      ¬ HasMinor g' 4 k4 → ¬ HasMinor g' 5 k23 → SphOuter es')
    (hes : RepEdges g es) (h4 : ¬ HasMinor g 4 k4) (h23 : ¬ HasMinor g 5 k23)
    (S : ℕ → Prop) (c u v : ℕ) (hS : ∀ a b, Adj g a b → S a → S b ∨ b = c)
    (hu : S u) (hu' : IsVertex g u) (hv : IsVertex g v) (hvS : ¬ S v) (hvc : v ≠ c) :
    SphOuter es := by
  classical
  let P : Edge → Bool := fun e => decide (S e.1 ∨ S e.2)
  have hP : ∀ a b, P (edge a b) = true ↔ S a ∨ S b := by
    intro a b
    simp only [P, decide_eq_true_eq, edge]
    rcases Nat.le_total a b with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h]; tauto
  have hadj1 : ∀ a b, Adj (g.filter P) a b ↔ Adj g a b ∧ (S a ∨ S b) := by
    intro a b; rw [adj_filter, hP]
  have hadj2 : ∀ a b, Adj (g.filter fun e => !P e) a b ↔ Adj g a b ∧ ¬ S a ∧ ¬ S b := by
    intro a b
    rw [adj_filter, Bool.not_eq_true', ← Bool.not_eq_true, hP]
    tauto
  have hrep1 : RepEdges (g.filter P) (es.filter P) := by
    refine ⟨hes.1.filter _, fun e => ?_⟩
    rw [List.mem_filter, hes.2, hadj1]
    simp only [P, decide_eq_true_eq]
    tauto
  have hrep2 : RepEdges (g.filter fun e => !P e) (es.filter fun e => !P e) := by
    refine ⟨hes.1.filter _, fun e => ?_⟩
    rw [List.mem_filter, hes.2, hadj2]
    simp only [P, Bool.not_eq_true', decide_eq_false_iff_not, not_or]
    tauto
  have hv1 : ∀ w, IsVertex (g.filter P) w → S w ∨ w = c := by
    rintro w ⟨a, ha⟩
    rw [hadj1] at ha
    rcases ha.2 with h | h
    · exact hS a w ha.1 h
    · exact Or.inl h
  have hv2 : ∀ w, IsVertex (g.filter fun e => !P e) w → ¬ S w := by
    rintro w ⟨a, ha⟩
    rw [hadj2] at ha
    exact ha.2.2
  have hsub1 : vset (g.filter P) ⊆ vset g := by
    intro w hw
    rw [mem_vset] at hw ⊢
    obtain ⟨a, ha⟩ := hw
    exact ⟨a, ((hadj1 a w).mp ha).1⟩
  have hsub2 : vset (g.filter fun e => !P e) ⊆ vset g := by
    intro w hw
    rw [mem_vset] at hw ⊢
    obtain ⟨a, ha⟩ := hw
    exact ⟨a, ((hadj2 a w).mp ha).1⟩
  have hc1 : (vset (g.filter P)).card < (vset g).card := by
    apply Finset.card_lt_card
    refine (Finset.ssubset_iff_of_subset hsub1).mpr ⟨v, mem_vset.mpr hv, fun h => ?_⟩
    rcases hv1 v (mem_vset.mp h) with h' | h'
    · exact hvS h'
    · exact hvc h'
  have hc2 : (vset (g.filter fun e => !P e)).card < (vset g).card := by
    apply Finset.card_lt_card
    exact (Finset.ssubset_iff_of_subset hsub2).mpr
      ⟨u, mem_vset.mpr hu', fun h => hv2 u (mem_vset.mp h) hu⟩
  have hS1 := IH _ _ hc1 hrep1
    (fun hm => h4 (HasMinor.mono (fun a b h => ((hadj1 a b).mp h).1) hm))
    (fun hm => h23 (HasMinor.mono (fun a b h => ((hadj1 a b).mp h).1) hm))
  have hS2 := IH _ _ hc2 hrep2
    (fun hm => h4 (HasMinor.mono (fun a b h => ((hadj2 a b).mp h).1) hm))
    (fun hm => h23 (HasMinor.mono (fun a b h => ((hadj2 a b).mp h).1) hm))
  have hcut := hS1.append_cut hS2 c (fun w hw1 hw2 => by
    rw [hrep1.isEnd_iff] at hw1
    rw [hrep2.isEnd_iff] at hw2
    rcases hv1 w hw1 with h | h
    · exact absurd h (hv2 w hw2)
    · exact h)
  exact hcut.perm (List.filter_append_perm P es)

/-- A graph with no three vertices: no edge, or one. -/
theorem small_sphOuter {g : Graph} {es : List Edge} (hes : RepEdges g es)
    (h3 : ¬ ∃ a b c, IsVertex g a ∧ IsVertex g b ∧ IsVertex g c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    SphOuter es := by
  cases es with
  | nil => exact sphOuter_nil
  | cons e rest =>
    have he := hes.adj (List.mem_cons_self)
    have hlt := hes.lt (List.mem_cons_self (a := e) (l := rest))
    have hall : ∀ e' ∈ e :: rest, e' = e := by
      intro e' he'
      have ha' := hes.adj he'
      have hlt' := hes.lt he'
      have hv : ∀ w, IsVertex g w → w = e.1 ∨ w = e.2 := by
        intro w hw
        by_contra hne
        push Not at hne
        exact h3 ⟨e.1, e.2, w, ⟨e.2, he.symm⟩, ⟨e.1, he⟩, hw, by omega, Ne.symm hne.1,
          Ne.symm hne.2⟩
      have h1 := hv e'.1 ⟨e'.2, ha'.symm⟩
      have h2 := hv e'.2 ⟨e'.1, ha'⟩
      ext <;> omega
    have hrest : rest = [] := by
      cases rest with
      | nil => rfl
      | cons e2 rest2 =>
        have h2 := hall e2 (by simp)
        have hnd := hes.1
        rw [List.nodup_cons] at hnd
        exact absurd (h2 ▸ List.mem_cons_self) hnd.1
    subst hrest
    have hS := sphOuter_single (a := e.1) (b := e.2) (by omega)
    simpa using hS

/-- **Minor-free graphs** (no `K₄` and no `K_{2,3}` minor) have spherical outerplanar
embeddings of their simple graphs. -/
theorem sphOuter_of_minorFree : ∀ (n : ℕ) (g : Graph) (es : List Edge), (vset g).card ≤ n →
    RepEdges g es → ¬ HasMinor g 4 k4 → ¬ HasMinor g 5 k23 → SphOuter es := by
  intro n
  induction n with
  | zero =>
    intro g es hn hes _ _
    cases es with
    | nil => exact sphOuter_nil
    | cons e rest =>
      have he := hes.adj (List.mem_cons_self (a := e) (l := rest))
      have : e.2 ∈ vset g := mem_vset.mpr ⟨e.1, he⟩
      have := Finset.card_pos.mpr ⟨_, this⟩
      omega
  | succ n ih =>
    intro g es hn hes h4 h23
    have IH : ∀ (g' : Graph) (es' : List Edge), (vset g').card < (vset g).card →
        RepEdges g' es' → ¬ HasMinor g' 4 k4 → ¬ HasMinor g' 5 k23 → SphOuter es' :=
      fun g' es' hlt => ih g' es' (by omega)
    by_cases hcut : ∃ x, ¬ ConnectedWithin g (fun v => IsVertex g v ∧ v ≠ x)
    · obtain ⟨x, hx⟩ := hcut
      rw [connectedWithin_iff] at hx
      push Not at hx
      obtain ⟨u, v, hu, hv, huv⟩ := hx
      refine split_sphOuter IH hes h4 h23 (Reach g (fun v => IsVertex g v ∧ v ≠ x) u) x u v
        ?_ (.refl hu) hu.1 hv.1 huv hv.2
      intro a b hab ha
      by_cases hb : b = x
      · exact Or.inr hb
      · exact Or.inl (ha.trans (.edge ha.right ⟨⟨a, hab⟩, hb⟩ hab))
    by_cases hconn : ConnectedWithin g (IsVertex g)
    · by_cases h3 : ∃ a b c, IsVertex g a ∧ IsVertex g b ∧ IsVertex g c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c
      · have h2 : TwoConnected g := ⟨h3, hconn, fun x => by
          by_contra hx
          exact hcut ⟨x, hx⟩⟩
        rcases twoConnectedK23_structure g h2 h23 with hk | ⟨ham, hham⟩
        · exact absurd hk.hasMinor h4
        · exact hham.sphOuter hes
      · exact small_sphOuter hes h3
    · rw [connectedWithin_iff] at hconn
      push Not at hconn
      obtain ⟨u, v, hu, hv, huv⟩ := hconn
      have hvu : v ≠ u := by
        rintro rfl
        exact huv (.refl hu)
      refine split_sphOuter IH hes h4 h23 (Reach g (IsVertex g) u) u u v ?_ (.refl hu) hu hv
        huv hvu
      intro a b hab ha
      exact Or.inl (ha.trans (.edge ha.right ⟨a, hab⟩ hab))

end STACS2027
