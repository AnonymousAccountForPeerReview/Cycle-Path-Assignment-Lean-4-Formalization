module

public import Outerplanar.EarAway
public import Outerplanar.OuterplanarCharacterization
import Mathlib.Tactic

@[expose] public section

namespace STACS2027

/-- A closed side of a cut contains a low-degree vertex avoiding the cut and every
vertex outside that side. -/
theorem lowDegree_split {g : Graph}
    (IH : ∀ g' : Graph, (vset g').card < (vset g).card → Outerplanar g' →
      (∃ u, IsVertex g' u) → ∀ z, ∃ u, IsVertex g' u ∧ u ≠ z ∧ LowDegree g' u)
    (hg : Outerplanar g) (S : ℕ → Prop) (cut u v z : ℕ)
    (hS : ∀ a b, Adj g a b → S a → S b ∨ b = cut)
    (hu : S u) (hu' : IsVertex g u) (hv : IsVertex g v)
    (hvS : ¬ S v) (hvc : v ≠ cut) (hzS : ¬ S z) :
    ∃ w, IsVertex g w ∧ w ≠ z ∧ LowDegree g w := by
  classical
  let P : Edge → Bool := fun e => decide (S e.1 ∨ S e.2)
  have hP : ∀ a b, P (edge a b) = true ↔ S a ∨ S b := by
    intro a b
    simp only [P, decide_eq_true_eq, edge]
    rcases Nat.le_total a b with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h]; tauto
  have hadj : ∀ a b, Adj (g.filter P) a b ↔ Adj g a b ∧ (S a ∨ S b) := by
    intro a b; rw [adj_filter, hP]
  have hvertex : ∀ w, IsVertex (g.filter P) w → S w ∨ w = cut := by
    rintro w ⟨a, ha⟩
    rw [hadj] at ha
    rcases ha.2 with h | h
    · exact hS a w ha.1 h
    · exact Or.inl h
  have hsub : vset (g.filter P) ⊆ vset g := by
    intro w hw
    obtain ⟨a, ha⟩ := mem_vset.mp hw
    exact mem_vset.mpr ⟨a, ((hadj a w).mp ha).1⟩
  have hcard : (vset (g.filter P)).card < (vset g).card := by
    apply Finset.card_lt_card
    refine (Finset.ssubset_iff_of_subset hsub).mpr ⟨v, mem_vset.mpr hv, fun h => ?_⟩
    rcases hvertex v (mem_vset.mp h) with h' | h'
    · exact hvS h'
    · exact hvc h'
  have hgu : IsVertex (g.filter P) u := by
    obtain ⟨a, ha⟩ := hu'
    exact ⟨a, (hadj a u).mpr ⟨ha, Or.inr hu⟩⟩
  have hg' : Outerplanar (g.filter P) :=
    ⟨fun hm => hg.1 (HasMinor.mono (fun a b h => ((hadj a b).mp h).1) hm),
      fun hm => hg.2 (HasMinor.mono (fun a b h => ((hadj a b).mp h).1) hm)⟩
  obtain ⟨w, hw, hwcut, hlow⟩ := IH _ hcard hg' ⟨u, hgu⟩ cut
  have hwS : S w := (hvertex w hw).resolve_right hwcut
  refine ⟨w, ?_, fun he => hzS (he ▸ hwS), ?_⟩
  · obtain ⟨a, ha⟩ := hw
    exact ⟨a, ((hadj a w).mp ha).1⟩
  · intro a b c ha hb hc
    exact hlow a b c ((hadj w a).mpr ⟨ha, Or.inl hwS⟩)
      ((hadj w b).mpr ⟨hb, Or.inl hwS⟩) ((hadj w c).mpr ⟨hc, Or.inl hwS⟩)

/-- A graph with at most two vertices has a low-degree vertex avoiding any one label. -/
theorem lowDegree_small {g : Graph} (hne : ∃ u, IsVertex g u)
    (hthree : ¬ ∃ a b c, IsVertex g a ∧ IsVertex g b ∧ IsVertex g c ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c) (z : ℕ) :
    ∃ u, IsVertex g u ∧ u ≠ z ∧ LowDegree g u := by
  obtain ⟨u, hu⟩ := hne
  obtain ⟨v, hvu⟩ := hu
  have hv : IsVertex g v := ⟨u, hvu.symm⟩
  have hall : ∀ w, IsVertex g w → w = u ∨ w = v := by
    intro w hw
    by_contra hn
    push Not at hn
    exact hthree ⟨u, v, w, ⟨v, hvu⟩, hv, hw, hvu.1.symm,
      Ne.symm hn.1, Ne.symm hn.2⟩
  have hlo : ∀ w, w = u ∨ w = v → LowDegree g w := by
    intro w hw a b c ha hb hc
    have hwa := hall a ⟨w, ha⟩
    have hwb := hall b ⟨w, hb⟩
    have hnwa := ha.1
    have hnwb := hb.1
    rcases hw with rfl | rfl <;> rcases hwa with rfl | rfl <;>
      rcases hwb with rfl | rfl <;> tauto
  by_cases huz : u = z
  · exact ⟨v, hv, fun he => hvu.1 (he.trans huz.symm), hlo v (Or.inr rfl)⟩
  · exact ⟨u, ⟨v, hvu⟩, huz, hlo u (Or.inl rfl)⟩

/-- Every nonempty outerplanar simple graph has a degree-two vertex avoiding any one
specified vertex. The proof treats disconnected graphs and cut vertices by induction. -/
theorem outerplanar_lowDegree_away : ∀ n (g : Graph), (vset g).card ≤ n →
    Outerplanar g → (∃ u, IsVertex g u) → ∀ z,
    ∃ u, IsVertex g u ∧ u ≠ z ∧ LowDegree g u := by
  intro n
  induction n with
  | zero =>
    intro g hn _ ⟨u, hu⟩ _
    have hp := Finset.card_pos.mpr ⟨u, mem_vset.mpr hu⟩
    omega
  | succ n ih =>
    intro g hn hg hne z
    have IH : ∀ g' : Graph, (vset g').card < (vset g).card → Outerplanar g' →
        (∃ u, IsVertex g' u) → ∀ z, ∃ u, IsVertex g' u ∧ u ≠ z ∧ LowDegree g' u :=
      fun g' hlt => ih g' (by omega)
    by_cases hcut : ∃ x, ¬ ConnectedWithin g (fun v => IsVertex g v ∧ v ≠ x)
    · obtain ⟨x, hx⟩ := hcut
      rw [connectedWithin_iff] at hx
      push Not at hx
      obtain ⟨u, v, hu, hv, huv⟩ := hx
      let Q := fun w => IsVertex g w ∧ w ≠ x
      have hclose : ∀ r a b, Adj g a b → Reach g Q r a → Reach g Q r b ∨ b = x := by
        intro r a b hab ha
        by_cases hb : b = x
        · exact Or.inr hb
        · exact Or.inl (ha.trans (.edge ha.right ⟨⟨a, hab⟩, hb⟩ hab))
      by_cases huz : Reach g Q u z
      · have hnot : ¬ Reach g Q v z := fun hvz => huv (huz.trans hvz.symm)
        have hvu : ¬ Reach g Q v u := fun h => huv h.symm
        exact lowDegree_split IH hg (Reach g Q v) x v u z (hclose v)
          (.refl hv) hv.1 hu.1 hvu hu.2 hnot
      · exact lowDegree_split IH hg (Reach g Q u) x u v z (hclose u)
          (.refl hu) hu.1 hv.1 huv hv.2 huz
    by_cases hconn : ConnectedWithin g (IsVertex g)
    · by_cases hthree : ∃ a b c, IsVertex g a ∧ IsVertex g b ∧ IsVertex g c ∧
          a ≠ b ∧ a ≠ c ∧ b ≠ c
      · have htwo : TwoConnected g := ⟨hthree, hconn, fun x => by
          by_contra hx
          exact hcut ⟨x, hx⟩⟩
        rcases twoConnectedK23_structure g htwo hg.2 with hk | ⟨K, hK⟩
        · exact False.elim (hg.1 hk.hasMinor)
        · exact hK.ear_away_vertex z
      · exact lowDegree_small hne hthree z
    · rw [connectedWithin_iff] at hconn
      push Not at hconn
      obtain ⟨u, v, hu, hv, huv⟩ := hconn
      have hclose : ∀ r a b, Adj g a b → Reach g (IsVertex g) r a →
          Reach g (IsVertex g) r b ∨ b = r := by
        intro r a b hab ha
        exact Or.inl (ha.trans (.edge ha.right ⟨a, hab⟩ hab))
      have hvu : v ≠ u := by
        intro he; subst v; exact huv (.refl hu)
      by_cases huz : Reach g (IsVertex g) u z
      · have hnot : ¬ Reach g (IsVertex g) v z := fun hvz => huv (huz.trans hvz.symm)
        have hnotu : ¬ Reach g (IsVertex g) v u := fun h => huv h.symm
        exact lowDegree_split IH hg (Reach g (IsVertex g) v) v v u z (hclose v)
          (.refl hv) hv hu hnotu hvu.symm hnot
      · exact lowDegree_split IH hg (Reach g (IsVertex g) u) u u v z (hclose u)
          (.refl hu) hu hv huv hvu huz

end STACS2027

@[expose] public section

namespace STACS2027

/-- Every nonempty vertex set of an arbitrary outerplanar graph has a vertex with at
most two neighbours in that set. Isolated vertices are allowed in the supplied list. -/
theorem outerplanar_degenerate {g : Graph} (hg : Outerplanar g)
    {U : List ℕ} (hne : U ≠ []) : ∃ u ∈ U, AtMostTwo g U u := by
  classical
  let P : Edge → Bool := fun e => decide (e.1 ∈ U ∧ e.2 ∈ U)
  have hP : ∀ a b, P (edge a b) = true ↔ a ∈ U ∧ b ∈ U := by
    intro a b
    simp only [P, decide_eq_true_eq, edge]
    rcases Nat.le_total a b with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h]; tauto
  have hadj : ∀ a b, Adj (g.filter P) a b ↔ Adj g a b ∧ a ∈ U ∧ b ∈ U := by
    intro a b; rw [adj_filter, hP]
  have hg' : Outerplanar (g.filter P) :=
    ⟨fun hm => hg.1 (HasMinor.mono (fun a b h => ((hadj a b).mp h).1) hm),
      fun hm => hg.2 (HasMinor.mono (fun a b h => ((hadj a b).mp h).1) hm)⟩
  by_cases hv : ∃ u, IsVertex (g.filter P) u
  · obtain ⟨u, hu, _, hlow⟩ := outerplanar_lowDegree_away
      (vset (g.filter P)).card (g.filter P) le_rfl hg' hv 0
    obtain ⟨a, ha⟩ := hu
    have hum : u ∈ U := ((hadj a u).mp ha).2.2
    refine ⟨u, hum, ?_⟩
    intro b c d hb hc hd hub huc hud
    exact hlow b c d ((hadj u b).mpr ⟨hub, hum, hb⟩)
      ((hadj u c).mpr ⟨huc, hum, hc⟩) ((hadj u d).mpr ⟨hud, hum, hd⟩)
  · obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil U hne
    refine ⟨u, hu, ?_⟩
    intro a b c ha _ _ hua _ _
    exact False.elim (hv ⟨u, a, ((hadj u a).mpr ⟨hua, hu, ha⟩).symm⟩)

/-- The drawing definition of outerplanarity gives the full degeneracy statement. -/
theorem outerplanarDrawing_degenerate {g : Graph} (hg : OuterplanarDrawing g)
    {U : List ℕ} (hne : U ≠ []) : ∃ u ∈ U, AtMostTwo g U u :=
  outerplanar_degenerate ((outerplanarDrawing_iff_minorFree g).mp hg) hne

/-- One global degree-two elimination order exists for every outerplanar graph, including
disconnected graphs and graphs with cut vertices. -/
theorem outerplanar_eliminationOrder {g : Graph} (hg : OuterplanarDrawing g) :
    ∃ rank, EliminationOrder g rank :=
  eliminationOrder_of_degenerate (fun _ hne _ => outerplanarDrawing_degenerate hg hne)

/-- Deleting vertices or edges preserves the drawing definition of outerplanarity. -/
theorem outerplanarDrawing_subgraph {g g' : Graph} (hg : OuterplanarDrawing g)
    (hsub : ∀ a b, Adj g' a b → Adj g a b) : OuterplanarDrawing g' := by
  have hm := (outerplanarDrawing_iff_minorFree g).mp hg
  exact (outerplanarDrawing_iff_minorFree g').mpr
    ⟨fun h => hm.1 (HasMinor.mono hsub h), fun h => hm.2 (HasMinor.mono hsub h)⟩

end STACS2027
