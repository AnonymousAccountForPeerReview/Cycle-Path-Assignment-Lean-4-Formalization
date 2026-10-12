module

public import NPHardness.FiniteCycles

/-!
Explicit representatives for cycle edge sets. This removes the need to rely
on an unproved claim about a vertex-order canonicalization convention.
-/

@[expose] public section
namespace STACS2027

theorem SameCycle.refl (c : Cycle) : SameCycle c c := ⟨fun _ h => h, fun _ h => h⟩

theorem SameCycle.symm {c d : Cycle} (h : SameCycle c d) : SameCycle d c := ⟨h.2, h.1⟩

theorem SameCycle.trans {c d e : Cycle} (h : SameCycle c d) (h' : SameCycle d e) :
    SameCycle c e := ⟨fun x hx => h'.1 x (h.1 x hx), fun x hx => h.2 x (h'.2 x hx)⟩

/-- The cycles of `cs` with no earlier cycle having the same edges. -/
def cycleRepresentatives (cs : List Cycle) : List Cycle :=
  cs.eraseDupsBy fun c d => decide (SameCycle c d)

theorem cycleRepresentatives_cons (c : Cycle) (cs : List Cycle) :
    cycleRepresentatives (c :: cs) =
      c :: cycleRepresentatives (cs.filter fun d => !decide (SameCycle d c)) := by
  simp [cycleRepresentatives, List.eraseDupsBy_cons]

theorem cycleRepresentatives_subset (cs : List Cycle) :
    ∀ c ∈ cycleRepresentatives cs, c ∈ cs := by
  cases cs with
  | nil => simp [cycleRepresentatives]
  | cons a cs =>
    rw [cycleRepresentatives_cons]
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · simp
    · have h := cycleRepresentatives_subset (cs.filter fun d => !decide (SameCycle d a)) c hc
      exact List.mem_cons_of_mem a (List.mem_filter.mp h).1
termination_by cs.length
decreasing_by have := List.length_filter_le (fun d => !decide (SameCycle d a)) cs; simp; omega

theorem cycleRepresentatives_pairwise (cs : List Cycle) :
    (cycleRepresentatives cs).Pairwise (fun c d => ¬ SameCycle c d) := by
  cases cs with
  | nil => simp [cycleRepresentatives]
  | cons a cs =>
    rw [cycleRepresentatives_cons]
    apply List.pairwise_cons.mpr
    refine ⟨?_, cycleRepresentatives_pairwise _⟩
    intro c hc hsame
    have h := cycleRepresentatives_subset _ c hc
    have hn := (List.mem_filter.mp h).2
    have ht : decide (SameCycle c a) = true := decide_eq_true hsame.symm
    simp [ht] at hn
termination_by cs.length
decreasing_by have := List.length_filter_le (fun d => !decide (SameCycle d a)) cs; simp; omega

theorem cycleRepresentatives_cover (cs : List Cycle) :
    ∀ c ∈ cs, ∃ d ∈ cycleRepresentatives cs, SameCycle c d := by
  cases cs with
  | nil => simp
  | cons a cs =>
    rw [cycleRepresentatives_cons]
    intro c hc
    by_cases h : SameCycle c a
    · exact ⟨a, by simp, h⟩
    · have hc' : c ∈ cs := by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact False.elim (h (SameCycle.refl c))
        · exact hc
      have hf : c ∈ cs.filter (fun d => !decide (SameCycle d a)) := by simp [hc', h]
      obtain ⟨d, hd, he⟩ := cycleRepresentatives_cover _ c hf
      exact ⟨d, List.mem_cons_of_mem a hd, he⟩
termination_by cs.length
decreasing_by have := List.length_filter_le (fun d => !decide (SameCycle d a)) cs; simp; omega

theorem cycleRepresentatives_nodup (cs : List Cycle) : (cycleRepresentatives cs).Nodup := by
  change (cycleRepresentatives cs).Pairwise (fun c d => c ≠ d)
  exact List.Pairwise.imp (R := fun c d => ¬ SameCycle c d)
    (fun {a b} hn heq => by subst b; exact hn (SameCycle.refl a))
    (cycleRepresentatives_pairwise cs)

end STACS2027
