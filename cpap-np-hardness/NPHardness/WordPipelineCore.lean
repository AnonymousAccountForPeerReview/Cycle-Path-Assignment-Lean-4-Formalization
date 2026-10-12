module

public import NPHardness.WordConstructorSafety
public import NPHardness.LinearPreprocessExtract

/-! Small-step composition infrastructure. Stage-terminal self loops can be
discarded when inlining stages into a deterministic pipeline. No stage is
assigned unit cost: every stage transition is individually simulated. -/

@[expose] public section
namespace STACS2027.WordPipeline

inductive Runs {S : Type} (step : S → S) : Nat → S → S → Prop where
  | refl (s) : Runs step 0 s s
  | next {t s u} : Runs step t (step s) u → Runs step (t+1) s u

theorem Runs.trans {S : Type} {step : S → S} {t u : Nat} {s q r : S}
    (h : Runs step t s q) (g : Runs step u q r) : Runs step (t+u) s r := by
  induction h with
  | refl => simpa using g
  | next h ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Runs.next (ih g)

/-- A stage may spend fewer transitions after terminal stutters are removed.
Every other simulated transition is one actual enclosing-machine transition. -/
theorem Runs.simulate {S T : Type} {small : S → S} {large : T → T} (embed : S → T)
    (hs : ∀ s, embed (small s) = embed s ∨ large (embed s) = embed (small s))
    {t : Nat} {s q : S} (h : Runs small t s q) :
    ∃ u, u ≤ t ∧ Runs large u (embed s) (embed q) := by
  induction h with
  | refl s => exact ⟨0,by omega,Runs.refl _⟩
  | @next t s q h ih =>
    obtain ⟨u,hu,hr⟩ := ih
    rcases hs s with he | he
    · rw [he] at hr
      exact ⟨u,by omega,hr⟩
    · rw [← he] at hr
      exact ⟨u+1,by omega,Runs.next hr⟩

end STACS2027.WordPipeline
