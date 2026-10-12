module

public import ApproximationHardness.Embed.EmbedSpec
import Lean.Elab.Tactic.Omega

/-! # Reading a chosen rotation from two precomputed local rotations -/

@[expose] public section

namespace STACS2027.Embed

theorem cnext_append_comm {A B : List Nat} {d : Nat}
    (hnd : (A ++ B).Nodup) (hd : d ∈ A ++ B) :
    cnext (B ++ A) d = cnext (A ++ B) d := by
  have hnd' : (B ++ A).Nodup := by
    exact (show (A ++ B).Perm (B ++ A) from List.perm_append_comm).nodup_iff.mp hnd
  have hd' : d ∈ B ++ A := by simpa [List.mem_append, or_comm] using hd
  exact (cyc_unique (cyc_append_comm (cyc_cnext hnd)) hnd' hd').symm

namespace ForestData

/-- Reversing the part order reverses the complete cyclic order at a vertex. -/
theorem rotInvN_choice {F : ForestData} (hF : F.Valid) (β : Nat → Bool)
    {d : Nat} (hd : d < 2 * F.E) :
    rotInvN hF β d = if β (F.rep d) then rotN hF (fun _ => false) d
      else rotInvN hF (fun _ => false) d := by
  have hv := isVertex_rep hF hd
  have hnd := cycOf_nodup hF (β := fun _ => false) hv
  have hm := (mem_cycOf hF (β := fun _ => false) hv).mpr ⟨hd, rfl⟩
  cases hb : β (F.rep d) with
  | false => simp [rotInvN, cycOf, Plan.ord, hb]
  | true =>
    simp only [↓reduceIte]
    by_cases hr : F.IsRoot (F.rep d)
    · by_cases hz : F.zOf (F.rep d) < 2 * F.E
      · simp only [rotInvN, rotN, cycOf, hr, ↓reduceIte, Plan.ord, hb,
          List.map_reverse, hz, List.reverse_append, List.reverse_singleton,
          List.reverse_reverse] at hnd hm ⊢
        exact cnext_append_comm hnd hm
      · simp [rotInvN, rotN, cycOf, hr, Plan.ord, hb, hz, List.map_reverse]
    · simp only [rotInvN, rotN, cycOf, hr, ↓reduceIte, Plan.ord, hb,
        List.map_reverse, List.reverse_cons, List.reverse_reverse] at hnd hm ⊢
      exact cnext_append_comm (A := [F.par (F.rep d)]) hnd hm

end ForestData

end STACS2027.Embed
