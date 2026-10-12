module

public import ApproximationHardness.Embed.SM
public import Mathlib.Data.List.Chain
import Lean.Elab.Tactic.Omega

/-!
# Linked classes used by the embedding solver

A nonzero pointer stores a dart identifier plus one. Empty classes have head zero;
their unused tail is unconstrained. The final successor of a class is unconstrained,
so its tail can be joined to the head of another disjoint class in constant time.
-/

@[expose] public section

namespace STACS2027.Embed

/-- An array represents the listed class through its head, tail, and successor pointers. -/
structure Linked (nx : Nat → Nat) (h t : Nat) (l : List Nat) : Prop where
  head : h = (l.head?.map (· + 1)).getD 0
  tail : ∀ a, l.getLast? = some a → t = a + 1
  nodup : l.Nodup
  links : l.IsChain (fun a b => nx a = b + 1)

namespace Linked

theorem nil (nx : Nat → Nat) (t : Nat) : Linked nx 0 t [] :=
  ⟨rfl, by simp, List.nodup_nil, List.IsChain.nil⟩

theorem singleton (nx : Nat → Nat) (a : Nat) : Linked nx (a + 1) (a + 1) [a] :=
  ⟨rfl, by simp, by simp, List.IsChain.singleton _⟩

theorem head_zero_iff {nx : Nat → Nat} {h t : Nat} {l : List Nat}
    (H : Linked nx h t l) : h = 0 ↔ l = [] := by
  rw [H.head]
  cases l <;> simp

theorem head_some_iff {nx : Nat → Nat} {h t a : Nat} {l : List Nat}
    (H : Linked nx h t l) : h = a + 1 ↔ l.head? = some a := by
  rw [H.head]
  cases l <;> simp

/-- Removing a class head uses its successor, except at the tail where the new head is zero. -/
theorem pop {nx : Nat → Nat} {h t a : Nat} {rest : List Nat}
    (H : Linked nx h t (a :: rest)) :
    Linked nx (if h = t then 0 else nx a) t rest := by
  have hh : h = a + 1 := H.head
  cases rest with
  | nil =>
    have ht : t = a + 1 := H.tail a rfl
    simpa [hh, ht] using nil nx t
  | cons b rest =>
    have hc := (List.isChain_cons_cons.mp H.links).1
    have hnd := List.nodup_cons.mp H.nodup
    have hne : h ≠ t := by
      intro he
      let z := (b :: rest).getLast (by simp)
      have hz : (b :: rest).getLast? = some z := List.getLast?_eq_some_getLast (by simp)
      have htz := H.tail z (by simpa using hz)
      have haz : a = z := by omega
      exact hnd.1 (haz ▸ List.mem_of_getLast? hz)
    refine ⟨by simp [hne, hc], ?_, hnd.2, H.links.tail⟩
    intro z hz
    exact H.tail z (by simpa using hz)

/-- Updating cells outside a class preserves its representation. -/
theorem frame {nx ny : Nat → Nat} {h t : Nat} {l : List Nat}
    (H : Linked nx h t l) (he : ∀ a ∈ l, ny a = nx a) : Linked ny h t l :=
  ⟨H.head, H.tail, H.nodup, H.links.imp_of_mem_imp (fun a b ha _ hab => by rw [he a ha]; exact hab)⟩

/-- A class remains represented after its unused final successor is changed. -/
theorem update_tail_links (nx : Nat → Nat) (v : Nat) :
    ∀ (l : List Nat) (a : Nat), l.Nodup → l.IsChain (fun x y => nx x = y + 1) →
      l.getLast? = some a → l.IsChain (fun x y => upd nx a v x = y + 1)
  | [], _, _, _, hl => by simp at hl
  | [x], _, _, _, _ => List.IsChain.singleton _
  | x :: y :: rest, a, hnd, hc, hl => by
    have hlast : (y :: rest).getLast? = some a := by simpa using hl
    have ham : a ∈ y :: rest := List.mem_of_getLast? hlast
    have hxa : x ≠ a := by
      intro he
      exact (List.nodup_cons.mp hnd).1 (he ▸ ham)
    rw [List.isChain_cons_cons] at hc ⊢
    refine ⟨?_, update_tail_links nx v (y :: rest) a (List.nodup_cons.mp hnd).2 hc.2 hlast⟩
    rw [upd_ne _ _ hxa]
    exact hc.1

/-- The constant-time concatenation operation correctly joins disjoint linked classes. -/
theorem append {nx : Nat → Nat} {h₁ t₁ h₂ t₂ : Nat} {A B : List Nat}
    (HA : Linked nx h₁ t₁ A) (HB : Linked nx h₂ t₂ B)
    (hd : ∀ a ∈ A, ∀ b ∈ B, a ≠ b) :
    Linked (appL nx h₁ t₁ h₂ t₂).2.2 (appL nx h₁ t₁ h₂ t₂).1
      (appL nx h₁ t₁ h₂ t₂).2.1 (A ++ B) := by
  cases A with
  | nil =>
    have hh : h₁ = 0 := HA.head
    simpa [appL, hh] using HB
  | cons x A =>
    have hh₁ : h₁ = x + 1 := HA.head
    cases B with
    | nil =>
      have hh₂ : h₂ = 0 := HB.head
      simpa [appL, hh₁, hh₂] using HA
    | cons y B =>
      have hh₂ : h₂ = y + 1 := HB.head
      let a := (x :: A).getLast (by simp)
      have hla : (x :: A).getLast? = some a := List.getLast?_eq_some_getLast (by simp)
      have hta : t₁ = a + 1 := HA.tail a hla
      have ham : a ∈ x :: A := List.mem_of_getLast? hla
      have hB : Linked (upd nx a (y + 1)) h₂ t₂ (y :: B) :=
        HB.frame fun b hb => upd_ne _ _ (Ne.symm (hd a ham b hb))
      have hlinksA := update_tail_links nx (y + 1) (x :: A) a HA.nodup HA.links hla
      simp only [appL, hh₁, hh₂, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
        ite_false, hta, Nat.add_sub_cancel]
      refine ⟨by simp, ?_, List.nodup_append.mpr ⟨HA.nodup, HB.nodup, hd⟩, ?_⟩
      · intro b hl
        rw [List.getLast?_append,
          List.getLast?_eq_some_getLast (l := y :: B) (by simp)] at hl
        simp only [Option.some_or, Option.some.injEq] at hl
        exact HB.tail b (by rw [List.getLast?_eq_some_getLast (by simp), hl])
      · apply List.IsChain.append hlinksA hB.links
        intro b hb c hc
        have hb' : b = a := by
          have hab : a = b := by simpa [hla] using hb
          exact hab.symm
        have hc' : c = y := by
          have hyc : y = c := by simpa using hc
          exact hyc.symm
        rw [hb', hc']
        exact upd_same nx a (y + 1)

/-- Joining a class does not alter any disjoint class. -/
theorem append_frame {nx : Nat → Nat} {h₁ t₁ h₂ t₂ h t : Nat} {A C : List Nat}
    (HA : Linked nx h₁ t₁ A) (HC : Linked nx h t C)
    (hd : ∀ a ∈ A, ∀ c ∈ C, a ≠ c) :
    Linked (appL nx h₁ t₁ h₂ t₂).2.2 h t C := by
  cases A with
  | nil =>
    have hh : h₁ = 0 := HA.head
    simpa [appL, hh] using HC
  | cons a A =>
    have hh : h₁ = a + 1 := HA.head
    by_cases h₂zero : h₂ = 0
    · simpa [appL, hh, h₂zero] using HC
    · let z := (a :: A).getLast (by simp)
      have hz : (a :: A).getLast? = some z := List.getLast?_eq_some_getLast (by simp)
      have htz := HA.tail z hz
      have hzm := List.mem_of_getLast? hz
      have H := HC.frame fun c hc => upd_ne nx h₂ (Ne.symm (hd z hzm c hc))
      simpa [appL, hh, h₂zero, htz] using H

/-- The append operation writes only the final successor of its first class. -/
theorem append_cell_frame {nx : Nat → Nat} {h₁ t₁ h₂ t₂ e : Nat} {A : List Nat}
    (HA : Linked nx h₁ t₁ A) (he : e ∉ A) :
    (appL nx h₁ t₁ h₂ t₂).2.2 e = nx e := by
  cases A with
  | nil =>
    have hh : h₁ = 0 := HA.head
    simp [appL, hh]
  | cons a A =>
    have hh : h₁ = a + 1 := HA.head
    by_cases hz : h₂ = 0
    · simp [appL, hh, hz]
    · let z := (a :: A).getLast (by simp)
      have hl : (a :: A).getLast? = some z := List.getLast?_eq_some_getLast (by simp)
      have ht : t₁ = z + 1 := HA.tail z hl
      have hne : e ≠ z := fun h => he (h ▸ List.mem_of_getLast? hl)
      simp [appL, hh, hz, ht, upd_ne _ _ hne]

/-- Two disjoint accumulated classes can be extended while sharing one successor array. -/
theorem double_append {nx : Nat → Nat} {ah at' bh bt uh ut vh vt : Nat}
    {A B U V : List Nat}
    (HA : Linked nx ah at' A) (HB : Linked nx bh bt B)
    (HU : Linked nx uh ut U) (HV : Linked nx vh vt V)
    (hAU : ∀ a ∈ A, ∀ u ∈ U, a ≠ u)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a ≠ b)
    (hAV : ∀ a ∈ A, ∀ v ∈ V, a ≠ v)
    (hBV : ∀ b ∈ B, ∀ v ∈ V, b ≠ v)
    (hBU : ∀ b ∈ B, ∀ u ∈ U, b ≠ u) :
    let r := appL nx ah at' uh ut
    let s := appL r.2.2 bh bt vh vt
    Linked s.2.2 r.1 r.2.1 (A ++ U) ∧ Linked s.2.2 s.1 s.2.1 (B ++ V) := by
  dsimp only
  have HAU := append HA HU hAU
  have HB' := append_frame (h₂ := uh) (t₂ := ut) HA HB hAB
  have HV' := append_frame (h₂ := uh) (t₂ := ut) HA HV hAV
  have HBV := append HB' HV' hBV
  refine ⟨append_frame HB' HAU ?_, HBV⟩
  intro b hb x hx
  rcases List.mem_append.mp hx with ha | hu
  · exact Ne.symm (hAB x ha b hb)
  · exact hBU b hb x hu

end Linked

namespace Sol

variable (S : Sol)

/-- The array head exposes exactly the class's largest stored key. -/
theorem khM_linked {nx : Nat → Nat} {h t : Nat} {l : List Nat}
    (H : Linked nx h t l) : S.khM h = S.kh l := by
  rw [H.head]
  cases l with
  | nil => rfl
  | cons a rest => simp [khM, kh]

/-- The two linked classes of an active group. -/
structure GroupRep (m : SMem) (g : Grp) : Prop where
  positive : Linked m.nx (m.ph g.id) (m.pt g.id) g.P
  negative : Linked m.nx (m.mh g.id) (m.mt g.id) g.M

/-- The array comparison used by the solver equals the abstract group's top-key comparison. -/
theorem gtopM_group {m : SMem} {g : Grp} (H : GroupRep m g) :
    S.gtopM m g.id = S.gtop g := by
  unfold gtopM gtop
  rw [khM_linked S H.positive, khM_linked S H.negative]

end Sol

end STACS2027.Embed
