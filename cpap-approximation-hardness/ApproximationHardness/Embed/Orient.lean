module

public import ApproximationHardness.Embed.ForestSolver
public import ApproximationHardness.Embed.DFSRun
import Lean.Elab.Tactic.Omega

/-!
# The orientation pass

The solver records, for every group it consumes, the identifier of the merged group plus one
(`parA`) and the flip bit (`flpA`). The orientation pass then sets, in order, the orientation of the
merged group of every node in reverse post-order and of every dart:
`o g = o (parA g - 1) xor flpA g` (or `false` if the group was never consumed).

`foldl_upd_spec`: in a fold updating distinct keys, a key whose value depends only on the keys set
before it keeps the value it is given. Hence the orientation pass is consistent with the merges
(`orient_consistent`).
-/

@[expose] public section

namespace STACS2027.Embed

open Complexity Complexity.Planar

theorem foldl_upd_other {α : Type} (κ : α → Nat) (V : (Nat → Bool) → α → Bool) :
    ∀ (L : List α) (o : Nat → Bool) (k : Nat), k ∉ L.map κ →
      (L.foldl (fun o a => upd o (κ a) (V o a)) o) k = o k
  | [], _, _, _ => rfl
  | a :: L, o, k, hk => by
    simp only [List.map_cons, List.mem_cons, not_or] at hk
    rw [List.foldl_cons, foldl_upd_other κ V L _ k hk.2, upd_ne _ _ hk.1]

/-- **Folds over distinct keys.** -/
theorem foldl_upd_spec {α : Type} (κ : α → Nat) (V : (Nat → Bool) → α → Bool) :
    ∀ (L : List α) (o0 : Nat → Bool), (L.map κ).Nodup →
      (∀ i (hi : i < L.length), ∀ o o' : Nat → Bool,
        (∀ k, (k ∉ L.map κ ∨ ∃ j, ∃ hj : j < i, k = κ (L[j]'(by omega))) → o k = o' k) →
        V o L[i] = V o' L[i]) →
      ∀ a ∈ L, (L.foldl (fun o a => upd o (κ a) (V o a)) o0) (κ a) =
        V (L.foldl (fun o a => upd o (κ a) (V o a)) o0) a
  | [], _, _, _, a, ha => by simp at ha
  | a :: t, o0, hnd, hdep, b, hb => by
    rw [List.map_cons] at hnd
    obtain ⟨hn1, hn2⟩ := List.nodup_cons.mp hnd
    rw [List.foldl_cons]
    have IH := foldl_upd_spec κ V t (upd o0 (κ a) (V o0 a)) hn2 (by
      intro i hi o o' hoo
      have := hdep (i + 1) (by simp; omega) o o' (by
        intro k hk
        apply hoo k
        rcases hk with hk | ⟨j, hj, rfl⟩
        · left; simp only [List.map_cons, List.mem_cons, not_or] at hk; exact hk.2
        · cases j with
          | zero => left; exact hn1
          | succ j => right; exact ⟨j, by omega, rfl⟩)
      simpa using this)
    rcases List.mem_cons.mp hb with rfl | hb
    · rw [foldl_upd_other κ V t _ _ hn1, upd_same]
      symm
      apply hdep 0 (by simp)
      intro k hk
      rcases hk with hk | ⟨j, hj, _⟩
      · simp only [List.map_cons, List.mem_cons, not_or] at hk
        rw [foldl_upd_other κ V t _ _ hk.2, upd_ne _ _ hk.1]
      · omega
    · exact IH b hb

namespace ForestData

variable {F : ForestData} (hF : F.Valid)

/-- The orientation given to a group from the arrays of the solver. -/
def oval (parA flpA : Nat → Nat) (o : Nat → Bool) (g : Nat) : Bool :=
  if parA g = 0 then false else (o (parA g - 1) ^^ decide (flpA g = 1))

/-- The keys of the orientation pass: merged groups in reverse post-order, then the darts. -/
def okey (F : ForestData) : Sum Nat Nat → Nat
  | .inl v => F.gid v
  | .inr e => e

/-- The items of the orientation pass. -/
def oitems (F : ForestData) (post : List Nat) : List (Sum Nat Nat) :=
  post.reverse.map Sum.inl ++ (List.range (2 * F.E)).map Sum.inr

/-- **The orientation pass.** -/
def orient (F : ForestData) (post : List Nat) (parA flpA : Nat → Nat) : Nat → Bool :=
  (oitems F post).foldl (fun o a => upd o (okey F a) (oval parA flpA o (okey F a))) (fun _ => false)

/-- The solver arrays record the merges. -/
structure Records (F : ForestData) (hF : F.Valid) (parA flpA : Nat → Nat) : Prop where
  par : ∀ v x, x ∈ (F.sol hF).consAt v → parA x.1 = F.gid v + 1
  flp : ∀ v x, x ∈ (F.sol hF).consAt v → flpA x.1 = if x.2 then 1 else 0
  zero : ∀ g, parA g ≠ 0 → ∃ v x, x ∈ (F.sol hF).consAt v ∧ x.1 = g

/-- The post-order: every plan node with a merge, every plan node below it before it. -/
structure PostOrder (F : ForestData) (hF : F.Valid) (post : List Nat) : Prop where
  nodup : post.Nodup
  lt : ∀ v ∈ post, v < 4 * F.E
  mem : ∀ v x, x ∈ (F.sol hF).consAt v → v ∈ post
  below : ∀ v w, (F.plan hF).Below v w → w ≠ v → v ∈ post → w ∈ post ∧ Before post w v

theorem oitems_getElem_inl (F : ForestData) {post : List Nat} {k : Nat} (hk : k < (oitems F post).length)
    (hk' : k < post.length) : (oitems F post)[k] = Sum.inl (post.reverse[k]'(by simpa using hk')) := by
  have h : (oitems F post)[k]? = some (Sum.inl (post.reverse[k]'(by simpa using hk'))) := by
    unfold oitems
    rw [List.getElem?_append_left (by simpa using hk'), List.getElem?_map,
      List.getElem?_eq_getElem (by simpa using hk')]
    rfl
  rw [List.getElem?_eq_getElem hk] at h
  exact Option.some.inj h

theorem idx_lt_of_before {l : List Nat} (hnd : l.Nodup) {i j : Nat} (hi : i < l.length) (hj : j < l.length)
    (h : Before l l[i] l[j]) : i < j := by
  obtain ⟨i', j', hij, hj', h1, h2⟩ := before_iff_idx.mp h
  have e1 : i' = i := DG.getD_inj hnd (by omega) hi (by rw [DG.getD_of_lt, DG.getD_of_lt]; exact h1)
  have e2 : j' = j := DG.getD_inj hnd hj' hj (by rw [DG.getD_of_lt, DG.getD_of_lt]; exact h2)
  omega

include hF

theorem consumed_gid_or_dart {v : Nat} {x : Nat × Bool} (hx : x ∈ (F.sol hF).consAt v) :
    (∃ w, (F.plan hF).Below v w ∧ w ≠ v ∧ x.1 = F.gid w) ∨ x.1 < 2 * F.E := by
  rcases (tree hF).consumed_below (good hF) hx with h | ⟨w, _, hw⟩
  · exact Or.inl h
  · right
    exact lt_of_mem_D hF ((Plan.mem_D _).mpr ⟨_, hw, by simp [Plan.ID, Plan.partW]⟩)

/-- **The orientation pass is consistent with the merges.** -/
theorem orient_consistent {post : List Nat} {parA flpA : Nat → Nat} (hR : Records F hF parA flpA)
    (hP : PostOrder F hF post) : (F.sol hF).Consistent (orient F post parA flpA) := by
  have hkeys : ((oitems F post).map (okey F)).Nodup := by
    unfold oitems
    rw [List.map_append, List.map_map, List.map_map]
    refine List.nodup_append.mpr ⟨?_, ?_, ?_⟩
    · exact nodup_map_of_injOn' _ ((List.reverse_perm _).nodup_iff.mpr hP.nodup) (fun a _ b _ h => by
        simp only [Function.comp, okey, gid] at h; omega)
    · exact nodup_map_of_injOn' _ List.nodup_range (fun a _ b _ h => by simpa [okey] using h)
    · intro a ha b hb e
      simp only [List.mem_map, Function.comp, okey] at ha hb
      obtain ⟨v, -, rfl⟩ := ha
      obtain ⟨d, hd, rfl⟩ := hb
      simp [gid] at e
      have := List.mem_range.mp hd
      omega
  -- the dependencies
  have hdep : ∀ i (hi : i < (oitems F post).length), ∀ o o' : Nat → Bool,
      (∀ k, (k ∉ (oitems F post).map (okey F) ∨ ∃ j, ∃ hj : j < i,
        k = okey F ((oitems F post)[j]'(by omega))) → o k = o' k) →
      oval parA flpA o (okey F (oitems F post)[i]) = oval parA flpA o' (okey F (oitems F post)[i]) := by
    intro i hi o o' hoo
    unfold oval
    split
    · rfl
    · rename_i hne
      obtain ⟨v, x, hx, hxe⟩ := hR.zero _ hne
      have hpar := hR.par v x hx
      rw [hxe] at hpar
      rw [hpar, Nat.add_sub_cancel]
      congr 1
      apply hoo
      right
      have hvpost := hP.mem v x hx
      obtain ⟨kv, hkv, hkve⟩ := List.getElem_of_mem (List.mem_reverse.mpr hvpost)
      have hkvL : kv < (oitems F post).length := by unfold oitems; simp at hkv ⊢; omega
      have hitem : (oitems F post)[kv]'hkvL = Sum.inl v := by
        rw [oitems_getElem_inl F hkvL (by simpa using hkv), hkve]
      refine ⟨kv, ?_, by rw [hitem]; rfl⟩
      -- the merged group comes before the consumed one
      by_cases hin : i < post.length
      · have hitemi : (oitems F post)[i] = Sum.inl (post.reverse[i]'(by simpa using hin)) :=
          oitems_getElem_inl F hi hin
        rw [hitemi] at hxe
        simp only [okey] at hxe
        rcases consumed_gid_or_dart hF hx with ⟨w, hbw, hwv, hxw⟩ | hxd
        · rw [hxe] at hxw
          have hw' : post.reverse[i]'(by simpa using hin) = w := by
            simp only [gid] at hxw; omega
          obtain ⟨_, hbef⟩ := hP.below v w hbw hwv hvpost
          have hnd := (List.reverse_perm _).nodup_iff.mpr hP.nodup
          have hb2 : Before post.reverse v w := before_reverse_iff.mpr hbef
          rw [← hkve, ← hw'] at hb2
          exact idx_lt_of_before hnd hkv (by simpa using hin) hb2
        · rw [hxe] at hxd; simp only [gid] at hxd; omega
      · simp at hkv; omega
  intro v x hx
  have hmem : ∃ a ∈ oitems F post, okey F a = x.1 := by
    rcases consumed_gid_or_dart hF hx with ⟨w, hbw, hwv, hxw⟩ | hxd
    · have hv := hP.mem v x hx
      exact ⟨Sum.inl w, by
        unfold oitems; exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_reverse.mpr
          (hP.below v w hbw hwv hv).1)), by rw [hxw]; rfl⟩
    · exact ⟨Sum.inr x.1, by unfold oitems; exact List.mem_append_right _ (List.mem_map_of_mem
        (List.mem_range.mpr hxd)), rfl⟩
  obtain ⟨a, ha, hae⟩ := hmem
  have := foldl_upd_spec (okey F) (fun o a => oval parA flpA o (okey F a)) (oitems F post) (fun _ => false)
    hkeys hdep a ha
  unfold orient
  rw [hae] at this
  rw [this]
  unfold oval
  rw [hR.par v x hx, hR.flp v x hx]
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, Nat.add_sub_cancel]
  cases x.2 <;> simp <;> rfl

end ForestData

end STACS2027.Embed
