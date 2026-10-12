module

public import NPHardness.PlanarAssemblyDarts

/-!
The assembled multigraph keeps two copies of every matched attachment edge.
This module counts their actual two-dart faces exactly, and separates these
faces from all remaining face orbits. No edge copy is deleted or deduplicated.
-/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.Planar

namespace PortPairing
variable {n : Nat} {G : Hypermap n} (P : PortPairing G)

theorem pair_injective {a b : Fin n} (h : P.pair a = P.pair b) : a=b := by
  have := congrArg P.pair h
  simpa only [P.pair_pair] using this

theorem iterate_marked_cases (k : Nat) {d : Fin n} (hd : P.marked d = true) :
    iterate P.assembled.face k d = d ∨ iterate P.assembled.face k d = P.pair d := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    rw [iterate_succ']
    rcases ih with h | h
    · exact Or.inr (by rw [h,P.assembled_face_marked hd])
    · exact Or.inl (by rw [h,P.assembled_face_marked (by rw [P.pair_marked,hd]),P.pair_pair])

theorem marked_cycleMin {d : Fin n} (hd : P.marked d = true) :
    CycleMin P.assembled.face d = true ↔ d.val ≤ (P.pair d).val := by
  have hn : 1<n := by
    have hp := (P.pair d).isLt
    have hdl := d.isLt
    apply Classical.byContradiction
    intro h
    have he : P.pair d = d := Fin.ext (by omega)
    exact P.pair_ne d hd he
  simp only [CycleMin,List.all_eq_true,List.mem_range,Nat.ble_eq]
  constructor
  · intro h
    have h1 := h 1 hn
    change d.val ≤ (P.assembled.face d).val at h1
    rwa [P.assembled_face_marked hd] at h1
  · intro h k _
    rcases P.iterate_marked_cases k hd with hk | hk
    · rw [hk]; exact Nat.le_refl _
    · rw [hk]; exact h

/-- One representative for each matched pair of marked darts. -/
def digonRoot (d : Fin n) : Bool := P.marked d && decide (d.val < (P.pair d).val)

def digonCount : Nat := (List.finRange n).countP P.digonRoot

theorem marked_cycleMin_eq (d : Fin n) :
    (CycleMin P.assembled.face d && P.marked d) = P.digonRoot d := by
  cases hd : P.marked d
  · simp [digonRoot,hd]
  · have hne : d.val ≠ (P.pair d).val := by
      intro he
      exact P.pair_ne d hd (Fin.ext he.symm)
    have he : CycleMin P.assembled.face d = true ↔ decide (d.val < (P.pair d).val) = true := by
      rw [P.marked_cycleMin hd,decide_eq_true_eq]
      omega
    simp only [digonRoot,hd,Bool.and_true,Bool.true_and]
    exact Bool.eq_iff_iff.mpr he

theorem countP_split {α : Type} (p q : α → Bool) (xs : List α) :
    xs.countP p = xs.countP (fun x => p x && q x) + xs.countP (fun x => p x && !q x) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases hp : p a <;> cases hq : q a <;> simp [hp,hq,ih] <;> omega

/-- Every marked pair contributes one face. -/
theorem digonCount_twice : 2*P.digonCount = (List.finRange n).countP P.marked := by
  let roots := List.finRange n
  have hp : (roots.map P.pair).Perm roots := by
    apply (List.perm_ext_iff_of_nodup
      (nodup_map_of_injOn' P.pair (List.nodup_finRange n)
        (fun _ _ _ _ h => P.pair_injective h)) (List.nodup_finRange n)).mpr
    intro d
    constructor
    · intro _; exact List.mem_finRange d
    · intro _
      exact List.mem_map.mpr ⟨P.pair d,List.mem_finRange _,P.pair_pair d⟩
  have hcount := hp.countP_eq P.digonRoot
  rw [List.countP_map] at hcount
  have hfun : (fun d => P.digonRoot (P.pair d)) =
      (fun d => P.marked d && decide ((P.pair d).val < d.val)) := by
    funext d
    simp only [digonRoot,P.pair_pair,P.pair_marked]
  change roots.countP (fun d => P.digonRoot (P.pair d)) = roots.countP P.digonRoot at hcount
  rw [hfun] at hcount
  have htotal : ∀ xs : List (Fin n), xs.countP P.marked =
      xs.countP P.digonRoot + xs.countP (fun d => P.marked d && decide ((P.pair d).val < d.val)) := by
    intro xs
    induction xs with
    | nil => simp
    | cons d xs ih =>
      cases hd : P.marked d
      · simp [digonRoot,hd,ih]
      · have hne : d.val ≠ (P.pair d).val := by
          intro he; exact P.pair_ne d hd (Fin.ext he.symm)
        rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · have hnot : ¬ (P.pair d).val < d.val := by omega
          simp [digonRoot,hd,hlt,hnot] at *
          omega
        · have hnot : ¬ d.val < (P.pair d).val := by omega
          simp [digonRoot,hd,hlt,hnot] at *
          omega
  have ht := htotal roots
  change 2*roots.countP P.digonRoot = roots.countP P.marked
  omega

end PortPairing
end STACS2027.PlanarAssembly
