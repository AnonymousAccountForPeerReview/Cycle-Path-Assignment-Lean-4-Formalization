module

public import NPHardness.PlanarPreprocessDeletionPerm
public import Complexity.Planar.Rot

/-! Removing greatest darts preserves the cyclic order of the surviving
rotation list, including its immediate successor, not merely its orbit. -/

@[expose] public section
namespace STACS2027.PlanarPreprocess.Deletion
open Complexity Complexity.Planar STACS2027.PlanarGluing

theorem rnext_split (before after : List Nat) (x : Nat) (hx : x ∉ before) :
    rnext (before++x::after) x = (after++before++[x]).headD 0 := by
  unfold rnext
  rw [List.idxOf_append,ite_eq_right hx]
  simp only [List.idxOf_cons_self,Nat.zero_add]
  cases after with
  | nil =>
    simp only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add,Nat.mod_self,
      List.nil_append]
    exact List.headD_eq_getD.symm
  | cons y ys =>
    rw [Nat.mod_eq_of_lt (by simp)]
    rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega)]
    simp

/-- Deleting one member of a duplicate-free cyclic list bypasses exactly its
incoming successor arrow. -/
theorem rnext_filter_ne {xs : List Nat} (hn : xs.Nodup) {x a : Nat}
    (hx : x ∈ xs) (hne : x ≠ a) :
    rnext (xs.filter (· != a)) x =
      if rnext xs x = a then rnext xs a else rnext xs x := by
  obtain ⟨before,after,rfl⟩ := List.mem_iff_append.mp hx
  have hxpre : x ∉ before := by
    intro h
    have hd := (List.nodup_append.mp hn).2.2 x h
    exact hd x (by simp) rfl
  have hxf : x ∉ before.filter (· != a) := fun h => hxpre ((List.mem_filter.mp h).1)
  rw [List.filter_append,List.filter_cons]
  simp only [bne_iff_ne]
  rw [ite_eq_left hne]
  rw [rnext_split _ _ _ hxf,rnext_split _ _ _ hxpre]
  cases after with
  | cons y ys =>
    change ((y::ys).filter (· != a) ++ before.filter (· != a) ++ [x]).headD 0 =
      if y=a then rnext (before++x::y::ys) a else y
    by_cases hy : y=a
    · subst y
      have ha : a ∉ before ∧ a ∉ ys := by
        have hd := List.nodup_append.mp hn
        exact ⟨fun h => hd.2.2 a h a (by simp) rfl,
          (List.nodup_cons.mp (List.nodup_cons.mp hd.2.1).2).1⟩
      rw [ite_eq_left rfl,List.filter_cons]
      simp only [bne_self_eq_false,Bool.false_eq_true,ite_false,List.filter_bne_eq_self_of_not_mem ha.1,
        List.filter_bne_eq_self_of_not_mem ha.2]
      have hax : a ∉ before++[x] := by simp [ha.1,Ne.symm hne]
      have he : before++x::a::ys=(before++[x])++a::ys := by simp
      rw [he,rnext_split _ _ _ hax]
      cases ys <;> cases before <;> simp
    · rw [ite_eq_right hy,List.filter_cons]
      simp [hy]
  | nil =>
    simp only [List.filter_nil,List.nil_append]
    cases before with
    | nil => simp [hne]
    | cons y ys =>
      change ((y::ys).filter (· != a) ++ [x]).headD 0 =
        if y=a then rnext ((y::ys)++[x]) a else y
      by_cases hy : y=a
      · subst y
        have ha : a ∉ ys := by
          have hd := (List.nodup_cons.mp hn).1
          exact fun h => hd (List.mem_append.mpr (Or.inl h))
        rw [ite_eq_left rfl,List.filter_cons]
        simp only [bne_self_eq_false,Bool.false_eq_true,ite_false,List.filter_bne_eq_self_of_not_mem ha]
        rw [show (a::ys)++[x]=[]++a::(ys++[x]) by rfl,rnext_split _ _ _ (by simp)]
        cases ys <;> simp
      · rw [ite_eq_right hy,List.filter_cons]
        simp [hy]

/-- Exact cyclic successor after excising the greatest dart. -/
theorem removeLast_rnext {n : Nat} (p : Fin (n+1) → Fin (n+1))
    (hp : ∀ x y, p x=p y → x=y) (xs : List Nat) (hn : xs.Nodup)
    (hb : ∀ x ∈ xs, x<n+1)
    (hrot : ∀ d : Fin (n+1), d.val∈xs → (p d).val=rnext xs d.val)
    (x : Fin n) (hx : x.val∈xs) :
    (removeLast p hp x).val = rnext (xs.filter (fun d => decide (d<n))) x.val := by
  have hfilter : xs.filter (fun d => decide (d<n))=xs.filter (· != n) := by
    apply List.filter_congr
    intro d hd
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,bne_iff_ne]
    have := hb d hd
    omega
  rw [hfilter,rnext_filter_ne hn hx (by have := x.isLt; omega)]
  have hs := hrot (embed x) hx
  change (p (embed x)).val=rnext xs x.val at hs
  by_cases he : p (embed x)=last n
  · have ha : rnext xs x.val=n := by
      have hv := congrArg Fin.val he
      change (p (embed x)).val=n at hv
      omega
    have hm : n∈xs := by rw [←ha]; exact rnext_mem hn hx
    rw [ite_eq_left ha]
    change (skipLast p (embed x)).val = _
    rw [skipLast,ite_eq_left he]
    exact hrot (last n) hm
  · have ha : rnext xs x.val≠n := by
      intro h
      apply he
      apply Fin.ext
      exact hs.trans h
    rw [ite_eq_right ha]
    change (skipLast p (embed x)).val = _
    rw [skipLast,ite_eq_right he]
    exact hs

theorem filter_lt_filter_lt (xs : List Nat) {n m : Nat} (hnm : n≤m) :
    (xs.filter (fun d => decide (d<m))).filter (fun d => decide (d<n)) =
      xs.filter (fun d => decide (d<n)) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro d _
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  omega

/-- Exact cyclic successor after excising the two darts of a final edge. -/
theorem removePair_rnext {n : Nat} (p : Fin (n+2) → Fin (n+2))
    (hp : ∀ x y, p x=p y → x=y) (xs : List Nat) (hn : xs.Nodup)
    (hb : ∀ x ∈ xs, x<n+2)
    (hrot : ∀ d : Fin (n+2), d.val∈xs → (p d).val=rnext xs d.val)
    (x : Fin n) (hx : x.val∈xs) :
    (removePair p hp x).val = rnext (xs.filter (fun d => decide (d<n))) x.val := by
  have hmem : x.val∈xs.filter (fun d => decide (d<n+1)) :=
    List.mem_filter.mpr ⟨hx,by simp only [decide_eq_true_eq]; have := x.isLt; omega⟩
  have h := removeLast_rnext (removeLast p hp) (removeLast_injective hp)
    (xs.filter (fun d => decide (d<n+1))) (hn.filter _) (by
      intro d hd
      exact of_decide_eq_true (List.mem_filter.mp hd).2)
    (fun d hd => removeLast_rnext p hp xs hn hb hrot d (List.mem_filter.mp hd).1) x hmem
  rw [filter_lt_filter_lt xs (by omega)] at h
  exact h

end STACS2027.PlanarPreprocess.Deletion
