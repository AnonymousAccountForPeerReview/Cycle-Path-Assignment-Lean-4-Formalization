module

public import Outerplanar.Palm
public import Outerplanar.Reach
public import Outerplanar.Convex
import Mathlib.Tactic

/-!
# Blocks from a palm tree

For a palm tree `P` of `g`, every edge `ab` has a lower end (the descendant) and lies in
the *block* of the head of its lower end (`P.block h`: ANONYMIZED and ANONYMIZED's
biconnected components). Then:

* every simple cycle of `g` lies in one block (`cycle_in_block`): a head `h` separates its
  subtree from the rest of the graph except at `par h` (`cycle_sep`);
* every block with a third vertex besides `h` and `par h` is 2-connected
  (`twoConnected_block`): the tree path from any vertex of the block up to `par h` stays in
  the block, and a vertex `z` of the block is bypassed below it through an edge from the
  subtree of the child of `z` to a proper ancestor of `z` (the child is not a head).
-/

@[expose] public section

namespace STACS2027

/-! ### Walks along cycles -/

theorem walk_of_pathEdges {g : Graph} :
    ∀ {l : List ℕ}, l.Nodup → (∀ e ∈ pathEdges l, e ∈ g) → WalkWithin g (fun _ => True) l
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | a :: b :: rest, hnd, he => by
    refine ⟨trivial, ⟨?_, he _ (by simp [pathEdges])⟩, walk_of_pathEdges hnd.of_cons ?_⟩
    · intro h; subst h; simp at hnd
    · intro e hm; exact he e (by simp only [pathEdges]; exact List.mem_cons_of_mem _ hm)

theorem IsCycle.walk {g : Graph} {k : ℕ} {c : Cycle} (hc : IsCycle g k c) :
    WalkWithin g (fun _ => True) c :=
  walk_of_pathEdges hc.2.2.1 (fun e he => hc.2.2.2 e (pathEdges_subset_cycleEdges c e he))

theorem IsCycle.adj_wrap {g : Graph} {k x : ℕ} {rest : List ℕ} (hc : IsCycle g k (x :: rest))
    (hr : rest ≠ []) : Adj g (rest.getLast hr) x := by
  have hu := edge_last_head_mem_cycleEdges (u := x :: rest) (by simp)
  simp only [List.head_cons, List.getLast_cons hr] at hu
  refine ⟨?_, hc.2.2.2 _ hu⟩
  intro h
  have hnd := hc.2.2.1
  rw [List.nodup_cons] at hnd
  exact hnd.1 (h ▸ List.getLast_mem hr)

theorem WalkWithin.of_mem {g : Graph} {S T : ℕ → Prop} :
    ∀ {w : List ℕ}, WalkWithin g S w → (∀ x ∈ w, T x) → WalkWithin g T w
  | [], _, _ => trivial
  | [a], _, h => h a (by simp)
  | a :: b :: rest, ⟨_, hab, hw⟩, h =>
    ⟨h a (by simp), hab, WalkWithin.of_mem hw (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

theorem WalkWithin.left {g : Graph} {S : ℕ → Prop} :
    ∀ {w1 w2 : List ℕ}, WalkWithin g S (w1 ++ w2) → WalkWithin g S w1
  | [], _, _ => trivial
  | [_], [], h => h
  | [_], _ :: _, h => h.1
  | _ :: b :: rest, _, ⟨ha, hab, hw⟩ => ⟨ha, hab, WalkWithin.left (w1 := b :: rest) hw⟩

theorem WalkWithin.right {g : Graph} {S : ℕ → Prop} :
    ∀ {w1 w2 : List ℕ}, WalkWithin g S (w1 ++ w2) → WalkWithin g S w2
  | [], _, h => h
  | [_], w2, h => by
    cases w2 with
    | nil => trivial
    | cons _ _ => exact h.2.2
  | _ :: b :: rest, _, ⟨_, _, hw⟩ => WalkWithin.right (w1 := b :: rest) hw

namespace Palm

variable {g : Graph} (P : Palm g)

open Classical

/-! ### Lower ends -/

/-- The lower end of the edge `ab`: its descendant end. -/
noncomputable def lower (a b : ℕ) : ℕ := if P.Anc a b then b else a

theorem lower_cases {a b : ℕ} (h : Adj g a b) :
    (P.lower a b = b ∧ P.Anc a b) ∨ (P.lower a b = a ∧ P.Anc b a) := by
  unfold lower
  by_cases hab : P.Anc a b
  · exact Or.inl ⟨ite_eq_left hab, hab⟩
  · refine Or.inr ⟨ite_eq_right hab, ?_⟩
    rcases P.palm a b h with h' | h'
    · exact absurd h' hab
    · exact h'

theorem lower_comm {a b : ℕ} (h : Adj g a b) : P.lower a b = P.lower b a := by
  have hb : IsVertex g b := ⟨a, h⟩
  have ha : IsVertex g a := ⟨b, h.symm⟩
  rcases P.lower_cases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases P.lower_cases h.symm with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact absurd (P.anc_antisymm ha h4 h2) (fun e => h.1 e.symm)
  · rw [h1, h3]
  · rw [h1, h3]
  · exact absurd (P.anc_antisymm ha h2 h4).symm h.1

/-! ### Blocks -/

/-- The block of the head `h`: the edges (written smaller end first) whose lower end has
head `h`. -/
noncomputable def block (h : ℕ) : Graph :=
  g.filter fun e => decide (e.1 < e.2 ∧ P.head (P.lower e.1 e.2) = h)

theorem adj_block {h u v : ℕ} : Adj (P.block h) u v ↔ Adj g u v ∧ P.head (P.lower u v) = h := by
  unfold block Adj
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hne, hg, hlt, hh⟩
    refine ⟨⟨hne, hg⟩, ?_⟩
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · simpa [edge, Nat.min_eq_left h'.le, Nat.max_eq_right h'.le] using hh
    · rw [P.lower_comm ⟨hne, hg⟩]
      simpa [edge, Nat.min_eq_right h'.le, Nat.max_eq_left h'.le] using hh
  · rintro ⟨⟨hne, hg⟩, hh⟩
    refine ⟨hne, hg, ?_, ?_⟩
    · simp only [edge]; omega
    · rcases Nat.lt_or_gt_of_ne hne with h' | h'
      · simpa [edge, Nat.min_eq_left h'.le, Nat.max_eq_right h'.le] using hh
      · rw [P.lower_comm ⟨hne, hg⟩] at hh
        simpa [edge, Nat.min_eq_right h'.le, Nat.max_eq_left h'.le] using hh

theorem block_sub (h : ℕ) : ∀ e ∈ P.block h, e ∈ g := fun _ he => (List.mem_filter.mp he).1

/-! ### Separation -/

/-- A walk from the subtree of a head that avoids its parent stays in the subtree. -/
theorem walk_sep {h : ℕ} (hh : P.IsHead h) :
    ∀ (w : List ℕ) (x : ℕ), P.Anc h x → WalkWithin g (fun v => v ≠ P.par h) (x :: w) →
      ∀ y ∈ x :: w, P.Anc h y
  | [], x, hx, _, y, hy => by simp at hy; subst hy; exact hx
  | z :: w, x, hx, ⟨_, hxz, hw⟩, y, hy => by
    have hz : P.Anc h z := by
      by_contra hc
      exact hw.mem z (by simp) (hh.2.2 x z hx hxz hc)
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact walk_sep hh w z hz hw y hy

/-- **Separation**: a cycle with a vertex in the subtree of a head lies in the subtree and
its parent. -/
theorem cycle_sep {h k : ℕ} {c : Cycle} (hh : P.IsHead h) (hc : IsCycle g k c) {v0 : ℕ}
    (hv0 : v0 ∈ c) (hh0 : P.Anc h v0) : ∀ v ∈ c, P.Anc h v ∨ v = P.par h := by
  obtain ⟨rest, hc', -, hperm⟩ := hc.rotate_to_vertex hv0
  have hmem : ∀ v, v ∈ c ↔ v ∈ v0 :: rest := fun v => hperm.mem_iff
  have hnd := hc'.2.2.1
  have hwalk := hc'.walk
  have hp0 : v0 ≠ P.par h := by
    intro he
    have : P.Anc h (P.par h) := he ▸ hh0
    exact hh.2.1 (P.anc_antisymm hh.1 (P.anc_par h) this)
  intro v hv
  rw [hmem v] at hv
  by_cases hpin : P.par h ∈ v0 :: rest
  · obtain ⟨A, B, hAB⟩ := List.append_of_mem hpin
    obtain ⟨A', rfl⟩ : ∃ A', A = v0 :: A' := by
      cases A with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hAB
        exact absurd hAB.1 hp0
      | cons a A' =>
        simp only [List.cons_append, List.cons.injEq] at hAB
        exact ⟨A', by rw [hAB.1]⟩
    have hwalk' : WalkWithin g (fun _ => True) ((v0 :: A') ++ (P.par h :: B)) := by
      rw [← hAB]; exact hwalk
    have hnd' : ((v0 :: A') ++ (P.par h :: B)).Nodup := by rw [← hAB]; exact hnd
    rw [List.nodup_append] at hnd'
    -- the part before `par h`
    have hwA : WalkWithin g (fun v => v ≠ P.par h) (v0 :: A') :=
      hwalk'.left.of_mem (fun x hx he => hnd'.2.2 x hx (P.par h) (by simp) he)
    have h1 := P.walk_sep hh A' v0 hh0 hwA
    -- the part after `par h`, walked backwards from `v0`
    have h2 : ∀ y ∈ B, P.Anc h y := by
      rcases List.eq_nil_or_concat B with hB | ⟨B', z, hB⟩
      · subst hB; simp
      · simp only [List.concat_eq_append] at hB
        subst hB
        have hcyc : IsCycle g k (v0 :: ((A' ++ P.par h :: B') ++ [z])) := by
          have : v0 :: rest = v0 :: ((A' ++ P.par h :: B') ++ [z]) := by rw [hAB]; simp
          rw [← this]; exact hc'
        have hlast : Adj g z v0 := by
          have hm : edge z v0 ∈ cycleEdges (v0 :: ((A' ++ P.par h :: B') ++ [z])) := by
            rw [cycleEdges_snoc]; simp
          refine ⟨?_, hcyc.2.2.2 _ hm⟩
          intro he
          have := hcyc.2.2.1
          rw [List.nodup_cons] at this
          exact this.1 (by simp [he])
        have hwB : WalkWithin g (fun _ => True) (B' ++ [z]) := by
          have h3 : WalkWithin g (fun _ => True) (P.par h :: (B' ++ [z])) := hwalk'.right
          exact WalkWithin.right (w1 := [P.par h]) h3
        have hrev : WalkWithin g (fun _ => True) (v0 :: z :: B'.reverse) := by
          refine ⟨trivial, hlast.symm, ?_⟩
          have := hwB.reverse
          simpa using this
        have hnB : P.par h ∉ B' ++ [z] := (List.nodup_cons.mp hnd'.2.1).1
        have hw2 : WalkWithin g (fun v => v ≠ P.par h) (v0 :: z :: B'.reverse) := by
          refine hrev.of_mem ?_
          intro x hx he
          rcases List.mem_cons.mp hx with hx | hx
          · exact hp0 (hx ▸ he)
          · apply hnB
            rcases List.mem_cons.mp hx with hx | hx
            · rw [← he, hx]; simp
            · rw [← he]; simp [List.mem_reverse.mp hx]
        intro y hy
        apply P.walk_sep hh _ v0 hh0 hw2 y
        rcases List.mem_append.mp hy with hy | hy
        · simp [hy]
        · simp at hy; simp [hy]
    rw [hAB] at hv
    rcases List.mem_append.mp hv with hv | hv
    · exact Or.inl (h1 v hv)
    · rcases List.mem_cons.mp hv with hv | hv
      · exact Or.inr hv
      · exact Or.inl (h2 v hv)
  · have hw : WalkWithin g (fun v => v ≠ P.par h) (v0 :: rest) :=
      hwalk.of_mem (fun x hx he => hpin (he ▸ hx))
    exact Or.inl (P.walk_sep hh rest v0 hh0 hw v hv)

/-! ### Every cycle lies in one block -/

theorem lower_facts {a b : ℕ} (hab : Adj g a b) :
    IsVertex g (P.lower a b) ∧ P.par (P.lower a b) ≠ P.lower a b ∧
      ∃ y, (y = a ∨ y = b) ∧ y ≠ P.lower a b ∧ P.Anc y (P.lower a b) ∧
        (P.lower a b = a ∨ P.lower a b = b) := by
  have ha : IsVertex g a := ⟨b, hab.symm⟩
  have hb : IsVertex g b := ⟨a, hab⟩
  rcases P.lower_cases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1]
  · exact ⟨hb, P.par_ne_of_anc h2 hab.1, a, Or.inl rfl, hab.1, h2, Or.inr rfl⟩
  · exact ⟨ha, P.par_ne_of_anc h2 hab.1.symm, b, Or.inr rfl, hab.1.symm, h2, Or.inl rfl⟩

/-- **Every simple cycle lies in one block**: the block of the head of the lower end of
any one of its edges. -/
theorem cycle_in_block {k : ℕ} {c : Cycle} (hc : IsCycle g k c) {a b : ℕ}
    (hab : edge a b ∈ cycleEdges c) :
    ∀ e ∈ cycleEdges c, e ∈ P.block (P.head (P.lower a b)) := by
  have hadj : ∀ {x y}, edge x y ∈ cycleEdges c → Adj g x y := by
    intro x y hxy
    refine ⟨?_, hc.2.2.2 _ hxy⟩
    intro he; subst he
    have := hc.edge_endpoints_ne hxy
    simp [edge] at this
  have hab' := hadj hab
  obtain ⟨hxv, hxr, y, hy, hyx, hyx', hx⟩ := P.lower_facts hab'
  set x := P.lower a b
  set h := P.head x
  obtain ⟨hh, hhx, hbet⟩ := P.head_spec hxv hxr
  have hxc : x ∈ c := by
    rcases hx with hx | hx <;> rw [hx]
    · exact (mem_of_mem_cycleEdges hab).1
    · exact (mem_of_mem_cycleEdges hab).2
  have hyc : y ∈ c := by
    rcases hy with hy | hy <;> rw [hy]
    · exact (mem_of_mem_cycleEdges hab).1
    · exact (mem_of_mem_cycleEdges hab).2
  have hsep := P.cycle_sep hh hc hxc hhx
  intro e he
  have hn := pathEdges_normalized _ e he
  rw [← hn] at he ⊢
  have he' := hadj he
  obtain ⟨hxv', hxr', y', hy', hyx2, hyx2', hx'⟩ := P.lower_facts he'
  set x' := P.lower e.1 e.2
  have hx'c : x' ∈ c := by
    rcases hx' with hx' | hx' <;> rw [hx']
    · exact (mem_of_mem_cycleEdges he).1
    · exact (mem_of_mem_cycleEdges he).2
  have hy'c : y' ∈ c := by
    rcases hy' with hy' | hy' <;> rw [hy']
    · exact (mem_of_mem_cycleEdges he).1
    · exact (mem_of_mem_cycleEdges he).2
  -- the lower end `x'` lies below `h`
  have hhx' : P.Anc h x' := by
    rcases hsep x' hx'c with h1 | h1
    · exact h1
    · exfalso
      rcases hsep y' hy'c with h2 | h2
      · have : P.Anc h (P.par h) := P.anc_trans h2 (h1 ▸ hyx2')
        exact hh.2.1 (P.anc_antisymm hh.1 (P.anc_par h) this)
      · exact hyx2 (h2.trans h1.symm)
  -- and has head `h`
  have hhead : P.head x' = h := by
    have hh' := P.anc_head hxv' hh hhx'
    obtain ⟨k1, k2, -⟩ := P.head_spec hxv' hxr'
    by_contra hne
    have hsep' := P.cycle_sep k1 hc hx'c k2
    rcases hsep' x hxc with h1 | h1
    · exact hbet _ h1 hh' hne k1
    · rcases hsep' y hyc with h2 | h2
      · have : P.Anc (P.head x') (P.par (P.head x')) := P.anc_trans h2 (h1 ▸ hyx')
        exact k1.2.1 (P.anc_antisymm k1.1 (P.anc_par _) this)
      · exact hyx (h2.trans h1.symm)
  apply List.mem_filter.mpr
  refine ⟨hc.2.2.2 _ he, ?_⟩
  simp only [decide_eq_true_eq]
  have hlt : (edge e.1 e.2).1 < (edge e.1 e.2).2 := by
    have := he'.1; simp only [edge]; omega
  refine ⟨hlt, ?_⟩
  have hl : P.lower (edge e.1 e.2).1 (edge e.1 e.2).2 = x' := by
    rcases Nat.lt_or_gt_of_ne he'.1 with h' | h'
    · simp [edge, Nat.min_eq_left h'.le, Nat.max_eq_right h'.le, x']
    · simp only [edge, Nat.min_eq_right h'.le, Nat.max_eq_left h'.le, x']
      exact P.lower_comm he'.symm
  rw [hl, hhead]

end Palm

end STACS2027
