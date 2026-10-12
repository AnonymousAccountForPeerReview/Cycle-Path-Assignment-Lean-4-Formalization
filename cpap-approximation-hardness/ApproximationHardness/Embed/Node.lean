module

public import ApproximationHardness.Embed.Frontier
import Lean.Elab.Tactic.Omega

/-!
# Starting and closing solver nodes

Stored results are required only on the live frontier. Initializing a new dart
group and closing a target preserve every disjoint live result.
-/

@[expose] public section

namespace STACS2027.Embed.Sol

/-- A stored node result consists of a represented linked stack and its least key. -/
structure Stored (m : SMem) (v : Nat) (r : Res) : Prop where
  stack : StackRep m (m.rs v) r.seg
  low : m.rl v = r.low

theorem StackRep.store_frame {m : SMem} {h : Nat} {seg : List Grp}
    (H : StackRep m h seg) (v rh rl : Nat) : StackRep (m.store v rh rl) h seg :=
  H.array_frame (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem StackRep.inf_frame {m : SMem} {h : Nat} {seg : List Grp}
    (H : StackRep m h seg) (v code : Nat) :
    StackRep {m with inf := upd m.inf v code} h seg :=
  H.array_frame (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem stored_store {m : SMem} {h : Nat} {r : Res}
    (H : StackRep m h r.seg) (v : Nat) : Stored (m.store v h r.low) v r := by
  constructor
  · simpa [SMem.store] using H.store_frame v h r.low
  · simp [SMem.store]

variable (S : Sol)

/-- The maximal open end is the head of a class in the top group. -/
theorem Inv.deepest_head {sides : Nat → Bool} {A : Nat → Prop} {r : Res} {x : Nat}
    (H : S.Inv sides A r) (hx : A x)
    (hmax : ∀ y, A y → y ≠ x → S.key y < S.key x) :
    ∀ g rest, r.seg = g :: rest → g.P.head? = some x ∨ g.M.head? = some x := by
  intro g rest hs
  have hc := H.core
  have hxe : x ∈ els r.seg := (H.mem x).mpr hx
  rw [hs] at hc hxe
  have hinA : ∀ y ∈ g.els, A y := fun y hy =>
    (H.mem y).mp (by rw [hs, els_cons]; exact List.mem_append_left _ hy)
  have hg : x ∈ g.els := by
    rw [els_cons] at hxe
    rcases List.mem_append.mp hxe with h | h
    · exact h
    · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (hc.ne g (List.mem_cons_self ..))
      have h1 := hc.lt_of_mem ha h
      by_cases he : a = x
      · subst a; omega
      · have h2 := hmax a (hinA a ha) he
        omega
  rcases mem_gels.mp hg with hp | hm
  · have hP := head_of_max (hc.sortP g (List.mem_cons_self ..)) hp
      (fun y hy he => hmax y (hinA y (List.mem_append_left _ hy)) he)
    exact Or.inl (by rw [hP]; rfl)
  · have hM := head_of_max (hc.sortM g (List.mem_cons_self ..)) hm
      (fun y hy he => hmax y (hinA y (List.mem_append_right _ hy)) he)
    exact Or.inr (by rw [hM]; rfl)

/-- Planarity-derived solver invariants supply the target's required head condition. -/
theorem Good.target_head (G : S.Good) {sides : Nat → Bool}
    (hfork : ∀ v p q, S.P.IsFork S.α S.key v p q → S.P.ForkOK S.α S.key sides p q)
    {v c d : Nat} (ht : S.P.IsTarget S.α S.key v c d) :
    ∀ g rest, (S.solve c).seg = g :: rest →
      g.P.head? = some (S.α d) ∨ g.M.head? = some (S.α d) := by
  apply Inv.deepest_head S (G.solve_inv hfork c)
  · exact mem_openEnds.mpr ⟨ht.mem, by rw [G.invol]; exact ht.not_mem⟩
  · intro e he hn
    obtain ⟨he, hp⟩ := mem_openEnds.mp he
    exact ht.deep e he hp hn

theorem itRes_foreign {m : SMem} {h : Nat} {seg : List Grp} {it : Item}
    (H : StackRep m h seg)
    (fresh : ∀ e, it = .dart e → ∀ g ∈ seg, g.id ≠ e) :
    StackRep (S.itRes m it).1 h seg := by
  cases it with
  | node c => exact H
  | dart e =>
    apply H.array_frame
    · intro _ _; rfl
    · intro g hg; simp [itRes, upd_ne _ _ (fresh e rfl g hg)]
    · intro g hg; simp [itRes, upd_ne _ _ (fresh e rfl g hg)]
    · intro g hg; simp [itRes, upd_ne _ _ (fresh e rfl g hg)]
    · intro _ _; rfl
    · intro g hg; simp [itRes, upd_ne _ _ (fresh e rfl g hg)]

/-- A newly initialized disjoint dart does not invalidate another stored result. -/
theorem itRes_stored_foreign {m : SMem} {v : Nat} {r : Res} {it : Item}
    (H : Stored m v r)
    (fresh : ∀ e, it = .dart e → ∀ g ∈ r.seg, g.id ≠ e) :
    Stored (S.itRes m it).1 v r := by
  constructor
  · have Hr := S.itRes_foreign H.stack fresh
    cases it <;> simpa [itRes] using Hr
  · cases it <;> simpa [itRes] using H.low

/-- A part is represented by its child's live result or by the initialized dart singleton. -/
theorem itRes_rep {m : SMem} {it : Item}
    (H : ∀ c, it = .node c → Stored m c (S.solve c)) :
    StackRep (S.itRes m it).1 (S.itRes m it).2.1 (S.rpart it).seg ∧
      (S.itRes m it).2.2 = (S.rpart it).low := by
  cases it with
  | node c => exact ⟨(H c rfl).stack, (H c rfl).low⟩
  | dart e => exact S.itRes_dart m e

/-- A leaf starts and finishes in one node step with the empty abstract result. -/
theorem nodeStep_leaf {s : SMS} {v : Nat} (hp : S.P.parts v = []) :
    Stored (S.nodeStep s v).m v (S.solve v) ∧ (S.nodeStep s v).k = s.k + 1 := by
  rw [S.solve_nil hp]
  constructor
  · constructor
    · simpa [nodeStep, hp, empty, SMem.store] using
        (StackRep.nil : StackRep (S.nodeStep s v).m 0 [])
    · simp [nodeStep, hp, SMem.store, empty]
  · simp [nodeStep, hp]

/-- A one-part node stores exactly that part's represented result. -/
theorem nodeStep_single {s : SMS} {v : Nat} {it : Item}
    (hp : S.P.parts v = [it])
    (H : ∀ c, it = .node c → Stored s.m c (S.solve c)) :
    Stored (S.nodeStep s v).m v (S.solve v) ∧ (S.nodeStep s v).k = s.k + 1 := by
  obtain ⟨Hr, Hl⟩ := S.itRes_rep H
  rw [S.solve_one hp]
  constructor
  · constructor
    · have hh : (S.nodeStep s v).m.rs v = (S.itRes s.m it).2.1 := by
        simp [nodeStep, hp, SMem.store]
      rw [hh]
      apply Hr.array_frame
      all_goals intro _ _; simp [nodeStep, hp, SMem.store]
    · simp [nodeStep, hp, SMem.store, Hl]
  · simp [nodeStep, hp]

/-- Closing a target changes only a class head belonging to the child's top group. -/
theorem closeM_foreign {m : SMem} {h e : Nat} {r : Res} {fh : Nat} {foreign : List Grp}
    (H : StackRep m h r.seg) (HF : StackRep m fh foreign)
    (fresh : ∀ g ∈ r.seg, ∀ q ∈ foreign, q.id ≠ g.id) :
    StackRep (S.closeM m e h r.low).1 fh foreign := by
  cases hs : r.seg with
  | nil =>
    have hz : h = 0 := H.head_zero_iff.mpr hs
    simpa [closeM, hz] using HF
  | cons g rest =>
    have hh : h = g.id + 1 := (StackRep.cons_iff.mp (hs ▸ H)).1
    apply HF.array_frame
    · intro _ _; simp [closeM, hh]; split <;> rfl
    · intro q hq
      simp only [closeM, hh, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
        ite_false, Nat.add_sub_cancel]
      split
      · exact upd_ne _ _ (fresh g (by simp [hs]) q hq)
      · rfl
    · intro _ _; simp [closeM, hh]; split <;> rfl
    · intro q hq
      simp only [closeM, hh, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
        ite_false, Nat.add_sub_cancel]
      split
      · rfl
      · exact upd_ne _ _ (fresh g (by simp [hs]) q hq)
    · intro _ _; simp [closeM, hh]; split <;> rfl
    · intro _ _; exact congrFun (S.closeM_group_next m e h r.low) _

/-- The two-part target transition stores the exact abstract head-removal result. -/
theorem twoStep_target {s : SMS} {v c d : Nat} {p q : Item}
    (ht : S.tgtOf p q = some (c, d)) (H : Stored s.m c (S.solve c))
    (hhead : ∀ g rest, (S.solve c).seg = g :: rest →
      g.P.head? = some (S.α d) ∨ g.M.head? = some (S.α d)) :
    Stored (S.twoStep s v p q).m v (S.closeRes (S.α d) (S.solve c)) ∧
      (S.twoStep s v p q).k = s.k + 1 := by
  obtain ⟨Hr, Hl⟩ := S.closeM_stack H.stack hhead
  rw [← H.low] at Hr Hl
  constructor
  · constructor
    · have hh : (S.twoStep s v p q).m.rs v =
          (S.closeM s.m (S.α d) (s.m.rs c) (s.m.rl c)).2.1 := by
        simp [twoStep, ht, SMem.store]
      rw [hh]
      apply Hr.array_frame
      all_goals intro _ _; simp [twoStep, ht, SMem.store]
    · simp [twoStep, ht, SMem.store, Hl]
  · simp [twoStep, ht]

end STACS2027.Embed.Sol
