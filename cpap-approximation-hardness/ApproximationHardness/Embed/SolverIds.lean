module

public import ApproximationHardness.Embed.SolverMain
import Lean.Elab.Tactic.Omega

/-!
# Every group is consumed at most once

When the plan is a forest (every node and every dart is a part of at most one node), the
identifiers of the groups of a node are distinct and were created below it, and a group consumed
at a fork disappears from the results of all nodes above it. Hence every identifier is consumed at
most once (`consumed_unique`), and only above the node where it was created (`consumed_below`).
-/

@[expose] public section

namespace STACS2027.Embed

namespace Plan

section below

variable {P : Plan}

theorem Below.ht_le {t w : Nat} (h : P.Below t w) : P.ht w ≤ P.ht t := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ hc ih => have := P.ht_lt _ _ hc; omega

theorem Below.trans {a b c : Nat} (h1 : P.Below a b) (h2 : P.Below b c) : P.Below a c := by
  induction h2 with
  | refl => exact h1
  | step _ hc ih => exact Below.step ih hc

end below

variable (P : Plan)

theorem below_child {v c : Nat} (h : Item.node c ∈ P.parts v) : P.Below v c := Below.step Below.refl h

/-- The first step down from `u` towards a node strictly below it. -/
theorem Below.first {P : Plan} {u w : Nat} (h : P.Below u w) (hne : w ≠ u) :
    ∃ c, Item.node c ∈ P.parts u ∧ P.Below c w := by
  induction h with
  | refl => exact absurd rfl hne
  | @step w c hb hc ih =>
    by_cases hw : w = u
    · subst hw; exact ⟨c, hc, Below.refl⟩
    · obtain ⟨c', hc', hb'⟩ := ih hw
      exact ⟨c', hc', Below.step hb' hc⟩

theorem below_cases {P : Plan} {u w : Nat} (h : P.Below u w) : w = u ∨ ∃ w0, P.Below u w0 ∧ Item.node w ∈ P.parts w0 := by
  cases h with
  | refl => exact Or.inl rfl
  | step hb hc => exact Or.inr ⟨_, hb, hc⟩

/-- The darts of a node are the dart parts of the nodes below it. -/
theorem mem_D_below {v e : Nat} : e ∈ P.D v ↔ ∃ w, P.Below v w ∧ Item.dart e ∈ P.parts w := by
  have main : ∀ k v, P.ht v = k → (e ∈ P.D v ↔ ∃ w, P.Below v w ∧ Item.dart e ∈ P.parts w) := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro v hv
      rw [P.mem_D]
      constructor
      · rintro ⟨it, hit, he⟩
        cases it with
        | dart d =>
          have : e = d := by simpa [ID, partW] using he
          subst this; exact ⟨v, Below.refl, hit⟩
        | node c =>
          obtain ⟨w, hw, hd⟩ := (ih _ (by rw [← hv]; exact P.ht_lt v c hit) c rfl).mp he
          exact ⟨w, (P.below_child hit).trans hw, hd⟩
      · rintro ⟨w, hw, hd⟩
        by_cases hwv : w = v
        · subst hwv; exact ⟨_, hd, by simp [ID, partW]⟩
        · obtain ⟨c, hc, hcw⟩ := hw.first hwv
          exact ⟨_, hc, (ih _ (by rw [← hv]; exact P.ht_lt v c hc) c rfl).mpr ⟨w, hcw, hd⟩⟩
  exact main _ v rfl

theorem D_mono {v c e : Nat} (h : P.Below v c) (he : e ∈ P.D c) : e ∈ P.D v := by
  obtain ⟨w, hw, hd⟩ := P.mem_D_below.mp he
  exact P.mem_D_below.mpr ⟨w, h.trans hw, hd⟩

end Plan

namespace Sol

variable (S : Sol)

/-- The plan is a forest and the identifiers of merged groups are fresh. -/
structure Tree : Prop where
  parts_nodup : ∀ v, (S.P.parts v).Nodup
  uniq_parent : ∀ v w c, Item.node c ∈ S.P.parts v → Item.node c ∈ S.P.parts w → v = w
  uniq_dart : ∀ v w d, Item.dart d ∈ S.P.parts v → Item.dart d ∈ S.P.parts w → v = w
  gid_inj : ∀ v w, S.gid v = S.gid w → v = w
  gid_dart : ∀ v w e, e ∈ S.P.D w → S.gid v ≠ e

/-- The identifiers created below `v`. -/
def Own (v g : Nat) : Prop := (∃ w, S.P.Below v w ∧ g = S.gid w) ∨ g ∈ S.P.D v

/-- The identifiers created in a part. -/
def OwnIt (it : Item) (g : Nat) : Prop :=
  match it with
  | .node c => S.Own c g
  | .dart e => g = e

/-- The identifiers of the groups of a result. -/
def gids (r : Res) : List Nat := r.seg.map Grp.id

variable {S}

theorem own_below {v c g : Nat} (h : S.P.Below v c) (ho : S.Own c g) : S.Own v g := by
  rcases ho with ⟨w, hw, rfl⟩ | hd
  · exact Or.inl ⟨w, h.trans hw, rfl⟩
  · exact Or.inr (S.P.D_mono h hd)

theorem ownIt_own {v : Nat} {it : Item} (hit : it ∈ S.P.parts v) {g : Nat} (h : S.OwnIt it g) : S.Own v g := by
  cases it with
  | node c => exact own_below (S.P.below_child hit) h
  | dart e =>
    subst h
    exact Or.inr (S.P.mem_D.mpr ⟨_, hit, by simp [Plan.ID, Plan.partW]⟩)

section tree

variable (T : S.Tree)
include T

theorem Tree.chain {u u' w : Nat} (h : S.P.Below u w) (h' : S.P.Below u' w) :
    S.P.Below u u' ∨ S.P.Below u' u := by
  induction h generalizing u' with
  | refl => exact Or.inr h'
  | @step w0 c hb hc ih =>
    rcases Plan.below_cases h' with rfl | ⟨w1, hb1, hc1⟩
    · exact Or.inl (Plan.Below.step hb hc)
    · have := T.uniq_parent _ _ _ hc hc1
      subst this
      exact ih hb1

theorem Tree.own_cmp {u u' g : Nat} (h : S.Own u g) (h' : S.Own u' g) :
    S.P.Below u u' ∨ S.P.Below u' u := by
  rcases h with ⟨w, hw, rfl⟩ | hd
  · rcases h' with ⟨w', hw', he⟩ | hd'
    · have := T.gid_inj _ _ he; subst this
      exact T.chain hw hw'
    · exact absurd rfl (T.gid_dart w u' _ hd')
  · rcases h' with ⟨w', hw', rfl⟩ | hd'
    · exact absurd rfl (T.gid_dart w' u _ hd)
    · obtain ⟨w, hw, hdw⟩ := S.P.mem_D_below.mp hd
      obtain ⟨w', hw', hdw'⟩ := S.P.mem_D_below.mp hd'
      have := T.uniq_dart _ _ _ hdw hdw'; subst this
      exact T.chain hw hw'

/-- Two children of a node have disjoint subtrees. -/
theorem Tree.not_below_sibling {v c c' : Nat} (hc : Item.node c ∈ S.P.parts v) (hc' : Item.node c' ∈ S.P.parts v)
    (hne : c ≠ c') : ¬ S.P.Below c c' := by
  intro h
  rcases Plan.below_cases h with rfl | ⟨w0, hb, hw⟩
  · exact hne rfl
  · have := T.uniq_parent _ _ _ hw hc'
    subst this
    have h1 := hb.ht_le
    have h2 := S.P.ht_lt _ _ hc
    omega

theorem Tree.gid_not_ownIt {v : Nat} {it : Item} (hit : it ∈ S.P.parts v) : ¬ S.OwnIt it (S.gid v) := by
  cases it with
  | node c =>
    rintro (⟨w, hw, he⟩ | hd)
    · have := T.gid_inj _ _ he; subst this
      have h1 := hw.ht_le
      have h2 := S.P.ht_lt _ _ hit
      omega
    · exact T.gid_dart v c _ hd rfl
  | dart e =>
    intro h
    exact T.gid_dart v v e (S.P.mem_D.mpr ⟨_, hit, by simp [Plan.ID, Plan.partW]⟩) h

/-- The two parts of a fork own disjoint identifiers. -/
theorem Tree.fork_disj {v : Nat} {p q : Item} (hf : S.P.IsFork S.α S.key v p q) {g : Nat}
    (hp : S.OwnIt p g) (hq : S.OwnIt q g) : False := by
  have hpm : p ∈ S.P.parts v := by rw [hf.parts]; simp
  have hqm : q ∈ S.P.parts v := by rw [hf.parts]; simp
  have hpq : p ≠ q := by
    intro e; subst e
    have := T.parts_nodup v; rw [hf.parts] at this; simp at this
  cases p with
  | node c =>
    cases q with
    | node c' =>
      have hcc : c ≠ c' := fun e => hpq (by rw [e])
      rcases T.own_cmp hp hq with h | h
      · exact T.not_below_sibling hpm hqm hcc h
      · exact T.not_below_sibling hqm hpm (Ne.symm hcc) h
    | dart e =>
      have hq' : g = e := hq
      subst hq'
      rcases hp with ⟨w, _, he⟩ | hd
      · exact T.gid_dart w v g (S.P.mem_D.mpr ⟨_, hqm, by simp [Plan.ID, Plan.partW]⟩) he.symm
      · exact hf.disj g hd (by simp [Plan.ID, Plan.partW])
  | dart e =>
    have hp' : g = e := hp
    subst hp'
    cases q with
    | node c' =>
      rcases hq with ⟨w, _, he⟩ | hd
      · exact T.gid_dart w v g (S.P.mem_D.mpr ⟨_, hpm, by simp [Plan.ID, Plan.partW]⟩) he.symm
      · exact hf.disj g (by simp [Plan.ID, Plan.partW]) hd
    | dart e' =>
      have : g = e' := hq
      subst this
      exact hpq rfl

end tree

/-! ### Identifiers of the results -/

theorem gids_close_sub (x : Nat) (r : Res) : (gids (S.closeRes x r)).Sublist (gids r) := by
  unfold gids
  cases hr : r.seg with
  | nil => unfold closeRes; rw [hr]; simp [empty]
  | cons g rest =>
    rw [closeRes_cons hr]
    simp only
    split <;> split <;> simp

theorem gids_merge (v : Nat) (rx ry : Res) :
    gids (S.mergeRes v rx ry) = if ry.seg = [] then gids rx else S.gid v :: (S.rest ry.low rx).map Grp.id := by
  unfold mergeRes gids; split <;> simp

theorem gids_rest_sub (lh : Nat) (rx : Res) : ((S.rest lh rx).map Grp.id).Sublist (gids rx) := by
  unfold gids; rw [← S.popped_append_rest lh rx, List.map_append]
  exact List.sublist_append_right _ _

theorem gids_popped_sub (lh : Nat) (rx : Res) : ((S.popped lh rx).map Grp.id).Sublist (gids rx) := by
  unfold gids; rw [← S.popped_append_rest lh rx, List.map_append]
  exact List.sublist_append_left _ _

theorem mergeCons_ids (rx ry : Res) :
    (S.mergeCons rx ry).map Prod.fst =
      if ry.seg = [] then [] else gids ry ++ (S.popped ry.low rx).map Grp.id := by
  unfold mergeCons gids; split <;> simp [List.map_append, List.map_map, Function.comp_def]

section tree

variable (T : S.Tree) (G : S.Good)
include T G

omit T G in
theorem Tree.rpart_own {v : Nat} {it : Item} (hit : it ∈ S.P.parts v)
    (IH : ∀ c, it = .node c → ∀ g ∈ gids (S.solve c), S.Own c g) : ∀ g ∈ gids (S.rpart it), S.OwnIt it g := by
  cases it with
  | node c => exact IH c rfl
  | dart e => intro g hg; simpa [gids, rpart, dartRes, OwnIt] using hg

/-- The identifiers of a node were created below it, and they are distinct. -/
theorem Tree.gids_ok : ∀ v, (∀ g ∈ gids (S.solve v), S.Own v g) ∧ (gids (S.solve v)).Nodup := by
  have main : ∀ k v, S.P.ht v = k → (∀ g ∈ gids (S.solve v), S.Own v g) ∧ (gids (S.solve v)).Nodup := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro v hv
      have IH : ∀ c, Item.node c ∈ S.P.parts v → (∀ g ∈ gids (S.solve c), S.Own c g) ∧ (gids (S.solve c)).Nodup :=
        fun c hc => ih _ (by rw [← hv]; exact S.P.ht_lt v c hc) c rfl
      have hpart : ∀ it ∈ S.P.parts v, (∀ g ∈ gids (S.rpart it), S.OwnIt it g) ∧ (gids (S.rpart it)).Nodup := by
        intro it hit
        refine ⟨Tree.rpart_own hit (fun c h => (IH c (h ▸ hit)).1), ?_⟩
        cases it with
        | node c => exact (IH c hit).2
        | dart e => simp [gids, rpart, dartRes]
      cases G.kind v with
      | leaf h => rw [S.solve_nil h]; simp [gids, empty]
      | out e h _ =>
        rw [S.solve_one h]
        have hit : Item.dart e ∈ S.P.parts v := by rw [h]; simp
        exact ⟨fun g hg => ownIt_own hit ((hpart _ hit).1 g hg), (hpart _ hit).2⟩
      | single c h =>
        rw [S.solve_one h]
        have hit : Item.node c ∈ S.P.parts v := by rw [h]; simp
        exact ⟨fun g hg => ownIt_own hit ((hpart _ hit).1 g hg), (hpart _ hit).2⟩
      | target c d ht =>
        rw [G.solve_target ht]
        have hit : Item.node c ∈ S.P.parts v := by rcases ht.parts with h | h <;> rw [h] <;> simp
        have hs := gids_close_sub (S := S) (S.α d) (S.solve c)
        exact ⟨fun g hg => ownIt_own hit ((hpart _ hit).1 g (hs.subset hg)), (hpart _ hit).2.sublist hs⟩
      | fork p q hf =>
        rw [S.solve_two hf.parts, G.twoRes_fork hf]
        have hp : p ∈ S.P.parts v := by rw [hf.parts]; simp
        have hq : q ∈ S.P.parts v := by rw [hf.parts]; simp
        have gm : ∀ (rx ry : Res) (itx : Item), itx ∈ S.P.parts v →
            (∀ g ∈ gids rx, S.OwnIt itx g) → (gids rx).Nodup →
            (∀ g ∈ gids (S.mergeRes v rx ry), S.Own v g ∨ g ∈ gids rx) ∧
            (gids (S.mergeRes v rx ry)).Nodup := by
          intro rx ry itx hitx ho hnd
          rw [gids_merge (S := S)]
          split
          · exact ⟨fun g hg => Or.inr hg, hnd⟩
          · refine ⟨fun g hg => ?_, ?_⟩
            · rcases List.mem_cons.mp hg with rfl | hg
              · exact Or.inl (Or.inl ⟨v, Plan.Below.refl, rfl⟩)
              · exact Or.inr ((gids_rest_sub (S := S) _ _).subset hg)
            · refine List.nodup_cons.mpr ⟨fun hm => ?_, hnd.sublist (gids_rest_sub (S := S) _ _)⟩
              exact T.gid_not_ownIt hitx (ho _ ((gids_rest_sub (S := S) _ _).subset hm))
        unfold forkRes
        split
        · obtain ⟨h1, h2⟩ := gm (S.rpart p) (S.rpart q) p hp (hpart p hp).1 (hpart p hp).2
          exact ⟨fun g hg => (h1 g hg).elim id (fun h => ownIt_own hp ((hpart p hp).1 g h)), h2⟩
        · obtain ⟨h1, h2⟩ := gm (S.rpart q) (S.rpart p) q hq (hpart q hq).1 (hpart q hq).2
          exact ⟨fun g hg => (h1 g hg).elim id (fun h => ownIt_own hq ((hpart q hq).1 g h)), h2⟩
  exact fun v => main _ v rfl

theorem Tree.rpart_ok {v : Nat} {it : Item} (hit : it ∈ S.P.parts v) :
    (∀ g ∈ gids (S.rpart it), S.OwnIt it g) ∧ (gids (S.rpart it)).Nodup := by
  refine ⟨Tree.rpart_own hit (fun c _ => (T.gids_ok G c).1), ?_⟩
  cases it with
  | node c => exact (T.gids_ok G c).2
  | dart e => simp [gids, rpart, dartRes]

omit T in
/-- A node with consumed groups is a fork. -/
theorem Good.fork_of_cons {v : Nat} {x : Nat × Bool} (hx : x ∈ S.consAt v) :
    ∃ p q, S.P.IsFork S.α S.key v p q := by
  cases G.kind v with
  | leaf h => simp [consAt, h] at hx
  | out e h _ => simp [consAt, h] at hx
  | single c h => simp [consAt, h] at hx
  | target c d ht => rw [G.consAt_target ht] at hx; simp at hx
  | fork p q hf => exact ⟨p, q, hf⟩

/-- **The groups consumed at a fork**: they come from its parts, are distinct, and leave its result. -/
theorem Tree.cons_ok {v : Nat} {p q : Item} (hf : S.P.IsFork S.α S.key v p q) :
    (∀ x ∈ S.consAt v, x.1 ∈ gids (S.rpart p) ∨ x.1 ∈ gids (S.rpart q)) ∧
    ((S.consAt v).map Prod.fst).Nodup ∧ (∀ x ∈ S.consAt v, x.1 ∉ gids (S.solve v)) := by
  have hp : p ∈ S.P.parts v := by rw [hf.parts]; simp
  have hq : q ∈ S.P.parts v := by rw [hf.parts]; simp
  have op := T.rpart_ok G hp
  have oq := T.rpart_ok G hq
  have hc : S.consAt v = S.forkCons (S.rpart p) (S.rpart q) := by
    unfold consAt; rw [hf.parts]; simp only; rw [G.twoCons_fork hf]
  have hs : S.solve v = S.forkRes v (S.rpart p) (S.rpart q) := by
    rw [S.solve_two hf.parts, G.twoRes_fork hf]
  rw [hc, hs]
  have gen : ∀ (rx ry : Res) (itx ity : Item), itx ∈ S.P.parts v → ity ∈ S.P.parts v →
      (∀ g ∈ gids rx, S.OwnIt itx g) → (gids rx).Nodup →
      (∀ g ∈ gids ry, S.OwnIt ity g) → (gids ry).Nodup →
      (∀ g, S.OwnIt itx g → S.OwnIt ity g → False) →
      (∀ x ∈ S.mergeCons rx ry, x.1 ∈ gids rx ∨ x.1 ∈ gids ry) ∧
      ((S.mergeCons rx ry).map Prod.fst).Nodup ∧ (∀ x ∈ S.mergeCons rx ry, x.1 ∉ gids (S.mergeRes v rx ry)) := by
    intro rx ry itx ity hitx hity hox hndx hoy hndy hdisj
    have hmem : ∀ x ∈ S.mergeCons rx ry, x.1 ∈ (S.mergeCons rx ry).map Prod.fst :=
      fun x hx => List.mem_map_of_mem hx
    rw [S.mergeCons_ids] at hmem
    have hsplit : gids rx = (S.popped ry.low rx).map Grp.id ++ (S.rest ry.low rx).map Grp.id := by
      unfold gids; rw [← List.map_append, S.popped_append_rest]
    refine ⟨fun x hx => ?_, ?_, fun x hx => ?_⟩
    · have := hmem x hx
      split at this
      · simp at this
      · rcases List.mem_append.mp this with h | h
        · exact Or.inr h
        · exact Or.inl ((gids_popped_sub (S := S) _ _).subset h)
    · rw [S.mergeCons_ids]
      split
      · exact List.nodup_nil
      · refine List.nodup_append.mpr ⟨hndy, hndx.sublist (gids_popped_sub (S := S) _ _), fun a ha b hb e => ?_⟩
        subst e
        exact hdisj a (hox a ((gids_popped_sub (S := S) _ _).subset hb)) (hoy a ha)
    · have := hmem x hx
      rw [gids_merge (S := S)]
      split at this
      · simp at this
      · rename_i hy0
        rw [ite_eq_right hy0]
        intro hm
        rcases List.mem_cons.mp hm with he | hm
        · rcases List.mem_append.mp this with h | h
          · have h1 := hoy _ h
            rw [he] at h1
            exact T.gid_not_ownIt hity h1
          · have h1 := hox _ ((gids_popped_sub (S := S) _ _).subset h)
            rw [he] at h1
            exact T.gid_not_ownIt hitx h1
        · rcases List.mem_append.mp this with h | h
          · exact hdisj x.1 (hox _ ((gids_rest_sub (S := S) _ _).subset hm)) (hoy _ h)
          · have := hndx; rw [hsplit] at this
            exact (List.nodup_append.mp this).2.2 _ h _ hm rfl
  unfold forkCons forkRes
  split
  · exact gen _ _ p q hp hq op.1 op.2 oq.1 oq.2 (fun g h1 h2 => T.fork_disj hf h1 h2)
  · obtain ⟨a, b, c⟩ := gen _ _ q p hq hp oq.1 oq.2 op.1 op.2 (fun g h1 h2 => T.fork_disj hf h2 h1)
    exact ⟨fun x hx => (a x hx).symm, b, c⟩

omit T in
theorem Tree.ids_sub : ∀ v, ∀ g ∈ gids (S.solve v), g = S.gid v ∨ ∃ it ∈ S.P.parts v, g ∈ gids (S.rpart it) := by
  intro v g hg
  cases G.kind v with
  | leaf h => rw [S.solve_nil h] at hg; simp [gids, empty] at hg
  | out e h _ => rw [S.solve_one h] at hg; exact Or.inr ⟨_, by rw [h]; simp, hg⟩
  | single c h => rw [S.solve_one h] at hg; exact Or.inr ⟨_, by rw [h]; simp, hg⟩
  | target c d ht =>
    rw [G.solve_target ht] at hg
    exact Or.inr ⟨.node c, by rcases ht.parts with h | h <;> rw [h] <;> simp,
      (gids_close_sub (S := S) (S.α d) (S.solve c)).subset hg⟩
  | fork p q hf =>
    rw [S.solve_two hf.parts, G.twoRes_fork hf] at hg
    have hp : p ∈ S.P.parts v := by rw [hf.parts]; simp
    have hq : q ∈ S.P.parts v := by rw [hf.parts]; simp
    unfold forkRes at hg
    split at hg
    · rw [gids_merge (S := S)] at hg
      split at hg
      · exact Or.inr ⟨p, hp, hg⟩
      · rcases List.mem_cons.mp hg with h | h
        · exact Or.inl h
        · exact Or.inr ⟨p, hp, (gids_rest_sub (S := S) _ _).subset h⟩
    · rw [gids_merge (S := S)] at hg
      split at hg
      · exact Or.inr ⟨q, hq, hg⟩
      · rcases List.mem_cons.mp hg with h | h
        · exact Or.inl h
        · exact Or.inr ⟨q, hq, (gids_rest_sub (S := S) _ _).subset h⟩

/-- Two different parts of a node own disjoint identifiers. -/
theorem Tree.parts_disj {v : Nat} {it it' : Item} (hit : it ∈ S.P.parts v) (hit' : it' ∈ S.P.parts v)
    (hne : it ≠ it') {g : Nat} (h : S.OwnIt it g) (h' : S.OwnIt it' g) : False := by
  cases G.kind v with
  | leaf hh => rw [hh] at hit; simp at hit
  | out e hh _ => rw [hh] at hit hit'; simp at hit hit'; exact hne (hit.trans hit'.symm)
  | single c hh => rw [hh] at hit hit'; simp at hit hit'; exact hne (hit.trans hit'.symm)
  | target c d ht =>
    have key : ∀ a b : Item, a ∈ S.P.parts v → b ∈ S.P.parts v → a ≠ b → S.OwnIt a g → S.OwnIt b g →
        a = .dart d → False := by
      intro a b ha hb hab hoa hob had
      subst had
      have hgd : g = d := hoa
      subst hgd
      have hbc : b = .node c := by
        rcases ht.parts with hh | hh <;> rw [hh] at hb <;> simp at hb <;>
          rcases hb with hb | hb <;> first | exact hb | exact absurd hb.symm hab
      subst hbc
      rcases hob with ⟨w, _, he⟩ | hd
      · exact T.gid_dart w v g (S.P.mem_D.mpr ⟨_, ha, by simp [Plan.ID, Plan.partW]⟩) he.symm
      · exact ht.not_mem hd
    have hcases : it = .dart d ∨ it' = .dart d := by
      rcases ht.parts with hh | hh <;> rw [hh] at hit hit' <;> simp at hit hit' <;>
        rcases hit with rfl | rfl <;> rcases hit' with rfl | rfl <;> simp_all
    rcases hcases with e | e
    · exact key it it' hit hit' hne h h' e
    · exact key it' it hit' hit (Ne.symm hne) h' h e
  | fork p q hf =>
    have := hf.parts
    rw [this] at hit hit'
    simp at hit hit'
    rcases hit with rfl | rfl <;> rcases hit' with rfl | rfl
    · exact hne rfl
    · exact T.fork_disj hf h h'
    · exact T.fork_disj hf h' h
    · exact hne rfl

theorem Tree.cons_own {u : Nat} {x : Nat × Bool} (hx : x ∈ S.consAt u) :
    ∃ it ∈ S.P.parts u, x.1 ∈ gids (S.rpart it) ∧ S.OwnIt it x.1 := by
  obtain ⟨p, q, hf⟩ := Good.fork_of_cons G hx
  have hp : p ∈ S.P.parts u := by rw [hf.parts]; simp
  have hq : q ∈ S.P.parts u := by rw [hf.parts]; simp
  rcases (T.cons_ok G hf).1 x hx with h | h
  · exact ⟨p, hp, h, (T.rpart_ok G hp).1 _ h⟩
  · exact ⟨q, hq, h, (T.rpart_ok G hq).1 _ h⟩

/-- **A consumed group is gone** from the results of all nodes at or above the fork. -/
theorem Tree.gone : ∀ v w, S.P.Below v w → ∀ x ∈ S.consAt w, x.1 ∉ gids (S.solve v) := by
  have main : ∀ k v, S.P.ht v = k → ∀ w, S.P.Below v w → ∀ x ∈ S.consAt w, x.1 ∉ gids (S.solve v) := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro v hv w hw x hx hm
      by_cases hwv : w = v
      · subst hwv
        obtain ⟨p, q, hf⟩ := Good.fork_of_cons G hx
        exact (T.cons_ok G hf).2.2 x hx hm
      · obtain ⟨c, hc, hcw⟩ := hw.first hwv
        have IH := ih _ (by rw [← hv]; exact S.P.ht_lt v c hc) c rfl w hcw x hx
        obtain ⟨it, hit, -, hown⟩ := T.cons_own G hx
        have hoc : S.Own c x.1 := own_below hcw (ownIt_own hit hown)
        rcases Tree.ids_sub G v x.1 hm with he | ⟨it', hit', hm'⟩
        · have : S.OwnIt (.node c) (S.gid v) := he ▸ hoc
          exact T.gid_not_ownIt hc this
        · by_cases hie : it' = .node c
          · subst hie; exact IH hm'
          · exact T.parts_disj G hit' hc hie ((T.rpart_ok G hit').1 _ hm') hoc
  exact fun v => main _ v rfl

omit T G in
theorem eq_of_mem_nodup_map {l : List (Nat × Bool)} (h : (l.map Prod.fst).Nodup) {x y : Nat × Bool}
    (hx : x ∈ l) (hy : y ∈ l) (he : x.1 = y.1) : x = y := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rw [List.map_cons] at h
    obtain ⟨h1, h2⟩ := List.nodup_cons.mp h
    rcases List.mem_cons.mp hx with rfl | hx1 <;> rcases List.mem_cons.mp hy with rfl | hy1
    · rfl
    · exact absurd (he ▸ List.mem_map_of_mem hy1) h1
    · exact absurd (he.symm ▸ List.mem_map_of_mem hx1) h1
    · exact ih h2 hx1 hy1

/-- **Every group is consumed at most once.** -/
theorem Tree.consumed_unique {u u' : Nat} {x x' : Nat × Bool} (hx : x ∈ S.consAt u) (hx' : x' ∈ S.consAt u')
    (he : x.1 = x'.1) : u = u' ∧ x = x' := by
  have below_eq : ∀ {u u' : Nat} {x x' : Nat × Bool}, x ∈ S.consAt u → x' ∈ S.consAt u' → x.1 = x'.1 →
      S.P.Below u u' → u = u' := by
    intro u u' x x' hx hx' he hb
    apply Classical.byContradiction
    intro hne
    obtain ⟨c, hc, hcu⟩ := hb.first (Ne.symm hne)
    have hgone := T.gone G c u' hcu x' hx'
    obtain ⟨it, hit, hm, hown⟩ := T.cons_own G hx
    obtain ⟨it', hit', -, hown'⟩ := T.cons_own G hx'
    have hoc : S.Own c x.1 := he ▸ own_below hcu (ownIt_own hit' hown')
    by_cases hie : it = .node c
    · subst hie; exact hgone (he ▸ hm)
    · exact T.parts_disj G hit hc hie hown hoc
  obtain ⟨it, hit, -, hown⟩ := T.cons_own G hx
  obtain ⟨it', hit', -, hown'⟩ := T.cons_own G hx'
  have huu : u = u' := by
    rcases T.own_cmp (ownIt_own hit hown) (he ▸ ownIt_own hit' hown') with h | h
    · exact below_eq hx hx' he h
    · exact (below_eq hx' hx he.symm h).symm
  subst huu
  obtain ⟨p, q, hf⟩ := Good.fork_of_cons G hx
  exact ⟨rfl, eq_of_mem_nodup_map (T.cons_ok G hf).2.1 hx hx' he⟩

/-- A consumed group was created strictly below the fork, or is a dart part at or below it. -/
theorem Tree.consumed_below {u : Nat} {x : Nat × Bool} (hx : x ∈ S.consAt u) :
    (∃ w, S.P.Below u w ∧ w ≠ u ∧ x.1 = S.gid w) ∨ (∃ w, S.P.Below u w ∧ Item.dart x.1 ∈ S.P.parts w) := by
  obtain ⟨it, hit, -, hown⟩ := T.cons_own G hx
  rcases ownIt_own hit hown with ⟨w, hw, he⟩ | hd
  · refine Or.inl ⟨w, hw, fun hwu => ?_, he⟩
    subst hwu
    exact T.gid_not_ownIt hit (he ▸ hown)
  · exact Or.inr (S.P.mem_D_below.mp hd)

end tree

end Sol

end STACS2027.Embed
