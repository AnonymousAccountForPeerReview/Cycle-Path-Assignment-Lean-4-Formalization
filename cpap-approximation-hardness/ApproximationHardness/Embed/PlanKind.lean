module

public import ApproximationHardness.Embed.PlanG
import Lean.Elab.Tactic.Omega

/-!
# Every node of the plan of a depth-first forest has a kind

A vertex with two parts is a fork (two children; a child and a dart opening a chord; two darts
opening chords) or a target (a child and a dart closing a chord from below it). The top of a tree
is a single node, a target (its root and its distinguished dart) or a fork (its root and the child
reached by its distinguished dart).
-/

@[expose] public section

namespace STACS2027.Embed

open Complexity Complexity.Planar

namespace ForestData

variable {F : ForestData} (hF : F.Valid)
include hF

/-- A fork from its parts: the keys of open ends differ by `open_key_inj`. -/
theorem mk_fork {v : Nat} (_hv : F.IsVertex v ∨ F.IsTop v) {p q : Item} (hp : F.parts v = [p, q])
    (disj : ∀ e ∈ (F.plan hF).ID p, e ∉ (F.plan hF).ID q)
    (pq : ∀ e ∈ (F.plan hF).ID p, pair e ∉ (F.plan hF).ID q)
    (qp : ∀ e ∈ (F.plan hF).ID q, pair e ∉ (F.plan hF).ID p)
    (keys : ∀ e ∈ openEnds pair ((F.plan hF).ID p), ∀ f ∈ openEnds pair ((F.plan hF).ID q),
      F.key e ≠ F.key f) :
    (F.plan hF).IsFork pair F.key v p q :=
  ⟨hp, disj, pq, qp, fun e _ => pair_ne e, fun e _ => pair_ne e, keys⟩

theorem open_in_D {v : Nat} {p q : Item} (hp : F.parts v = [p, q])
    (pq : ∀ e ∈ (F.plan hF).ID p, pair e ∉ (F.plan hF).ID q) {e : Nat}
    (he : e ∈ openEnds pair ((F.plan hF).ID p)) :
    e ∈ (F.plan hF).D v ∧ pair e ∉ (F.plan hF).D v := by
  obtain ⟨h1, h2⟩ := mem_openEnds.mp he
  refine ⟨(Plan.mem_D _).mpr ⟨p, by show p ∈ F.parts v; rw [hp]; simp, h1⟩, fun h => ?_⟩
  obtain ⟨it, hit, hi⟩ := (Plan.mem_D _).mp h
  change it ∈ F.parts v at hit
  rw [hp] at hit
  simp at hit
  rcases hit with rfl | rfl
  · exact h2 hi
  · exact pq e h1 hi

theorem keys_of_vertex {v : Nat} (hv : F.IsVertex v) {p q : Item} (hp : F.parts v = [p, q])
    (disj : ∀ e ∈ (F.plan hF).ID p, e ∉ (F.plan hF).ID q)
    (pq : ∀ e ∈ (F.plan hF).ID p, pair e ∉ (F.plan hF).ID q)
    (qp : ∀ e ∈ (F.plan hF).ID q, pair e ∉ (F.plan hF).ID p) :
    ∀ e ∈ openEnds pair ((F.plan hF).ID p), ∀ f ∈ openEnds pair ((F.plan hF).ID q), F.key e ≠ F.key f := by
  intro e he f hf hk
  have hq : F.parts v = [q, p] → False := fun h => by
    rw [hp] at h; simp at h
    obtain ⟨rfl, -⟩ := h
    exact disj e (mem_openEnds.mp he).1 (mem_openEnds.mp he).1
  obtain ⟨e1, e2⟩ := open_in_D hF hp pq he
  have hp' : F.parts v = [p, q] := hp
  obtain ⟨f1, f2⟩ : f ∈ (F.plan hF).D v ∧ pair f ∉ (F.plan hF).D v := by
    obtain ⟨h1, h2⟩ := mem_openEnds.mp hf
    refine ⟨(Plan.mem_D _).mpr ⟨q, by show q ∈ F.parts v; rw [hp]; simp, h1⟩, fun h => ?_⟩
    obtain ⟨it, hit, hi⟩ := (Plan.mem_D _).mp h
    change it ∈ F.parts v at hit
    rw [hp] at hit
    simp at hit
    rcases hit with rfl | rfl
    · exact qp f h1 hi
    · exact h2 hi
  have := open_key_inj hF hv e1 e2 f1 f2 hk
  subst this
  exact disj e (mem_openEnds.mp he).1 (mem_openEnds.mp hf).1

omit hF in
theorem zOf_mem_of_three {r : Nat} (h3 : (F.dartsAt r).length = 3) : F.zOf r ∈ F.dartsAt r := by
  unfold zOf; rw [ite_eq_left h3]
  split
  · rename_i d hd; exact (List.mem_filter.mp (List.mem_of_getLast? hd)).1
  · cases hl : F.dartsAt r with
    | nil => rw [hl] at h3; simp at h3
    | cons a l => simp [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast]

omit hF in
theorem item_down {q : Nat} (h : F.IsDown q) : F.item q = .node (F.rep (pair q)) := by
  unfold item; rw [ite_eq_left h]

omit hF in
theorem item_back {q : Nat} (h : ¬ F.IsDown q) : F.item q = .dart q := by
  unfold item; rw [ite_eq_right h]

theorem id_node {c e : Nat} : e ∈ (F.plan hF).ID (.node c) ↔ e ∈ (F.plan hF).D c := Iff.rfl

theorem id_dart {d e : Nat} : e ∈ (F.plan hF).ID (.dart d) ↔ e = d := by
  simp [Plan.ID, Plan.partW]

theorem child_depth {c v : Nat} (hc : F.IsVertex c) (hcr : ¬ F.IsRoot c) (hcu : F.up c = v) :
    F.depth c = F.depth v + 1 := by
  have := hF.depth_up c hc hcr; rw [hcu] at this; exact this

theorem not_desc_child_parent {c v : Nat} (hc : F.IsVertex c) (hcr : ¬ F.IsRoot c) (hcu : F.up c = v)
    (hv : F.IsVertex v) : ¬ F.Desc c v := fun h => by
  have := desc_depth hF hv h
  have := child_depth hF hc hcr hcu
  omega

/-- A chord does not join two sibling subtrees. -/
theorem sibling_no_chord {c1 c2 e : Nat} (hc1 : F.IsVertex c1) (hr1 : ¬ F.IsRoot c1)
    (hc2 : F.IsVertex c2) (hr2 : ¬ F.IsRoot c2) (hup : F.up c1 = F.up c2) (hne : c1 ≠ c2)
    (hb : F.IsBack e) (h1 : F.Desc c1 (F.rep e)) (h2 : F.Desc c2 (F.rep (pair e))) : False := by
  have d1 := hF.depth_up c1 hc1 hr1
  have d2 := hF.depth_up c2 hc2 hr2
  have hev := isVertex_rep hF hb.1
  have hpv := isVertex_rep hF (pair_lt hb.1)
  rcases hF.back e hb.1 hb.2 with h | h
  · exact hne (desc_unique hF hev h1 (desc_trans h2 h) (by rw [d1, d2, hup]))
  · exact hne (desc_unique hF hpv (desc_trans h1 h) h2 (by rw [d1, d2, hup]))

omit hF in
theorem down_child_par {q : Nat} (h : F.IsDown q) : F.par (F.rep (pair q)) = pair q := h.2

/-- A target from a child and a dart closing a chord from below it. -/
theorem mk_target {v q d : Nat} (hv : F.IsVertex v) (hq : q ∈ F.dartsAt v) (hqd : F.IsDown q)
    (hd : F.InEnd d) (hdv : F.rep d = v)
    (hdX : d ≠ (if F.IsRoot v then F.zOf v else F.par v))
    (honly : ∀ t ∈ F.dartsAt v, F.IsDown t → t = q)
    (hp : F.parts v = [.node (F.rep (pair q)), .dart d] ∨ F.parts v = [.dart d, .node (F.rep (pair q))]) :
    (F.plan hF).IsTarget pair F.key v (F.rep (pair q)) d := by
  obtain ⟨hql, hqr⟩ := mem_dartsAt.mp hq
  obtain ⟨hc, hcr, hcu⟩ := down_child hF hql hqd
  rw [hqr] at hcu
  have hdc := child_depth hF hc hcr hcu
  have hnz : ¬ (F.IsRoot (F.rep d) ∧ d = F.zOf (F.rep d)) := by
    rintro ⟨hr, hz⟩
    rw [hdv] at hr hz
    exact hdX (by rw [ite_eq_left hr]; exact hz)
  have hkey : F.key (pair d) = F.depth v + 1 := by
    unfold key; rw [pair_pair, ite_eq_right hnz, hdv]
  refine ⟨hp, ?_, ?_, ?_, ?_⟩
  · show F.tgt d = v
    unfold tgt; rw [ite_eq_right hnz, hdv]
  · obtain ⟨c', hc', hcr', hcu', hdesc⟩ := inEnd_child hF hd
    rw [hdv] at hcu'
    obtain ⟨ht, htd, htc⟩ := child_down hF hc' hcr' hcu'
    have := honly _ ht htd
    rw [this] at htc
    rw [← htc] at hdesc
    exact (mem_D_vertex hF _ hc _).mpr ⟨isBack_pair hd.1, hdesc, fun h => absurd h hcr⟩
  · intro h
    have := ((mem_D_vertex hF _ hc d).mp h).2.1
    rw [hdv] at this
    exact not_desc_child_parent hF hc hcr hcu hv this
  · intro e he hpe hed
    obtain ⟨ha1, ha2⟩ := open_partner hF hc hcr he hpe
    obtain ⟨hk1, hk2⟩ := key_of_open hF hc hcr he hpe
    rw [hkey]
    have hav := isVertex_rep hF (pair_lt ((mem_D_vertex hF _ hc e).mp he).1.1)
    have hav' : F.Desc (F.rep (pair e)) v := by
      apply desc_of_desc hF hc ha1 ⟨1, hcu⟩
      have := desc_depth hF hc ha1
      have : F.depth (F.rep (pair e)) ≠ F.depth (F.rep (pair q)) :=
        fun h => ha2 (desc_unique hF hc ha1 (desc_refl _) h)
      omega
    rcases hk2 with hk | hk
    · omega
    · rw [hk]
      by_cases hav2 : F.rep (pair e) = v
      · exfalso
        obtain ⟨heb, hed', _⟩ := (mem_D_vertex hF _ hc e).mp he
        have inE : F.InEnd (pair e) := ⟨isBack_pair heb, by
          rw [pair_pair, hav2]; exact desc_trans ⟨1, hcu⟩ hed'⟩
        by_cases hroot : F.IsRoot v
        · by_cases hz : pair e = F.zOf v
          · unfold key at hk
            rw [ite_eq_left ⟨by rw [hav2]; exact hroot, by rw [hav2]; exact hz⟩] at hk
            omega
          · have hdz : d ≠ F.zOf v := by rw [ite_eq_left hroot] at hdX; exact hdX
            exact hed (by rw [← inEnd_unique_root hF hroot inE hd hav2 hdv hz hdz, pair_pair])
        · exact hed (by rw [← inEnd_unique hF hroot inE hd hav2 hdv, pair_pair])
      · have := desc_depth hF hv hav'
        have : F.depth (F.rep (pair e)) ≠ F.depth v := fun h => hav2 (desc_unique hF hv hav' (desc_refl _) h)
        omega

/-- Every vertex of the plan has a kind. -/
theorem kind_vertex {v : Nat} (hv : F.IsVertex v) : (F.plan hF).Kind pair F.key v := by
  let X := if F.IsRoot v then F.zOf v else F.par v
  have hpv : F.parts v = ((F.dartsAt v).erase X).map F.item := parts_vertex hv
  have hndL : ((F.dartsAt v).erase X).Nodup := (dartsAt_nodup v).erase X
  have hmemL : ∀ q, q ∈ (F.dartsAt v).erase X ↔ q ∈ F.dartsAt v ∧ q ≠ X := by
    intro q; rw [(dartsAt_nodup v).mem_erase_iff]; exact And.comm
  have hpX : ¬ F.IsRoot v → X = F.par v := fun h => by simp only [X, ite_eq_right h]
  have hzX : F.IsRoot v → X = F.zOf v := fun h => by simp only [X, ite_eq_left h]
  have hlen : ((F.dartsAt v).erase X).length ≤ 2 := by
    rw [List.length_erase]
    have hdeg := hF.deg v
    split
    · omega
    · rename_i hX
      by_cases hroot : F.IsRoot v
      · have : (F.dartsAt v).length ≠ 3 := fun h3 => hX (by
          rw [hzX hroot]; exact zOf_mem_of_three h3)
        omega
      · exfalso; apply hX
        rw [hpX hroot]; exact mem_dartsAt.mpr ⟨hF.par_lt v hv hroot, hF.par_rep v hv hroot⟩
  have hcover : ∀ u ∈ F.dartsAt v, u ≠ X → u ∈ (F.dartsAt v).erase X := fun u hu hux => (hmemL u).mpr ⟨hu, hux⟩
  -- a down dart at a vertex with a back dart among its parts is a part
  have honly : ∀ d ∈ F.dartsAt v, ¬ F.IsTree d → ∀ t ∈ F.dartsAt v, F.IsDown t → t ≠ X := by
    intro d hd hdt t ht htd htX
    by_cases hroot : F.IsRoot v
    · rw [hzX hroot] at htX
      have h3 : (F.dartsAt v).length = 3 := (zOf_mem (htX ▸ (mem_dartsAt.mp ht).1)).2
      have := (List.mem_filter.mp (zOf_back h3 hd hdt)).2
      rw [← htX] at this
      simp [IsTree, htd] at this
    · rw [hpX hroot] at htX
      exact not_up_and_down hF (mem_dartsAt.mp ht).1 (htX ▸ par_isUp hF hv hroot) htd
  rcases hL : (F.dartsAt v).erase X with _ | ⟨q1, _ | ⟨q2, _ | ⟨q3, L⟩⟩⟩
  · exact Plan.Kind.leaf (by show F.parts v = []; rw [hpv, hL]; rfl)
  · have hp : F.parts v = [F.item q1] := by rw [hpv, hL]; rfl
    by_cases hd : F.IsDown q1
    · exact Plan.Kind.single _ (by show F.parts v = _; rw [hp, item_down hd])
    · exact Plan.Kind.out q1 (by show F.parts v = _; rw [hp, item_back hd]) (pair_ne q1)
  · have hp : F.parts v = [F.item q1, F.item q2] := by rw [hpv, hL]; rfl
    have m1 := (hmemL q1).mp (by rw [hL]; simp)
    have m2 := (hmemL q2).mp (by rw [hL]; simp)
    have hne : q1 ≠ q2 := by have := hndL; rw [hL] at this; simpa using this
    obtain ⟨hl1, hr1⟩ := mem_dartsAt.mp m1.1
    obtain ⟨hl2, hr2⟩ := mem_dartsAt.mp m2.1
    have hnot : ∀ u ∈ F.dartsAt v, u ≠ X → u = q1 ∨ u = q2 := by
      intro u hu hux
      have := hcover u hu hux; rw [hL] at this; simpa using this
    by_cases d1 : F.IsDown q1 <;> by_cases d2 : F.IsDown q2
    · -- two children
      obtain ⟨hc1, hcr1, hcu1⟩ := down_child hF hl1 d1
      obtain ⟨hc2, hcr2, hcu2⟩ := down_child hF hl2 d2
      rw [hr1] at hcu1; rw [hr2] at hcu2
      have hcc : F.rep (pair q1) ≠ F.rep (pair q2) := fun e => hne (pair_inj (by
        rw [← down_child_par d1, ← down_child_par d2, e]))
      rw [item_down d1, item_down d2] at hp
      have disj : ∀ e ∈ (F.plan hF).ID (.node (F.rep (pair q1))), e ∉ (F.plan hF).ID (.node (F.rep (pair q2))) := by
        intro e h1 h2
        have a1 := ((mem_D_vertex hF _ hc1 e).mp h1).2.1
        have a2 := ((mem_D_vertex hF _ hc2 e).mp h2).2.1
        exact hcc (desc_unique hF (isVertex_rep hF ((mem_D_vertex hF _ hc1 e).mp h1).1.1) a1 a2
          (by rw [child_depth hF hc1 hcr1 hcu1, child_depth hF hc2 hcr2 hcu2]))
      have pq : ∀ e ∈ (F.plan hF).ID (.node (F.rep (pair q1))), pair e ∉ (F.plan hF).ID (.node (F.rep (pair q2))) := by
        intro e h1 h2
        exact sibling_no_chord hF hc1 hcr1 hc2 hcr2 (hcu1.trans hcu2.symm) hcc
          ((mem_D_vertex hF _ hc1 e).mp h1).1 ((mem_D_vertex hF _ hc1 e).mp h1).2.1
          ((mem_D_vertex hF _ hc2 _).mp h2).2.1
      have qp : ∀ e ∈ (F.plan hF).ID (.node (F.rep (pair q2))), pair e ∉ (F.plan hF).ID (.node (F.rep (pair q1))) := by
        intro e h1 h2
        exact sibling_no_chord hF hc2 hcr2 hc1 hcr1 (hcu2.trans hcu1.symm) (Ne.symm hcc)
          ((mem_D_vertex hF _ hc2 e).mp h1).1 ((mem_D_vertex hF _ hc2 e).mp h1).2.1
          ((mem_D_vertex hF _ hc1 _).mp h2).2.1
      exact Plan.Kind.fork _ _ (mk_fork hF (Or.inl hv) hp disj pq qp (keys_of_vertex hF hv hp disj pq qp))
    · -- a child and a dart
      have hb2 := back_of_not_tree_part hv m2.1 m2.2 d2
      obtain ⟨hc, hcr, hcu⟩ := down_child hF hl1 d1
      rw [hr1] at hcu
      rcases back_in_or_out hF hb2 with hin | hout
      · have hon : ∀ t ∈ F.dartsAt v, F.IsDown t → t = q1 := by
          intro t ht htd
          rcases hnot t ht (honly q2 m2.1 hb2.2 t ht htd) with e | e
          · exact e
          · exact absurd (e ▸ htd) d2
        refine Plan.Kind.target _ _ (mk_target hF hv m1.1 d1 hin hr2 m2.2 hon (Or.inl ?_))
        rw [hp, item_down d1, item_back d2]
      · rw [item_down d1, item_back d2] at hp
        have hpd := isVertex_rep hF (pair_lt hl2)
        have up2 := hout.2
        rw [hr2] at up2
        have disj : ∀ e ∈ (F.plan hF).ID (.node (F.rep (pair q1))), e ∉ (F.plan hF).ID (.dart q2) := by
          intro e h1 h2
          rw [id_dart hF] at h2; subst h2
          have := ((mem_D_vertex hF _ hc _).mp h1).2.1
          rw [hr2] at this
          exact not_desc_child_parent hF hc hcr hcu hv this
        have pq : ∀ e ∈ (F.plan hF).ID (.node (F.rep (pair q1))), pair e ∉ (F.plan hF).ID (.dart q2) := by
          intro e h1 h2
          rw [id_dart hF] at h2
          have := ((mem_D_vertex hF _ hc _).mp h1).2.1
          rw [← pair_pair e, h2] at this
          exact not_desc_child_parent hF hc hcr hcu hv (desc_trans this up2)
        have qp : ∀ e ∈ (F.plan hF).ID (.dart q2), pair e ∉ (F.plan hF).ID (.node (F.rep (pair q1))) := by
          intro e h1 h2
          rw [id_dart hF] at h1; subst h1
          have := ((mem_D_vertex hF _ hc _).mp h2).2.1
          exact not_desc_child_parent hF hc hcr hcu hv (desc_trans this up2)
        exact Plan.Kind.fork _ _ (mk_fork hF (Or.inl hv) hp disj pq qp (keys_of_vertex hF hv hp disj pq qp))
    · -- a dart and a child
      have hb1 := back_of_not_tree_part hv m1.1 m1.2 d1
      obtain ⟨hc, hcr, hcu⟩ := down_child hF hl2 d2
      rw [hr2] at hcu
      rcases back_in_or_out hF hb1 with hin | hout
      · have hon : ∀ t ∈ F.dartsAt v, F.IsDown t → t = q2 := by
          intro t ht htd
          rcases hnot t ht (honly q1 m1.1 hb1.2 t ht htd) with e | e
          · exact absurd (e ▸ htd) d1
          · exact e
        refine Plan.Kind.target _ _ (mk_target hF hv m2.1 d2 hin hr1 m1.2 hon (Or.inr ?_))
        rw [hp, item_down d2, item_back d1]
      · rw [item_down d2, item_back d1] at hp
        have up1 := hout.2
        rw [hr1] at up1
        have qp : ∀ e ∈ (F.plan hF).ID (.node (F.rep (pair q2))), e ∉ (F.plan hF).ID (.dart q1) := by
          intro e h1 h2
          rw [id_dart hF] at h2; subst h2
          have := ((mem_D_vertex hF _ hc _).mp h1).2.1
          rw [hr1] at this
          exact not_desc_child_parent hF hc hcr hcu hv this
        have disj : ∀ e ∈ (F.plan hF).ID (.dart q1), e ∉ (F.plan hF).ID (.node (F.rep (pair q2))) :=
          fun e h1 h2 => qp e h2 h1
        have pq : ∀ e ∈ (F.plan hF).ID (.dart q1), pair e ∉ (F.plan hF).ID (.node (F.rep (pair q2))) := by
          intro e h1 h2
          rw [id_dart hF] at h1; subst h1
          have := ((mem_D_vertex hF _ hc _).mp h2).2.1
          exact not_desc_child_parent hF hc hcr hcu hv (desc_trans this up1)
        have qp' : ∀ e ∈ (F.plan hF).ID (.node (F.rep (pair q2))), pair e ∉ (F.plan hF).ID (.dart q1) := by
          intro e h1 h2
          rw [id_dart hF] at h2
          have := ((mem_D_vertex hF _ hc _).mp h1).2.1
          rw [← pair_pair e, h2] at this
          exact not_desc_child_parent hF hc hcr hcu hv (desc_trans this up1)
        exact Plan.Kind.fork _ _ (mk_fork hF (Or.inl hv) hp disj pq qp' (keys_of_vertex hF hv hp disj pq qp'))
    · -- two darts: both open chords
      have hb1 := back_of_not_tree_part hv m1.1 m1.2 d1
      have hb2 := back_of_not_tree_part hv m2.1 m2.2 d2
      have noin : ∀ q, q = q1 ∨ q = q2 → ¬ F.InEnd q := by
        intro q hq hin
        have hqr : F.rep q = v := by rcases hq with rfl | rfl <;> assumption
        obtain ⟨c, hc, hcr, hcu, _⟩ := inEnd_child hF hin
        rw [hqr] at hcu
        obtain ⟨ht, htd, _⟩ := child_down hF hc hcr hcu
        rcases hnot _ ht (honly q1 m1.1 hb1.2 _ ht htd) with e | e
        · exact d1 (e ▸ htd)
        · exact d2 (e ▸ htd)
      have o1 := (back_in_or_out hF hb1).resolve_left (noin q1 (Or.inl rfl))
      have o2 := (back_in_or_out hF hb2).resolve_left (noin q2 (Or.inr rfl))
      by_cases hroot : F.IsRoot v
      · exact absurd (back_root_inEnd hF hb1 (by rw [hr1]; exact hroot)) (noin q1 (Or.inl rfl))
      · rw [item_back d1, item_back d2] at hp
        have disj : ∀ e ∈ (F.plan hF).ID (.dart q1), e ∉ (F.plan hF).ID (.dart q2) := by
          intro e h1 h2; rw [id_dart hF] at h1 h2; exact hne (h1.symm.trans h2)
        have pq : ∀ e ∈ (F.plan hF).ID (.dart q1), pair e ∉ (F.plan hF).ID (.dart q2) := by
          intro e h1 h2; rw [id_dart hF] at h1 h2; subst h1
          exact hF.noloop _ hl1 (by rw [h2, hr2, hr1])
        have qp : ∀ e ∈ (F.plan hF).ID (.dart q2), pair e ∉ (F.plan hF).ID (.dart q1) := by
          intro e h1 h2; rw [id_dart hF] at h1 h2; subst h1
          exact hF.noloop _ hl2 (by rw [h2, hr2, hr1])
        exact Plan.Kind.fork _ _ (mk_fork hF (Or.inl hv) hp disj pq qp (keys_of_vertex hF hv hp disj pq qp))
  · exfalso; rw [hL] at hlen; simp at hlen

/-- Every top node of the plan has a kind. -/
theorem kind_top {r : Nat} (hr : F.IsVertex r) (hroot : F.IsRoot r) :
    (F.plan hF).Kind pair F.key (F.top r) := by
  have hp := parts_top hr hroot
  by_cases hzl : F.zOf r < 2 * F.E
  · rw [ite_eq_left hzl] at hp
    have hzm := zOf_mem hzl
    obtain ⟨_, hzr⟩ := mem_dartsAt.mp hzm.1
    by_cases hzd : F.IsDown (F.zOf r)
    · rw [item_down hzd] at hp
      obtain ⟨hc, hcr, hcu⟩ := down_child hF hzl hzd
      rw [hzr] at hcu
      have disj : ∀ e ∈ (F.plan hF).ID (.node r), e ∉ (F.plan hF).ID (.node (F.rep (pair (F.zOf r)))) := by
        intro e h1 h2
        exact ((mem_D_vertex hF r hr e).mp h1).2.2 hroot |>.2 ⟨hzl, hzd, ((mem_D_vertex hF _ hc e).mp h2).2.1⟩
      have pq : ∀ e ∈ (F.plan hF).ID (.node r), pair e ∉ (F.plan hF).ID (.node (F.rep (pair (F.zOf r)))) := by
        intro e h1 h2
        have := open_partner_root hF hr hroot h1 (fun h => disj _ h h2)
        have hb := isBack_pair ((mem_D_vertex hF r hr e).mp h1).1
        rw [this] at hb
        exact hb.2 (Or.inr hzd)
      have qp : ∀ e ∈ (F.plan hF).ID (.node (F.rep (pair (F.zOf r)))), pair e ∉ (F.plan hF).ID (.node r) := by
        intro e h1 h2
        have := open_partner_root hF hr hroot h2 (by rw [pair_pair]; exact fun h => disj _ h h1)
        rw [pair_pair] at this
        have hb := ((mem_D_vertex hF _ hc e).mp h1).1
        rw [this] at hb
        exact hb.2 (Or.inr hzd)
      refine Plan.Kind.fork _ _ (mk_fork hF (Or.inr (top_isTop hr hroot).2.1) hp disj pq qp ?_)
      intro e he f _ _
      obtain ⟨h1, h2⟩ := mem_openEnds.mp he
      have := open_partner_root hF hr hroot h1 h2
      have hb := isBack_pair ((mem_D_vertex hF r hr e).mp h1).1
      rw [this] at hb
      exact hb.2 (Or.inr hzd)
    · rw [item_back hzd] at hp
      have hzb : F.IsBack (F.zOf r) := ⟨hzl, fun ht => by
        rcases ht with hu | hd
        · exact hu.1 (by rw [hzr]; exact hroot)
        · exact hzd hd⟩
      have hin := back_root_inEnd hF hzb (by rw [hzr]; exact hroot)
      refine Plan.Kind.target r (F.zOf r) ⟨Or.inl hp, ?_, ?_, ?_, ?_⟩
      · show F.tgt (F.zOf r) = F.top r
        unfold tgt; rw [ite_eq_left ⟨by rw [hzr]; exact hroot, by rw [hzr]⟩, hzr]
      · apply (mem_D_vertex hF r hr _).mpr
        refine ⟨isBack_pair hzb, by have := hin.2; rw [hzr] at this; exact this, fun _ => ⟨pair_ne _, ?_⟩⟩
        rintro ⟨_, h, _⟩; exact hzd h
      · intro h
        exact ((mem_D_vertex hF r hr _).mp h).2.2 hroot |>.1 rfl
      · intro e he hpe hez
        exact absurd (by rw [← open_partner_root hF hr hroot he hpe, pair_pair]) hez
  · rw [ite_eq_right hzl] at hp
    exact Plan.Kind.single r hp

/-- **Every node of the plan of a depth-first forest has a kind.** -/
theorem kind (v : Nat) : (F.plan hF).Kind pair F.key v := by
  by_cases hv : F.IsVertex v
  · exact kind_vertex hF hv
  · by_cases ht : F.IsTop v
    · obtain ⟨h1, h2, h3⟩ := ht
      have : v = F.top (v - 2 * F.E) := by unfold top; omega
      rw [this]; exact kind_top hF h2 h3
    · exact Plan.Kind.leaf (by show F.parts v = []; unfold parts; rw [ite_eq_right hv, ite_eq_right ht])

end ForestData

end STACS2027.Embed
