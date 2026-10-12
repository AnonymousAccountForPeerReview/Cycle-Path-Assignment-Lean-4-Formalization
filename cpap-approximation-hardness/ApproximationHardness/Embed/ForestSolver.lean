module

public import ApproximationHardness.Embed.SolverIds
public import ApproximationHardness.Embed.Bridge3
import Lean.Elab.Tactic.Omega

/-!
# The solver on the plan of a depth-first forest

The solver data of a forest (`ForestData.sol`): its plan, the partner of a dart, the keys, the test
`isIn d` (the partner of `d` lies deeper), `INF = H + 2`, and `gid v = 4E + v`. They satisfy the
hypotheses of the solver (`good`, `tree`). Hence, if the graph has a planar embedding, the bits of
every consistent orientation give a planar embedding (`planar_of_consistent`).
-/

@[expose] public section

namespace STACS2027.Embed

open Complexity Complexity.Planar STACS2027.PlanarGluing STACS2027.PlanarAssembly

namespace ForestData

variable (F : ForestData)

/-- A key plus one larger than all keys. -/
def INF : Nat := F.H + 2

/-- The identifier of the group a fork creates. -/
def gid (v : Nat) : Nat := 4 * F.E + v

/-- The partner of `d` lies deeper. -/
def isIn (d : Nat) : Bool := decide (F.depth (F.rep d) < F.depth (F.rep (pair d)))

variable {F} (hF : F.Valid)

/-- The solver data of a forest. -/
def sol : Sol := ⟨F.plan hF, pair, F.key, F.isIn, F.INF, F.gid⟩

include hF

omit hF in
theorem top_of_isTop {v : Nat} (h : F.IsTop v) :
    v = F.top (v - 2 * F.E) ∧ F.IsVertex (v - 2 * F.E) ∧ F.IsRoot (v - 2 * F.E) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by unfold top; omega, h2, h3⟩

omit hF in
theorem parts_other {v : Nat} (hv : ¬ F.IsVertex v) (ht : ¬ F.IsTop v) : F.parts v = [] := by
  unfold parts; rw [ite_eq_right hv, ite_eq_right ht]

omit hF in
/-- The dart parts of a node. -/
theorem dart_part {v d : Nat} (h : Item.dart d ∈ F.parts v) :
    (F.IsVertex v ∧ d ∈ F.dartsAt v ∧ ¬ F.IsDown d ∧ d ≠ (if F.IsRoot v then F.zOf v else F.par v)) ∨
    (∃ r, F.IsVertex r ∧ F.IsRoot r ∧ v = F.top r ∧ d = F.zOf r ∧ F.zOf r < 2 * F.E ∧ ¬ F.IsDown d) := by
  by_cases hv : F.IsVertex v
  · rw [parts_vertex hv] at h
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp h
    have hqd : ¬ F.IsDown q := fun hd => by rw [item_down hd] at hqe; cases hqe
    rw [item_back hqd] at hqe; cases hqe
    have hmem := ((dartsAt_nodup v).mem_erase_iff).mp hq
    exact Or.inl ⟨hv, hmem.2, hqd, hmem.1⟩
  · by_cases ht : F.IsTop v
    · obtain ⟨hvt, hr, hroot⟩ := top_of_isTop ht
      right
      refine ⟨_, hr, hroot, hvt, ?_⟩
      rw [hvt, parts_top hr hroot] at h
      rcases List.mem_cons.mp h with h | h
      · cases h
      · split at h
        · rename_i hzl
          rw [List.mem_singleton] at h
          have hzd : ¬ F.IsDown (F.zOf (v - 2 * F.E)) := fun hd => by rw [item_down hd] at h; cases h
          rw [item_back hzd] at h; cases h
          exact ⟨rfl, hzl, hzd⟩
        · simp at h
    · rw [parts_other hv ht] at h; simp at h

omit hF in
/-- The node parts of a node. -/
theorem node_part {v c : Nat} (h : Item.node c ∈ F.parts v) :
    (F.IsVertex v ∧ ∃ q ∈ F.dartsAt v, q ≠ (if F.IsRoot v then F.zOf v else F.par v) ∧ F.IsDown q ∧
      c = F.rep (pair q)) ∨
    (∃ r, F.IsVertex r ∧ F.IsRoot r ∧ v = F.top r ∧
      (c = r ∨ (F.zOf r < 2 * F.E ∧ F.IsDown (F.zOf r) ∧ c = F.rep (pair (F.zOf r))))) := by
  by_cases hv : F.IsVertex v
  · rw [parts_vertex hv] at h
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp h
    have hqd : F.IsDown q := by
      apply Classical.byContradiction; intro hd; rw [item_back hd] at hqe; cases hqe
    rw [item_down hqd] at hqe; cases hqe
    have hmem := ((dartsAt_nodup v).mem_erase_iff).mp hq
    exact Or.inl ⟨hv, q, hmem.2, hmem.1, hqd, rfl⟩
  · by_cases ht : F.IsTop v
    · obtain ⟨hvt, hr, hroot⟩ := top_of_isTop ht
      right
      refine ⟨_, hr, hroot, hvt, ?_⟩
      rw [hvt, parts_top hr hroot] at h
      rcases List.mem_cons.mp h with h | h
      · cases h; exact Or.inl rfl
      · split at h
        · rename_i hzl
          rw [List.mem_singleton] at h
          have hzd : F.IsDown (F.zOf (v - 2 * F.E)) := by
            apply Classical.byContradiction; intro hd; rw [item_back hd] at h; cases h
          rw [item_down hzd] at h; cases h
          exact Or.inr ⟨hzl, hzd, rfl⟩
        · simp at h
    · rw [parts_other hv ht] at h; simp at h

theorem lt_of_mem_D {v e : Nat} (h : e ∈ (F.plan hF).D v) : e < 2 * F.E := by
  by_cases hv : F.IsVertex v
  · exact ((mem_D_vertex hF v hv e).mp h).1.1
  · by_cases ht : F.IsTop v
    · obtain ⟨hvt, hr, hroot⟩ := top_of_isTop ht
      rw [hvt] at h
      exact ((mem_D_top hF hr hroot e).mp h).1.1
    · obtain ⟨it, hit, -⟩ := (Plan.mem_D _).mp h
      change it ∈ F.parts v at hit
      rw [parts_other hv ht] at hit; simp at hit

theorem depth_child {c v : Nat} (hc : F.IsVertex c) (hcr : ¬ F.IsRoot c) (hcu : F.up c = v) {u : Nat}
    (hu : F.IsVertex u) (h : F.Desc c u) : F.depth v < F.depth u := by
  have := desc_depth hF hu h
  have := child_depth hF hc hcr hcu
  omega

theorem isIn_target {v c d : Nat} (ht : (F.plan hF).IsTarget pair F.key v c d) : F.isIn d = true := by
  have hpp : F.parts v = [.node c, .dart d] ∨ F.parts v = [.dart d, .node c] := ht.parts
  have hdp : Item.dart d ∈ F.parts v := by rcases hpp with h | h <;> rw [h] <;> simp
  have hcp : Item.node c ∈ F.parts v := by rcases hpp with h | h <;> rw [h] <;> simp
  have hmem : pair d ∈ (F.plan hF).D c := ht.mem
  unfold isIn
  apply decide_eq_true
  rcases dart_part hdp with ⟨hv, hdm, -, -⟩ | ⟨r, hr, hroot, rfl, rfl, hzl, hzd⟩
  · have hdr := (mem_dartsAt.mp hdm).2
    rcases node_part hcp with ⟨-, q, hq, -, hqd, rfl⟩ | ⟨r, hr', hroot', hvt, -⟩
    · obtain ⟨hql, hqr⟩ := mem_dartsAt.mp hq
      obtain ⟨hc, hcr, hcu⟩ := down_child hF hql hqd
      rw [hqr] at hcu
      have hdesc := ((mem_D_vertex hF _ hc _).mp hmem).2.1
      rw [hdr]
      exact depth_child hF hc hcr hcu (isVertex_rep hF (pair_lt (mem_dartsAt.mp hdm).1)) hdesc
    · exact absurd (hvt ▸ hv) (top_isTop hr' hroot').1
  · have hzr := (mem_dartsAt.mp (zOf_mem hzl).1).2
    have hcr : c = r := by
      have hp := parts_top hr hroot
      rw [ite_eq_left hzl, item_back hzd] at hp
      rcases ht.parts with h | h <;> (change F.parts (F.top r) = _ at h) <;> rw [hp] at h <;> simp at h
      exact h.symm
    subst hcr
    have hdesc := ((mem_D_vertex hF _ hr _).mp hmem).2.1
    have hpv := isVertex_rep hF (pair_lt hzl)
    have hne : F.rep (pair (F.zOf c)) ≠ c := fun h => rep_ne_pair hF hzl (h.trans hzr.symm)
    rw [hzr, hF.depth_root c hr hroot]
    have := desc_depth hF hpv hdesc
    rw [hF.depth_root c hr hroot] at this
    rcases Nat.eq_zero_or_pos (F.depth (F.rep (pair (F.zOf c)))) with h0 | h0
    · exact absurd (desc_unique hF hpv hdesc (desc_refl _) (by rw [h0, hF.depth_root c hr hroot])).symm hne
    · exact h0

theorem isIn_fork {v c d : Nat}
    (hf : (F.plan hF).IsFork pair F.key v (.node c) (.dart d) ∨ (F.plan hF).IsFork pair F.key v (.dart d) (.node c)) :
    F.isIn d = false := by
  have hparts : F.parts v = [.node c, .dart d] ∨ F.parts v = [.dart d, .node c] := by
    rcases hf with h | h
    · exact Or.inl h.parts
    · exact Or.inr h.parts
  have hdp : Item.dart d ∈ F.parts v := by rcases hparts with h | h <;> rw [h] <;> simp
  have hcp : Item.node c ∈ F.parts v := by rcases hparts with h | h <;> rw [h] <;> simp
  have hno : pair d ∉ (F.plan hF).D c := by
    rcases hf with h | h
    · exact h.qp d (by simp [Plan.ID, Plan.partW])
    · exact h.pq d (by simp [Plan.ID, Plan.partW])
  unfold isIn
  apply decide_eq_false
  intro hlt
  rcases dart_part hdp with ⟨hv, hdm, hdd, hdX⟩ | ⟨r, hr, hroot, rfl, rfl, hzl, hzd⟩
  · obtain ⟨hdl, hdr⟩ := mem_dartsAt.mp hdm
    have hb := back_of_not_tree_part hv hdm hdX hdd
    have hpv := isVertex_rep hF (pair_lt hdl)
    rcases hF.back d hdl hb.2 with h | h
    · have := desc_depth hF (isVertex_rep hF hdl) h; omega
    · rw [hdr] at h hlt
      have hne : F.rep (pair d) ≠ v := by rw [← hdr]; exact rep_ne_pair hF hdl
      obtain ⟨c', hc', hcr', hcu', hdesc⟩ := desc_child hF hpv h hne
      obtain ⟨ht, htd, htc⟩ := child_down hF hc' hcr' hcu'
      have htX : pair (F.par c') ≠ (if F.IsRoot v then F.zOf v else F.par v) := by
        intro htX
        by_cases hroot : F.IsRoot v
        · rw [ite_eq_left hroot] at htX
          have hzl : F.zOf v < 2 * F.E := htX ▸ (mem_dartsAt.mp ht).1
          have hz := zOf_back (zOf_mem hzl).2 hdm hb.2
          have := (List.mem_filter.mp hz).2
          simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
          exact this (Or.inr (htX ▸ htd))
        · rw [ite_eq_right hroot] at htX
          exact not_up_and_down hF (mem_dartsAt.mp ht).1 (htX ▸ par_isUp hF hv hroot) htd
      have hpart : F.item (pair (F.par c')) ∈ F.parts v := by
        rw [parts_vertex hv]
        exact List.mem_map_of_mem (((dartsAt_nodup v).mem_erase_iff).mpr ⟨htX, ht⟩)
      rw [item_down htd, htc] at hpart
      have hcc : c' = c := by
        rcases hparts with h' | h' <;> rw [h'] at hpart <;> simp at hpart <;> exact hpart
      subst hcc
      exact hno ((mem_D_vertex hF _ hc' _).mpr ⟨isBack_pair hb, hdesc, fun h => absurd h hcr'⟩)
  · have hzr := (mem_dartsAt.mp (zOf_mem hzl).1).2
    have hcr : c = r := by
      have hp := parts_top hr hroot
      rw [ite_eq_left hzl, item_back hzd] at hp
      rcases hparts with h | h <;> rw [hp] at h <;> simp at h
      exact h.symm
    subst hcr
    have hb : F.IsBack (F.zOf c) := ⟨hzl, fun ht => ht.elim (fun hu => hu.1 (by rw [hzr]; exact hroot)) hzd⟩
    have hin := back_root_inEnd hF hb (by rw [hzr]; exact hroot)
    apply hno
    refine (mem_D_vertex hF _ hr _).mpr ⟨isBack_pair hb, by have := hin.2; rw [hzr] at this; exact this,
      fun _ => ⟨?_, ?_⟩⟩
    · exact pair_ne _
    · rintro ⟨_, hd, _⟩; exact hzd hd

theorem key_lt {e : Nat} (he : e < 2 * F.E) : F.key e + 1 < F.INF := by
  unfold key INF
  have := hF.depth_lt _ (isVertex_rep hF (pair_lt he))
  split <;> omega

/-- The forest satisfies the hypotheses of the solver. -/
theorem good : (F.sol hF).Good where
  invol := pair_pair
  kind := kind hF
  isIn_target := fun _ _ _ ht => isIn_target hF ht
  isIn_fork := fun _ _ _ hf => isIn_fork hF hf
  bound := fun _ _e he => key_lt hF (lt_of_mem_D hF he)

omit hF in
theorem item_inj {d d' : Nat} (h : F.item d = F.item d') : d = d' := by
  unfold item at h
  split at h <;> split at h
  · rename_i h1 h2
    injection h with he
    have := h1.2; rw [he, h2.2] at this
    exact (pair_inj this).symm
  · cases h
  · cases h
  · cases h; rfl

/-- The plan of a forest is a forest. -/
theorem tree : (F.sol hF).Tree where
  parts_nodup := by
    intro v
    show (F.parts v).Nodup
    by_cases hv : F.IsVertex v
    · rw [parts_vertex hv]
      exact nodup_map_of_injOn' _ ((dartsAt_nodup v).erase _) (fun a _ b _ h => item_inj h)
    · by_cases ht : F.IsTop v
      · obtain ⟨hvt, hr, hroot⟩ := top_of_isTop ht
        rw [hvt, parts_top hr hroot]
        split
        · rename_i hzl
          refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩⟩
          rw [List.mem_singleton]
          unfold item; split
          · rename_i hd
            intro h; injection h with h
            exact rep_ne_pair hF hzl (h.symm.trans (mem_dartsAt.mp (zOf_mem hzl).1).2.symm)
          · intro h; cases h
        · exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
      · rw [parts_other hv ht]; exact List.nodup_nil
  uniq_parent := by
    intro v w c hv hw
    change Item.node c ∈ F.parts v at hv
    change Item.node c ∈ F.parts w at hw
    have hup : ∀ {u : Nat}, F.IsVertex u → ∀ q ∈ F.dartsAt u, F.IsDown q → c = F.rep (pair q) →
        F.IsVertex c ∧ ¬ F.IsRoot c ∧ F.up c = u ∧ F.par c = pair q := by
      intro u _ q hq hqd hc
      obtain ⟨hql, hqr⟩ := mem_dartsAt.mp hq
      obtain ⟨h1, h2, h3⟩ := down_child hF hql hqd
      subst hc
      exact ⟨h1, h2, by rw [h3, hqr], hqd.2⟩
    rcases node_part hv with ⟨hv', q, hq, hqX, hqd, hc⟩ | ⟨r, hr, hroot, rfl, hc⟩ <;>
      rcases node_part hw with ⟨hw', q', hq', hqX', hqd', hc'⟩ | ⟨r', hr', hroot', rfl, hc'⟩
    · obtain ⟨-, -, h1, -⟩ := hup hv' q hq hqd hc
      obtain ⟨-, -, h2, -⟩ := hup hw' q' hq' hqd' hc'
      rw [← h1, ← h2]
    · obtain ⟨-, hcr, h1, hp1⟩ := hup hv' q hq hqd hc
      rcases hc' with rfl | ⟨hzl, hzd, hc'⟩
      · exact absurd hroot' hcr
      · exfalso
        have hzm := (zOf_mem hzl).1
        obtain ⟨-, -, h2, hp2⟩ := hup hr' _ hzm hzd hc'
        have hvr : v = r' := by rw [← h1, h2]
        subst hvr
        rw [ite_eq_left hroot'] at hqX
        exact hqX (pair_inj (hp1.symm.trans hp2))
    · obtain ⟨-, hcr, h1, hp1⟩ := hup hw' q' hq' hqd' hc'
      rcases hc with rfl | ⟨hzl, hzd, hc⟩
      · exact absurd hroot hcr
      · exfalso
        have hzm := (zOf_mem hzl).1
        obtain ⟨-, -, h2, hp2⟩ := hup hr _ hzm hzd hc
        have hvr : w = r := by rw [← h1, h2]
        subst hvr
        rw [ite_eq_left hroot] at hqX'
        exact hqX' (pair_inj (hp1.symm.trans hp2))
    · congr 1
      rcases hc with rfl | ⟨hzl, hzd, hc⟩ <;> rcases hc' with h' | ⟨hzl', hzd', hc'⟩
      · exact h'
      · obtain ⟨-, hcr, -, -⟩ := hup hr' _ (zOf_mem hzl').1 hzd' hc'
        exact absurd hroot hcr
      · obtain ⟨-, hcr, -, -⟩ := hup hr _ (zOf_mem hzl).1 hzd hc
        exact absurd (h' ▸ hroot') hcr
      · obtain ⟨-, -, h1, -⟩ := hup hr _ (zOf_mem hzl).1 hzd hc
        obtain ⟨-, -, h2, -⟩ := hup hr' _ (zOf_mem hzl').1 hzd' hc'
        rw [← h1, ← h2]
  uniq_dart := by
    intro v w d hv hw
    change Item.dart d ∈ F.parts v at hv
    change Item.dart d ∈ F.parts w at hw
    rcases dart_part hv with ⟨hv', hdm, -, hdX⟩ | ⟨r, hr, hroot, rfl, rfl, hzl, -⟩ <;>
      rcases dart_part hw with ⟨hw', hdm', -, hdX'⟩ | ⟨r', hr', hroot', rfl, hz', hzl', -⟩
    · rw [← (mem_dartsAt.mp hdm).2, (mem_dartsAt.mp hdm').2]
    · exfalso
      have h1 := (mem_dartsAt.mp hdm).2
      have h2 := (mem_dartsAt.mp (zOf_mem hzl').1).2
      rw [← hz'] at h2
      have : v = r' := h1.symm.trans h2
      subst this
      rw [ite_eq_left hroot'] at hdX
      exact hdX hz'
    · exfalso
      have h1 := (mem_dartsAt.mp hdm').2
      have h2 := (mem_dartsAt.mp (zOf_mem hzl).1).2
      have : w = r := h1.symm.trans h2
      subst this
      rw [ite_eq_left hroot] at hdX'
      exact hdX' rfl
    · have h1 := (mem_dartsAt.mp (zOf_mem hzl).1).2
      have h2 := (mem_dartsAt.mp (zOf_mem hzl').1).2
      rw [← hz'] at h2
      rw [← h1, h2]
  gid_inj := fun v w h => by simp only [sol, gid] at h; omega
  gid_dart := fun v w e he => by
    have := lt_of_mem_D hF he
    simp only [sol, gid]; omega

/-- **The solver embeds a planar graph.** If the graph has a planar embedding, then for every
orientation of the groups consistent with the merges of the solver, the bits read off it give a
planar embedding. -/
theorem planar_of_consistent
    (hex : ∃ G : Hypermap (2 * F.E), IsGraphEdge G.edge ∧
      (∀ d d', Reaches G.node d d' ↔ F.rep d'.val = F.rep d.val) ∧ G.Planar)
    {o : Nat → Bool} (ho : (F.sol hF).Consistent o) : (hyp hF ((F.sol hF).bit o)).Planar := by
  obtain ⟨s0, hs0⟩ := (exists_planar_iff hF).mp hex
  apply (hyp_planar_iff hF _).mpr
  intro r _ _
  exact (good hF).wn_all hs0 ho (F.top r)

end ForestData

end STACS2027.Embed
