module

public import ApproximationHardness.Embed.DFS
public import ApproximationHardness.Embed.TreeOn
public import ApproximationHardness.Embed.Word
import Lean.Elab.Tactic.Omega

/-!
# The invariant of the depth-first search

`DG.Inv`: the visited vertices carry a forest whose open vertices are the ancestors of the current
vertex; every explored dart reaches a visited vertex and is a forest dart or joins an ancestor and
a descendant; the neighbours of a finished vertex are finished or its ancestors; and `post` lists
the finished vertices after their descendants. Every step of the search keeps it.
-/

@[expose] public section

namespace STACS2027.Embed

open Complexity Complexity.Planar

namespace DG

variable (G : DG)

/-- **The invariant of the search.** -/
structure Inv (s : DS) : Prop where
  vert : ∀ u, s.st u ≠ 0 → u < 2 * G.E ∧ G.rep u = u
  st_le : ∀ u, s.st u ≤ 2
  tree : (G.fd s).TreeOn (fun u => s.st u ≠ 0)
  parv : ∀ u, s.st u ≠ 0 → s.par u < 2 * G.E → G.rep (s.par u) = u
  hbound : ∀ u, s.st u ≠ 0 → s.depth u < s.H
  path : s.inner = true → s.st s.cur = 1 ∧ ∀ u, s.st u = 1 ↔ (G.fd s).Desc u s.cur
  closed : s.inner = false → ∀ u, s.st u ≠ 1
  ptr_le : ∀ u, s.ptr u ≤ (G.darts u).length
  ptr0 : ∀ u, s.st u = 0 → s.ptr u = 0
  ptr2 : ∀ u, s.st u = 2 → s.ptr u = (G.darts u).length
  expl : ∀ u, s.st u ≠ 0 → ∀ k, k < s.ptr u → s.st (G.rep (pair ((G.darts u).getD k 0))) ≠ 0
  finN : ∀ w, s.st w = 2 → ∀ e ∈ G.darts w, s.st (G.rep (pair e)) = 2 ∨ (G.fd s).Desc (G.rep (pair e)) w
  back : ∀ u, s.st u ≠ 0 → ∀ k, k < s.ptr u → (G.fd s).IsTree ((G.darts u).getD k 0) ∨
    (G.fd s).Desc (G.rep (pair ((G.darts u).getD k 0))) u ∨ (G.fd s).Desc u (G.rep (pair ((G.darts u).getD k 0)))
  scan : ∀ u, u < s.r → u < 2 * G.E → G.rep u = u → s.st u ≠ 0
  scanR : s.inner = true → s.r < 2 * G.E ∧ (G.fd s).Desc s.r s.cur ∧ 2 * G.E ≤ s.par s.r ∧ s.st s.r ≠ 0
  vl_nd : s.vl.Nodup
  vl_mem : ∀ u, u ∈ s.vl ↔ s.st u ≠ 0
  ex_nd : s.ex.Nodup
  ex_mem : ∀ d, d ∈ s.ex ↔ ∃ u, s.st u ≠ 0 ∧ ∃ k, k < s.ptr u ∧ (G.darts u).getD k 0 = d
  post_nd : s.post.Nodup
  post_mem : ∀ x, x ∈ s.post ↔ (x < 2 * G.E ∧ s.st x = 2) ∨
    (2 * G.E ≤ x ∧ s.st (x - 2 * G.E) = 2 ∧ 2 * G.E ≤ s.par (x - 2 * G.E))
  post_desc : ∀ u c, u ∈ s.post → u < 2 * G.E → s.st c ≠ 0 → (G.fd s).Desc u c → c ≠ u → Before s.post c u
  post_top : ∀ u c, 2 * G.E + u ∈ s.post → s.st c ≠ 0 → (G.fd s).Desc u c → Before s.post c (2 * G.E + u)

variable {G}

theorem mem_darts {u d : Nat} : d ∈ G.darts u ↔ d < 2 * G.E ∧ G.rep d = u := by
  simp [darts]

theorem darts_nodup (u : Nat) : (G.darts u).Nodup := List.nodup_range.filter _

theorem getD_of_lt {l : List Nat} {k : Nat} (h : k < l.length) : l.getD k 0 = l[k] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_mem {l : List Nat} {k : Nat} (h : k < l.length) : l.getD k 0 ∈ l := by
  rw [getD_of_lt h]; exact List.getElem_mem h

theorem exists_getD {l : List Nat} {d : Nat} (h : d ∈ l) : ∃ k, k < l.length ∧ l.getD k 0 = d := by
  obtain ⟨k, hk, he⟩ := List.getElem_of_mem h
  exact ⟨k, hk, by rw [getD_of_lt hk, he]⟩

theorem getD_inj {l : List Nat} (hnd : l.Nodup) {k k' : Nat} (hk : k < l.length) (hk' : k' < l.length)
    (h : l.getD k 0 = l.getD k' 0) : k = k' := by
  induction l generalizing k k' with
  | nil => simp at hk
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := List.nodup_cons.mp hnd
    cases k with
    | zero =>
      cases k' with
      | zero => rfl
      | succ k' =>
        simp only [List.getD_cons_zero, List.getD_cons_succ] at h
        simp at hk'
        exact absurd (h ▸ getD_mem (l := l) (by omega)) h1
    | succ k =>
      cases k' with
      | zero =>
        simp only [List.getD_cons_zero, List.getD_cons_succ] at h
        simp at hk
        exact absurd (h.symm ▸ getD_mem (l := l) (by omega)) h1
      | succ k' =>
        simp only [List.getD_cons_succ] at h
        simp at hk hk'
        have := ih h2 (by omega) (by omega) h
        omega

theorem before_snoc {l : List Nat} {c x : Nat} (h : c ∈ l) : Before (l ++ [x]) c x :=
  before_append_mid h (List.mem_singleton_self x)

/-- The next dart lies at the current vertex. -/
theorem nd_mem {s : DS} (h : s.ptr s.cur < (G.darts s.cur).length) : G.nd s ∈ G.darts s.cur :=
  getD_mem h

section ok

variable (hG : G.Ok)
include hG

theorem nw_facts {s : DS} (h : s.ptr s.cur < (G.darts s.cur).length) :
    G.nd s < 2 * G.E ∧ G.rep (G.nd s) = s.cur ∧ G.nw s < 2 * G.E ∧ G.rep (G.nw s) = G.nw s ∧ G.nw s ≠ s.cur := by
  obtain ⟨h1, h2⟩ := mem_darts.mp (nd_mem h)
  refine ⟨h1, h2, hG.rep_lt _ (pair_lt h1), hG.rep_rep _ (pair_lt h1), ?_⟩
  unfold nw; rw [← h2]; exact hG.noloop _ h1

/-! ### Exploring a dart to an unvisited vertex -/

theorem inv_exploreNew {s : DS} (hI : G.Inv s) (hi : s.inner = true)
    (hp : s.ptr s.cur < (G.darts s.cur).length) (hw : s.st (G.nw s) = 0) : G.Inv (G.step s) := by
  obtain ⟨hdl, hdr, hwl, hwr, hwc⟩ := nw_facts hG hp
  have hwd : G.nw s = G.rep (pair (G.nd s)) := rfl
  have hnd : (G.darts s.cur).getD (s.ptr s.cur) 0 = G.nd s := rfl
  obtain ⟨s', hs'⟩ : ∃ s' : DS, s' = { s with
      ptr := upd s.ptr s.cur (s.ptr s.cur + 1)
      ex := s.ex ++ [G.nd s]
      st := upd s.st (G.nw s) 1
      par := upd s.par (G.nw s) (pair (G.nd s))
      depth := upd s.depth (G.nw s) (s.depth s.cur + 1)
      H := max s.H (s.depth s.cur + 2)
      cur := G.nw s
      vl := s.vl ++ [G.nw s] } := ⟨_, rfl⟩
  have hstep : G.step s = s' := by rw [hs', step, ite_eq_left hi, ite_eq_left hp, ite_eq_left hw]
  rw [hstep]
  have e_st : s'.st = upd s.st (G.nw s) 1 := by rw [hs']
  have e_par : s'.par = upd s.par (G.nw s) (pair (G.nd s)) := by rw [hs']
  have e_depth : s'.depth = upd s.depth (G.nw s) (s.depth s.cur + 1) := by rw [hs']
  have e_ptr : s'.ptr = upd s.ptr s.cur (s.ptr s.cur + 1) := by rw [hs']
  have e_H : s'.H = max s.H (s.depth s.cur + 2) := by rw [hs']
  have e_cur : s'.cur = G.nw s := by rw [hs']
  have e_inner : s'.inner = s.inner := by rw [hs']
  have e_r : s'.r = s.r := by rw [hs']
  have e_post : s'.post = s.post := by rw [hs']
  have e_vl : s'.vl = s.vl ++ [G.nw s] := by rw [hs']
  have e_ex : s'.ex = s.ex ++ [G.nd s] := by rw [hs']
  clear hs' hstep
  generalize G.nd s = d at hdl hdr hwd hnd e_par e_ex
  generalize G.nw s = w at hwl hwr hwc hw hwd e_st e_par e_depth e_cur e_vl
  obtain ⟨hcur1, hpath⟩ := hI.path hi
  have hcw : s.cur ≠ w := Ne.symm hwc
  have hvis : ∀ u, s.st u ≠ 0 → u ≠ w := fun u hu e => hu (e ▸ hw)
  have hcurv : s.st s.cur ≠ 0 := by omega
  -- the new forest
  have hparF : ∀ u, s.st u ≠ 0 → (G.fd s').par u = (G.fd s).par u := fun u hu => by
    show s'.par u = s.par u; rw [e_par, upd_ne _ _ (hvis u hu)]
  have hcl : ∀ u, s.st u ≠ 0 → s.st ((G.fd s).up u) ≠ 0 := fun u hu => ForestData.treeOn_up hI.tree hu
  have hdesc : ∀ v u, s.st u ≠ 0 → ((G.fd s').Desc v u ↔ (G.fd s).Desc v u) := fun v u hu =>
    ForestData.desc_congr (F := G.fd s) (F' := G.fd s') (P := fun u => s.st u ≠ 0) rfl rfl hparF hcl hu
  have hwroot : ¬ (G.fd s').IsRoot w := by
    show ¬ 2 * G.E ≤ s'.par w
    rw [e_par, upd_same]; have := pair_lt hdl; omega
  have hwup : (G.fd s').up w = s.cur := by
    show (if (G.fd s').IsRoot w then w else G.rep (pair (s'.par w))) = s.cur
    rw [ite_eq_right hwroot, e_par, upd_same, pair_pair, hdr]
  have hT' : ∀ u, s.st u ≠ 0 → (G.fd s').up u = (G.fd s).up u := by
    intro u hu
    have := ForestData.iterate_up_congr (F := G.fd s) (F' := G.fd s') (P := fun u => s.st u ≠ 0) rfl rfl
      hparF hcl 1 u hu
    exact this
  have hdescw : ∀ v, (G.fd s').Desc v w ↔ v = w ∨ (G.fd s).Desc v s.cur := by
    intro v
    rw [ForestData.desc_nonroot_iff hwroot, hwup, hdesc v s.cur hcurv]
  have hst' : ∀ u, s'.st u ≠ 0 ↔ s.st u ≠ 0 ∨ u = w := by
    intro u; rw [e_st]; by_cases h : u = w
    · subst h; simp
    · rw [upd_ne _ _ h]; simp [h]
  have hst2 : ∀ u, s'.st u = 2 ↔ s.st u = 2 := by
    intro u; rw [e_st]; by_cases h : u = w
    · subst h; simp [hw]
    · rw [upd_ne _ _ h]
  have hst1 : ∀ u, s'.st u = 1 ↔ u = w ∨ s.st u = 1 := by
    intro u; rw [e_st]; by_cases h : u = w
    · subst h; simp
    · rw [upd_ne _ _ h]; simp [h]
  have hptr : ∀ u, s'.ptr u = if u = s.cur then s.ptr s.cur + 1 else s.ptr u := fun u => by rw [e_ptr]; rfl
  have hdepth : ∀ u, u ≠ w → s'.depth u = s.depth u := fun u h => by rw [e_depth, upd_ne _ _ h]
  have htree : (G.fd s').IsTree d := by
    right
    refine ⟨?_, ?_⟩
    · show ¬ 2 * G.E ≤ s'.par (G.rep (pair d))
      rw [← hwd, e_par, upd_same]; have := pair_lt hdl; omega
    · show s'.par (G.rep (pair d)) = pair d
      rw [← hwd, e_par, upd_same]
  have htreeT : ∀ e, (G.fd s).IsTree e → s.st (G.rep e) ≠ 0 →
      ((G.fd s).IsUp (pair e) → s.st (G.rep (pair e)) ≠ 0) → (G.fd s').IsTree e := by
    intro e ht he hpe
    rcases ht with hu | hdn
    · left
      have hne := hvis _ he
      exact ⟨by show ¬ 2 * G.E ≤ s'.par (G.rep e); rw [e_par, upd_ne _ _ hne]; exact hu.1,
        by show s'.par (G.rep e) = e; rw [e_par, upd_ne _ _ hne]; exact hu.2⟩
    · right
      have hne := hvis _ (hpe hdn)
      exact ⟨by show ¬ 2 * G.E ≤ s'.par (G.rep (pair e)); rw [e_par, upd_ne _ _ hne]; exact hdn.1,
        by show s'.par (G.rep (pair e)) = pair e; rw [e_par, upd_ne _ _ hne]; exact hdn.2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- vert
  · intro u hu
    rcases (hst' u).mp hu with h | rfl
    · exact hI.vert u h
    · exact ⟨hwl, hwr⟩
  -- st_le
  · intro u; rw [e_st]; by_cases h : u = w
    · subst h; simp
    · rw [upd_ne _ _ h]; exact hI.st_le u
  -- tree
  · intro u hu
    rcases (hst' u).mp hu with h | rfl
    · have hT := hI.tree u h
      have hne := hvis u h
      have hr : (G.fd s').IsRoot u ↔ (G.fd s).IsRoot u := by
        show 2 * G.E ≤ s'.par u ↔ 2 * G.E ≤ s.par u; rw [e_par, upd_ne _ _ hne]
      have hup := hT' u h
      refine ⟨fun h' => ?_, fun h' => ?_⟩
      · show s'.depth u = 0; rw [hdepth u hne]; exact hT.1 (hr.mp h')
      · obtain ⟨h1, h2⟩ := hT.2 (fun h'' => h' (hr.mpr h''))
        refine ⟨(hst' _).mpr (Or.inl (by rw [hup]; exact h1)), ?_⟩
        show s'.depth u = s'.depth ((G.fd s').up u) + 1
        rw [hup, hdepth u hne, hdepth _ (hvis _ h1)]; exact h2
    · refine ⟨fun h' => absurd h' hwroot, fun _ => ⟨?_, ?_⟩⟩
      · rw [hwup]; exact (hst' _).mpr (Or.inl hcurv)
      · show s'.depth u = s'.depth ((G.fd s').up u) + 1
        rw [hwup, e_depth, upd_same, upd_ne _ _ hcw]
  -- parv
  · intro u hu hpl
    rcases (hst' u).mp hu with h | rfl
    · have hne := hvis u h
      rw [e_par, upd_ne _ _ hne] at hpl ⊢
      exact hI.parv u h hpl
    · rw [e_par, upd_same]; exact hwd.symm
  -- hbound
  · intro u hu
    rw [e_H]
    rcases (hst' u).mp hu with h | rfl
    · rw [hdepth u (hvis u h)]; have := hI.hbound u h; omega
    · rw [e_depth, upd_same]; omega
  -- path
  · intro _
    rw [e_cur]
    refine ⟨(hst1 w).mpr (Or.inl rfl), fun u => ?_⟩
    rw [hdescw u, hst1 u, hpath u]
  -- closed
  · intro h; rw [e_inner] at h; rw [hi] at h; simp at h
  -- ptr_le
  · intro u
    rw [hptr]; split
    · rename_i h; subst h; omega
    · exact hI.ptr_le u
  -- ptr0
  · intro u hu
    have h1 : u ≠ w := by intro e; subst e; rw [e_st, upd_same] at hu; simp at hu
    rw [e_st, upd_ne _ _ h1] at hu
    have h2 : u ≠ s.cur := by intro e; subst e; omega
    rw [hptr, ite_eq_right h2]; exact hI.ptr0 u hu
  -- ptr2
  · intro u hu
    rw [hst2] at hu
    have h2 : u ≠ s.cur := by intro e; subst e; omega
    rw [hptr, ite_eq_right h2]; exact hI.ptr2 u hu
  -- expl
  · intro u hu k hk
    rw [hst']
    rw [hptr] at hk
    rcases (hst' u).mp hu with h | rfl
    · split at hk
      · rename_i he; subst he
        by_cases hkk : k < s.ptr s.cur
        · exact Or.inl (hI.expl _ h k hkk)
        · have : k = s.ptr s.cur := by omega
          subst this; rw [hnd, ← hwd]; exact Or.inr rfl
      · exact Or.inl (hI.expl u h k hk)
    · rw [ite_eq_right hwc, hI.ptr0 _ hw] at hk; omega
  -- finN
  · intro u hu e he
    rw [hst2] at hu ⊢
    rw [hdesc _ u (by omega)]
    exact hI.finN u hu e he
  -- back
  · intro u hu k hk
    rw [hptr] at hk
    rcases (hst' u).mp hu with h | rfl
    · have old : ∀ k, k < s.ptr u → (G.fd s').IsTree ((G.darts u).getD k 0) ∨
          (G.fd s').Desc (G.rep (pair ((G.darts u).getD k 0))) u ∨
          (G.fd s').Desc u (G.rep (pair ((G.darts u).getD k 0))) := by
        intro k hk
        have hx := hI.expl u h k hk
        rcases hI.back u h k hk with h1 | h1 | h1
        · have hkl : k < (G.darts u).length := by have := hI.ptr_le u; omega
          have hrep : G.rep ((G.darts u).getD k 0) = u := (mem_darts.mp (getD_mem hkl)).2
          exact Or.inl (htreeT _ h1 (by rw [hrep]; exact h) (fun _ => hx))
        · exact Or.inr (Or.inl ((hdesc _ u h).mpr h1))
        · exact Or.inr (Or.inr ((hdesc _ _ hx).mpr h1))
      split at hk
      · rename_i he; subst he
        by_cases hkk : k < s.ptr s.cur
        · exact old k hkk
        · have : k = s.ptr s.cur := by omega
          subst this; rw [hnd]; exact Or.inl htree
      · exact old k hk
    · rw [ite_eq_right hwc, hI.ptr0 _ hw] at hk; omega
  -- scan
  · intro u hu hl hr
    rw [e_r] at hu
    exact (hst' u).mpr (Or.inl (hI.scan u hu hl hr))
  -- scanR
  · intro _
    obtain ⟨h1, h2, h3, h4⟩ := hI.scanR hi
    rw [e_r, e_cur]
    refine ⟨h1, (hdescw _).mpr (Or.inr h2), ?_, (hst' _).mpr (Or.inl h4)⟩
    rw [e_par, upd_ne _ _ (hvis _ h4)]; exact h3
  -- vl_nd
  · rw [e_vl]
    refine List.nodup_append.mpr ⟨hI.vl_nd, nodup_one w, fun a ha b hb e => ?_⟩
    rw [List.mem_singleton] at hb; subst hb; subst e
    exact (hI.vl_mem _).mp ha hw
  -- vl_mem
  · intro u
    rw [hst', e_vl, List.mem_append, List.mem_singleton, hI.vl_mem]
  -- ex_nd
  · rw [e_ex]
    refine List.nodup_append.mpr ⟨hI.ex_nd, nodup_one d, fun a ha b hb e => ?_⟩
    rw [List.mem_singleton] at hb; subst hb; subst e
    obtain ⟨u, hu, k, hk, hke⟩ := (hI.ex_mem _).mp ha
    have hkl : k < (G.darts u).length := by have := hI.ptr_le u; omega
    have hu' : u = s.cur := by rw [← (mem_darts.mp (getD_mem hkl)).2, hke]; exact hdr
    subst hu'
    have := getD_inj (darts_nodup _) hkl hp (hke.trans hnd.symm)
    omega
  -- ex_mem
  · intro e
    rw [e_ex, List.mem_append, List.mem_singleton, hI.ex_mem]
    constructor
    · rintro (⟨u, hu, k, hk, he⟩ | rfl)
      · refine ⟨u, (hst' u).mpr (Or.inl hu), k, ?_, he⟩
        rw [hptr]; split
        · rename_i h'; subst h'; omega
        · exact hk
      · exact ⟨s.cur, (hst' _).mpr (Or.inl hcurv), s.ptr s.cur, by rw [hptr, ite_eq_left rfl]; omega, hnd⟩
    · rintro ⟨u, hu, k, hk, he⟩
      rw [hptr] at hk
      rcases (hst' u).mp hu with h | rfl
      · split at hk
        · rename_i hu'; subst hu'
          by_cases hkk : k < s.ptr s.cur
          · exact Or.inl ⟨_, h, k, hkk, he⟩
          · have : k = s.ptr s.cur := by omega
            subst this; exact Or.inr (he.symm.trans hnd)
        · exact Or.inl ⟨u, h, k, hk, he⟩
      · rw [ite_eq_right hwc, hI.ptr0 _ hw] at hk; omega
  -- post_nd
  · rw [e_post]; exact hI.post_nd
  -- post_mem
  · intro x
    rw [e_post, hst2, hst2, hI.post_mem]
    constructor
    · rintro (h | ⟨h1, h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2, by rw [e_par, upd_ne _ _ (hvis _ (by omega))]; exact h3⟩
    · rintro (h | ⟨h1, h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2, by rw [e_par, upd_ne _ _ (hvis _ (by omega))] at h3; exact h3⟩
  -- post_desc
  · intro u c hu hul hc hd hcu
    rw [e_post] at hu ⊢
    have hu2 : s.st u = 2 := by
      rcases (hI.post_mem u).mp hu with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · omega
    rcases (hst' c).mp hc with h | rfl
    · exact hI.post_desc u c hu hul h ((hdesc u c h).mp hd) hcu
    · rcases (hdescw u).mp hd with h | h
      · exact absurd h hcu.symm
      · have := (hpath u).mpr h; omega
  -- post_top
  · intro u c hu hc hd
    rw [e_post] at hu ⊢
    have hu2 : s.st u = 2 := by
      rcases (hI.post_mem _).mp hu with ⟨h, _⟩ | ⟨_, h, _⟩
      · omega
      · simpa using h
    rcases (hst' c).mp hc with h | rfl
    · exact hI.post_top u c hu h ((hdesc u c h).mp hd)
    · rcases (hdescw u).mp hd with h | h
      · subst h; omega
      · have := (hpath u).mpr h; omega

/-! ### Exploring a dart to a visited vertex -/

theorem inv_exploreOld {s : DS} (hI : G.Inv s) (hi : s.inner = true)
    (hp : s.ptr s.cur < (G.darts s.cur).length) (hw : s.st (G.nw s) ≠ 0) : G.Inv (G.step s) := by
  obtain ⟨hdl, hdr, hwl, hwr, hwc⟩ := nw_facts hG hp
  have hwd : G.nw s = G.rep (pair (G.nd s)) := rfl
  have hnd : (G.darts s.cur).getD (s.ptr s.cur) 0 = G.nd s := rfl
  obtain ⟨s', hs'⟩ : ∃ s' : DS, s' = { s with
      ptr := upd s.ptr s.cur (s.ptr s.cur + 1)
      ex := s.ex ++ [G.nd s] } := ⟨_, rfl⟩
  have hstep : G.step s = s' := by rw [hs', step, ite_eq_left hi, ite_eq_left hp, ite_eq_right hw]
  rw [hstep]
  have e_st : s'.st = s.st := by rw [hs']
  have e_ptr : s'.ptr = upd s.ptr s.cur (s.ptr s.cur + 1) := by rw [hs']
  have e_cur : s'.cur = s.cur := by rw [hs']
  have e_inner : s'.inner = s.inner := by rw [hs']
  have e_r : s'.r = s.r := by rw [hs']
  have e_post : s'.post = s.post := by rw [hs']
  have e_vl : s'.vl = s.vl := by rw [hs']
  have e_ex : s'.ex = s.ex ++ [G.nd s] := by rw [hs']
  have e_par : s'.par = s.par := by rw [hs']
  have e_depth : s'.depth = s.depth := by rw [hs']
  have e_H : s'.H = s.H := by rw [hs']
  have hfd : G.fd s' = G.fd s := by unfold fd; rw [hs']
  clear hs' hstep
  generalize G.nd s = d at hdl hdr hwd hnd e_ex
  generalize G.nw s = w at hwl hwr hwc hw hwd
  obtain ⟨hcur1, hpath⟩ := hI.path hi
  have hcurv : s.st s.cur ≠ 0 := by omega
  have hptr : ∀ u, s'.ptr u = if u = s.cur then s.ptr s.cur + 1 else s.ptr u := fun u => by rw [e_ptr]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e_st]; exact hI.vert
  · rw [e_st]; exact hI.st_le
  · rw [e_st, hfd]; exact hI.tree
  · rw [e_st, e_par]; exact hI.parv
  · rw [e_st, e_depth, e_H]; exact hI.hbound
  · rw [e_inner, e_st, e_cur, hfd]; exact hI.path
  · rw [e_inner, e_st]; exact hI.closed
  · intro u; rw [hptr]; split
    · rename_i h; subst h; omega
    · exact hI.ptr_le u
  · intro u hu; rw [e_st] at hu
    have : u ≠ s.cur := by intro e; subst e; omega
    rw [hptr, ite_eq_right this]; exact hI.ptr0 u hu
  · intro u hu; rw [e_st] at hu
    have : u ≠ s.cur := by intro e; subst e; omega
    rw [hptr, ite_eq_right this]; exact hI.ptr2 u hu
  · intro u hu k hk
    rw [e_st] at hu ⊢
    rw [hptr] at hk
    split at hk
    · rename_i he; subst he
      by_cases hkk : k < s.ptr s.cur
      · exact hI.expl _ hu k hkk
      · have : k = s.ptr s.cur := by omega
        subst this; rw [hnd, ← hwd]; exact hw
    · exact hI.expl u hu k hk
  · rw [e_st, hfd]; exact hI.finN
  · intro u hu k hk
    rw [e_st] at hu
    rw [hptr] at hk
    rw [hfd]
    split at hk
    · rename_i he; subst he
      by_cases hkk : k < s.ptr s.cur
      · exact hI.back _ hu k hkk
      · have : k = s.ptr s.cur := by omega
        subst this; rw [hnd, ← hwd]
        have hw2 := hI.st_le w
        by_cases h1 : s.st w = 1
        · exact Or.inr (Or.inl ((hpath w).mp h1))
        · have h2 : s.st w = 2 := by omega
          have hpd : pair d ∈ G.darts w := mem_darts.mpr ⟨pair_lt hdl, hwd.symm⟩
          rcases hI.finN w h2 (pair d) hpd with h | h
          · rw [pair_pair, hdr] at h; omega
          · rw [pair_pair, hdr] at h; exact Or.inr (Or.inr h)
    · exact hI.back u hu k hk
  · rw [e_r, e_st]; exact hI.scan
  · rw [e_inner, e_r, e_cur, e_par, e_st, hfd]; exact hI.scanR
  · rw [e_vl]; exact hI.vl_nd
  · rw [e_vl, e_st]; exact hI.vl_mem
  · rw [e_ex]
    refine List.nodup_append.mpr ⟨hI.ex_nd, nodup_one d, fun a ha b hb e => ?_⟩
    rw [List.mem_singleton] at hb; subst hb; subst e
    obtain ⟨u, hu, k, hk, hke⟩ := (hI.ex_mem _).mp ha
    have hkl : k < (G.darts u).length := by have := hI.ptr_le u; omega
    have hu' : u = s.cur := by rw [← (mem_darts.mp (getD_mem hkl)).2, hke]; exact hdr
    subst hu'
    have := getD_inj (darts_nodup _) hkl hp (hke.trans hnd.symm)
    omega
  · intro e
    rw [e_ex, List.mem_append, List.mem_singleton, hI.ex_mem, e_st]
    constructor
    · rintro (⟨u, hu, k, hk, he⟩ | rfl)
      · refine ⟨u, hu, k, ?_, he⟩
        rw [hptr]; split
        · rename_i h'; subst h'; omega
        · exact hk
      · exact ⟨s.cur, hcurv, s.ptr s.cur, by rw [hptr, ite_eq_left rfl]; omega, hnd⟩
    · rintro ⟨u, hu, k, hk, he⟩
      rw [hptr] at hk
      split at hk
      · rename_i hu'; subst hu'
        by_cases hkk : k < s.ptr s.cur
        · exact Or.inl ⟨_, hu, k, hkk, he⟩
        · have : k = s.ptr s.cur := by omega
          subst this; exact Or.inr (he.symm.trans hnd)
      · exact Or.inl ⟨u, hu, k, hk, he⟩
  · rw [e_post]; exact hI.post_nd
  · rw [e_post, e_st, e_par]; exact hI.post_mem
  · rw [e_post, e_st, hfd]; exact hI.post_desc
  · rw [e_post, e_st, hfd]; exact hI.post_top

/-! ### Finishing a vertex -/

omit hG in
theorem treeOn_congr {F : ForestData} {P Q : Nat → Prop} (h : ∀ u, P u ↔ Q u) (hT : F.TreeOn P) : F.TreeOn Q := by
  have : P = Q := funext fun u => propext (h u)
  rw [← this]; exact hT

/-- The neighbours of the current vertex, once all its darts are explored, are finished or its
ancestors. -/
theorem fin_neighbours {s : DS} (hI : G.Inv s) (hi : s.inner = true)
    (hp : ¬ s.ptr s.cur < (G.darts s.cur).length) :
    ∀ e ∈ G.darts s.cur, s.st (G.rep (pair e)) = 2 ∨ (s.st (G.rep (pair e)) = 1 ∧
      (G.fd s).Desc (G.rep (pair e)) s.cur ∧ G.rep (pair e) ≠ s.cur) := by
  intro e he
  have hlen : s.ptr s.cur = (G.darts s.cur).length := by have := hI.ptr_le s.cur; omega
  obtain ⟨hcur1, hpath⟩ := hI.path hi
  obtain ⟨k, hk, hke⟩ := exists_getD he
  have hx := hI.expl s.cur (by omega) k (by omega)
  rw [hke] at hx
  have h2 := hI.st_le (G.rep (pair e))
  obtain ⟨hel, her⟩ := mem_darts.mp he
  by_cases h1 : s.st (G.rep (pair e)) = 1
  · exact Or.inr ⟨h1, (hpath _).mp h1, by rw [← her]; exact hG.noloop e hel⟩
  · left; omega

theorem inv_finishRoot {s : DS} (hI : G.Inv s) (hi : s.inner = true)
    (hp : ¬ s.ptr s.cur < (G.darts s.cur).length) (hr : 2 * G.E ≤ s.par s.cur) : G.Inv (G.step s) := by
  obtain ⟨s', hs'⟩ : ∃ s' : DS, s' = { s with
      st := upd s.st s.cur 2
      post := s.post ++ [s.cur, 2 * G.E + s.cur]
      inner := false
      r := s.r + 1 } := ⟨_, rfl⟩
  have hstep : G.step s = s' := by rw [hs', step, ite_eq_left hi, ite_eq_right hp, ite_eq_left hr]
  rw [hstep]
  have e_st : s'.st = upd s.st s.cur 2 := by rw [hs']
  have e_ptr : s'.ptr = s.ptr := by rw [hs']
  have e_inner : s'.inner = false := by rw [hs']
  have e_r : s'.r = s.r + 1 := by rw [hs']
  have e_post : s'.post = s.post ++ [s.cur, 2 * G.E + s.cur] := by rw [hs']
  have e_vl : s'.vl = s.vl := by rw [hs']
  have e_ex : s'.ex = s.ex := by rw [hs']
  have e_par : s'.par = s.par := by rw [hs']
  have e_depth : s'.depth = s.depth := by rw [hs']
  have e_H : s'.H = s.H := by rw [hs']
  have hfd : G.fd s' = G.fd s := by unfold fd; rw [hs']
  clear hs' hstep
  obtain ⟨hcur1, hpath⟩ := hI.path hi
  have hcurv : s.st s.cur ≠ 0 := by omega
  obtain ⟨hcl, hcr⟩ := hI.vert s.cur hcurv
  have hlen : s.ptr s.cur = (G.darts s.cur).length := by have := hI.ptr_le s.cur; omega
  have hroot : (G.fd s).IsRoot s.cur := hr
  have hrc : s.r = s.cur := by
    obtain ⟨_, h2, _, _⟩ := hI.scanR hi
    exact (ForestData.desc_root_iff hroot).mp h2
  have hopen : ∀ u, s.st u = 1 → u = s.cur := fun u h => (ForestData.desc_root_iff hroot).mp ((hpath u).mp h)
  have hst' : ∀ u, s'.st u ≠ 0 ↔ s.st u ≠ 0 := by
    intro u; rw [e_st]; by_cases h : u = s.cur
    · subst h; simp; omega
    · rw [upd_ne _ _ h]
  have hst2 : ∀ u, s'.st u = 2 ↔ s.st u = 2 ∨ u = s.cur := by
    intro u; rw [e_st]; by_cases h : u = s.cur
    · subst h; simp
    · rw [upd_ne _ _ h]; simp [h]
  have hfinC : ∀ c, s.st c ≠ 0 → (G.fd s).Desc s.cur c → c ≠ s.cur → s.st c = 2 := by
    intro c hc hd hne
    have := hI.st_le c
    by_cases h1 : s.st c = 1
    · exact absurd (hopen c h1) hne
    · omega
  have hcurP : s.cur ∉ s.post := by
    rw [hI.post_mem]; rintro (⟨_, h⟩ | ⟨h, _⟩) <;> omega
  have htopP : 2 * G.E + s.cur ∉ s.post := by
    rw [hI.post_mem]; rintro (⟨h, _⟩ | ⟨_, h, _⟩)
    · omega
    · rw [show 2 * G.E + s.cur - 2 * G.E = s.cur by omega] at h; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu; exact hI.vert u ((hst' u).mp hu)
  · intro u; rw [e_st]; by_cases h : u = s.cur
    · subst h; simp
    · rw [upd_ne _ _ h]; exact hI.st_le u
  · rw [hfd]; exact treeOn_congr (fun u => (hst' u).symm) hI.tree
  · intro u hu; rw [e_par]; exact hI.parv u ((hst' u).mp hu)
  · intro u hu; rw [e_depth, e_H]; exact hI.hbound u ((hst' u).mp hu)
  · intro h; rw [e_inner] at h; simp at h
  · intro _ u
    rw [e_st]; by_cases h : u = s.cur
    · subst h; simp
    · rw [upd_ne _ _ h]; exact fun h1 => h (hopen u h1)
  · rw [e_ptr]; exact hI.ptr_le
  · intro u hu; rw [e_ptr]
    have : s.st u = 0 := by
      apply Classical.byContradiction; intro h; exact ((hst' u).mpr h) hu
    exact hI.ptr0 u this
  · intro u hu; rw [e_ptr]
    rcases (hst2 u).mp hu with h | rfl
    · exact hI.ptr2 u h
    · exact hlen
  · intro u hu k hk
    rw [e_ptr] at hk
    exact (hst' _).mpr (hI.expl u ((hst' u).mp hu) k hk)
  · intro w hw e he
    rw [hfd, hst2]
    rcases (hst2 w).mp hw with h | rfl
    · rcases hI.finN w h e he with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
    · rcases fin_neighbours hG hI hi hp e he with h' | ⟨h1, _, hne⟩
      · exact Or.inl (Or.inl h')
      · exact absurd (hopen _ h1) hne
  · intro u hu k hk
    rw [e_ptr] at hk; rw [hfd]
    exact hI.back u ((hst' u).mp hu) k hk
  · intro u hu hl hrep
    rw [e_r] at hu
    rw [hst']
    by_cases h : u < s.r
    · exact hI.scan u h hl hrep
    · have : u = s.cur := by omega
      subst this; exact hcurv
  · intro h; rw [e_inner] at h; simp at h
  · rw [e_vl]; exact hI.vl_nd
  · intro u; rw [e_vl, hst']; exact hI.vl_mem u
  · rw [e_ex]; exact hI.ex_nd
  · intro d; rw [e_ex, e_ptr]
    rw [hI.ex_mem]
    exact ⟨fun ⟨u, hu, h⟩ => ⟨u, (hst' u).mpr hu, h⟩, fun ⟨u, hu, h⟩ => ⟨u, (hst' u).mp hu, h⟩⟩
  · rw [e_post]
    refine List.nodup_append.mpr ⟨hI.post_nd, ?_, ?_⟩
    · refine List.nodup_cons.mpr ⟨by simp; omega, nodup_one _⟩
    · intro a ha b hb e; subst e
      simp at hb
      rcases hb with rfl | rfl
      · exact hcurP ha
      · exact htopP ha
  · intro x
    rw [e_post, List.mem_append, hI.post_mem, hst2, hst2, e_par]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (((⟨h1, h2⟩ | ⟨h1, h2, h3⟩)) | rfl | rfl)
      · exact Or.inl ⟨h1, Or.inl h2⟩
      · exact Or.inr ⟨h1, Or.inl h2, h3⟩
      · exact Or.inl ⟨hcl, Or.inr rfl⟩
      · exact Or.inr ⟨by omega, Or.inr (by omega), by rw [show 2 * G.E + s.cur - 2 * G.E = s.cur by omega]; exact hr⟩
    · rintro (⟨h1, h2 | rfl⟩ | ⟨h1, h2 | h2, h3⟩)
      · exact Or.inl (Or.inl ⟨h1, h2⟩)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (Or.inr ⟨h1, h2, h3⟩)
      · exact Or.inr (Or.inr (by omega))
  · intro u c hu hul hc hd hcu
    rw [e_post] at hu ⊢
    rw [hfd] at hd
    have hc' := (hst' c).mp hc
    rcases List.mem_append.mp hu with hu | hu
    · exact before_append_left (hI.post_desc u c hu hul hc' hd hcu)
    · simp at hu
      rcases hu with rfl | rfl
      · have h2 := hfinC c hc' hd hcu
        have hcp : c ∈ s.post := (hI.post_mem c).mpr (Or.inl ⟨(hI.vert c hc').1, h2⟩)
        exact before_append_mid hcp (by simp)
      · omega
  · intro u c hu hc hd
    rw [e_post] at hu ⊢
    rw [hfd] at hd
    have hc' := (hst' c).mp hc
    rcases List.mem_append.mp hu with hu | hu
    · exact before_append_left (hI.post_top u c hu hc' hd)
    · simp at hu
      rcases hu with h | h
      · omega
      · have hu' : u = s.cur := by omega
        subst hu'
        by_cases hcc : c = s.cur
        · subst hcc
          exact before_append_right (List.Sublist.refl _)
        · have h2 := hfinC c hc' hd hcc
          have hcp : c ∈ s.post := (hI.post_mem c).mpr (Or.inl ⟨(hI.vert c hc').1, h2⟩)
          exact before_append_mid hcp (by simp)

theorem inv_finishNonroot {s : DS} (hI : G.Inv s) (hi : s.inner = true)
    (hp : ¬ s.ptr s.cur < (G.darts s.cur).length) (hr : ¬ 2 * G.E ≤ s.par s.cur) : G.Inv (G.step s) := by
  obtain ⟨s', hs'⟩ : ∃ s' : DS, s' = { s with
      st := upd s.st s.cur 2
      post := s.post ++ [s.cur]
      cur := G.rep (pair (s.par s.cur)) } := ⟨_, rfl⟩
  have hstep : G.step s = s' := by rw [hs', step, ite_eq_left hi, ite_eq_right hp, ite_eq_right hr]
  rw [hstep]
  have e_st : s'.st = upd s.st s.cur 2 := by rw [hs']
  have e_ptr : s'.ptr = s.ptr := by rw [hs']
  have e_inner : s'.inner = s.inner := by rw [hs']
  have e_r : s'.r = s.r := by rw [hs']
  have e_cur : s'.cur = G.rep (pair (s.par s.cur)) := by rw [hs']
  have e_post : s'.post = s.post ++ [s.cur] := by rw [hs']
  have e_vl : s'.vl = s.vl := by rw [hs']
  have e_ex : s'.ex = s.ex := by rw [hs']
  have e_par : s'.par = s.par := by rw [hs']
  have e_depth : s'.depth = s.depth := by rw [hs']
  have e_H : s'.H = s.H := by rw [hs']
  have hfd : G.fd s' = G.fd s := by unfold fd; rw [hs']
  clear hs' hstep
  obtain ⟨hcur1, hpath⟩ := hI.path hi
  have hcurv : s.st s.cur ≠ 0 := by omega
  obtain ⟨hcl, hcr⟩ := hI.vert s.cur hcurv
  have hlen : s.ptr s.cur = (G.darts s.cur).length := by have := hI.ptr_le s.cur; omega
  have hroot : ¬ (G.fd s).IsRoot s.cur := hr
  have hup : (G.fd s).up s.cur = G.rep (pair (s.par s.cur)) := by
    show (if (G.fd s).IsRoot s.cur then s.cur else G.rep (pair (s.par s.cur))) = _
    rw [ite_eq_right hroot]
  have hpv : s.st (G.rep (pair (s.par s.cur))) ≠ 0 := by
    rw [← hup]; exact ((hI.tree s.cur hcurv).2 hroot).1
  have hnotdesc : ¬ (G.fd s).Desc s.cur ((G.fd s).up s.cur) := ForestData.desc_up_not hI.tree hcurv hroot
  have hp1 : s.st (G.rep (pair (s.par s.cur))) = 1 := (hpath _).mpr (by rw [← hup]; exact ForestData.desc_up)
  have hpc : G.rep (pair (s.par s.cur)) ≠ s.cur := by
    intro e; apply hnotdesc; rw [hup, e]; exact ForestData.desc_refl _
  have hst' : ∀ u, s'.st u ≠ 0 ↔ s.st u ≠ 0 := by
    intro u; rw [e_st]; by_cases h : u = s.cur
    · subst h; simp; omega
    · rw [upd_ne _ _ h]
  have hst2 : ∀ u, s'.st u = 2 ↔ s.st u = 2 ∨ u = s.cur := by
    intro u; rw [e_st]; by_cases h : u = s.cur
    · subst h; simp
    · rw [upd_ne _ _ h]; simp [h]
  have hfinC : ∀ c, s.st c ≠ 0 → (G.fd s).Desc s.cur c → c ≠ s.cur → s.st c = 2 := by
    intro c hc hd hne
    have := hI.st_le c
    by_cases h1 : s.st c = 1
    · exact absurd (ForestData.desc_antisymm' hI.tree hcurv ((hpath c).mp h1) hd) hne
    · omega
  have hcurP : s.cur ∉ s.post := by
    rw [hI.post_mem]; rintro (⟨_, h⟩ | ⟨h, _⟩) <;> omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu; exact hI.vert u ((hst' u).mp hu)
  · intro u; rw [e_st]; by_cases h : u = s.cur
    · subst h; simp
    · rw [upd_ne _ _ h]; exact hI.st_le u
  · rw [hfd]; exact treeOn_congr (fun u => (hst' u).symm) hI.tree
  · intro u hu; rw [e_par]; exact hI.parv u ((hst' u).mp hu)
  · intro u hu; rw [e_depth, e_H]; exact hI.hbound u ((hst' u).mp hu)
  · intro _
    rw [e_cur, hfd, e_st, upd_ne _ _ hpc]
    refine ⟨hp1, fun u => ?_⟩
    rw [← hup]
    by_cases h : u = s.cur
    · subst h; simp only [upd_same]
      exact ⟨fun h => by omega, fun h => absurd h hnotdesc⟩
    · rw [upd_ne _ _ h, hpath u, ForestData.desc_nonroot_iff hroot]
      exact ⟨fun h' => h'.resolve_left h, Or.inr⟩
  · intro h; rw [e_inner, hi] at h; simp at h
  · rw [e_ptr]; exact hI.ptr_le
  · intro u hu; rw [e_ptr]
    have : s.st u = 0 := by
      apply Classical.byContradiction; intro h; exact ((hst' u).mpr h) hu
    exact hI.ptr0 u this
  · intro u hu; rw [e_ptr]
    rcases (hst2 u).mp hu with h | rfl
    · exact hI.ptr2 u h
    · exact hlen
  · intro u hu k hk
    rw [e_ptr] at hk
    exact (hst' _).mpr (hI.expl u ((hst' u).mp hu) k hk)
  · intro w hw e he
    rw [hfd, hst2]
    rcases (hst2 w).mp hw with h | rfl
    · rcases hI.finN w h e he with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
    · rcases fin_neighbours hG hI hi hp e he with h' | ⟨_, hd, _⟩
      · exact Or.inl (Or.inl h')
      · exact Or.inr hd
  · intro u hu k hk
    rw [e_ptr] at hk; rw [hfd]
    exact hI.back u ((hst' u).mp hu) k hk
  · intro u hu hl hrep
    rw [e_r] at hu
    exact (hst' u).mpr (hI.scan u hu hl hrep)
  · intro _
    obtain ⟨h1, h2, h3, h4⟩ := hI.scanR hi
    rw [e_r, e_cur, hfd, e_par, hst']
    refine ⟨h1, ?_, h3, h4⟩
    have hrc : s.r ≠ s.cur := by intro e; rw [e] at h3; exact hr h3
    rw [← hup]
    exact ((ForestData.desc_nonroot_iff hroot).mp h2).resolve_left hrc
  · rw [e_vl]; exact hI.vl_nd
  · intro u; rw [e_vl, hst']; exact hI.vl_mem u
  · rw [e_ex]; exact hI.ex_nd
  · intro d; rw [e_ex, e_ptr]
    rw [hI.ex_mem]
    exact ⟨fun ⟨u, hu, h⟩ => ⟨u, (hst' u).mpr hu, h⟩, fun ⟨u, hu, h⟩ => ⟨u, (hst' u).mp hu, h⟩⟩
  · rw [e_post]
    refine List.nodup_append.mpr ⟨hI.post_nd, nodup_one _, ?_⟩
    intro a ha b hb e; subst e
    simp at hb; subst hb; exact hcurP ha
  · intro x
    rw [e_post, List.mem_append, hI.post_mem, hst2, hst2, e_par, List.mem_singleton]
    constructor
    · rintro (((⟨h1, h2⟩ | ⟨h1, h2, h3⟩)) | rfl)
      · exact Or.inl ⟨h1, Or.inl h2⟩
      · exact Or.inr ⟨h1, Or.inl h2, h3⟩
      · exact Or.inl ⟨hcl, Or.inr rfl⟩
    · rintro (⟨h1, h2 | rfl⟩ | ⟨h1, h2 | h2, h3⟩)
      · exact Or.inl (Or.inl ⟨h1, h2⟩)
      · exact Or.inr rfl
      · exact Or.inl (Or.inr ⟨h1, h2, h3⟩)
      · rw [h2] at h3; exact absurd h3 hr
  · intro u c hu hul hc hd hcu
    rw [e_post] at hu ⊢
    rw [hfd] at hd
    have hc' := (hst' c).mp hc
    rcases List.mem_append.mp hu with hu | hu
    · exact before_append_left (hI.post_desc u c hu hul hc' hd hcu)
    · rw [List.mem_singleton] at hu; subst hu
      have h2 := hfinC c hc' hd hcu
      have hcp : c ∈ s.post := (hI.post_mem c).mpr (Or.inl ⟨(hI.vert c hc').1, h2⟩)
      exact before_snoc hcp
  · intro u c hu hc hd
    rw [e_post] at hu ⊢
    rw [hfd] at hd
    have hc' := (hst' c).mp hc
    rcases List.mem_append.mp hu with hu | hu
    · exact before_append_left (hI.post_top u c hu hc' hd)
    · rw [List.mem_singleton] at hu; omega

/-! ### Starting a tree, skipping, halting -/

omit hG in
theorem inv_start {s : DS} (hI : G.Inv s) (hi : s.inner = false) (hr : s.r < 2 * G.E)
    (hv : G.rep s.r = s.r ∧ s.st s.r = 0) : G.Inv (G.step s) := by
  obtain ⟨s', hs'⟩ : ∃ s' : DS, s' = { s with
      st := upd s.st s.r 1
      par := upd s.par s.r (2 * G.E)
      depth := upd s.depth s.r 0
      cur := s.r
      inner := true
      vl := s.vl ++ [s.r]
      H := max s.H 1 } := ⟨_, rfl⟩
  have hstep : G.step s = s' := by
    rw [hs', step, ite_eq_right (by rw [hi]; simp), ite_eq_left hr, ite_eq_left hv]
  rw [hstep]
  have e_st : s'.st = upd s.st s.r 1 := by rw [hs']
  have e_par : s'.par = upd s.par s.r (2 * G.E) := by rw [hs']
  have e_depth : s'.depth = upd s.depth s.r 0 := by rw [hs']
  have e_ptr : s'.ptr = s.ptr := by rw [hs']
  have e_H : s'.H = max s.H 1 := by rw [hs']
  have e_cur : s'.cur = s.r := by rw [hs']
  have e_inner : s'.inner = true := by rw [hs']
  have e_r : s'.r = s.r := by rw [hs']
  have e_post : s'.post = s.post := by rw [hs']
  have e_vl : s'.vl = s.vl ++ [s.r] := by rw [hs']
  have e_ex : s'.ex = s.ex := by rw [hs']
  clear hs' hstep
  obtain ⟨hrr, hw⟩ := hv
  have hvis : ∀ u, s.st u ≠ 0 → u ≠ s.r := fun u hu e => hu (e ▸ hw)
  have hclosed := hI.closed hi
  have hparF : ∀ u, s.st u ≠ 0 → (G.fd s').par u = (G.fd s).par u := fun u hu => by
    show s'.par u = s.par u; rw [e_par, upd_ne _ _ (hvis u hu)]
  have hcl : ∀ u, s.st u ≠ 0 → s.st ((G.fd s).up u) ≠ 0 := fun u hu => ForestData.treeOn_up hI.tree hu
  have hdesc : ∀ v u, s.st u ≠ 0 → ((G.fd s').Desc v u ↔ (G.fd s).Desc v u) := fun v u hu =>
    ForestData.desc_congr (F := G.fd s) (F' := G.fd s') (P := fun u => s.st u ≠ 0) rfl rfl hparF hcl hu
  have hT' : ∀ u, s.st u ≠ 0 → (G.fd s').up u = (G.fd s).up u := fun u hu =>
    ForestData.iterate_up_congr (F := G.fd s) (F' := G.fd s') (P := fun u => s.st u ≠ 0) rfl rfl hparF hcl 1 u hu
  have hrroot : (G.fd s').IsRoot s.r := by
    show 2 * G.E ≤ s'.par s.r; rw [e_par, upd_same]; exact Nat.le_refl _
  have hdescr : ∀ v, (G.fd s').Desc v s.r ↔ v = s.r := fun v => ForestData.desc_root_iff hrroot
  have hst' : ∀ u, s'.st u ≠ 0 ↔ s.st u ≠ 0 ∨ u = s.r := by
    intro u; rw [e_st]; by_cases h : u = s.r
    · subst h; simp
    · rw [upd_ne _ _ h]; simp [h]
  have hst2 : ∀ u, s'.st u = 2 ↔ s.st u = 2 := by
    intro u; rw [e_st]; by_cases h : u = s.r
    · subst h; simp [hw]
    · rw [upd_ne _ _ h]
  have hdepth : ∀ u, u ≠ s.r → s'.depth u = s.depth u := fun u h => by rw [e_depth, upd_ne _ _ h]
  have htreeT : ∀ e, (G.fd s).IsTree e → s.st (G.rep e) ≠ 0 →
      ((G.fd s).IsUp (pair e) → s.st (G.rep (pair e)) ≠ 0) → (G.fd s').IsTree e := by
    intro e ht he hpe
    rcases ht with hu | hdn
    · left
      have hne := hvis _ he
      exact ⟨by show ¬ 2 * G.E ≤ s'.par (G.rep e); rw [e_par, upd_ne _ _ hne]; exact hu.1,
        by show s'.par (G.rep e) = e; rw [e_par, upd_ne _ _ hne]; exact hu.2⟩
    · right
      have hne := hvis _ (hpe hdn)
      exact ⟨by show ¬ 2 * G.E ≤ s'.par (G.rep (pair e)); rw [e_par, upd_ne _ _ hne]; exact hdn.1,
        by show s'.par (G.rep (pair e)) = pair e; rw [e_par, upd_ne _ _ hne]; exact hdn.2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    rcases (hst' u).mp hu with h | rfl
    · exact hI.vert u h
    · exact ⟨hr, hrr⟩
  · intro u; rw [e_st]; by_cases h : u = s.r
    · subst h; simp
    · rw [upd_ne _ _ h]; exact hI.st_le u
  · intro u hu
    rcases (hst' u).mp hu with h | rfl
    · have hT := hI.tree u h
      have hne := hvis u h
      have hrt : (G.fd s').IsRoot u ↔ (G.fd s).IsRoot u := by
        show 2 * G.E ≤ s'.par u ↔ 2 * G.E ≤ s.par u; rw [e_par, upd_ne _ _ hne]
      have hup := hT' u h
      refine ⟨fun h' => ?_, fun h' => ?_⟩
      · show s'.depth u = 0; rw [hdepth u hne]; exact hT.1 (hrt.mp h')
      · obtain ⟨h1, h2⟩ := hT.2 (fun h'' => h' (hrt.mpr h''))
        refine ⟨(hst' _).mpr (Or.inl (by rw [hup]; exact h1)), ?_⟩
        show s'.depth u = s'.depth ((G.fd s').up u) + 1
        rw [hup, hdepth u hne, hdepth _ (hvis _ h1)]; exact h2
    · exact ⟨fun _ => by show s'.depth _ = 0; rw [e_depth, upd_same], fun h => absurd hrroot h⟩
  · intro u hu hpl
    rcases (hst' u).mp hu with h | rfl
    · have hne := hvis u h
      rw [e_par, upd_ne _ _ hne] at hpl ⊢
      exact hI.parv u h hpl
    · rw [e_par, upd_same] at hpl; omega
  · intro u hu
    rw [e_H]
    rcases (hst' u).mp hu with h | rfl
    · rw [hdepth u (hvis u h)]; have := hI.hbound u h; omega
    · rw [e_depth, upd_same]; omega
  · intro _
    rw [e_cur]
    refine ⟨by rw [e_st, upd_same], fun u => ?_⟩
    rw [hdescr u, e_st]
    by_cases h : u = s.r
    · subst h; simp
    · rw [upd_ne _ _ h]; exact ⟨fun h' => absurd h' (hclosed u), fun h' => absurd h' h⟩
  · intro h; rw [e_inner] at h; simp at h
  · rw [e_ptr]; exact hI.ptr_le
  · intro u hu; rw [e_ptr]
    have h1 : u ≠ s.r := by intro e; subst e; rw [e_st, upd_same] at hu; simp at hu
    rw [e_st, upd_ne _ _ h1] at hu
    exact hI.ptr0 u hu
  · intro u hu; rw [e_ptr]; rw [hst2] at hu; exact hI.ptr2 u hu
  · intro u hu k hk
    rw [e_ptr] at hk
    rw [hst']
    rcases (hst' u).mp hu with h | rfl
    · exact Or.inl (hI.expl u h k hk)
    · rw [hI.ptr0 _ hw] at hk; omega
  · intro u hu e he
    rw [hst2] at hu ⊢
    rw [hdesc _ u (by omega)]
    exact hI.finN u hu e he
  · intro u hu k hk
    rw [e_ptr] at hk
    rcases (hst' u).mp hu with h | rfl
    · have hx := hI.expl u h k hk
      rcases hI.back u h k hk with h1 | h1 | h1
      · have hkl : k < (G.darts u).length := by have := hI.ptr_le u; omega
        have hrep : G.rep ((G.darts u).getD k 0) = u := (mem_darts.mp (getD_mem hkl)).2
        exact Or.inl (htreeT _ h1 (by rw [hrep]; exact h) (fun _ => hx))
      · exact Or.inr (Or.inl ((hdesc _ u h).mpr h1))
      · exact Or.inr (Or.inr ((hdesc _ _ hx).mpr h1))
    · rw [hI.ptr0 _ hw] at hk; omega
  · intro u hu hl hrep
    rw [e_r] at hu
    exact (hst' u).mpr (Or.inl (hI.scan u hu hl hrep))
  · intro _
    rw [e_r, e_cur]
    exact ⟨hr, ForestData.desc_refl _, by rw [e_par, upd_same]; exact Nat.le_refl _, by rw [e_st, upd_same]; simp⟩
  · rw [e_vl]
    refine List.nodup_append.mpr ⟨hI.vl_nd, nodup_one _, fun a ha b hb e => ?_⟩
    rw [List.mem_singleton] at hb; subst hb; subst e
    exact (hI.vl_mem _).mp ha hw
  · intro u
    rw [hst', e_vl, List.mem_append, List.mem_singleton, hI.vl_mem]
  · rw [e_ex]; exact hI.ex_nd
  · intro d; rw [e_ex, e_ptr, hI.ex_mem]
    constructor
    · rintro ⟨u, hu, h⟩; exact ⟨u, (hst' u).mpr (Or.inl hu), h⟩
    · rintro ⟨u, hu, k, hk, h⟩
      rcases (hst' u).mp hu with h' | rfl
      · exact ⟨u, h', k, hk, h⟩
      · rw [hI.ptr0 _ hw] at hk; omega
  · rw [e_post]; exact hI.post_nd
  · intro x
    rw [e_post, hst2, hst2, hI.post_mem]
    constructor
    · rintro (h | ⟨h1, h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2, by rw [e_par, upd_ne _ _ (hvis _ (by omega))]; exact h3⟩
    · rintro (h | ⟨h1, h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2, by rw [e_par, upd_ne _ _ (hvis _ (by omega))] at h3; exact h3⟩
  · intro u c hu hul hc hd hcu
    rw [e_post] at hu ⊢
    have hu2 : s.st u = 2 := by
      rcases (hI.post_mem u).mp hu with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · omega
    rcases (hst' c).mp hc with h | rfl
    · exact hI.post_desc u c hu hul h ((hdesc u c h).mp hd) hcu
    · rw [(hdescr u).mp hd] at hu2; omega
  · intro u c hu hc hd
    rw [e_post] at hu ⊢
    have hu2 : s.st u = 2 := by
      rcases (hI.post_mem _).mp hu with ⟨h, _⟩ | ⟨_, h, _⟩
      · omega
      · simpa using h
    rcases (hst' c).mp hc with h | rfl
    · exact hI.post_top u c hu h ((hdesc u c h).mp hd)
    · rw [(hdescr u).mp hd] at hu2; omega

omit hG in
theorem inv_skip {s : DS} (hI : G.Inv s) (hi : s.inner = false) (hr : s.r < 2 * G.E)
    (hv : ¬ (G.rep s.r = s.r ∧ s.st s.r = 0)) : G.Inv (G.step s) := by
  have hstep : G.step s = { s with r := s.r + 1 } := by
    rw [step, ite_eq_right (by rw [hi]; simp), ite_eq_left hr, ite_eq_right hv]
  rw [hstep]
  have hfd : G.fd { s with r := s.r + 1 } = G.fd s := rfl
  refine ⟨hI.vert, hI.st_le, hI.tree, hI.parv, hI.hbound, fun h => absurd h (by rw [hi]; simp), hI.closed,
    hI.ptr_le, hI.ptr0, hI.ptr2, hI.expl, hI.finN, hI.back, ?_, fun h => absurd h (by rw [hi]; simp),
    hI.vl_nd, hI.vl_mem, hI.ex_nd, hI.ex_mem, hI.post_nd, hI.post_mem, hI.post_desc, hI.post_top⟩
  intro u hu hl hrep
  by_cases h : u < s.r
  · exact hI.scan u h hl hrep
  · have : u = s.r := by simp at hu; omega
    subst this
    intro h0; exact hv ⟨hrep, h0⟩

/-- **Every step keeps the invariant.** -/
theorem inv_step {s : DS} (hI : G.Inv s) : G.Inv (G.step s) := by
  by_cases hi : s.inner = true
  · by_cases hp : s.ptr s.cur < (G.darts s.cur).length
    · by_cases hw : s.st (G.nw s) = 0
      · exact inv_exploreNew hG hI hi hp hw
      · exact inv_exploreOld hG hI hi hp hw
    · by_cases hr : 2 * G.E ≤ s.par s.cur
      · exact inv_finishRoot hG hI hi hp hr
      · exact inv_finishNonroot hG hI hi hp hr
  · have hi' : s.inner = false := by simpa using hi
    by_cases hr : s.r < 2 * G.E
    · by_cases hv : G.rep s.r = s.r ∧ s.st s.r = 0
      · exact inv_start hI hi' hr hv
      · exact inv_skip hI hi' hr hv
    · have : G.step s = s := by rw [step, ite_eq_right hi, ite_eq_right hr]
      rw [this]; exact hI

omit hG in
theorem inv_init : G.Inv DG.init := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [init, ForestData.TreeOn]

theorem inv_iterate : ∀ n, G.Inv (iterate G.step n DG.init) := by
  intro n
  induction n with
  | zero => exact inv_init
  | succ n ih => rw [iterate_succ']; exact inv_step hG ih

end ok

end DG

end STACS2027.Embed
