module

public import Outerplanar.Algo.Graph
import Mathlib.Tactic

/-!
# Correctness of the low-point, head and block passes

The passes `lowOf`, `headOf`, `lowerOf` and `blocksOf` of `Outerplanar.Algo.Graph` compute
ANONYMIZED and ANONYMIZED's low points, the heads and the blocks of the palm tree `P` that the
depth-first search `dfsOf g` of the id graph `idEdges g` yields (`palm_dfsOf`).

* The id graph: its edges are written smaller end first between ids below `numV g`
  (`idEdges_lt`), without repetitions (`idEdges_nodup`); its adjacency is membership in the
  neighbour lists `nbOf` (`adj_iff_mem_nbOf`), which satisfy the hypotheses of the search
  (`ok_idEdges`).
* Low points: the pass processes the preorder list from the end, so when a vertex is
  processed the low points of its children (later in preorder) are final (`lowOf_eq`). By
  induction in reverse preorder, `lowOf v` is the least of `pre v` and the preorder numbers
  of the ends of the edges from the subtree of `v` other than the tree edge `v — par v`
  (`IsLow`, `isLow_lowOf`). Since every edge joins an ancestor and a descendant, a non-root
  `v` is a head iff `pre (par v) ≤ lowOf v` (`isHead_iff_lowOf`, `isHead_iff_dfsOf`).
* Heads: the pass processes the preorder list from the start, so the head of the parent is
  final when a vertex is processed (`headOf_eq`); by induction in preorder, it computes
  `P.head` (`headOf_lowOf`, `headOf_dfsOf`).
* Lower ends (`lowerOf_dfsOf`) and blocks: `blocksOf g` is the list of the blocks
  `P.block h`, `h < numV g` (`blocksOf_eq`).
-/

@[expose] public section

namespace STACS2027.Algo

/-! ### The id graph -/

theorem nodup_eraseDups_aux {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → l.eraseDups.Nodup
  | _, [], _ => by simp
  | 0, _ :: _, h => by simp at h
  | n + 1, a :: as, h => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.mpr ⟨fun ha => ?_, nodup_eraseDups_aux n _
      (Nat.le_trans (List.length_filter_le _ _) (by simp at h; omega))⟩
    have := List.mem_filter.mp (List.mem_eraseDups.mp ha)
    simp at this

theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup :=
  nodup_eraseDups_aux _ l le_rfl

theorem mem_proper {g : Graph} {e : Edge} : e ∈ proper g ↔ e ∈ g ∧ e.1 < e.2 := by
  simp [proper]

theorem mem_labels {g : Graph} {x : ℕ} : x ∈ labels g ↔ ∃ e ∈ proper g, x = e.1 ∨ x = e.2 := by
  simp only [labels, List.mem_eraseDups, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false]

theorem idOf_lt {g : Graph} {x : ℕ} (hx : x ∈ labels g) : idOf g x < numV g :=
  List.idxOf_lt_length_of_mem hx

theorem idOf_inj {g : Graph} {x y : ℕ} (hx : x ∈ labels g) (h : idOf g x = idOf g y) : x = y :=
  (List.idxOf_inj hx).mp h

theorem mem_idEdges {g : Graph} {e : Edge} :
    e ∈ idEdges g ↔ ∃ d ∈ proper g, edge (idOf g d.1) (idOf g d.2) = e := by
  simp [idEdges]

/-- Every id edge is written smaller end first, between ids below `numV g`. -/
theorem idEdges_lt {g : Graph} {e : Edge} (he : e ∈ idEdges g) : e.1 < e.2 ∧ e.2 < numV g := by
  obtain ⟨d, hd, rfl⟩ := mem_idEdges.mp he
  have hd' := mem_proper.mp hd
  have h1 : d.1 ∈ labels g := mem_labels.mpr ⟨d, hd, Or.inl rfl⟩
  have h2 : d.2 ∈ labels g := mem_labels.mpr ⟨d, hd, Or.inr rfl⟩
  have hne : idOf g d.1 ≠ idOf g d.2 := fun h => absurd (idOf_inj h1 h) (Nat.ne_of_lt hd'.2)
  have := idOf_lt h1
  have := idOf_lt h2
  simp only [edge]
  omega

/-- The id edges have no repetitions. -/
theorem idEdges_nodup (g : Graph) : (idEdges g).Nodup := nodup_eraseDups _

theorem mem_nbOf {E : List Edge} {u w : ℕ} :
    w ∈ nbOf E u ↔ ∃ e ∈ E, (e.1 = u ∧ e.2 = w) ∨ (e.1 ≠ u ∧ e.2 = u ∧ e.1 = w) := by
  simp only [nbOf, List.mem_flatMap]
  refine exists_congr fun e => and_congr_right fun _ => ?_
  by_cases h1 : e.1 = u
  · simp [h1, eq_comm]
  · by_cases h2 : e.2 = u
    · simp [h1, h2, eq_comm]
    · simp [h1, h2]

/-- Adjacency in the id graph is membership in the neighbour lists. -/
theorem adj_iff_mem_nbOf {g : Graph} {u w : ℕ} :
    Adj (idEdges g) u w ↔ w ∈ nbOf (idEdges g) u := by
  rw [mem_nbOf]
  constructor
  · rintro ⟨hne, he⟩
    refine ⟨_, he, ?_⟩
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · left; simp only [edge]; omega
    · right; simp only [edge]; omega
  · rintro ⟨⟨a, b⟩, he, h⟩
    have hab := (idEdges_lt he).1
    dsimp only at h hab
    rcases h with ⟨rfl, rfl⟩ | ⟨-, rfl, rfl⟩
    · refine ⟨Nat.ne_of_lt hab, ?_⟩
      have : edge a b = (a, b) := by simp only [edge]; ext <;> simp <;> omega
      rw [this]; exact he
    · refine ⟨Nat.ne_of_gt hab, ?_⟩
      have : edge b a = (a, b) := by simp only [edge]; ext <;> simp <;> omega
      rw [this]; exact he

/-- The vertices of the id graph are ids. -/
theorem lt_of_isVertex {g : Graph} {v : ℕ} (hv : IsVertex (idEdges g) v) : v < numV g := by
  obtain ⟨u, hne, he⟩ := hv
  have := (idEdges_lt he).2
  simp only [edge] at this
  omega

theorem mem_range_of_isVertex {g : Graph} {v : ℕ} (hv : IsVertex (idEdges g) v) :
    v ∈ List.range (numV g) :=
  List.mem_range.mpr (lt_of_isVertex hv)

/-- The neighbour lists of the id graph satisfy the hypotheses of the search. -/
theorem ok_idEdges (g : Graph) : DFS.Ok (List.range (numV g)) (nbOf (idEdges g)) where
  symm _ _ h := adj_iff_mem_nbOf.mp (adj_iff_mem_nbOf.mpr h).symm
  noloop _ h := (adj_iff_mem_nbOf.mpr h).1 rfl
  closed _ _ h := mem_range_of_isVertex ⟨_, (adj_iff_mem_nbOf.mpr h).symm⟩

/-! ### Updates along a list -/

theorem foldr_update_apply {F : ℕ → (ℕ → ℕ) → ℕ} (x : ℕ → ℕ) {w : ℕ} :
    ∀ {a : List ℕ}, w ∉ a → (a.foldr (fun v f => Function.update f v (F v f)) x) w = x w
  | [], _ => rfl
  | c :: a, h => by
    rw [List.foldr_cons, Function.update_of_ne (fun e => h (by simp [e])),
      foldr_update_apply x (fun h' => h (List.mem_cons_of_mem _ h'))]

theorem foldl_update_apply {G : (ℕ → ℕ) → ℕ → ℕ} {w : ℕ} :
    ∀ (x : ℕ → ℕ) {b : List ℕ}, w ∉ b → (b.foldl (fun f v => Function.update f v (G f v)) x) w = x w
  | _, [], _ => rfl
  | x, c :: b, h => by
    rw [List.foldl_cons, foldl_update_apply _ (fun h' => h (List.mem_cons_of_mem _ h')),
      Function.update_of_ne (fun e => h (by simp [e]))]

/-! ### Folds taking minima -/

theorem foldl_min_le_init {p : ℕ → Prop} [DecidablePred p] (g : ℕ → ℕ) :
    ∀ (l : List ℕ) (a : ℕ), l.foldl (fun acc w => if p w then acc else min acc (g w)) a ≤ a
  | [], _ => le_rfl
  | w :: l, a => by
    rw [List.foldl_cons]
    refine (foldl_min_le_init g l _).trans ?_
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _

theorem foldl_min_le {p : ℕ → Prop} [DecidablePred p] (g : ℕ → ℕ) :
    ∀ (l : List ℕ) (a : ℕ), ∀ w ∈ l, ¬ p w →
      l.foldl (fun acc w => if p w then acc else min acc (g w)) a ≤ g w
  | [], _, _, h, _ => absurd h List.not_mem_nil
  | x :: l, a, w, hw, hp => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hw with rfl | hw
    · refine (foldl_min_le_init g l _).trans ?_
      rw [ite_eq_right hp]
      exact min_le_right _ _
    · exact foldl_min_le g l _ w hw hp

theorem foldl_min_cases {p : ℕ → Prop} [DecidablePred p] (g : ℕ → ℕ) :
    ∀ (l : List ℕ) (a : ℕ), l.foldl (fun acc w => if p w then acc else min acc (g w)) a = a ∨
      ∃ w ∈ l, ¬ p w ∧ l.foldl (fun acc w => if p w then acc else min acc (g w)) a = g w
  | [], _ => Or.inl rfl
  | x :: l, a => by
    rw [List.foldl_cons]
    rcases foldl_min_cases (p := p) g l (if p x then a else min a (g x)) with h | ⟨w, hw, hp, h⟩
    · rw [h]
      by_cases hx : p x
      · exact Or.inl (ite_eq_left hx)
      · rw [ite_eq_right hx]
        rcases min_choice a (g x) with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨x, by simp, hx, h'⟩
    · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, hp, h⟩

theorem foldl_min_congr {p : ℕ → Prop} [DecidablePred p] {g g' : ℕ → ℕ} :
    ∀ (l : List ℕ) (a : ℕ), (∀ w ∈ l, g w = g' w) →
      l.foldl (fun acc w => if p w then acc else min acc (g w)) a =
        l.foldl (fun acc w => if p w then acc else min acc (g' w)) a
  | [], _, _ => rfl
  | x :: l, a, h => by
    simp only [List.foldl_cons]
    rw [h x (by simp)]
    exact foldl_min_congr l _ (fun w hw => h w (List.mem_cons_of_mem _ hw))

/-! ### One low-point step -/

section LowStep

variable (s : DFS.State) (nb : ℕ → List ℕ) (f : ℕ → ℕ) (v : ℕ)

theorem lowStep_le_pre : lowStep s nb f v ≤ s.pre v :=
  foldl_min_le_init (p := fun w => w = s.par v ∧ s.par v ≠ v) _ _ _

theorem lowStep_le {w : ℕ} (hw : w ∈ nb v) (hp : ¬ (w = s.par v ∧ s.par v ≠ v)) :
    lowStep s nb f v ≤ if s.par w = v ∧ w ≠ v then f w else s.pre w :=
  foldl_min_le (fun w => if s.par w = v ∧ w ≠ v then f w else s.pre w) _ _ w hw hp

theorem lowStep_cases : lowStep s nb f v = s.pre v ∨ ∃ w ∈ nb v, ¬ (w = s.par v ∧ s.par v ≠ v) ∧
    lowStep s nb f v = if s.par w = v ∧ w ≠ v then f w else s.pre w :=
  foldl_min_cases (fun w => if s.par w = v ∧ w ≠ v then f w else s.pre w) _ _

variable {s nb f v} in
theorem lowStep_congr {f' : ℕ → ℕ} (h : ∀ w ∈ nb v, s.par w = v → w ≠ v → f w = f' w) :
    lowStep s nb f v = lowStep s nb f' v := by
  unfold lowStep
  refine foldl_min_congr _ _ (fun w hw => ?_)
  by_cases hc : s.par w = v ∧ w ≠ v
  · rw [ite_eq_left hc, ite_eq_left hc, h w hw hc.1 hc.2]
  · rw [ite_eq_right hc, ite_eq_right hc]

end LowStep

/-! ### The preorder list -/

section Ord

variable {s : DFS.State}

theorem mem_right_of_pre_lt (hO : DFS.OrdInv s) {a b : List ℕ} {v w : ℕ}
    (hab : s.ord = a ++ v :: b) (hw : s.pre w ≠ 0) (hlt : s.pre v < s.pre w) : w ∈ b := by
  have hnd := hO.nodup
  rw [hab, List.nodup_append] at hnd
  have hva : v ∉ a := fun h => hnd.2.2 v h v (by simp) rfl
  have hvo : v ∈ s.ord := by rw [hab]; simp
  have hwo : w ∈ s.ord := (hO.mem w).mp hw
  have hpv := hO.pre_eq v hvo
  have hpw := hO.pre_eq w hwo
  rw [hab, List.idxOf_append_of_notMem hva, List.idxOf_cons_self] at hpv
  rw [hab] at hpw hwo
  rcases List.mem_append.mp hwo with h | h
  · rw [List.idxOf_append_of_mem h] at hpw
    have := List.idxOf_lt_length_of_mem h
    omega
  · rcases List.mem_cons.mp h with rfl | h
    · omega
    · exact h

theorem mem_left_of_pre_lt (hO : DFS.OrdInv s) {a b : List ℕ} {v w : ℕ}
    (hab : s.ord = a ++ v :: b) (hw : s.pre w ≠ 0) (hlt : s.pre w < s.pre v) : w ∈ a := by
  have hnd := hO.nodup
  rw [hab, List.nodup_append] at hnd
  have hva : v ∉ a := fun h => hnd.2.2 v h v (by simp) rfl
  have hvo : v ∈ s.ord := by rw [hab]; simp
  have hwo : w ∈ s.ord := (hO.mem w).mp hw
  have hpv := hO.pre_eq v hvo
  have hpw := hO.pre_eq w hwo
  rw [hab, List.idxOf_append_of_notMem hva, List.idxOf_cons_self] at hpv
  by_contra hwa
  rw [hab, List.idxOf_append_of_notMem hwa] at hpw
  omega

/-- The low-point pass: when `v` is processed, the low points of its children are final. -/
theorem lowOf_eq (hO : DFS.OrdInv s) {nb : ℕ → List ℕ}
    (hchild : ∀ v w, s.pre v ≠ 0 → w ∈ nb v → s.par w = v → w ≠ v →
      s.pre w ≠ 0 ∧ s.pre v < s.pre w)
    {v : ℕ} (hv : s.pre v ≠ 0) : lowOf s nb v = lowStep s nb (lowOf s nb) v := by
  obtain ⟨a, b, hab⟩ := List.append_of_mem ((hO.mem v).mp hv)
  have hnd := hO.nodup
  rw [hab, List.nodup_append] at hnd
  have hva : v ∉ a := fun h => hnd.2.2 v h v (by simp) rfl
  have hdisj : ∀ x ∈ b, x ∉ a := fun x hx hxa => hnd.2.2 x hxa x (by simp [hx]) rfl
  have hvb : v ∉ b := (List.nodup_cons.mp hnd.2.1).1
  set L := b.foldr (fun v lowf => Function.update lowf v (lowStep s nb lowf v)) (fun _ => 0)
  have hlow : lowOf s nb = a.foldr (fun v lowf => Function.update lowf v (lowStep s nb lowf v))
      (Function.update L v (lowStep s nb L v)) := by
    unfold lowOf; rw [hab, List.foldr_append, List.foldr_cons]
  have hagree : ∀ x ∈ b, lowOf s nb x = L x := by
    intro x hx
    rw [hlow, foldr_update_apply _ (hdisj x hx), Function.update_of_ne (fun e => hvb (by rw [← e]; exact hx))]
  have h1 : lowOf s nb v = lowStep s nb L v := by
    rw [hlow, foldr_update_apply _ hva, Function.update_self]
  rw [h1]
  apply lowStep_congr
  intro w hw hpw hwv
  obtain ⟨hw0, hlt⟩ := hchild v w hv hw hpw hwv
  exact (hagree w (mem_right_of_pre_lt hO hab hw0 hlt)).symm

/-- The head pass: when `v` is processed, the head of its parent is final. -/
theorem headOf_eq (hO : DFS.OrdInv s)
    (hpar : ∀ v, s.pre v ≠ 0 → s.par v ≠ v → s.pre (s.par v) ≠ 0 ∧ s.pre (s.par v) < s.pre v)
    (low : ℕ → ℕ) {v : ℕ} (hv : s.pre v ≠ 0) :
    headOf s low v =
      if s.par v = v then v else if s.pre (s.par v) ≤ low v then v else headOf s low (s.par v) := by
  obtain ⟨a, b, hab⟩ := List.append_of_mem ((hO.mem v).mp hv)
  have hnd := hO.nodup
  rw [hab, List.nodup_append] at hnd
  have hdisj : ∀ x ∈ b, x ∉ a := fun x hx hxa => hnd.2.2 x hxa x (by simp [hx]) rfl
  have hvb : v ∉ b := (List.nodup_cons.mp hnd.2.1).1
  set H := a.foldl (fun hf v => Function.update hf v
    (if s.par v = v then v else if s.pre (s.par v) ≤ low v then v else hf (s.par v))) (fun _ => 0)
  have hhead : headOf s low = b.foldl (fun hf v => Function.update hf v
      (if s.par v = v then v else if s.pre (s.par v) ≤ low v then v else hf (s.par v)))
      (Function.update H v
        (if s.par v = v then v else if s.pre (s.par v) ≤ low v then v else H (s.par v))) := by
    unfold headOf; rw [hab, List.foldl_append, List.foldl_cons]
  have h1 : headOf s low v =
      if s.par v = v then v else if s.pre (s.par v) ≤ low v then v else H (s.par v) := by
    rw [hhead, foldl_update_apply _ hvb, Function.update_self]
  rw [h1]
  by_cases hr : s.par v = v
  · rw [ite_eq_left hr, ite_eq_left hr]
  · obtain ⟨hp0, hlt⟩ := hpar v hv hr
    have hpa : s.par v ∈ a := mem_left_of_pre_lt hO hab hp0 hlt
    have : headOf s low (s.par v) = H (s.par v) := by
      rw [hhead, foldl_update_apply _ (fun h => hdisj _ h hpa), Function.update_of_ne hr]
    rw [this]

end Ord

/-! ### Palm trees -/

/-- Below a proper ancestor `v` of `u` lies a child `c` of `v` that is an ancestor of `u`. -/
theorem exists_child {g : Graph} (P : Palm g) {v u : ℕ} (h : P.Anc v u) (hne : u ≠ v) :
    ∃ c, P.par c = v ∧ c ≠ v ∧ P.Anc c u := by
  obtain ⟨k, hk⟩ := h
  induction k with
  | zero => exact absurd hk hne
  | succ k ih =>
    by_cases hc : P.par^[k] u = v
    · exact ih hc
    · exact ⟨P.par^[k] u, by rw [← Function.iterate_succ_apply' P.par k u]; exact hk, hc, ⟨k, rfl⟩⟩

theorem head_of_isHead {g : Graph} (P : Palm g) {v : ℕ} (hh : P.IsHead v) : P.head v = v := by
  rw [Palm.head, Palm.headAux, ite_eq_right hh.2.1, ite_eq_left hh]

/-- `x` is the low point of `v` in the palm tree `P` with neighbour lists `nb`: the least of
`pre v` and the preorder numbers `pre w` of the ends `w` of the edges `u — w` from the subtree
of `v`, other than the tree edge `v — par v`. -/
def IsLow {E : Graph} (P : Palm E) (nb : ℕ → List ℕ) (v x : ℕ) : Prop :=
  x ≤ P.pre v ∧
  (∀ u w, P.Anc v u → w ∈ nb u → ¬ (u = v ∧ w = P.par v) → x ≤ P.pre w) ∧
  (x = P.pre v ∨ ∃ u w, P.Anc v u ∧ w ∈ nb u ∧ ¬ (u = v ∧ w = P.par v) ∧ x = P.pre w)

/-- The lower end of an edge is its end with the larger preorder number. -/
theorem lowerOf_eq_lower {E : Graph} (P : Palm E) {s : DFS.State} (hpre : P.pre = s.pre)
    {e : Edge} (he : Adj E e.1 e.2) : lowerOf s e = P.lower e.1 e.2 := by
  unfold lowerOf
  rw [← hpre]
  rcases P.lower_cases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases P.pre_anc ⟨e.1, he⟩ h2 with h | h
    · exact absurd h he.1
    · rw [h1, ite_eq_left h]
  · rcases P.pre_anc ⟨e.2, he.symm⟩ h2 with h | h
    · exact absurd h.symm he.1
    · rw [h1, ite_eq_right (by omega)]

/-! ### Low points and heads of the search -/

section Search

variable {vs : List ℕ} {nb : ℕ → List ℕ} {E : Graph}

theorem vis_of_isVertex (hok : DFS.Ok vs nb) (hvs : ∀ v, IsVertex E v → v ∈ vs) {v : ℕ}
    (hv : IsVertex E v) : (DFS.final vs nb).pre v ≠ 0 := by
  rcases (DFS.final_inv hok).roots v (hvs v hv) with h | h
  · rw [(DFS.final_halted hok).2] at h; simp at h
  · exact h

/-- The low-point pass computes the low points. -/
theorem isLow_lowOf (hok : DFS.Ok vs nb) (hnb : ∀ v w, w ∈ nb v ↔ Adj E v w)
    (hvs : ∀ v, IsVertex E v → v ∈ vs) (P : Palm E) (hpar : P.par = (DFS.final vs nb).par)
    (hpre : P.pre = (DFS.final vs nb).pre) {v : ℕ} (hv : IsVertex E v) :
    IsLow P nb v (lowOf (DFS.final vs nb) nb v) := by
  set s := DFS.final vs nb with hs
  have hI : DFS.Inv vs nb s := DFS.final_inv hok
  have hH : DFS.Halted s := DFS.final_halted hok
  have hO : DFS.OrdInv s := DFS.final_ordInv
  have hvert : ∀ u w, w ∈ nb u → IsVertex E w := fun u w h => ⟨u, (hnb u w).mp h⟩
  have hvert' : ∀ u w, w ∈ nb u → IsVertex E u := fun u w h => ⟨w, ((hnb u w).mp h).symm⟩
  have hchild : ∀ v w, s.pre v ≠ 0 → w ∈ nb v → s.par w = v → w ≠ v →
      s.pre w ≠ 0 ∧ s.pre v < s.pre w := by
    intro v w hv hw hpw hwv
    have hw0 := (hI.fin_rel v hv (by rw [hH.1]; simp) w hw).1
    have := hI.par_pre w hw0 (by rw [hpw]; exact hwv.symm)
    rw [hpw] at this
    exact ⟨hw0, this⟩
  have hbound : ∀ w, P.pre w ≤ s.ord.length := fun w => by
    rw [hpre, ← hO.cnt_eq]; exact hI.pre_le w
  suffices H : ∀ n v, s.ord.length + 1 - P.pre v = n → IsVertex E v → IsLow P nb v (lowOf s nb v)
    from H _ v rfl hv
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro v hn hv
  have hx : lowOf s nb v = lowStep s nb (lowOf s nb) v :=
    lowOf_eq hO hchild (vis_of_isVertex hok hvs hv)
  have hlt : ∀ c, P.par c = v → c ≠ v → IsVertex E c → P.pre v < P.pre c :=
    fun c hpc hcv hc => by
      have := P.par_pre c hc (by rw [hpc]; exact hcv.symm)
      rwa [hpc] at this
  have ihc : ∀ c, P.par c = v → c ≠ v → IsVertex E c → IsLow P nb c (lowOf s nb c) :=
    fun c hpc hcv hc =>
      ih _ (by have := hlt c hpc hcv hc; have := hbound c; omega) c rfl hc
  have hle := lowStep_le_pre s nb (lowOf s nb) v
  have hle2 := fun w => lowStep_le s nb (lowOf s nb) v (w := w)
  have hcases := lowStep_cases s nb (lowOf s nb) v
  rw [← hx] at hle hle2 hcases
  simp only [← hpar, ← hpre] at hle hle2 hcases
  refine ⟨hle, ?_, ?_⟩
  · intro u w hvu hw hne
    by_cases huv : u = v
    · rw [huv] at hw
      have hp : ¬ (w = P.par v ∧ P.par v ≠ v) := fun h => hne ⟨huv, h.1⟩
      have h1 := hle2 w hw hp
      by_cases hc : P.par w = v ∧ w ≠ v
      · rw [ite_eq_left hc] at h1
        exact h1.trans (ihc w hc.1 hc.2 (hvert v w hw)).1
      · rwa [ite_eq_right hc] at h1
    · obtain ⟨c, hpc, hcv, hcu⟩ := exists_child P hvu huv
      have hc : IsVertex E c := P.isVertex_anc (hvert' u w hw) hcu
      have hcnb : c ∈ nb v := by
        have := P.par_adj c hc (by rw [hpc]; exact hcv.symm)
        rw [hpc] at this
        exact (hnb v c).mpr this
      have hp : ¬ (c = P.par v ∧ P.par v ≠ v) := by
        rintro ⟨h1, h2⟩
        have h3 := P.par_pre v hv h2
        rw [← h1] at h3
        have := hlt c hpc hcv hc
        omega
      have h1 := hle2 c hcnb hp
      rw [ite_eq_left ⟨hpc, hcv⟩] at h1
      by_cases hex : u = c ∧ w = P.par c
      · rw [hex.2, hpc]; exact hle
      · exact h1.trans ((ihc c hpc hcv hc).2.1 u w hcu hw hex)
  · rcases hcases with h | ⟨w, hw, hp, h⟩
    · exact Or.inl h
    · right
      have hwv : w ≠ P.par v := by
        intro e
        refine hp ⟨e, fun hr => hok.noloop v ?_⟩
        rw [hr] at e; rw [e] at hw; exact hw
      by_cases hc : P.par w = v ∧ w ≠ v
      · rw [ite_eq_left hc] at h
        rcases (ihc w hc.1 hc.2 (hvert v w hw)).2.2 with h' | ⟨u', w', hwu', hw', -, h'⟩
        · exact ⟨v, w, P.anc_refl v, hw, fun h'' => hwv h''.2, h.trans h'⟩
        · have hvw : P.Anc v w := by rw [← hc.1]; exact P.anc_par w
          refine ⟨u', w', P.anc_trans hvw hwu', hw', ?_, h.trans h'⟩
          rintro ⟨rfl, -⟩
          exact hc.2 (P.anc_antisymm hv hwu' hvw)
      · rw [ite_eq_right hc] at h
        exact ⟨v, w, P.anc_refl v, hw, fun h'' => hwv h''.2, h⟩

/-- ANONYMIZED and ANONYMIZED's test: a non-root `v` is a head iff its low point is at least the
preorder number of its parent. -/
theorem isHead_iff_lowOf (hok : DFS.Ok vs nb) (hnb : ∀ v w, w ∈ nb v ↔ Adj E v w)
    (hvs : ∀ v, IsVertex E v → v ∈ vs) (P : Palm E) (hpar : P.par = (DFS.final vs nb).par)
    (hpre : P.pre = (DFS.final vs nb).pre) {v : ℕ} (hv : IsVertex E v) (hr : P.par v ≠ v) :
    P.IsHead v ↔ P.pre (P.par v) ≤ lowOf (DFS.final vs nb) nb v := by
  obtain ⟨-, hB, hC⟩ := isLow_lowOf hok hnb hvs P hpar hpre hv
  have hpp := P.par_pre v hv hr
  constructor
  · rintro ⟨-, -, hh⟩
    rcases hC with h | ⟨u, w, hvu, hw, -, h⟩
    · omega
    · rw [h]
      by_cases hvw : P.Anc v w
      · rcases P.pre_anc ⟨u, (hnb u w).mp hw⟩ hvw with e | e
        · rw [← e]; omega
        · omega
      · rw [hh u w hvu ((hnb u w).mp hw) hvw]
  · intro hle
    refine ⟨hv, hr, fun u w hvu huw hvw => ?_⟩
    rcases P.palm u w huw with hk | hk
    · exact absurd (P.anc_trans hvu hk) hvw
    · rcases P.anc_chain hvu hk with h | h
      · exact absurd h hvw
      · have hwv : w ≠ v := fun e => hvw (by rw [e]; exact P.anc_refl v)
        have hwp : P.Anc w (P.par v) := P.anc_par_of_ne h hwv
        by_contra hne
        have := hB u w hvu ((hnb u w).mpr huw) (fun h' => hne h'.2)
        rcases P.pre_anc (P.isVertex_par hv) hwp with e | e
        · exact hne e
        · omega

/-- The head pass computes the heads. -/
theorem headOf_lowOf (hok : DFS.Ok vs nb) (hnb : ∀ v w, w ∈ nb v ↔ Adj E v w)
    (hvs : ∀ v, IsVertex E v → v ∈ vs) (P : Palm E) (hpar : P.par = (DFS.final vs nb).par)
    (hpre : P.pre = (DFS.final vs nb).pre) {v : ℕ} (hv : IsVertex E v) (hr : P.par v ≠ v) :
    headOf (DFS.final vs nb) (lowOf (DFS.final vs nb) nb) v = P.head v := by
  have hI : DFS.Inv vs nb (DFS.final vs nb) := DFS.final_inv hok
  have hO : DFS.OrdInv (DFS.final vs nb) := DFS.final_ordInv
  have hparf : ∀ v, (DFS.final vs nb).pre v ≠ 0 → (DFS.final vs nb).par v ≠ v →
      (DFS.final vs nb).pre ((DFS.final vs nb).par v) ≠ 0 ∧
        (DFS.final vs nb).pre ((DFS.final vs nb).par v) < (DFS.final vs nb).pre v :=
    fun v hv hr => ⟨hI.par_vis v hv hr, hI.par_pre v hv hr⟩
  suffices H : ∀ n v, P.pre v = n → IsVertex E v → P.par v ≠ v →
      headOf (DFS.final vs nb) (lowOf (DFS.final vs nb) nb) v = P.head v from H _ v rfl hv hr
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro v hn hv hr
  have hfix := headOf_eq hO hparf (lowOf (DFS.final vs nb) nb) (vis_of_isVertex hok hvs hv)
  simp only [← hpar, ← hpre] at hfix
  rw [hfix, ite_eq_right hr]
  have hiff := isHead_iff_lowOf hok hnb hvs P hpar hpre hv hr
  by_cases hh : P.IsHead v
  · rw [ite_eq_left (hiff.mp hh), head_of_isHead P hh]
  · rw [ite_eq_right (fun h => hh (hiff.mpr h))]
    have hpv := P.isVertex_par hv
    have hpr : P.par (P.par v) ≠ P.par v := fun h => hh (P.isHead_of_root_child hv hr h)
    rw [ih _ (by have := P.par_pre v hv hr; omega) (P.par v) rfl hpv hpr]
    obtain ⟨h1, h2, -⟩ := P.head_spec hv hr
    have hne : P.head v ≠ v := fun e => hh (by rw [← e]; exact h1)
    exact P.head_eq_of_between hv hr (P.anc_par v) (P.anc_par_of_ne h2 hne)

end Search

/-! ### The passes on the id graph -/

section IdGraph

variable {g : Graph}

theorem nb_iff_adj (g : Graph) : ∀ v w, w ∈ nbOf (idEdges g) v ↔ Adj (idEdges g) v w :=
  fun _ _ => adj_iff_mem_nbOf.symm

/-- The search of the id graph yields a palm tree of it. -/
theorem palm_dfsOf (g : Graph) :
    ∃ P : Palm (idEdges g), P.par = (dfsOf g).par ∧ P.pre = (dfsOf g).pre :=
  DFS.palm_of_final (ok_idEdges g) (nb_iff_adj g) (fun _ hv => mem_range_of_isVertex hv)

/-- **The low-point test** (ANONYMIZED and ANONYMIZED): in the palm tree `P` of the search of the
id graph, a non-root vertex `v` is a head iff the preorder number of its parent is at most the
low point of `v` computed by the low-point pass. -/
theorem isHead_iff_dfsOf (P : Palm (idEdges g)) (hpar : P.par = (dfsOf g).par)
    (hpre : P.pre = (dfsOf g).pre) {v : ℕ} (hv : IsVertex (idEdges g) v)
    (hr : (dfsOf g).par v ≠ v) :
    P.IsHead v ↔ (dfsOf g).pre ((dfsOf g).par v) ≤ lowOf (dfsOf g) (nbOf (idEdges g)) v := by
  have := isHead_iff_lowOf (ok_idEdges g) (nb_iff_adj g) (fun _ hv => mem_range_of_isVertex hv)
    P hpar hpre hv (by rw [hpar]; exact hr)
  rw [hpar, hpre] at this
  exact this

/-- **Low points**: for every vertex `v` of the id graph, the low-point pass computes the low
point of `v` in the palm tree `P` of the search (`IsLow`). -/
theorem isLow_dfsOf (P : Palm (idEdges g)) (hpar : P.par = (dfsOf g).par)
    (hpre : P.pre = (dfsOf g).pre) {v : ℕ} (hv : IsVertex (idEdges g) v) :
    IsLow P (nbOf (idEdges g)) v (lowOf (dfsOf g) (nbOf (idEdges g)) v) :=
  isLow_lowOf (ok_idEdges g) (nb_iff_adj g) (fun _ hv => mem_range_of_isVertex hv) P hpar hpre hv

/-- The head pass maps every root of the search to itself. -/
theorem headOf_dfsOf_root (low : ℕ → ℕ) {v : ℕ} (hv : IsVertex (idEdges g) v)
    (hr : (dfsOf g).par v = v) : headOf (dfsOf g) low v = v := by
  have hok := ok_idEdges g
  have hI := DFS.final_inv hok
  unfold dfsOf at hr ⊢
  rw [headOf_eq DFS.final_ordInv (fun v hv hr => ⟨hI.par_vis v hv hr, hI.par_pre v hv hr⟩) low
    (vis_of_isVertex hok (fun _ hv => mem_range_of_isVertex hv) hv)]
  exact ite_eq_left hr

/-- **The head pass**: for every non-root vertex `v` of the id graph, the head computed by
the head pass is the head `P.head v` of `v` in the palm tree `P` of the search. -/
theorem headOf_dfsOf (P : Palm (idEdges g)) (hpar : P.par = (dfsOf g).par)
    (hpre : P.pre = (dfsOf g).pre) {v : ℕ} (hv : IsVertex (idEdges g) v)
    (hr : (dfsOf g).par v ≠ v) :
    headOf (dfsOf g) (lowOf (dfsOf g) (nbOf (idEdges g))) v = P.head v :=
  headOf_lowOf (ok_idEdges g) (nb_iff_adj g) (fun _ hv => mem_range_of_isVertex hv)
    P hpar hpre hv (by rw [hpar]; exact hr)

theorem adj_of_mem_idEdges {e : Edge} (he : e ∈ idEdges g) : Adj (idEdges g) e.1 e.2 := by
  have hlt := (idEdges_lt he).1
  refine ⟨Nat.ne_of_lt hlt, ?_⟩
  have : edge e.1 e.2 = e := by simp only [edge]; ext <;> simp <;> omega
  rw [this]; exact he

/-- **Lower ends**: the lower end computed from the preorder numbers is the lower end (the
descendant end) of the edge in the palm tree `P` of the search. -/
theorem lowerOf_dfsOf (P : Palm (idEdges g)) (hpre : P.pre = (dfsOf g).pre) :
    ∀ e ∈ idEdges g, lowerOf (dfsOf g) e = P.lower e.1 e.2 :=
  fun _ he => lowerOf_eq_lower P hpre (adj_of_mem_idEdges he)

/-- **The blocks**: the blocks computed by the block pass, bucketed by head, are the blocks
`P.block h`, `h < numV g`, of the palm tree `P` of the search of the id graph. -/
theorem blocksOf_eq (g : Graph) :
    ∃ P : Palm (idEdges g), P.par = (dfsOf g).par ∧ P.pre = (dfsOf g).pre ∧
      blocksOf g = (List.range (numV g)).map P.block := by
  obtain ⟨P, hpar, hpre⟩ := palm_dfsOf g
  refine ⟨P, hpar, hpre, ?_⟩
  simp only [blocksOf]
  refine List.map_congr_left fun h _ => ?_
  unfold Palm.block
  refine List.filter_congr fun e he => ?_
  have hadj := adj_of_mem_idEdges he
  obtain ⟨hxv, hxr, -⟩ := P.lower_facts hadj
  rw [lowerOf_dfsOf P hpre e he, headOf_dfsOf P hpar hpre hxv (by rw [← hpar]; exact hxr)]
  simp [(idEdges_lt he).1]

end IdGraph

end STACS2027.Algo
