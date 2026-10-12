module

public import Hardness.APX.Membership

/-!
# Bounded-occurrence MAX-3-SAT: definitions and occurrence numbering

* `max3SATQ Q`: MAX-3-SAT restricted to the formulas satisfying `Q` (assignments no longer than
  the instance, as in `max3SAT`); `max3SATB B`: every variable occurs at most `B` times, so that
  `max3SATB 3 = max3SAT3`.
* `lReducible_of_sol`: identity maps are an L-reduction between maximization problems with the
  same solutions on the instances of the first one.
* Occurrence numbering: `annC pre cl` annotates every literal of the clause `cl` with the number
  of earlier occurrences of its variable (in `pre` and in `cl`), and `ann f` annotates every
  literal of the formula `f` with the number of earlier occurrences of its variable in `f`. The
  occurrences of `x`, in order, get the numbers `0, 1, …, occ f x - 1` (`filter_annC`), and the
  list of all pairs (variable, number) is a permutation of the standard list `stdPairs`
  (`pairs_perm`).
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity

open Complexity.PT Complexity.Reg

/-- MAX-3-SAT restricted to the formulas satisfying `Q`. -/
def max3SATQ (Q : SAT.CNF → Prop) : OptProblem where
  maximize := true
  Sol x y v := ∃ f, SAT.encode f = x ∧ SAT.IsThreeCNF f ∧ Q f ∧
    y.length ≤ x.length ∧ v = SAT.satCount (SAT.assignmentOf y) f

/-- MAX-3-SAT restricted to formulas in which every variable occurs at most `B` times. -/
def max3SATB (B : Nat) : OptProblem := max3SATQ fun f => ∀ u, SAT.occurrences f u ≤ B

theorem max3SATB_three : max3SATB 3 = max3SAT3 := rfl

/-- Identity maps are an L-reduction (with `α = β = 1`) between maximization problems such
that solutions of `P` are solutions of `Q`, and on the instances of `P` the solutions of `Q`
are solutions of `P`. -/
theorem lReducible_of_sol {P Q : OptProblem} (hP : P.maximize = true) (hQ : Q.maximize = true)
    (h₁ : ∀ x y v, P.Sol x y v → Q.Sol x y v)
    (h₂ : ∀ x y v y' v', P.Sol x y v → Q.Sol x y' v' → P.Sol x y' v') : LReducible P Q := by
  refine ⟨fun x => x, fun w => (Reg.unpair w).2, 1, 1, polyTime_id, polyTime_pair_snd, ?_⟩
  intro x opt hopt
  obtain ⟨⟨y₀, hy₀⟩, hmax⟩ := hopt
  refine ⟨opt, ⟨⟨y₀, h₁ _ _ _ hy₀⟩, fun y' v' hy' => ⟨fun _ => ?_, fun hm => ?_⟩⟩, by omega, ?_⟩
  · exact (hmax y' v' (h₂ _ _ _ _ _ hy₀ hy')).1 hP
  · rw [hQ] at hm
    cases hm
  · intro y' v' hy'
    refine ⟨v', ?_, by omega⟩
    simp only [Reg.unpair_pairWords]
    exact h₂ _ _ _ _ _ hy₀ hy'

/-- Solutions of `max3SATQ Q` on the instance `encode f`. -/
theorem max3SATQ_sol_encode {Q : SAT.CNF → Prop} {f : SAT.CNF} {y : Word} {v : Nat} :
    (max3SATQ Q).Sol (SAT.encode f) y v ↔
      SAT.IsThreeCNF f ∧ Q f ∧ y.length ≤ (SAT.encode f).length ∧
        v = SAT.satCount (SAT.assignmentOf y) f := by
  constructor
  · rintro ⟨f', hf, h3, hq, hl, hv⟩
    obtain rfl := SAT.encode_injective _ _ hf
    exact ⟨h3, hq, hl, hv⟩
  · rintro ⟨h3, hq, hl, hv⟩
    exact ⟨f, rfl, h3, hq, hl, hv⟩

/-- Solutions of MAX-3-SAT are solutions of the problem without restriction. -/
theorem lReducible_max3SAT_max3SATQ_true : LReducible max3SAT (max3SATQ fun _ => True) :=
  lReducible_of_sol rfl rfl (fun _ _ _ ⟨f, hf, h3, hl, hv⟩ => ⟨f, hf, h3, trivial, hl, hv⟩)
    (fun _ _ _ _ _ _ ⟨f, hf, h3, _, hl, hv⟩ => ⟨f, hf, h3, hl, hv⟩)

/-- 3-OCCURRENCE MAX-3-SAT L-reduces to MAX-3-SAT by the identity maps. -/
theorem lReducible_max3SAT3_max3SAT : LReducible max3SAT3 max3SAT :=
  lReducible_of_sol rfl rfl (fun _ _ _ ⟨f, hf, h3, _, hl, hv⟩ => ⟨f, hf, h3, hl, hv⟩)
    (fun x _ _ _ _ ⟨f, hf, h3, ho, _, _⟩ ⟨f', hf', _, hl, hv⟩ => by
      obtain rfl := SAT.encode_injective _ _ (hf'.trans hf.symm)
      exact ⟨f', hf', h3, ho, hl, hv⟩)

/-- `max3SATB 3` L-reduces to 3-OCCURRENCE MAX-3-SAT (they are the same problem). -/
theorem lReducible_max3SATB_three : LReducible (max3SATB 3) max3SAT3 := by
  rw [max3SATB_three]
  exact LReducible.refl _

namespace Occ

/-! ### Counting occurrences -/

/-- The number of occurrences of the variable `x` in the list of literals `L`. -/
def cnt (L : List SAT.Literal) (x : Nat) : Nat := L.countP fun l => l.var == x

/-- The number of occurrences of the variable `x` in `f`. -/
def occ (f : SAT.CNF) (x : Nat) : Nat := cnt f.flatten x

@[fun_prop] protected theorem PT.cnt {α : Type} [Code α] {L : α → List SAT.Literal}
    {x : α → Nat} (hL : PT L) (hx : PT x) : PT (fun a => cnt (L a) (x a)) := by
  unfold cnt
  fun_prop

@[fun_prop] protected theorem PT.occ {α : Type} [Code α] {f : α → SAT.CNF}
    {x : α → Nat} (hf : PT f) (hx : PT x) : PT (fun a => occ (f a) (x a)) := by
  unfold occ
  fun_prop

theorem occurrences_eq_occ (f : SAT.CNF) (x : Nat) : SAT.occurrences f x = occ f x := by
  unfold SAT.occurrences occ cnt
  refine List.countP_congr fun l _ => ?_
  simp

theorem cnt_append (L M : List SAT.Literal) (x : Nat) : cnt (L ++ M) x = cnt L x + cnt M x :=
  List.countP_append

theorem cnt_singleton (l : SAT.Literal) (x : Nat) :
    cnt [l] x = if l.var = x then 1 else 0 := by
  simp [cnt, List.countP_cons]

theorem cnt_eq_zero_of_le {L : List SAT.Literal} {V x : Nat} (hL : ∀ l ∈ L, l.var < V)
    (hx : V ≤ x) : cnt L x = 0 := by
  unfold cnt
  rw [List.countP_eq_zero]
  intro l hl
  have := hL l hl
  simp only [beq_iff_eq]
  omega

theorem var_lt_of_mem_flatten {f : SAT.CNF} {l : SAT.Literal} (h : l ∈ f.flatten) :
    l.var < SAT.variableBound f := by
  obtain ⟨cl, hc, hl⟩ := List.mem_flatten.mp h
  exact SAT.literal_lt_variableBound hc hl

theorem occ_eq_zero_of_le {f : SAT.CNF} {x : Nat} (hx : SAT.variableBound f ≤ x) :
    occ f x = 0 :=
  cnt_eq_zero_of_le (fun _ hl => var_lt_of_mem_flatten hl) hx

theorem occ_pos_of_mem {f : SAT.CNF} {l : SAT.Literal} (h : l ∈ f.flatten) : 0 < occ f l.var := by
  unfold occ cnt
  exact List.countP_pos_iff.mpr ⟨l, h, by simp⟩

theorem satCount_cons (y : SAT.Assignment) (cl : SAT.Clause) (f : SAT.CNF) :
    SAT.satCount y (cl :: f) = (if SAT.evalClause y cl then 1 else 0) + SAT.satCount y f := by
  simp only [SAT.satCount, List.countP_cons]
  omega

theorem satCount_append (y : SAT.Assignment) (f g : SAT.CNF) :
    SAT.satCount y (f ++ g) = SAT.satCount y f + SAT.satCount y g := by
  simp only [SAT.satCount, List.countP_append]

/-! ### Annotations -/

/-- Induction on lists from the right. -/
theorem snoc_induction {α : Type} {P : List α → Prop} (h0 : P [])
    (h1 : ∀ l a, P l → P (l ++ [a])) (l : List α) : P l := by
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact h0
  | cons a t ih =>
    rw [List.reverse_cons]
    exact h1 _ _ ih

/-- Annotate every literal of `cl` with the number of earlier occurrences of its variable in
`pre` and in `cl`. -/
def annC (pre : List SAT.Literal) (cl : SAT.Clause) : List (SAT.Literal × Nat) :=
  cl.zipIdx.map fun r => (r.1, cnt (pre ++ cl.take r.2) r.1.var)

/-- Annotate every literal of `f` with the number of earlier occurrences of its variable. -/
def ann (f : SAT.CNF) : List (List (SAT.Literal × Nat)) :=
  f.zipIdx.map fun q => annC (f.take q.2).flatten q.1

@[fun_prop] protected theorem PT.annC {α : Type} [Code α] {pre : α → List SAT.Literal}
    {cl : α → SAT.Clause} (hp : PT pre) (hc : PT cl) : PT (fun a => annC (pre a) (cl a)) := by
  unfold annC
  fun_prop

@[fun_prop] protected theorem PT.ann {α : Type} [Code α] {f : α → SAT.CNF} (hf : PT f) :
    PT (fun a => ann (f a)) := by
  unfold ann
  fun_prop

theorem annC_nil (pre : List SAT.Literal) : annC pre [] = [] := rfl

theorem annC_append (pre L M : List SAT.Literal) :
    annC pre (L ++ M) = annC pre L ++ annC (pre ++ L) M := by
  unfold annC
  rw [List.zipIdx_append, List.map_append]
  congr 1
  · refine List.map_congr_left fun r hr => ?_
    obtain ⟨a, i⟩ := r
    have hi := (List.mem_zipIdx hr).2.1
    simp only [Nat.zero_add] at hi
    simp only [List.take_append_of_le_length (Nat.le_of_lt hi)]
  · rw [List.zipIdx_eq_map_add (l := M), List.map_map]
    refine List.map_congr_left fun r _ => ?_
    obtain ⟨a, j⟩ := r
    simp only [Function.comp_apply, Nat.zero_add, List.take_append, List.append_assoc,
      List.take_of_length_le (Nat.le_add_right L.length j), Nat.add_sub_cancel_left]

theorem annC_singleton (pre : List SAT.Literal) (l : SAT.Literal) :
    annC pre [l] = [(l, cnt pre l.var)] := by
  simp [annC]

theorem annC_map_fst (pre : List SAT.Literal) (cl : SAT.Clause) :
    (annC pre cl).map Prod.fst = cl := by
  unfold annC
  rw [List.map_map]
  exact List.zipIdx_map_fst 0 cl

theorem length_annC (pre : List SAT.Literal) (cl : SAT.Clause) : (annC pre cl).length = cl.length := by
  simp [annC]

theorem ann_map_fst (f : SAT.CNF) : (ann f).map (fun c => c.map Prod.fst) = f := by
  unfold ann
  rw [List.map_map]
  conv => rhs; rw [← List.zipIdx_map_fst 0 f]
  refine List.map_congr_left fun q _ => ?_
  simp only [Function.comp_apply, annC_map_fst]

theorem ann_snoc (f : SAT.CNF) (cl : SAT.Clause) :
    ann (f ++ [cl]) = ann f ++ [annC f.flatten cl] := by
  unfold ann
  rw [List.zipIdx_append, List.map_append]
  congr 1
  · refine List.map_congr_left fun q hq => ?_
    obtain ⟨a, i⟩ := q
    have hi := (List.mem_zipIdx hq).2.1
    simp only [Nat.zero_add] at hi
    simp only [List.take_append_of_le_length (Nat.le_of_lt hi)]
  · simp

/-- The annotations of a formula are those of its list of literals. -/
theorem flatten_ann (f : SAT.CNF) : (ann f).flatten = annC [] f.flatten := by
  refine snoc_induction (P := fun f : SAT.CNF => (ann f).flatten = annC [] f.flatten) rfl
    (fun f cl ih => ?_) f
  rw [ann_snoc, List.flatten_append, ih, List.flatten_append, annC_append]
  simp

/-- The occurrences of `x` in `L` are numbered `cnt pre x, cnt pre x + 1, …`. -/
theorem filter_annC (pre L : List SAT.Literal) (x : Nat) :
    ((annC pre L).filter (fun q => q.1.var == x)).map Prod.snd =
      List.range' (cnt pre x) (cnt L x) := by
  refine snoc_induction (P := fun L => ((annC pre L).filter (fun q => q.1.var == x)).map Prod.snd =
      List.range' (cnt pre x) (cnt L x)) rfl (fun L l ih => ?_) L
  rw [annC_append, annC_singleton, List.filter_append, List.map_append, ih, cnt_append,
    cnt_append, cnt_singleton]
  by_cases h : l.var = x
  · subst h
    simp only [List.filter_cons, beq_self_eq_true, ite_true, List.filter_nil, List.map_cons,
      List.map_nil, List.range'_concat, Nat.one_mul]
  · simp [h]

theorem snd_lt_of_mem_annC {L : List SAT.Literal} {q : SAT.Literal × Nat} (h : q ∈ annC [] L) :
    q.2 < cnt L q.1.var := by
  have h1 : q.2 ∈ ((annC [] L).filter (fun r => r.1.var == q.1.var)).map Prod.snd :=
    List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨h, by simp⟩, rfl⟩
  rw [filter_annC] at h1
  simpa [cnt] using (List.mem_range'_1.mp h1).2

theorem fst_mem_of_mem_annC {pre L : List SAT.Literal} {q : SAT.Literal × Nat}
    (h : q ∈ annC pre L) : q.1 ∈ L := by
  have : q.1 ∈ (annC pre L).map Prod.fst := List.mem_map.mpr ⟨q, h, rfl⟩
  rwa [annC_map_fst] at this

/-! ### The pairs (variable, number) -/

/-- The standard list of pairs `(x, j)` with `x < V` and `j < k x`. -/
def stdPairs (V : Nat) (k : Nat → Nat) : List (Nat × Nat) :=
  (List.range V).flatMap fun x => (List.range (k x)).map fun j => (x, j)

theorem nodup_stdPairs (V : Nat) (k : Nat → Nat) : (stdPairs V k).Nodup := by
  unfold stdPairs
  refine List.nodup_flatMap.mpr ⟨fun x _ => ?_, ?_⟩
  · exact List.nodup_range.map fun a b h => (Prod.mk.inj h).2
  · refine List.Pairwise.imp ?_ List.pairwise_lt_range
    intro a b hab
    refine List.disjoint_left.mpr fun p hpa hpb => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hpa
    obtain ⟨j, -, hj⟩ := List.mem_map.mp hpb
    have := (Prod.mk.inj hj).1
    omega

theorem mem_stdPairs {V : Nat} {k : Nat → Nat} {p : Nat × Nat} :
    p ∈ stdPairs V k ↔ p.1 < V ∧ p.2 < k p.1 := by
  obtain ⟨x, j⟩ := p
  simp only [stdPairs, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl, rfl⟩
    exact ⟨ha, hb⟩
  · rintro ⟨hx, hj⟩
    exact ⟨x, hx, j, hj, rfl, rfl⟩

theorem countP_stdPairs (V : Nat) (k : Nat → Nat) (p : Nat × Nat → Bool) :
    (stdPairs V k).countP p = ((List.range V).map fun x => (List.range (k x)).countP fun j => p (x, j)).sum := by
  unfold stdPairs
  rw [List.countP_flatMap]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp only [Function.comp_apply, List.countP_map]
  rfl

theorem length_stdPairs (V : Nat) (k : Nat → Nat) :
    (stdPairs V k).length = ((List.range V).map k).sum := by
  unfold stdPairs
  rw [List.length_flatMap]
  simp

/-- The pairs (variable, number) of the annotated literals of `L`. -/
def pairsOf (L : List SAT.Literal) : List (Nat × Nat) :=
  (annC [] L).map fun q => (q.1.var, q.2)

/-- The pairs (variable, number) are the standard pairs, up to order. -/
theorem pairs_perm {L : List SAT.Literal} {V : Nat} (hL : ∀ l ∈ L, l.var < V) :
    (pairsOf L).Perm (stdPairs V (cnt L)) := by
  rw [List.perm_iff_count]
  rintro ⟨x, j⟩
  simp only [(nodup_stdPairs V (cnt L)).count, mem_stdPairs]
  unfold pairsOf
  have e : List.count (x, j) ((annC [] L).map fun q => (q.1.var, q.2)) =
      List.count j (((annC [] L).filter (fun q => q.1.var == x)).map Prod.snd) := by
    simp only [List.count, List.countP_map, List.countP_filter]
    refine List.countP_congr fun q _ => ?_
    simp only [Function.comp_apply, Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq]
    tauto
  rw [e, filter_annC, (List.nodup_range' (s := cnt [] x) (n := cnt L x)).count]
  simp only [List.mem_range'_1]
  by_cases hx : x < V
  · simp [hx, cnt]
  · have : cnt L x = 0 := cnt_eq_zero_of_le hL (by omega)
    simp [hx, this]

theorem countP_annC {L : List SAT.Literal} {V : Nat} (hL : ∀ l ∈ L, l.var < V)
    (p : Nat × Nat → Bool) :
    (annC [] L).countP (fun q => p (q.1.var, q.2)) =
      ((List.range V).map fun x => (List.range (cnt L x)).countP fun j => p (x, j)).sum := by
  have h := (pairs_perm hL).countP_eq p
  unfold pairsOf at h
  rw [List.countP_map] at h
  rw [← countP_stdPairs, ← h]
  rfl

theorem length_eq_sum_cnt {L : List SAT.Literal} {V : Nat} (hL : ∀ l ∈ L, l.var < V) :
    L.length = ((List.range V).map (cnt L)).sum := by
  have h := (pairs_perm hL).length_eq
  unfold pairsOf at h
  rw [List.length_map, length_annC, length_stdPairs] at h
  exact h

end Occ

end Complexity
