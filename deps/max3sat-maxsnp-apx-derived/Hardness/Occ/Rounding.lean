module

public import Hardness.Occ.Analysis

/-!
# Consistency gadgets: rounding and lifting assignments

* `satCount_red_le`: every assignment `σ` of `red f` satisfies at most `I + satCount a f`
  clauses, where `a = majority f σ` is the majority rounding and `I` the number of gadget
  clauses. On the replaced clauses, `σ` gains at most the number of contacts disagreeing with
  the majority (`satCount_relabel_le`), which is the minority of the contacts
  (`countP_ne_majority`), and the cut property makes every gadget lose at least as many
  clauses.
* `satCount_red_lift`: an assignment of `f` copied to all nodes satisfies exactly
  `I + satCount a f` clauses.
* `length_gadgetCNF_le`: `I ≤ M * (number of literals of f)`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.Occ

open Complexity.PT

/-! ### Replaced clauses -/

theorem evalClause_relabel_le (σ a : SAT.Assignment) (h : SAT.Literal × Nat → Nat)
    (c : List (SAT.Literal × Nat)) :
    (if SAT.evalClause σ (c.map fun q => (⟨h q, q.1.positive⟩ : SAT.Literal)) then 1 else 0) ≤
      (if SAT.evalClause a (c.map Prod.fst) then 1 else 0) +
        c.countP (fun q => σ (h q) != a q.1.var) := by
  induction c with
  | nil => simp
  | cons q c ih =>
    simp only [List.map_cons, SAT.evalClause_cons, List.countP_cons]
    obtain ⟨⟨v, pos⟩, j⟩ := q
    revert ih
    generalize SAT.evalClause σ (c.map fun q => (⟨h q, q.1.positive⟩ : SAT.Literal)) = e1
    generalize SAT.evalClause a (c.map Prod.fst) = e2
    generalize c.countP (fun q => σ (h q) != a q.1.var) = m
    simp only [SAT.evalLiteral]
    generalize σ (h (⟨v, pos⟩, j)) = b1
    generalize a v = b2
    intro ih
    cases pos <;> cases b1 <;> cases b2 <;> cases e1 <;> cases e2 <;> simp at ih ⊢ <;> omega

theorem satCount_relabel_le (σ a : SAT.Assignment) (h : SAT.Literal × Nat → Nat)
    (A : List (List (SAT.Literal × Nat))) :
    SAT.satCount σ (A.map fun c => c.map fun q => (⟨h q, q.1.positive⟩ : SAT.Literal)) ≤
      SAT.satCount a (A.map fun c => c.map Prod.fst) +
        A.flatten.countP (fun q => σ (h q) != a q.1.var) := by
  induction A with
  | nil => simp [SAT.satCount]
  | cons c A ih =>
    rw [List.map_cons, List.map_cons, satCount_cons, satCount_cons, List.flatten_cons,
      List.countP_append]
    have := evalClause_relabel_le σ a h c
    omega

/-- The contacts disagreeing with the majority are the minority. -/
theorem countP_ne_majority (k : Nat) (s : Nat → Bool) :
    (List.range k).countP (fun j => s j != decide (k ≤ 2 * (List.range k).countP s)) =
      min ((List.range k).countP s) ((List.range k).countP fun j => !s j) := by
  have hsum : (List.range k).countP s + (List.range k).countP (fun j => !s j) = k := by
    have := List.length_eq_countP_add_countP s (l := List.range k)
    rw [List.length_range] at this
    have e : (List.range k).countP (fun j => decide ¬(s j = true)) =
        (List.range k).countP (fun j => !s j) :=
      List.countP_congr fun j _ => by cases s j <;> simp
    rw [e] at this
    omega
  by_cases hk : k ≤ 2 * (List.range k).countP s
  · have e : (List.range k).countP (fun j => s j != decide (k ≤ 2 * (List.range k).countP s)) =
        (List.range k).countP (fun j => !s j) :=
      List.countP_congr fun j _ => by simp [hk]
    rw [e]
    omega
  · have e : (List.range k).countP (fun j => s j != decide (k ≤ 2 * (List.range k).countP s)) =
        (List.range k).countP s :=
      List.countP_congr fun j _ => by simp [hk]
    rw [e]
    omega

theorem any_congr {α : Type} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons, h a List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

namespace Gadget

variable {g : Gadget} {Adm : Nat → Prop} {B M : Nat}

/-! ### Gadget clauses -/

theorem evalClause_arcClause (σ : SAT.Assignment) (W x : Nat) (e : Nat × Nat) :
    SAT.evalClause σ (arcClause W x e) = !(σ (x * W + e.1) && !σ (x * W + e.2)) := by
  simp only [arcClause, SAT.evalClause_cons, SAT.evalClause_nil, SAT.evalLiteral_negative,
    SAT.evalLiteral_positive, Bool.or_false]
  cases σ (x * W + e.1) <;> cases σ (x * W + e.2) <;> rfl

theorem satCount_block_add (σ : SAT.Assignment) (f : SAT.CNF) (x : Nat) (hk : occ f x ≠ 0) :
    SAT.satCount σ (g.block f x) +
        (g.arcs (occ f x)).countP
          (fun e => σ (x * g.width f + e.1) && !σ (x * g.width f + e.2)) =
      (g.block f x).length := by
  unfold block
  simp only [hk, ↓reduceIte]
  rw [SAT.satCount, List.countP_map, List.length_map,
    List.length_eq_countP_add_countP (fun e => σ (x * g.width f + e.1) && !σ (x * g.width f + e.2)),
    Nat.add_comm]
  congr 1
  refine List.countP_congr fun e _ => ?_
  simp only [Function.comp_apply, evalClause_arcClause]
  cases σ (x * g.width f + e.1) && !σ (x * g.width f + e.2) <;> simp

/-! ### Rounding -/

theorem satCount_relabel_round (f : SAT.CNF) (σ : SAT.Assignment) :
    SAT.satCount σ (g.relabel f) ≤ SAT.satCount (g.majority f σ) f +
      ((List.range (SAT.variableBound f)).map fun x =>
        (List.range (occ f x)).countP fun j =>
          σ (x * g.width f + g.cont (occ f x) j) != g.majority f σ x).sum := by
  have h := satCount_relabel_le σ (g.majority f σ)
    (fun q => q.1.var * g.width f + g.cont (occ f q.1.var) q.2) (ann f)
  rw [ann_map_fst, flatten_ann] at h
  have e : (annC [] f.flatten).countP (fun q => σ (q.1.var * g.width f +
      g.cont (occ f q.1.var) q.2) != g.majority f σ q.1.var) =
      ((List.range (SAT.variableBound f)).map fun x => (List.range (occ f x)).countP fun j =>
        σ (x * g.width f + g.cont (occ f x) j) != g.majority f σ x).sum :=
    countP_annC (fun _ hl => var_lt_of_mem_flatten hl)
      (fun p => σ (p.1 * g.width f + g.cont (occ f p.1) p.2) != g.majority f σ p.1)
  rw [← e]
  exact h

/-- **The rounding inequality.** -/
theorem satCount_red_le (hg : g.Good Adm B M) (f : SAT.CNF)
    (hA : ∀ x, 1 ≤ occ f x → Adm (occ f x)) (σ : SAT.Assignment) :
    SAT.satCount σ (g.red f) ≤ (g.gadgetCNF f).length + SAT.satCount (g.majority f σ) f := by
  have h1 := satCount_relabel_round (g := g) f σ
  have h2 : ∀ x ∈ List.range (SAT.variableBound f),
      (List.range (occ f x)).countP (fun j =>
          σ (x * g.width f + g.cont (occ f x) j) != g.majority f σ x) +
        SAT.satCount σ (g.block f x) ≤ (g.block f x).length := by
    intro x _
    by_cases h0 : occ f x = 0
    · simp [h0, block, SAT.satCount]
    · have hk : 1 ≤ occ f x := by omega
      have hcut := hg.cut _ hk (hA x hk) fun v => σ (x * g.width f + v)
      have hm := countP_ne_majority (occ f x) fun j => σ (x * g.width f + g.cont (occ f x) j)
      have hb := satCount_block_add (g := g) σ f x h0
      have e : g.majority f σ x =
          decide (occ f x ≤ 2 * (List.range (occ f x)).countP
            fun j => σ (x * g.width f + g.cont (occ f x) j)) := rfl
      rw [e, hm]
      omega
  have h3 := sum_map_le_sum_map _ _ _ h2
  rw [sum_map_add, ← satCount_gadgetCNF, ← length_gadgetCNF] at h3
  rw [red, satCount_append]
  omega

/-- The rounded word writes the majority rounding on the variables of `f`. -/
theorem satCount_roundWord (f : SAT.CNF) (y : Word) :
    SAT.satCount (SAT.assignmentOf (g.roundWord f y)) f =
      SAT.satCount (g.majority f (SAT.assignmentOf y)) f :=
  SAT.satCount_congr fun _ hc _ hl => by
    simp [roundWord, SAT.assignmentOf, SAT.var_lt_encode_length hc hl]

theorem length_roundWord (f : SAT.CNF) (y : Word) :
    (g.roundWord f y).length = (SAT.encode f).length := by
  simp [roundWord]

/-! ### Lifting -/

/-- **The lifting equality.** -/
theorem satCount_red_lift (hg : g.Good Adm B M) (f : SAT.CNF)
    (hA : ∀ x, 1 ≤ occ f x → Adm (occ f x)) (a : SAT.Assignment) :
    SAT.satCount (fun n => a (n / g.width f)) (g.red f) =
      (g.gadgetCNF f).length + SAT.satCount a f := by
  rw [red, satCount_append, Nat.add_comm]
  congr 1
  · rw [satCount_gadgetCNF, length_gadgetCNF]
    congr 1
    refine List.map_congr_left fun x hx => ?_
    have hW := nodes_lt_width (g := g) f (List.mem_range.mp hx)
    unfold block
    split
    · rfl
    · next h0 =>
      have hk : 1 ≤ occ f x := by omega
      have hadm := hA x hk
      rw [SAT.satCount, List.countP_eq_length]
      intro cl hcl
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hcl
      obtain ⟨h1, h2⟩ := hg.arcs_lt _ hk hadm e he
      rw [evalClause_arcClause, name_div (Nat.lt_trans h1 hW), name_div (Nat.lt_trans h2 hW)]
      cases a x <;> rfl
  · conv => rhs; rw [← ann_map_fst f]
    unfold relabel SAT.satCount
    rw [List.countP_map, List.countP_map]
    refine List.countP_congr fun c hc => ?_
    simp only [Function.comp_apply, SAT.evalClause, List.any_map]
    rw [any_congr]
    intro q hq
    have hq' : q ∈ annC [] f.flatten := by
      rw [← flatten_ann]
      exact List.mem_flatten.mpr ⟨c, hc, hq⟩
    have hmem := fst_mem_of_mem_annC hq'
    have hj := snd_lt_of_mem_annC hq'
    have hk := occ_pos_of_mem hmem
    have hW := nodes_lt_width (g := g) f (var_lt_of_mem_flatten hmem)
    have hc' := hg.cont_lt _ hk (hA _ hk) q.2 hj
    simp only [Function.comp_apply, newLit, SAT.evalLiteral, name_div (Nat.lt_trans hc' hW)]

/-- The lifted word writes the lifted assignment on the variables of `red f`. -/
theorem satCount_liftWord (f : SAT.CNF) (y : Word) :
    SAT.satCount (SAT.assignmentOf (g.liftWord f y)) (g.red f) =
      SAT.satCount (fun n => SAT.assignmentOf y (n / g.width f)) (g.red f) :=
  SAT.satCount_congr fun _ hc _ hl => by
    simp [liftWord, SAT.assignmentOf, SAT.var_lt_encode_length hc hl]

theorem length_liftWord (f : SAT.CNF) (y : Word) :
    (g.liftWord f y).length = (SAT.encode (g.red f)).length := by
  simp [liftWord]

/-! ### Size -/

theorem length_gadgetCNF_le (hg : g.Good Adm B M) (f : SAT.CNF)
    (hA : ∀ x, 1 ≤ occ f x → Adm (occ f x)) :
    (g.gadgetCNF f).length ≤ M * f.flatten.length := by
  rw [length_gadgetCNF, length_eq_sum_cnt (V := SAT.variableBound f)
    (fun _ hl => var_lt_of_mem_flatten hl), ← sum_map_mul_left]
  refine sum_map_le_sum_map _ _ _ fun x _ => ?_
  rw [length_block]
  split
  · exact Nat.zero_le _
  · next h0 =>
    have hk : 1 ≤ occ f x := by omega
    exact hg.length_le _ hk (hA x hk)

end Gadget

end Complexity.Occ
