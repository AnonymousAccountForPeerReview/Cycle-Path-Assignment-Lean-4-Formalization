module

public import Hardness.Occ.Rounding

/-!
# Consistency gadgets give L-reductions

`lReducible_gadget`: for a polynomial-time gadget family satisfying `Gadget.Good Adm B M`, and
formulas restricted by `Q` to admissible numbers of occurrences, `f ↦ red f` and
`(f, y) ↦ roundWord f y` form an L-reduction from `max3SATQ Q` to `max3SATB B` with
`α = 6 * M + 1` and `β = 1`: the optima satisfy `opt' = I + opt` (`I` the number of gadget
clauses), every assignment of value `v'` is rounded to one of value `v ≥ v' - I`, and
`I ≤ M * (number of literals) ≤ 3 * M * (number of nonempty clauses) ≤ 6 * M * opt`.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity

open Complexity.PT Complexity.Reg

namespace Occ

/-! ### Lower bounds for the optimum -/

/-- A 3-CNF formula has at most three literals per nonempty clause. -/
theorem length_flatten_le (f : SAT.CNF) (h3 : SAT.IsThreeCNF f) :
    f.flatten.length ≤ 3 * f.countP (fun cl => !cl.isEmpty) := by
  induction f with
  | nil => simp
  | cons cl f ih =>
    have h1 := h3 cl List.mem_cons_self
    have h2 := ih fun c hc => h3 c (List.mem_cons_of_mem _ hc)
    rw [List.flatten_cons, List.length_append, List.countP_cons]
    cases cl with
    | nil =>
      simp only [List.length_nil, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte]
      omega
    | cons l cl =>
      simp only [List.isEmpty_cons, Bool.not_false, ↓reduceIte]
      omega

/-- Every nonempty clause is satisfied by the all-false or by the all-true assignment. -/
theorem countP_nonempty_le (f : SAT.CNF) :
    f.countP (fun cl => !cl.isEmpty) ≤
      SAT.satCount (fun _ => false) f + SAT.satCount (fun _ => true) f := by
  induction f with
  | nil => simp [SAT.satCount]
  | cons cl f ih =>
    rw [List.countP_cons, satCount_cons, satCount_cons]
    cases cl with
    | nil => simp only [List.isEmpty_nil]; simp; omega
    | cons l cl =>
      obtain ⟨v, pos⟩ := l
      cases pos <;> simp [SAT.evalLiteral] <;> omega

theorem satCount_assignmentOf_nil (f : SAT.CNF) :
    SAT.satCount (SAT.assignmentOf []) f = SAT.satCount (fun _ => false) f :=
  SAT.satCount_congr fun _ _ _ _ => by simp [SAT.assignmentOf]

theorem satCount_assignmentOf_replicate (f : SAT.CNF) :
    SAT.satCount (SAT.assignmentOf (List.replicate (SAT.encode f).length true)) f =
      SAT.satCount (fun _ => true) f :=
  SAT.satCount_congr fun _ hc _ hl => by
    simp [SAT.assignmentOf, List.getD_eq_getElem?_getD, SAT.var_lt_encode_length hc hl]

/-! ### The L-reduction -/

/-- **Consistency gadgets give L-reductions.** -/
theorem lReducible_gadget {g : Gadget} {Adm : Nat → Prop} {B M : Nat} (hg : g.Good Adm B M)
    (hpt : g.IsPT) {Q : SAT.CNF → Prop} (hQ : ∀ f, Q f → ∀ x, 1 ≤ occ f x → Adm (occ f x)) :
    LReducible (max3SATQ Q) (max3SATB B) := by
  have hf : PolyTime (fun x : Word => SAT.encode (g.red (parseCNF x))) :=
    PT.polyTime ((Gadget.PT.red hpt).comp pt_parseCNF)
  have hgw : PolyTime (fun z : Word => g.roundWord (parseCNF (unpair z).1) (unpair z).2) :=
    PT.polyTime_pairWords_word (h := fun x y : Word => g.roundWord (parseCNF x) y)
      ((Gadget.PT.roundWord hpt).comp (PT.pair (pt_parseCNF.comp PT.fst') PT.snd'))
  refine ⟨_, _, 6 * M + 1, 1, hf, hgw, ?_⟩
  intro x opt hopt
  obtain ⟨⟨y₀, f, rfl, h3, hQf, hlen₀, hv₀⟩, hmax⟩ := hopt
  simp only [parseCNF_encode]
  have hA := hQ f hQf
  have hle : ∀ y : Word, y.length ≤ (SAT.encode f).length →
      SAT.satCount (SAT.assignmentOf y) f ≤ opt :=
    fun y hy => (hmax y _ ⟨f, rfl, h3, hQf, hy, rfl⟩).1 rfl
  have h3' := Gadget.isThreeCNF_red (g := g) f h3
  have hocc : ∀ u, SAT.occurrences (g.red f) u ≤ B := Gadget.occurrences_red_le hg f hA
  have hround : ∀ y : Word, SAT.satCount (SAT.assignmentOf y) (g.red f) ≤
      (g.gadgetCNF f).length + SAT.satCount (SAT.assignmentOf (g.roundWord f y)) f := by
    intro y
    rw [Gadget.satCount_roundWord]
    exact Gadget.satCount_red_le hg f hA _
  have hroundLen : ∀ y, (g.roundWord f y).length ≤ (SAT.encode f).length :=
    fun y => Nat.le_of_eq (Gadget.length_roundWord f y)
  have hsol : ∀ y v', (max3SATB B).Sol (SAT.encode (g.red f)) y v' →
      v' = SAT.satCount (SAT.assignmentOf y) (g.red f) := by
    intro y v' hy
    exact (max3SATQ_sol_encode (Q := fun f => ∀ u, SAT.occurrences f u ≤ B)).mp hy |>.2.2.2
  refine ⟨(g.gadgetCNF f).length + opt,
    ⟨⟨g.liftWord f y₀, ?_⟩, fun y' v' hy' => ⟨fun _ => ?_, fun hm => by cases hm⟩⟩, ?_, ?_⟩
  · refine ⟨g.red f, rfl, h3', hocc, Nat.le_of_eq (Gadget.length_liftWord f y₀), ?_⟩
    rw [Gadget.satCount_liftWord, Gadget.satCount_red_lift hg f hA, hv₀]
  · rw [hsol y' v' hy']
    have := hround y'
    have := hle _ (hroundLen y')
    omega
  · have h1 := Gadget.length_gadgetCNF_le hg f hA
    have h2 := length_flatten_le f h3
    have h3 := countP_nonempty_le f
    have h4 := hle [] (by simp)
    have h5 := hle _ (Nat.le_of_eq (List.length_replicate (n := (SAT.encode f).length) (a := true)))
    rw [satCount_assignmentOf_nil] at h4
    rw [satCount_assignmentOf_replicate] at h5
    have h6 : M * f.flatten.length ≤ M * (3 * (2 * opt)) :=
      Nat.mul_le_mul_left M (Nat.le_trans h2 (Nat.mul_le_mul_left 3 (by omega)))
    have e : M * (3 * (2 * opt)) = 6 * M * opt := by
      rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm M 3, Nat.mul_assoc 3 M 2,
        Nat.mul_comm M 2, ← Nat.mul_assoc]
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · intro y' v' hy'
    have hv' := hsol y' v' hy'
    refine ⟨SAT.satCount (SAT.assignmentOf (g.roundWord f y')) f, ?_, ?_⟩
    · simp only [unpair_pairWords, parseCNF_encode]
      exact ⟨f, rfl, h3, hQf, hroundLen y', rfl⟩
    · have h1 := hround y'
      have h2 := hle _ (hroundLen y')
      subst hv'
      unfold absDiff
      omega

end Occ

end Complexity
