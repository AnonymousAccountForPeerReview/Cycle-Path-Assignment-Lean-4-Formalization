module

public import Hardness.MaxSNP.Defs
public import Hardness.Unbounded
public import Hardness.MaxSNP.LReduction
public import Mathlib.Data.List.Nodup

/-!
# MAX-3-SAT is in MaxSNP

For the formula `φ₃` and the maps `sat2snp`, `snp2sat` of `Hardness.MaxSNP.Defs`: for every
3-CNF formula `f` and every family of solution relations `S`, the number of 4-tuples of the
universe satisfying `φ₃` in the structure `sat2snp f` equals the number of clauses of `f`
satisfied by the assignment `v ↦ S.holds 0 [v]` (`countP_φ₃`). The structure `sat2snp f` has
the input signature `ga₃` (`fits_sat2snp`), the unary relation of an assignment has the
solution signature `sa₃` (`fits_relOf`), and `φ₃` is well formed (`wellFormed_φ₃`). Hence
MAX-3-SAT L-reduces to `maxSNP0 ga₃ sa₃ 4 φ₃` with constants `α = β = 1`
(`lReducible_max3SATu_maxSNP0`), given that the two maps are polynomial-time.

The file also contains general facts: the tuples of `tuples n k`, existence of optima for
bounded maximization problems, and for the instances of `maxSNP0`.

Throughout this file MAX-3-SAT is the auxiliary problem `max3SATu` of `Hardness.Unbounded`, in
which every word is an assignment; the results are transferred to `max3SAT` (assignments no
longer than the instance) in `Hardness.Final.Max3SAT`.
-/

@[expose] public section

namespace Complexity

open Complexity.PT Complexity.Reg

/-! ### Tuples -/

/-- The tuples of `tuples n k` are the lists of length `k` with entries below `n`. -/
theorem mem_tuples {n k : Nat} {t : List Nat} :
    t ∈ tuples n k ↔ t.length = k ∧ ∀ a ∈ t, a < n := by
  induction k generalizing t with
  | zero =>
    cases t <;> simp [tuples_zero]
  | succ k ih =>
    simp only [tuples_succ, List.mem_flatMap, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨u, hu, a, ha, rfl⟩
      obtain ⟨h1, h2⟩ := ih.mp hu
      refine ⟨by simp [h1], ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · exact h2 b hb
    · rintro ⟨h1, h2⟩
      cases t with
      | nil => simp at h1
      | cons a u =>
        exact ⟨u, ih.mpr ⟨by simpa using h1, fun b hb => h2 b (List.mem_cons_of_mem _ hb)⟩,
          a, h2 a List.mem_cons_self, rfl⟩

/-- Each tuple occurs once in `tuples n k`. -/
theorem nodup_tuples (n k : Nat) : (tuples n k).Nodup := by
  induction k with
  | zero => simp [tuples_zero]
  | succ k ih =>
    rw [tuples_succ, List.nodup_flatMap]
    refine ⟨fun t _ => ?_, ?_⟩
    · exact List.Nodup.map (fun a b h => by simpa using h) List.nodup_range
    · refine List.Pairwise.imp ?_ ih
      intro t u htu x hx hy
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
      obtain ⟨b, -, hb⟩ := List.mem_map.mp hy
      exact htu (List.cons.inj hb).2.symm

/-- Counting a predicate on a duplicate-free list `L` whose solutions in `L` are the members of
a duplicate-free list `M`. -/
theorem countP_eq_length_of_nodup {α : Type} {L M : List α} (p : α → Bool) (hL : L.Nodup)
    (hM : M.Nodup) (h : ∀ t, (t ∈ L ∧ p t = true) ↔ t ∈ M) : L.countP p = M.length := by
  rw [List.countP_eq_length_filter]
  refine List.Perm.length_eq ?_
  refine (List.perm_ext_iff_of_nodup (hL.filter _) hM).mpr fun t => ?_
  rw [List.mem_filter]
  exact h t

/-- Counting over an enumerated list a predicate that ignores the index. -/
theorem countP_zipIdx {α : Type} (p : α → Bool) (l : List α) :
    l.zipIdx.countP (fun q => p q.1) = l.countP p := by
  have h := List.countP_map (p := p) (f := Prod.fst) (l := l.zipIdx)
  rw [List.zipIdx_map_fst] at h
  exact h.symm

theorem fst_mem_of_mem_zipIdx {α : Type} {l : List α} {q : α × Nat} (h : q ∈ l.zipIdx) :
    q.1 ∈ l := by
  have h' : q.1 ∈ l.zipIdx.map Prod.fst := List.mem_map.mpr ⟨q, h, rfl⟩
  rwa [List.zipIdx_map_fst] at h'

theorem snd_lt_of_mem_zipIdx {α : Type} {l : List α} {q : α × Nat} (h : q ∈ l.zipIdx) :
    q.2 < l.length := by
  have h' : q.2 ∈ l.zipIdx.map Prod.snd := List.mem_map.mpr ⟨q, h, rfl⟩
  rw [List.zipIdx_map_snd, List.mem_range'_1] at h'
  omega

/-! ### Optima of bounded maximization problems -/

/-- A nonempty bounded set of natural numbers has a greatest element. -/
theorem exists_max_of_bounded (p : Nat → Prop) :
    ∀ B, (∃ v, p v) → (∀ v, p v → v ≤ B) → ∃ m, p m ∧ ∀ v, p v → v ≤ m
  | 0, ⟨v, hv⟩, hb => ⟨v, hv, fun w hw => by
      have := hb w hw
      omega⟩
  | B + 1, hne, hb => by
      by_cases h : p (B + 1)
      · exact ⟨B + 1, h, hb⟩
      · refine exists_max_of_bounded p B hne fun v hv => ?_
        have h1 := hb v hv
        have h2 : v ≠ B + 1 := fun e => h (e ▸ hv)
        omega

/-- A maximization instance with a solution and bounded values has an optimum. -/
theorem OptProblem.exists_isOpt_of_bounded {P : OptProblem} (hmax : P.maximize = true)
    {x : Word} (B : Nat) (hne : ∃ y v, P.Sol x y v) (hb : ∀ y v, P.Sol x y v → v ≤ B) :
    ∃ opt, P.IsOpt x opt := by
  obtain ⟨m, ⟨y, hy⟩, hm⟩ := exists_max_of_bounded (fun v => ∃ y, P.Sol x y v) B
    (by obtain ⟨y, v, h⟩ := hne; exact ⟨v, y, h⟩) (fun v ⟨y, h⟩ => hb y v h)
  refine ⟨m, ⟨y, hy⟩, fun y' v' h' => ⟨fun _ => hm v' ⟨y', h'⟩, fun hmin => ?_⟩⟩
  rw [hmax] at hmin
  cases hmin

/-! ### Instances and solutions of `maxSNP0` -/

/-- The code of a family of relations in the `PT` framework is `encodeRelations`. -/
theorem enc_relations (R : Relations) : Code.enc R = encodeRelations R := rfl

/-- The code of a structure: the universe size and the input relations. -/
theorem enc_structure (n : Nat) (G : Relations) :
    Code.enc (n, G) = SAT.writeNat n ++ encodeRelations G := rfl

theorem encodeRelations_injective : Function.Injective encodeRelations :=
  fun _ _ h => Code.enc_injective (α := Relations) h

/-- The solutions of the structure `(n, G)` are the codes of structures of the solution
signature over its universe, provided `G` has the input signature. -/
theorem maxSNP0_sol_iff {ga sa : List Nat} {k : Nat} {φ : QF} {n : Nat} {G : Relations}
    {y : Word} {v : Nat} :
    (maxSNP0 ga sa k φ).Sol (SAT.writeNat n ++ encodeRelations G) y v ↔
      G.Fits n ga ∧ ∃ S : Relations, S.Fits n sa ∧ y = encodeRelations S ∧
        v = (tuples n k).countP fun t => φ.eval G S t := by
  constructor
  · rintro ⟨n', G', S, hG, hS, hx, hy, hv⟩
    obtain ⟨rfl, hG'⟩ := writeNat_inj hx
    obtain rfl := encodeRelations_injective hG'
    exact ⟨hG, S, hS, hy, hv⟩
  · rintro ⟨hG, S, hS, hy, hv⟩
    exact ⟨n, G, S, hG, hS, rfl, hy, hv⟩

/-- The structure of a signature in which every relation is empty. -/
theorem Relations.fits_empty (n : Nat) (ar : List Nat) :
    Relations.Fits (ar.map fun _ => ([] : List (List Nat))) n ar := by
  refine ⟨List.length_map _, fun p hp => ?_⟩
  obtain ⟨a, -, ha⟩ := List.mem_map.mp (List.of_mem_zip hp).1
  rw [← ha]
  exact ⟨List.nodup_nil, fun t ht => absurd ht List.not_mem_nil⟩

/-- Every instance of `maxSNP0` has an optimum. -/
theorem maxSNP0_exists_opt (ga sa : List Nat) (k : Nat) (φ : QF) (n : Nat) {G : Relations}
    (hG : G.Fits n ga) :
    ∃ opt, (maxSNP0 ga sa k φ).IsOpt (SAT.writeNat n ++ encodeRelations G) opt := by
  refine OptProblem.exists_isOpt_of_bounded rfl (tuples n k).length
    ⟨_, _, maxSNP0_sol_iff.mpr ⟨hG, _, Relations.fits_empty n sa, rfl, rfl⟩⟩ ?_
  intro y v h
  obtain ⟨-, S, -, -, rfl⟩ := maxSNP0_sol_iff.mp h
  exact List.countP_le_length

/-- The tuple `t` belongs to the `i`-th relation. -/
theorem Relations.holds_eq (R : Relations) (i : Nat) (t : List Nat) :
    R.holds i t = decide (t ∈ R.getD i []) := by
  rw [Bool.eq_iff_iff]
  simp [Relations.holds]

/-! ### Assignments -/

/-- The truth value of a clause depends only on the values of its variables. -/
theorem SAT.evalClause_congr {a b : SAT.Assignment} {cl : SAT.Clause}
    (h : ∀ l ∈ cl, a l.var = b l.var) : SAT.evalClause a cl = SAT.evalClause b cl := by
  induction cl with
  | nil => rfl
  | cons l cl ih =>
    simp only [SAT.evalClause_cons]
    rw [ih fun m hm => h m (List.mem_cons_of_mem _ hm)]
    have h1 := h l List.mem_cons_self
    simp [SAT.evalLiteral, h1]

/-- The number of satisfied clauses depends only on the values of the variables of the
formula. -/
theorem SAT.satCount_congr {a b : SAT.Assignment} {f : SAT.CNF}
    (h : ∀ cl ∈ f, ∀ l ∈ cl, a l.var = b l.var) : SAT.satCount a f = SAT.satCount b f :=
  List.countP_congr fun cl hc => by rw [SAT.evalClause_congr (h cl hc)]

theorem SAT.satCount_le_length (a : SAT.Assignment) (f : SAT.CNF) :
    SAT.satCount a f ≤ f.length :=
  List.countP_le_length

/-- Every variable of `f` is below the length of the code of `f`. -/
theorem SAT.var_lt_encode_length {f : SAT.CNF} {cl : SAT.Clause} {l : SAT.Literal}
    (hc : cl ∈ f) (hl : l ∈ cl) : l.var < (SAT.encode f).length := by
  have h1 := size_lt_of_mem hl
  have h2 := size_lt_of_mem hc
  rw [size_literal] at h1
  have h3 : size f = (SAT.encode f).length := rfl
  omega

/-- The word listing the first `n` values of an assignment writes that assignment below
`n`. -/
theorem SAT.assignmentOf_map_range (n : Nat) (a : SAT.Assignment) {v : Nat} (hv : v < n) :
    SAT.assignmentOf ((List.range n).map a) v = a v := by
  simp [SAT.assignmentOf, hv]

/-- Every assignment is written, as far as `f` is concerned, by a word. -/
theorem SAT.exists_word_assignment (a : SAT.Assignment) (f : SAT.CNF) :
    ∃ y : Word, ∀ cl ∈ f, ∀ l ∈ cl, SAT.assignmentOf y l.var = a l.var :=
  ⟨(List.range (SAT.encode f).length).map a, fun _ hc _ hl =>
    SAT.assignmentOf_map_range _ a (SAT.var_lt_encode_length hc hl)⟩

/-- The unary relation of the true variables below `n`. -/
def relOf (n : Nat) (a : SAT.Assignment) : Relations :=
  [((List.range n).filter a).map fun v => [v]]

theorem holds_relOf (n : Nat) (a : SAT.Assignment) (v : Nat) :
    (relOf n a).holds 0 [v] = (decide (v < n) && a v) := by
  rw [Relations.holds_eq, Bool.eq_iff_iff]
  simp [relOf]

/-- The relation of the true variables below `n` is a structure of signature `sa₃`. -/
theorem fits_relOf (n : Nat) (a : SAT.Assignment) : (relOf n a).Fits n sa₃ := by
  refine ⟨rfl, fun p hp => ?_⟩
  simp only [relOf, sa₃, List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
  subst hp
  refine ⟨(List.nodup_range.filter _).map (fun u w h => by simpa using h), fun t ht => ?_⟩
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
  have hv' := List.mem_range.mp (List.mem_filter.mp hv).1
  exact ⟨rfl, fun b hb => by
    rw [List.mem_singleton] at hb
    rw [hb]
    exact hv'⟩

/-- Every assignment is given, as far as `f` is concerned, by a unary relation. -/
theorem satCount_relOf (a : SAT.Assignment) (f : SAT.CNF) :
    SAT.satCount (fun v => (relOf (SAT.encode f).length a).holds 0 [v]) f = SAT.satCount a f :=
  SAT.satCount_congr fun _ hc _ hl => by
    simp [holds_relOf, SAT.var_lt_encode_length hc hl]

/-- The assignment written by `snp2sat f S` agrees on `f` with the solution relation. -/
theorem satCount_snp2sat (f : SAT.CNF) (S : Relations) :
    SAT.satCount (SAT.assignmentOf (snp2sat f S)) f =
      SAT.satCount (fun v => S.holds 0 [v]) f :=
  SAT.satCount_congr fun _ hc _ hl =>
    SAT.assignmentOf_map_range _ _ (SAT.var_lt_encode_length hc hl)

/-! ### Padded clauses -/

theorem lit1_mem {cl : SAT.Clause} (hne : cl ≠ []) : lit1 cl ∈ cl := by
  cases cl with
  | nil => exact absurd rfl hne
  | cons l t => simp [lit1]

theorem lit2_mem {cl : SAT.Clause} (hne : cl ≠ []) : lit2 cl ∈ cl := by
  cases cl with
  | nil => exact absurd rfl hne
  | cons l t => cases t <;> simp [lit1, lit2]

theorem lit3_mem {cl : SAT.Clause} (hne : cl ≠ []) : lit3 cl ∈ cl := by
  cases cl with
  | nil => exact absurd rfl hne
  | cons l t =>
    cases t with
    | nil => simp [lit1, lit3]
    | cons m u => cases u <;> simp [lit1, lit3]

/-- A nonempty clause with at most three literals is equivalent to its three padded
literals. -/
theorem evalClause_eq_lits (a : SAT.Assignment) {cl : SAT.Clause} (hne : cl ≠ [])
    (h3 : cl.length ≤ 3) :
    SAT.evalClause a cl =
      (SAT.evalLiteral a (lit1 cl) || (SAT.evalLiteral a (lit2 cl) ||
        SAT.evalLiteral a (lit3 cl))) := by
  match cl, hne, h3 with
  | [], hne, _ => exact absurd rfl hne
  | [l], _, _ => simp [lit1, lit2, lit3]
  | [l, m], _, _ =>
    simp only [lit1, lit2, lit3, List.headD_cons, List.tail_cons, List.headD_nil,
      SAT.evalClause_cons, SAT.evalClause_nil]
    cases SAT.evalLiteral a l <;> cases SAT.evalLiteral a m <;> rfl
  | [l, m, k], _, _ =>
    simp only [lit1, lit2, lit3, List.headD_cons, List.tail_cons,
      SAT.evalClause_cons, SAT.evalClause_nil, Bool.or_false]
  | _ :: _ :: _ :: _ :: _, _, h => simp at h

theorem signCode_inj {b₁ b₂ b₃ c₁ c₂ c₃ : Bool}
    (h : signCode b₁ b₂ b₃ = signCode c₁ c₂ c₃) : b₁ = c₁ ∧ b₂ = c₂ ∧ b₃ = c₃ := by
  revert h
  cases b₁ <;> cases b₂ <;> cases b₃ <;> cases c₁ <;> cases c₂ <;> cases c₃ <;>
    simp [signCode]

/-! ### The structure of a formula -/

theorem getD_sat2snp (f : SAT.CNF) (b₁ b₂ b₃ : Bool) :
    (sat2snp f).2.getD (signCode b₁ b₂ b₃) [] = snpRel f (signCode b₁ b₂ b₃) := by
  cases b₁ <;> cases b₂ <;> cases b₃ <;> rfl

theorem mem_snpRel {f : SAT.CNF} {s : Nat} {t : List Nat} :
    t ∈ snpRel f s ↔
      ∃ q ∈ f.zipIdx, q.1 ≠ [] ∧ clauseSign q.1 = s ∧ clauseTuple q = t := by
  simp only [snpRel, List.mem_map, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
    List.isEmpty_eq_false_iff, beq_iff_eq]
  constructor
  · rintro ⟨q, ⟨hq, hne, hs⟩, ht⟩
    exact ⟨q, hq, hne, hs, ht⟩
  · rintro ⟨q, hq, hne, hs, ht⟩
    exact ⟨q, ⟨hq, hne, hs⟩, ht⟩

/-- The tuple of a nonempty clause of `f` is a 4-tuple of the universe of `sat2snp f`. -/
theorem clauseTuple_mem_tuples {f : SAT.CNF} {q : SAT.Clause × Nat} (hq : q ∈ f.zipIdx)
    (hne : q.1 ≠ []) : clauseTuple q ∈ tuples (sat2snp f).1 4 := by
  have hc := fst_mem_of_mem_zipIdx hq
  have hi := snd_lt_of_mem_zipIdx hq
  have hlen := length_lt_size f
  have hsz : size f = (SAT.encode f).length := rfl
  refine mem_tuples.mpr ⟨rfl, ?_⟩
  have h1 := SAT.var_lt_encode_length hc (lit1_mem hne)
  have h2 := SAT.var_lt_encode_length hc (lit2_mem hne)
  have h3 := SAT.var_lt_encode_length hc (lit3_mem hne)
  intro b hb
  simp only [clauseTuple, List.mem_cons, List.not_mem_nil, or_false] at hb
  show b < (SAT.encode f).length
  rcases hb with rfl | rfl | rfl | rfl <;> omega

/-- The tuples of distinct clauses are distinct (their first entries are the clause numbers). -/
theorem nodup_map_clauseTuple {f : SAT.CNF} {p : SAT.Clause × Nat → Bool} :
    ((f.zipIdx.filter p).map clauseTuple).Nodup := by
  refine List.Nodup.of_map (fun t : List Nat => t.headD 0) ?_
  rw [List.map_map]
  have hs : ((fun t : List Nat => t.headD 0) ∘ clauseTuple) = Prod.snd := rfl
  rw [hs]
  refine List.Nodup.sublist (List.filter_sublist.map Prod.snd) ?_
  rw [List.zipIdx_map_snd]
  exact List.nodup_range' (s := 0) (n := f.length)

/-- The input relations of `sat2snp f` form a structure of signature `ga₃`. -/
theorem fits_sat2snp (f : SAT.CNF) : (sat2snp f).2.Fits (sat2snp f).1 ga₃ := by
  refine ⟨rfl, fun p hp => ?_⟩
  obtain ⟨h1, h2⟩ := List.of_mem_zip hp
  have h1' : p.1 ∈ [0, 1, 2, 3, 4, 5, 6, 7].map (snpRel f) := h1
  obtain ⟨s, -, hs⟩ := List.mem_map.mp h1'
  rw [ga₃, List.mem_replicate] at h2
  rw [← hs, h2.2]
  refine ⟨nodup_map_clauseTuple, fun t ht => ?_⟩
  obtain ⟨q, hq, hne, -, rfl⟩ := mem_snpRel.mp ht
  exact mem_tuples.mp (clauseTuple_mem_tuples hq hne)

/-- `φ₃` is a well-formed formula in four variables for the signatures `ga₃` and `sa₃`. -/
theorem wellFormed_φ₃ : φ₃.WellFormed ga₃ sa₃ 4 := by
  simp [φ₃, branchQF, litQF, signCode, QF.WellFormed, ga₃, sa₃]

/-! ### Evaluating the formula -/

theorem eval_litQF (G S : Relations) (t : List Nat) (pos : Bool) (i : Nat) :
    (litQF pos i).eval G S t =
      SAT.evalLiteral (fun v => S.holds 0 [v]) ⟨t.getD i 0, pos⟩ := by
  cases pos <;> rfl

theorem eval_branchQF (G S : Relations) (t : List Nat) (b₁ b₂ b₃ : Bool) :
    (branchQF b₁ b₂ b₃).eval G S t =
      (G.holds (signCode b₁ b₂ b₃) [t.getD 0 0, t.getD 1 0, t.getD 2 0, t.getD 3 0] &&
        (SAT.evalLiteral (fun v => S.holds 0 [v]) ⟨t.getD 1 0, b₁⟩ ||
          (SAT.evalLiteral (fun v => S.holds 0 [v]) ⟨t.getD 2 0, b₂⟩ ||
            SAT.evalLiteral (fun v => S.holds 0 [v]) ⟨t.getD 3 0, b₃⟩))) := by
  simp only [branchQF, QF.eval, eval_litQF, List.map_cons, List.map_nil]

theorem eval_φ₃ (G S : Relations) (t : List Nat) :
    φ₃.eval G S t = true ↔ ∃ b₁ b₂ b₃, (branchQF b₁ b₂ b₃).eval G S t = true := by
  simp only [φ₃, QF.eval, Bool.or_eq_true]
  constructor
  · rintro (h | h | h | h | h | h | h | h) <;> exact ⟨_, _, _, h⟩
  · rintro ⟨b₁, b₂, b₃, h⟩
    cases b₁ <;> cases b₂ <;> cases b₃ <;> simp [h]

/-- In the structure of a 3-CNF formula, the 4-tuples satisfying `φ₃` are the tuples of the
clauses satisfied by the assignment `v ↦ S.holds 0 [v]`. -/
theorem eval_φ₃_iff {f : SAT.CNF} (h3 : SAT.IsThreeCNF f) (S : Relations) {t : List Nat}
    (ht : t.length = 4) :
    φ₃.eval (sat2snp f).2 S t = true ↔
      t ∈ (f.zipIdx.filter fun q =>
        SAT.evalClause (fun v => S.holds 0 [v]) q.1).map clauseTuple := by
  match t, ht with
  | [i, v₁, v₂, v₃], _ =>
    rw [eval_φ₃]
    simp only [eval_branchQF, Relations.holds_eq, getD_sat2snp, List.getD_cons_zero,
      List.getD_cons_succ, Bool.and_eq_true, decide_eq_true_eq, mem_snpRel, List.mem_map,
      List.mem_filter]
    constructor
    · rintro ⟨b₁, b₂, b₃, ⟨q, hq, hne, hs, hq'⟩, hl⟩
      obtain ⟨e₁, e₂, e₃⟩ := signCode_inj hs
      refine ⟨q, ⟨hq, ?_⟩, hq'⟩
      rw [evalClause_eq_lits _ hne (h3 _ (fst_mem_of_mem_zipIdx hq))]
      simp only [clauseTuple, List.cons.injEq, and_true] at hq'
      obtain ⟨-, r₁, r₂, r₃⟩ := hq'
      rw [← r₁, ← r₂, ← r₃, ← e₁, ← e₂, ← e₃] at hl
      exact hl
    · rintro ⟨q, ⟨hq, he⟩, hq'⟩
      have hne : q.1 ≠ [] := by
        intro h0
        rw [h0] at he
        simp at he
      refine ⟨(lit1 q.1).positive, (lit2 q.1).positive, (lit3 q.1).positive,
        ⟨q, hq, hne, rfl, hq'⟩, ?_⟩
      rw [evalClause_eq_lits _ hne (h3 _ (fst_mem_of_mem_zipIdx hq))] at he
      simp only [clauseTuple, List.cons.injEq, and_true] at hq'
      obtain ⟨-, r₁, r₂, r₃⟩ := hq'
      rw [← r₁, ← r₂, ← r₃]
      exact he

/-- The value of the solution `S` in the structure of a 3-CNF formula `f` is the number of
clauses of `f` satisfied by the assignment `v ↦ S.holds 0 [v]`. -/
theorem countP_φ₃ {f : SAT.CNF} (h3 : SAT.IsThreeCNF f) (S : Relations) :
    ((tuples (sat2snp f).1 4).countP fun t => φ₃.eval (sat2snp f).2 S t) =
      SAT.satCount (fun v => S.holds 0 [v]) f := by
  have hM : ((f.zipIdx.filter fun q =>
      SAT.evalClause (fun v => S.holds 0 [v]) q.1).map clauseTuple).Nodup :=
    nodup_map_clauseTuple
  rw [countP_eq_length_of_nodup _ (nodup_tuples _ _) hM, List.length_map,
    ← List.countP_eq_length_filter, countP_zipIdx (SAT.evalClause _) f]
  · rfl
  · intro t
    constructor
    · rintro ⟨ht, he⟩
      exact (eval_φ₃_iff h3 S (mem_tuples.mp ht).1).mp he
    · intro hm
      have hm' := hm
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm'
      obtain ⟨hq, he⟩ := List.mem_filter.mp hq
      have hne : q.1 ≠ [] := by
        intro h0
        rw [h0] at he
        simp at he
      have ht : clauseTuple q ∈ tuples (sat2snp f).1 4 := clauseTuple_mem_tuples hq hne
      exact ⟨ht, (eval_φ₃_iff h3 S (mem_tuples.mp ht).1).mpr hm⟩

/-! ### The L-reduction -/

theorem max3SATu_sol_encode {f : SAT.CNF} {y : Word} {v : Nat} :
    max3SATu.Sol (SAT.encode f) y v ↔
      SAT.IsThreeCNF f ∧ v = SAT.satCount (SAT.assignmentOf y) f := by
  constructor
  · rintro ⟨f', hf, h3, hv⟩
    obtain rfl := SAT.encode_injective _ _ hf
    exact ⟨h3, hv⟩
  · rintro ⟨h3, hv⟩
    exact ⟨f, rfl, h3, hv⟩

/-- MAX-3-SAT L-reduces to the MaxSNP₀ problem of `φ₃`, with constants `α = β = 1`: values are
preserved exactly. -/
theorem lReducible_max3SATu_maxSNP0 (h₁ : PT sat2snp)
    (h₂ : PT (fun p : SAT.CNF × Relations => snp2sat p.1 p.2)) :
    LReducible max3SATu (maxSNP0 ga₃ sa₃ 4 φ₃) := by
  obtain ⟨F, hF, hF'⟩ := h₁
  obtain ⟨H, hH, hH'⟩ := h₂
  refine ⟨F, fun w => afterOnes (H ((unpair w).1 ++ (unpair w).2)), 1, 1, hF,
    polyTime_comp polyTime_afterOnes
      (polyTime_comp hH (polyTime_append polyTime_pair_fst polyTime_pair_snd)), ?_⟩
  intro x opt hopt
  obtain ⟨⟨y₀, f, rfl, h3, hv₀⟩, hmax⟩ := hopt
  have hFx : F (SAT.encode f) = SAT.writeNat (sat2snp f).1 ++ encodeRelations (sat2snp f).2 :=
    hF' f
  -- every solution of the structure is a relation, whose value is a value of the formula
  have hval : ∀ S : Relations,
      max3SATu.Sol (SAT.encode f) (snp2sat f S)
        ((tuples (sat2snp f).1 4).countP fun t => φ₃.eval (sat2snp f).2 S t) := by
    intro S
    rw [max3SATu_sol_encode, countP_φ₃ h3 S, satCount_snp2sat]
    exact ⟨h3, rfl⟩
  have hle : ∀ y v', (maxSNP0 ga₃ sa₃ 4 φ₃).Sol (F (SAT.encode f)) y v' → v' ≤ opt := by
    intro y v' hy
    rw [hFx] at hy
    obtain ⟨-, S, -, -, rfl⟩ := maxSNP0_sol_iff.mp hy
    exact (hmax _ _ (hval S)).1 rfl
  refine ⟨opt, ⟨⟨encodeRelations (relOf (SAT.encode f).length (SAT.assignmentOf y₀)), ?_⟩,
    fun y v' hy => ⟨fun _ => hle y v' hy, fun hmin => by cases hmin⟩⟩, by omega, ?_⟩
  · rw [hFx]
    refine maxSNP0_sol_iff.mpr ⟨fits_sat2snp f, relOf (SAT.encode f).length (SAT.assignmentOf y₀),
      fits_relOf _ _, rfl, ?_⟩
    rw [countP_φ₃ h3, satCount_relOf]
    exact hv₀
  · intro y v' hy
    rw [hFx] at hy
    obtain ⟨-, S, -, rfl, rfl⟩ := maxSNP0_sol_iff.mp hy
    have hg : afterOnes (H ((unpair (pairWords (SAT.encode f) (encodeRelations S))).1 ++
        (unpair (pairWords (SAT.encode f) (encodeRelations S))).2)) = snp2sat f S := by
      rw [unpair_pairWords]
      have h := hH' (f, S)
      rw [show Code.enc (f, S) = SAT.encode f ++ encodeRelations S from rfl] at h
      rw [h, afterOnes_enc_word]
    refine ⟨_, ?_, Nat.le_of_eq (Nat.one_mul _).symm⟩
    show max3SATu.Sol (SAT.encode f) (afterOnes _) _
    rw [hg]
    exact hval S

/-- MAX-3-SAT L-reduces to the MaxSNP₀ problem of `φ₃`, given the obligations. -/
theorem lReducible_max3SATu_maxSNP0_of (ob : Obligations) :
    LReducible max3SATu (maxSNP0 ga₃ sa₃ 4 φ₃) :=
  lReducible_max3SATu_maxSNP0 ob.sat2snp ob.snp2sat

end Complexity
