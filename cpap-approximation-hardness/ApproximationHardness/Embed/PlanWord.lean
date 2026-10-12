module

public import ApproximationHardness.Embed.Word
import Lean.Elab.Tactic.Omega

/-!
# Words of plan trees

A plan is a forest whose nodes have at most two ordered parts: child nodes and darts. A bit per
node chooses the order of its parts (`β v = true` reverses them), and the word of a node lists the
darts of its subtree in that order (`Plan.W`).

Every node is of one of five kinds (`Plan.Kind`): no part, one dart, one child, a *target* (a child
and a dart whose partner is the deepest open end of the child), or a *fork* (two parts without
chords between them).

* **Sufficiency** (`Plan.suff`): if the bits place every target dart on the side `s` prescribes
  and order the two parts of every fork so that their open ends form a valley, every word is
  well nested and its open ends form a valley.
* **Necessity** (`Plan.nec`): if the word of a node `t` is well nested and closed, the sides read
  off the bits (`Plan.sides0`) make the open ends of every node below `t` a valley; so the parts
  of every fork below `t` satisfy `ForkOK`.
-/

@[expose] public section

namespace STACS2027.Embed

/-- A part of a node: a child node or a dart. -/
inductive Item where
  | node (c : Nat)
  | dart (d : Nat)
deriving DecidableEq

/-- A plan: the parts of every node, a height decreasing towards the children, and for every
dart closed at a target node, that node. -/
structure Plan where
  parts : Nat → List Item
  ht : Nat → Nat
  tgt : Nat → Nat
  ht_lt : ∀ v c, Item.node c ∈ parts v → ht c < ht v

theorem nodup_one (a : Nat) : [a].Nodup := List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩

theorem flatMap_congr' {l : List Item} {f g : Item → List Nat} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.flatMap_cons]
    rw [h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

namespace Plan

variable (P : Plan)

/-- The parts of `v` in the order chosen by the bit `β v`. -/
def ord (β : Nat → Bool) (v : Nat) : List Item := if β v then (P.parts v).reverse else P.parts v

/-- The word of the subtree of `v`. -/
def W (β : Nat → Bool) (v : Nat) : List Nat :=
  (P.ord β v).flatMap fun it => match it with
    | .node c => if _h : P.ht c < P.ht v then W β c else []
    | .dart d => [d]
termination_by P.ht v

/-- The word of a part. -/
def partW (β : Nat → Bool) : Item → List Nat
  | .node c => P.W β c
  | .dart d => [d]

theorem mem_ord {β : Nat → Bool} {v : Nat} {it : Item} : it ∈ P.ord β v ↔ it ∈ P.parts v := by
  unfold ord; split <;> simp

theorem W_eq (β : Nat → Bool) (v : Nat) : P.W β v = (P.ord β v).flatMap (P.partW β) := by
  rw [W]
  apply flatMap_congr'
  intro it hit
  cases it with
  | node c => simp only [partW]; rw [dite_eq_left (P.ht_lt v c (P.mem_ord.mp hit))]
  | dart d => rfl

theorem W_of_ord {β : Nat → Bool} {v : Nat} {l : List Item} (h : P.ord β v = l) :
    P.W β v = l.flatMap (P.partW β) := by rw [W_eq, h]

theorem mem_W (β β' : Nat → Bool) : ∀ v e, e ∈ P.W β v ↔ e ∈ P.W β' v := by
  have key : ∀ k v, P.ht v = k → ∀ e, e ∈ P.W β v ↔ e ∈ P.W β' v := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro v hv e
      rw [W_eq, W_eq, List.mem_flatMap, List.mem_flatMap]
      constructor
      · rintro ⟨it, hit, he⟩
        refine ⟨it, P.mem_ord.mpr (P.mem_ord.mp hit), ?_⟩
        cases it with
        | node c =>
          exact (ih (P.ht c) (by rw [← hv]; exact P.ht_lt v c (P.mem_ord.mp hit)) c rfl e).mp he
        | dart d => exact he
      · rintro ⟨it, hit, he⟩
        refine ⟨it, P.mem_ord.mpr (P.mem_ord.mp hit), ?_⟩
        cases it with
        | node c =>
          exact (ih (P.ht c) (by rw [← hv]; exact P.ht_lt v c (P.mem_ord.mp hit)) c rfl e).mpr he
        | dart d => exact he
  exact fun v e => key _ v rfl e

/-- The darts of the subtree of `v` (the word for the zero bits). -/
def D (v : Nat) : List Nat := P.W (fun _ => false) v

/-- The darts of a part. -/
def ID (it : Item) : List Nat := P.partW (fun _ => false) it

theorem mem_W_D {β : Nat → Bool} {v e : Nat} : e ∈ P.W β v ↔ e ∈ P.D v := P.mem_W β _ v e

theorem mem_partW {β : Nat → Bool} {it : Item} {e : Nat} : e ∈ P.partW β it ↔ e ∈ P.ID it := by
  cases it with
  | node c => exact P.mem_W_D
  | dart d => exact Iff.rfl


theorem mem_D {v e : Nat} : e ∈ P.D v ↔ ∃ it ∈ P.parts v, e ∈ P.ID it := by
  unfold D ID
  rw [W_eq, List.mem_flatMap]
  simp only [mem_ord]

/-! ### Kinds of nodes -/

variable (α : Nat → Nat) (key : Nat → Nat)

/-- A target node: a child `c` and a dart `d` whose partner is the deepest open end of `c`. -/
structure IsTarget (v c d : Nat) : Prop where
  parts : P.parts v = [.node c, .dart d] ∨ P.parts v = [.dart d, .node c]
  tgt : P.tgt d = v
  mem : α d ∈ P.D c
  not_mem : d ∉ P.D c
  deep : ∀ e ∈ P.D c, α e ∉ P.D c → e ≠ α d → key e < key (α d)

/-- A fork: two parts without common darts and without chords between them, whose open ends
have distinct keys. -/
structure IsFork (v : Nat) (p q : Item) : Prop where
  parts : P.parts v = [p, q]
  disj : ∀ e ∈ P.ID p, e ∉ P.ID q
  pq : ∀ e ∈ P.ID p, α e ∉ P.ID q
  qp : ∀ e ∈ P.ID q, α e ∉ P.ID p
  dp : ∀ e, p = .dart e → α e ≠ e
  dq : ∀ e, q = .dart e → α e ≠ e
  keys : ∀ e ∈ openEnds α (P.ID p), ∀ f ∈ openEnds α (P.ID q), key e ≠ key f

/-- The five kinds of nodes. -/
inductive Kind (v : Nat) : Prop where
  | leaf : P.parts v = [] → Kind v
  | out (e : Nat) : P.parts v = [.dart e] → α e ≠ e → Kind v
  | single (c : Nat) : P.parts v = [.node c] → Kind v
  | target (c d : Nat) : P.IsTarget α key v c d → Kind v
  | fork (p q : Item) : P.IsFork α key v p q → Kind v

/-- The bits place the parts of `v` as the sides `s` prescribe. -/
def Placed (s : Nat → Bool) (β : Nat → Bool) (v : Nat) : Prop :=
  (∀ c d, P.IsTarget α key v c d →
    P.ord β v = if s (α d) then [.node c, .dart d] else [.dart d, .node c]) ∧
  (∀ p q, P.IsFork α key v p q →
    (P.ord β v = [p, q] ∧ ∀ e ∈ openEnds α (P.ID p), ∀ f ∈ openEnds α (P.ID q), VR s key e f) ∨
    (P.ord β v = [q, p] ∧ ∀ e ∈ openEnds α (P.ID p), ∀ f ∈ openEnds α (P.ID q), VR s key f e))

/-- The two parts of a fork can be ordered so that their open ends form a valley. -/
def ForkOK (s : Nat → Bool) (p q : Item) : Prop :=
  (∀ e ∈ openEnds α (P.ID p), ∀ f ∈ openEnds α (P.ID q), VR s key e f) ∨
  (∀ e ∈ openEnds α (P.ID p), ∀ f ∈ openEnds α (P.ID q), VR s key f e)

/-! ### Shapes of words -/

theorem ord_nil {β : Nat → Bool} {v : Nat} (h : P.parts v = []) : P.ord β v = [] := by
  unfold ord; rw [h]; split <;> rfl

theorem ord_one {β : Nat → Bool} {v : Nat} {a : Item} (h : P.parts v = [a]) : P.ord β v = [a] := by
  unfold ord; rw [h]; split <;> rfl

theorem ord_two {β : Nat → Bool} {v : Nat} {a b : Item} (h : P.parts v = [a, b]) :
    P.ord β v = [a, b] ∨ P.ord β v = [b, a] := by
  unfold ord; rw [h]; split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem W_pair {β : Nat → Bool} {v : Nat} {a b : Item} (h : P.ord β v = [a, b]) :
    P.W β v = P.partW β a ++ P.partW β b := by
  rw [W_of_ord P h]; simp

theorem W_single {β : Nat → Bool} {v : Nat} {a : Item} (h : P.ord β v = [a]) :
    P.W β v = P.partW β a := by
  rw [W_of_ord P h]; simp

theorem mem_openEnds_congr {α : Nat → Nat} {l l' : List Nat} (h : ∀ x, x ∈ l ↔ x ∈ l') {e : Nat} :
    e ∈ openEnds α l ↔ e ∈ openEnds α l' := by
  simp only [mem_openEnds, h]

theorem openEnds_singleton {α : Nat → Nat} {e : Nat} (he : α e ≠ e) : openEnds α [e] = [e] := by
  simp [openEnds, he]

theorem eq_cons_of_first {l : List Nat} (hnd : l.Nodup) {x : Nat} (hx : x ∈ l)
    (h : ∀ y ∈ l, y ≠ x → Before l x y) : l = x :: l.filter fun y => decide (y ≠ x) := by
  cases l with
  | nil => simp at hx
  | cons a t =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hnd
    by_cases hax : a = x
    · subst hax
      rw [List.filter_cons]
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false]
      congr 1
      exact (List.filter_eq_self.mpr (fun y hy => by simp; intro e; exact ha (e ▸ hy))).symm
    · have := h a (List.mem_cons_self ..) hax
      rcases before_cons_iff.mp this with ⟨e, _⟩ | hb
      · exact absurd e.symm hax
      · exact absurd (before_mem hb).2 ha

theorem eq_snoc_of_last {l : List Nat} (hnd : l.Nodup) {x : Nat} (hx : x ∈ l)
    (h : ∀ y ∈ l, y ≠ x → Before l y x) : l = l.filter (fun y => decide (y ≠ x)) ++ [x] := by
  have hr := eq_cons_of_first (l := l.reverse) (((List.reverse_perm _).nodup_iff).mpr hnd)
    (List.mem_reverse.mpr hx) (fun y hy hyx => before_reverse_iff.mpr (h y (List.mem_reverse.mp hy) hyx))
  have := congrArg List.reverse hr
  rw [List.reverse_reverse, List.reverse_cons, ← List.filter_reverse, List.reverse_reverse] at this
  exact this

variable {α key}

theorem dart_good {s : Nat → Bool} {e : Nat} (he : α e ≠ e) :
    [e].Nodup ∧ WN α [e] ∧ Valley s key (openEnds α [e]) := by
  refine ⟨nodup_one e, wn_singleton α e, ?_⟩
  rw [openEnds_singleton he]
  exact List.pairwise_singleton _ _

/-! ### Distinct darts -/

theorem W_nodup (hK : ∀ v, P.Kind α key v) (β : Nat → Bool) : ∀ v, (P.W β v).Nodup := by
  have main : ∀ k v, P.ht v = k → (P.W β v).Nodup := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro v hv
      have IH : ∀ c, Item.node c ∈ P.parts v → (P.W β c).Nodup :=
        fun c hc => ih _ (by rw [← hv]; exact P.ht_lt v c hc) c rfl
      have pnd : ∀ it ∈ P.parts v, (P.partW β it).Nodup := by
        intro it hit
        cases it with
        | node c => exact IH c hit
        | dart d => exact nodup_one d
      cases hK v with
      | leaf h => rw [W_of_ord P (P.ord_nil h)]; simp
      | out e h _ => rw [W_single P (P.ord_one h)]; exact pnd _ (by rw [h]; simp)
      | single c h => rw [W_single P (P.ord_one h)]; exact pnd _ (by rw [h]; simp)
      | target c d ht =>
        have hc : Item.node c ∈ P.parts v := by rcases ht.parts with h | h <;> rw [h] <;> simp
        have hd : d ∉ P.W β c := fun h => ht.not_mem (P.mem_W_D.mp h)
        have hpp := ht.parts
        rcases hpp with h | h <;> rcases P.ord_two (β := β) h with ho | ho <;> rw [W_pair P ho] <;>
          simp only [partW] <;>
          first
          | exact List.nodup_append.mpr ⟨IH c hc, nodup_one d,
              fun a ha b hb => by rw [List.mem_singleton] at hb; subst hb; exact fun e => hd (e ▸ ha)⟩
          | exact List.nodup_cons.mpr ⟨hd, by simpa using IH c hc⟩
      | fork p q hf =>
        have hp : p ∈ P.parts v := by rw [hf.parts]; simp
        have hq : q ∈ P.parts v := by rw [hf.parts]; simp
        rcases P.ord_two (β := β) hf.parts with ho | ho <;> rw [W_pair P ho]
        · exact List.nodup_append.mpr ⟨pnd p hp, pnd q hq, fun a ha b hb e =>
            hf.disj a (P.mem_partW.mp ha) (P.mem_partW.mp (e ▸ hb))⟩
        · exact List.nodup_append.mpr ⟨pnd q hq, pnd p hp, fun a ha b hb e =>
            hf.disj b (P.mem_partW.mp hb) (P.mem_partW.mp (e ▸ ha))⟩
  exact fun v => main _ v rfl

/-! ### Sufficiency -/

/-- **Sufficiency.** Bits placing every part as the sides prescribe make every word well nested,
with its open ends in a valley. -/
theorem suff (hα : ∀ x, α (α x) = x) (hK : ∀ v, P.Kind α key v) {s β : Nat → Bool}
    (hP : ∀ v, P.Placed α key s β v) :
    ∀ v, WN α (P.W β v) ∧ Valley s key (openEnds α (P.W β v)) := by
  have hnd := P.W_nodup hK β
  have main : ∀ k v, P.ht v = k → WN α (P.W β v) ∧ Valley s key (openEnds α (P.W β v)) := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro v hv
      have IH : ∀ c, Item.node c ∈ P.parts v → WN α (P.W β c) ∧ Valley s key (openEnds α (P.W β c)) :=
        fun c hc => ih _ (by rw [← hv]; exact P.ht_lt v c hc) c rfl
      cases hK v with
      | leaf h => rw [W_of_ord P (P.ord_nil h)]; exact ⟨wn_nil α, List.Pairwise.nil⟩
      | out e h he =>
        rw [W_single P (P.ord_one h)]
        exact (dart_good (key := key) he).2
      | single c h =>
        rw [W_single P (P.ord_one h)]
        exact IH c (by rw [h]; simp)
      | target c d ht =>
        have hc : Item.node c ∈ P.parts v := by rcases ht.parts with h | h <;> rw [h] <;> simp
        obtain ⟨hcw, hcv⟩ := IH c hc
        have hcn := hnd c
        have hdin : α d ∈ P.W β c := P.mem_W_D.mpr ht.mem
        have hdout : d ∉ P.W β c := fun h => ht.not_mem (P.mem_W_D.mp h)
        let O := openEnds α (P.W β c)
        have hdO : α d ∈ O := mem_openEnds.mpr ⟨hdin, by rw [hα]; exact hdout⟩
        have hOnd : O.Nodup := hcn.filter _
        have hmax : ∀ y ∈ O, y ≠ α d → key y < key (α d) := by
          intro y hy hyd
          obtain ⟨h1, h2⟩ := mem_openEnds.mp hy
          exact ht.deep y (P.mem_W_D.mp h1) (fun h => h2 (P.mem_W_D.mpr h)) hyd
        have hord := (hP v).1 c d ht
        cases hs : s (α d)
        · rw [hs] at hord
          simp only [Bool.false_eq_true, ite_false] at hord
          rw [W_pair P hord]
          simp only [partW]
          have first := valley_first hcv hOnd hdO hs hmax
          refine ⟨?_, ?_⟩
          · show WN α (d :: P.W β c)
            apply wn_cons_close hα (List.nodup_cons.mpr ⟨hdout, hcn⟩) hcw
            intro z hz
            apply Classical.byContradiction
            intro hz'
            have hzO : z ∈ O := mem_openEnds.mpr ⟨(before_mem hz).1, hz'⟩
            have hzd : z ≠ α d := fun e => before_irrefl hcn _ (e ▸ hz)
            have := (before_filter_iff.mp (first z hzO hzd)).1
            exact before_asymm hcn this hz
          · show Valley s key (openEnds α (d :: P.W β c))
            rw [openEnds_cons_close hα hdin]
            exact List.Pairwise.sublist List.filter_sublist hcv
        · rw [hs] at hord
          simp only [ite_true] at hord
          rw [W_pair P hord]
          simp only [partW]
          have last := valley_last hcv hOnd hdO hs hmax
          refine ⟨?_, ?_⟩
          · apply wn_snoc_close hα (List.nodup_append.mpr ⟨hcn, nodup_one d,
              fun a ha b hb => by rw [List.mem_singleton] at hb; subst hb; exact fun e => hdout (e ▸ ha)⟩) hcw
            intro z hz
            apply Classical.byContradiction
            intro hz'
            have hzO : z ∈ O := mem_openEnds.mpr ⟨(before_mem hz).2, hz'⟩
            have hzd : z ≠ α d := fun e => before_irrefl hcn _ (e ▸ hz)
            have := (before_filter_iff.mp (last z hzO hzd)).1
            exact before_asymm hcn this hz
          · rw [openEnds_snoc_close hα hdin]
            exact List.Pairwise.sublist List.filter_sublist hcv
      | fork p q hf =>
        have hp : p ∈ P.parts v := by rw [hf.parts]; simp
        have hq : q ∈ P.parts v := by rw [hf.parts]; simp
        have good : ∀ it ∈ P.parts v, (∀ e, it = .dart e → α e ≠ e) →
            WN α (P.partW β it) ∧ Valley s key (openEnds α (P.partW β it)) := by
          intro it hit hd
          cases it with
          | node c => exact IH c hit
          | dart e => exact (dart_good (key := key) (hd e rfl)).2
        have gp := good p hp hf.dp
        have gq := good q hq hf.dq
        have np : (P.partW β p).Nodup := by
          cases p with
          | node c => exact hnd c
          | dart e => exact nodup_one e
        have nq : (P.partW β q).Nodup := by
          cases q with
          | node c => exact hnd c
          | dart e => exact nodup_one e
        have pq : ∀ a ∈ P.partW β p, α a ∉ P.partW β q :=
          fun a ha h => hf.pq a (P.mem_partW.mp ha) (P.mem_partW.mp h)
        have qp : ∀ a ∈ P.partW β q, α a ∉ P.partW β p :=
          fun a ha h => hf.qp a (P.mem_partW.mp ha) (P.mem_partW.mp h)
        have dpq : ∀ a ∈ P.partW β p, ∀ b ∈ P.partW β q, a ≠ b :=
          fun a ha b hb e => hf.disj a (P.mem_partW.mp ha) (P.mem_partW.mp (e ▸ hb))
        have mo : ∀ it e, e ∈ openEnds α (P.partW β it) ↔ e ∈ openEnds α (P.ID it) :=
          fun it e => mem_openEnds_congr (fun x => P.mem_partW)
        rcases (hP v).2 p q hf with ⟨ho, hx⟩ | ⟨ho, hx⟩ <;> rw [W_pair P ho]
        · refine ⟨wn_append gp.1 gq.1 (List.nodup_append.mpr ⟨np, nq, dpq⟩) pq qp, ?_⟩
          rw [openEnds_append pq qp]
          exact List.pairwise_append.mpr ⟨gp.2, gq.2, fun e he f hf' =>
            hx e ((mo p e).mp he) f ((mo q f).mp hf')⟩
        · refine ⟨wn_append gq.1 gp.1 (List.nodup_append.mpr ⟨nq, np,
            fun a ha b hb e => dpq b hb a ha e.symm⟩) qp pq, ?_⟩
          rw [openEnds_append qp pq]
          exact List.pairwise_append.mpr ⟨gq.2, gp.2, fun f hf' e he =>
            hx e ((mo p e).mp he) f ((mo q f).mp hf')⟩
  exact fun v => main _ v rfl

/-! ### Necessity -/

variable (α) in
/-- The side of an open end read off the bits: right iff the end comes before its partner in the
word of the target node of the partner. -/
noncomputable def sides0 (β : Nat → Bool) (e : Nat) : Bool :=
  open Classical in decide (Before (P.W β (P.tgt (α e))) e (α e))

/-- The nodes of the subtree of `t`. -/
inductive Below (t : Nat) : Nat → Prop where
  | refl : Below t t
  | step {w c : Nat} : Below t w → Item.node c ∈ P.parts w → Below t c

/-- **Necessity.** If the word of `t` is well nested and closed, the sides read off the bits make
the open ends of every node below `t` a valley. -/
theorem nec (hα : ∀ x, α (α x) = x) (hK : ∀ v, P.Kind α key v) {β : Nat → Bool} {t : Nat}
    (hWN : WN α (P.W β t)) (hcl : openEnds α (P.W β t) = []) :
    ∀ v, P.Below t v → WN α (P.W β v) ∧ Valley (P.sides0 α β) key (openEnds α (P.W β v)) := by
  have hnd := P.W_nodup hK β
  intro v hb
  induction hb with
  | refl => exact ⟨hWN, by rw [hcl]; exact List.Pairwise.nil⟩
  | @step w c _ hc ih =>
    obtain ⟨hww, hwv⟩ := ih
    cases hK w with
    | leaf h => rw [h] at hc; simp at hc
    | out e h _ => rw [h] at hc; simp at hc
    | single c' h =>
      rw [h, List.mem_singleton] at hc
      cases hc
      rw [W_single P (P.ord_one h)] at hww hwv
      exact ⟨hww, hwv⟩
    | target c' d ht =>
      have hcc : c = c' := by
        rcases ht.parts with h | h <;> rw [h] at hc <;> simp at hc <;> exact hc
      subst hcc
      have hcn := hnd c
      have hdin : α d ∈ P.W β c := P.mem_W_D.mpr ht.mem
      have hdout : d ∉ P.W β c := fun h => ht.not_mem (P.mem_W_D.mp h)
      have hdd : α d ≠ d := fun e => hdout (e ▸ hdin)
      let O := openEnds α (P.W β c)
      have hdO : α d ∈ O := mem_openEnds.mpr ⟨hdin, by rw [hα]; exact hdout⟩
      have hOnd : O.Nodup := hcn.filter _
      have hdeep : ∀ y ∈ O, y ≠ α d → key y < key (α d) := by
        intro y hy hyd
        obtain ⟨h1, h2⟩ := mem_openEnds.mp hy
        exact ht.deep y (P.mem_W_D.mp h1) (fun h => h2 (P.mem_W_D.mpr h)) hyd
      have hsd : P.sides0 α β (α d) = true ↔ Before (P.W β w) (α d) d := by
        unfold sides0; rw [hα, ht.tgt]; exact @decide_eq_true_iff _ (Classical.propDecidable _)
      have hpp := ht.parts
      have hw : P.W β w = d :: P.W β c ∨ P.W β w = P.W β c ++ [d] := by
        rcases hpp with h | h <;> rcases P.ord_two (β := β) h with ho | ho <;> rw [W_pair P ho] <;>
          simp [partW]
      rcases hw with hw | hw
      · rw [hw] at hww hwv hsd
        have hfirst : ∀ y ∈ O, y ≠ α d → Before O (α d) y := by
          intro y hy hyd
          obtain ⟨h1, h2⟩ := mem_openEnds.mp hy
          rcases before_total h1 hdin hyd with hb | hb
          · exfalso
            have := (hww d y (before_cons_iff.mpr (Or.inl ⟨rfl, h1⟩))
              (before_cons_iff.mpr (Or.inr hb))).1
            have hay := (before_mem this).2
            rcases List.mem_cons.mp hay with e | e
            · exact hyd (by rw [← hα y, e])
            · exact h2 e
          · exact before_filter_iff.mpr ⟨hb, by simp [hα, hdout], by simpa using h2⟩
        have hO : O = α d :: openEnds α (P.W β w) := by
          rw [hw, openEnds_cons_close hα hdin]
          exact eq_cons_of_first hOnd hdO hfirst
        refine ⟨wn_infix (A := [d]) (B := []) (by simpa using List.nodup_cons.mpr ⟨hdout, hcn⟩)
          (by simpa using hww), ?_⟩
        show Valley _ key O
        rw [hO]
        apply valley_cons (by rw [hw]; exact hwv)
        · apply Bool.eq_false_iff.mpr
          intro h0
          rcases before_cons_iff.mp (hsd.mp h0) with ⟨e, _⟩ | hb
          · exact hdd e
          · exact hdout (before_mem hb).2
        · intro y hy
          rw [hw, openEnds_cons_close hα hdin] at hy
          obtain ⟨h1, h2⟩ := List.mem_filter.mp hy
          exact hdeep y h1 (by simpa using h2)
      · rw [hw] at hww hwv hsd
        have hlast : ∀ y ∈ O, y ≠ α d → Before O y (α d) := by
          intro y hy hyd
          obtain ⟨h1, h2⟩ := mem_openEnds.mp hy
          rcases before_total h1 hdin hyd with hb | hb
          · exact before_filter_iff.mpr ⟨hb, by simpa using h2, by simp [hα, hdout]⟩
          · exfalso
            have := (hww (α d) y (before_append_left hb)
              (by rw [hα]; exact before_append_mid h1 (List.mem_singleton_self d))).1
            have hay := (before_mem this).2
            rcases List.mem_append.mp hay with e | e
            · exact h2 e
            · rw [List.mem_singleton] at e; exact hyd (by rw [← hα y, e])
        have hO : O = openEnds α (P.W β w) ++ [α d] := by
          rw [hw, openEnds_snoc_close hα hdin]
          exact eq_snoc_of_last hOnd hdO hlast
        refine ⟨wn_infix (A := []) (B := [d])
          (by simpa using List.nodup_append.mpr ⟨hcn, nodup_one d,
            fun a ha b hb => by rw [List.mem_singleton] at hb; subst hb; exact fun e => hdout (e ▸ ha)⟩)
          (by simpa using hww), ?_⟩
        show Valley _ key O
        rw [hO]
        apply valley_snoc (by rw [hw]; exact hwv)
        · exact hsd.mpr (before_append_mid hdin (List.mem_singleton_self d))
        · intro y hy
          rw [hw, openEnds_snoc_close hα hdin] at hy
          obtain ⟨h1, h2⟩ := List.mem_filter.mp hy
          exact hdeep y h1 (by simpa using h2)
    | fork p q hf =>
      have pq : ∀ a ∈ P.partW β p, α a ∉ P.partW β q :=
        fun a ha h => hf.pq a (P.mem_partW.mp ha) (P.mem_partW.mp h)
      have qp : ∀ a ∈ P.partW β q, α a ∉ P.partW β p :=
        fun a ha h => hf.qp a (P.mem_partW.mp ha) (P.mem_partW.mp h)
      have hcpq : p = .node c ∨ q = .node c := by
        rw [hf.parts] at hc; simp at hc
        rcases hc with h | h
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      have hwn := hnd w
      rcases P.ord_two (β := β) hf.parts with ho | ho <;> rw [W_pair P ho] at hww hwv hwn
      · rw [openEnds_append pq qp] at hwv
        rcases hcpq with rfl | rfl
        · refine ⟨wn_infix (A := []) (B := P.partW β q) (by simpa [partW] using hwn) (by simpa [partW] using hww), ?_⟩
          exact List.Pairwise.sublist (List.sublist_append_left _ _) hwv
        · refine ⟨wn_infix (A := P.partW β p) (B := []) (by simpa [partW] using hwn) (by simpa [partW] using hww), ?_⟩
          exact List.Pairwise.sublist (List.sublist_append_right _ _) hwv
      · rw [openEnds_append qp pq] at hwv
        rcases hcpq with rfl | rfl
        · refine ⟨wn_infix (A := P.partW β q) (B := []) (by simpa [partW] using hwn) (by simpa [partW] using hww), ?_⟩
          exact List.Pairwise.sublist (List.sublist_append_right _ _) hwv
        · refine ⟨wn_infix (A := []) (B := P.partW β p) (by simpa [partW] using hwn) (by simpa [partW] using hww), ?_⟩
          exact List.Pairwise.sublist (List.sublist_append_left _ _) hwv

/-- At a fork whose open ends form a valley, the parts satisfy `ForkOK`. -/
theorem forkOK_of_valley {s β : Nat → Bool} {v : Nat} {p q : Item} (hf : P.IsFork α key v p q)
    (hv : Valley s key (openEnds α (P.W β v))) : P.ForkOK α key s p q := by
  have pq : ∀ a ∈ P.partW β p, α a ∉ P.partW β q :=
    fun a ha h => hf.pq a (P.mem_partW.mp ha) (P.mem_partW.mp h)
  have qp : ∀ a ∈ P.partW β q, α a ∉ P.partW β p :=
    fun a ha h => hf.qp a (P.mem_partW.mp ha) (P.mem_partW.mp h)
  have mo : ∀ it e, e ∈ openEnds α (P.partW β it) ↔ e ∈ openEnds α (P.ID it) :=
    fun it e => mem_openEnds_congr (fun x => P.mem_partW)
  rcases P.ord_two (β := β) hf.parts with ho | ho <;> rw [W_pair P ho] at hv
  · rw [openEnds_append pq qp] at hv
    exact Or.inl fun e he f hf' => (List.pairwise_append.mp hv).2.2 e ((mo p e).mpr he) f ((mo q f).mpr hf')
  · rw [openEnds_append qp pq] at hv
    exact Or.inr fun e he f hf' => (List.pairwise_append.mp hv).2.2 f ((mo q f).mpr hf') e ((mo p e).mpr he)

/-- Every fork below a well-nested closed word satisfies `ForkOK` for the sides read off the bits. -/
theorem nec_forkOK (hα : ∀ x, α (α x) = x) (hK : ∀ v, P.Kind α key v) {β : Nat → Bool} {t : Nat}
    (hWN : WN α (P.W β t)) (hcl : openEnds α (P.W β t) = []) {v : Nat} (hb : P.Below t v) {p q : Item}
    (hf : P.IsFork α key v p q) : P.ForkOK α key (P.sides0 α β) p q :=
  P.forkOK_of_valley hf (P.nec hα hK hWN hcl v hb).2

/-! ### Bits from sides -/

theorem not_target_and_fork {v c d : Nat} {p q : Item} (ht : P.IsTarget α key v c d)
    (hf : P.IsFork α key v p q) : False := by
  rcases ht.parts with h | h <;> rw [hf.parts] at h <;> simp at h <;> obtain ⟨rfl, rfl⟩ := h
  · exact hf.qp d (by simp [ID, partW]) (by simpa [ID, partW, D] using ht.mem)
  · exact hf.pq d (by simp [ID, partW]) (by simpa [ID, partW, D] using ht.mem)

/-- **Bits from sides.** If every fork satisfies `ForkOK`, some bits place every part as the sides
prescribe. -/
theorem exists_placed (hK : ∀ v, P.Kind α key v) {s : Nat → Bool}
    (hF : ∀ v p q, P.IsFork α key v p q → P.ForkOK α key s p q) :
    ∃ β, ∀ v, P.Placed α key s β v := by
  have hex : ∀ v, ∃ b : Bool, P.Placed α key s (fun _ => b) v := by
    intro v
    cases hK v with
    | leaf h =>
      refine ⟨false, fun c d ht => ?_, fun p q hf => ?_⟩
      · rcases ht.parts with h' | h' <;> rw [h] at h' <;> simp at h'
      · have := hf.parts; rw [h] at this; simp at this
    | out e h _ =>
      refine ⟨false, fun c d ht => ?_, fun p q hf => ?_⟩
      · rcases ht.parts with h' | h' <;> rw [h] at h' <;> simp at h'
      · have := hf.parts; rw [h] at this; simp at this
    | single c h =>
      refine ⟨false, fun c d ht => ?_, fun p q hf => ?_⟩
      · rcases ht.parts with h' | h' <;> rw [h] at h' <;> simp at h'
      · have := hf.parts; rw [h] at this; simp at this
    | target c d ht =>
      have uniq : ∀ c' d', P.IsTarget α key v c' d' → c' = c ∧ d' = d := by
        intro c' d' ht'
        rcases ht.parts with h | h <;> rcases ht'.parts with h' | h' <;> rw [h] at h' <;> simp at h' <;>
          constructor <;> omega
      rcases ht.parts with h | h
      · refine ⟨!s (α d), fun c' d' ht' => ?_, fun p q hf => absurd (P.not_target_and_fork ht hf) id⟩
        obtain ⟨e1, e2⟩ := uniq c' d' ht'
        rw [e1, e2]
        cases hs : s (α d) <;> simp [ord, h]
      · refine ⟨s (α d), fun c' d' ht' => ?_, fun p q hf => absurd (P.not_target_and_fork ht hf) id⟩
        obtain ⟨e1, e2⟩ := uniq c' d' ht'
        rw [e1, e2]
        cases hs : s (α d) <;> simp [ord, h]
    | fork p q hf =>
      have uniq : ∀ p' q', P.IsFork α key v p' q' → p' = p ∧ q' = q := by
        intro p' q' hf'
        have := hf'.parts; rw [hf.parts] at this; simp at this; exact ⟨this.1.symm, this.2.symm⟩
      rcases hF v p q hf with hx | hx
      · refine ⟨false, fun c d ht => absurd (P.not_target_and_fork ht hf) id, fun p' q' hf' => ?_⟩
        obtain ⟨rfl, rfl⟩ := uniq p' q' hf'
        exact Or.inl ⟨by unfold ord; rw [hf.parts]; rfl, hx⟩
      · refine ⟨true, fun c d ht => absurd (P.not_target_and_fork ht hf) id, fun p' q' hf' => ?_⟩
        obtain ⟨rfl, rfl⟩ := uniq p' q' hf'
        exact Or.inr ⟨by unfold ord; rw [hf.parts]; rfl, hx⟩
  refine ⟨fun v => Classical.choose (hex v), fun v => ?_⟩
  have h := Classical.choose_spec (hex v)
  have e : P.ord (fun v => Classical.choose (hex v)) v = P.ord (fun _ => Classical.choose (hex v)) v := rfl
  exact ⟨fun c d ht => e ▸ h.1 c d ht, fun p q hf => e ▸ h.2 p q hf⟩

end Plan

end STACS2027.Embed
