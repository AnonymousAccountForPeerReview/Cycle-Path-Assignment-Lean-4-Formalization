module

public import ApproximationHardness.Embed.SolverInv
import Lean.Elab.Tactic.Omega

/-!
# Correctness of the solver

If some sides satisfy every fork (`ForkOK`), then for every orientation `o` of the groups that is
consistent with the merges (`Consistent`), the sides `o` and the bits `bit o` place every part of
every node (`placed_all`); so every word is well nested (`wn_all`).
-/

@[expose] public section

namespace STACS2027.Embed

namespace Plan

variable (P : Plan) {α : Nat → Nat} {key : Nat → Nat}

theorem mem_ID_dart {d e : Nat} : e ∈ P.ID (.dart d) ↔ e = d := by
  simp [ID, partW]

theorem mem_ID_node {c e : Nat} : e ∈ P.ID (.node c) ↔ e ∈ P.D c := Iff.rfl

theorem openEnds_dart {d e : Nat} (hd : α d ≠ d) : e ∈ openEnds α (P.ID (.dart d)) ↔ e = d := by
  rw [mem_openEnds, P.mem_ID_dart, P.mem_ID_dart]
  constructor
  · exact fun h => h.1
  · rintro rfl; exact ⟨rfl, hd⟩

theorem openEnds_D_nil {v e : Nat} (h : P.parts v = []) : e ∉ openEnds α (P.D v) := by
  rw [mem_openEnds, P.mem_D, h]; simp

theorem openEnds_D_one {v e : Nat} {it : Item} (h : P.parts v = [it]) :
    e ∈ openEnds α (P.D v) ↔ e ∈ openEnds α (P.ID it) := by
  simp only [mem_openEnds, P.mem_D, h, List.mem_singleton, exists_eq_left]

theorem openEnds_D_target (hα : ∀ x, α (α x) = x) {v c d : Nat} (ht : P.IsTarget α key v c d) (e : Nat) :
    e ∈ openEnds α (P.D v) ↔ e ∈ openEnds α (P.D c) ∧ e ≠ α d := by
  have hD : ∀ x, x ∈ P.D v ↔ x ∈ P.D c ∨ x = d := by
    intro x
    rw [P.mem_D]
    rcases ht.parts with h | h <;> rw [h] <;> simp [P.mem_ID_dart, P.mem_ID_node, or_comm]
  rw [mem_openEnds, mem_openEnds, hD, hD]
  constructor
  · rintro ⟨h1 | rfl, h2⟩
    · refine ⟨⟨h1, fun h => h2 (Or.inl h)⟩, fun e' => h2 (Or.inr (by rw [e', hα]))⟩
    · exact absurd (Or.inl ht.mem) h2
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨Or.inl h1, ?_⟩
    rintro (h | h)
    · exact h2 h
    · exact h3 (by rw [← h, hα])

theorem openEnds_D_fork {v : Nat} {p q : Item} (hf : P.IsFork α key v p q) (e : Nat) :
    e ∈ openEnds α (P.D v) ↔ e ∈ openEnds α (P.ID p) ∨ e ∈ openEnds α (P.ID q) := by
  have hD : ∀ x, x ∈ P.D v ↔ x ∈ P.ID p ∨ x ∈ P.ID q := by
    intro x; rw [P.mem_D, hf.parts]; simp
  rw [mem_openEnds, mem_openEnds, mem_openEnds, hD, hD]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact Or.inl ⟨h1, fun h => h2 (Or.inl h)⟩
    · exact Or.inr ⟨h1, fun h => h2 (Or.inr h)⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · refine ⟨Or.inl h1, ?_⟩
      rintro (h | h)
      · exact h2 h
      · exact hf.pq e h1 h
    · refine ⟨Or.inr h1, ?_⟩
      rintro (h | h)
      · exact hf.qp e h1 h
      · exact h2 h

end Plan

namespace Sol

variable (S : Sol)

/-- The hypotheses on the data of the solver. -/
structure Good : Prop where
  invol : ∀ x, S.α (S.α x) = x
  kind : ∀ v, S.P.Kind S.α S.key v
  isIn_target : ∀ v c d, S.P.IsTarget S.α S.key v c d → S.isIn d = true
  isIn_fork : ∀ v c d, S.P.IsFork S.α S.key v (.node c) (.dart d) ∨ S.P.IsFork S.α S.key v (.dart d) (.node c) →
    S.isIn d = false
  bound : ∀ v, ∀ e ∈ S.P.D v, S.key e + 1 < S.INF

variable {S}

theorem forkOK_ab {s : Nat → Bool} {p q : Item} (h : S.P.ForkOK S.α S.key s p q) :
    (∀ a b, a ∈ openEnds S.α (S.P.ID p) → b ∈ openEnds S.α (S.P.ID q) → VR s S.key a b) ∨
      (∀ a b, a ∈ openEnds S.α (S.P.ID p) → b ∈ openEnds S.α (S.P.ID q) → VR s S.key b a) :=
  h.imp (fun h a b ha hb => h a ha b hb) (fun h a b ha hb => h a ha b hb)

section good

variable (G : S.Good)
include G

theorem Good.twoRes_fork {v : Nat} {p q : Item} (hf : S.P.IsFork S.α S.key v p q) (rp rq : Res) :
    S.twoRes v p q rp rq = S.forkRes v rp rq := by
  cases p with
  | node c =>
    cases q with
    | node c' => rfl
    | dart d => simp only [twoRes]; rw [G.isIn_fork v c d (Or.inl hf)]; rfl
  | dart d =>
    cases q with
    | node c => simp only [twoRes]; rw [G.isIn_fork v c d (Or.inr hf)]; rfl
    | dart d' => rfl

theorem Good.twoCons_fork {v : Nat} {p q : Item} (hf : S.P.IsFork S.α S.key v p q) (rp rq : Res) :
    S.twoCons p q rp rq = S.forkCons rp rq := by
  cases p with
  | node c =>
    cases q with
    | node c' => rfl
    | dart d => simp only [twoCons]; rw [G.isIn_fork v c d (Or.inl hf)]; rfl
  | dart d =>
    cases q with
    | node c => simp only [twoCons]; rw [G.isIn_fork v c d (Or.inr hf)]; rfl
    | dart d' => rfl

theorem Good.twoBit_fork {v : Nat} {p q : Item} (hf : S.P.IsFork S.α S.key v p q) (o : Nat → Bool) (rp rq : Res) :
    S.twoBit v o p q rp rq = S.forkBit v o rp rq := by
  cases p with
  | node c =>
    cases q with
    | node c' => rfl
    | dart d => simp only [twoBit]; rw [G.isIn_fork v c d (Or.inl hf)]; rfl
  | dart d =>
    cases q with
    | node c => simp only [twoBit]; rw [G.isIn_fork v c d (Or.inr hf)]; rfl
    | dart d' => rfl

theorem Good.solve_target {v c d : Nat} (ht : S.P.IsTarget S.α S.key v c d) :
    S.solve v = S.closeRes (S.α d) (S.solve c) := by
  have hin := G.isIn_target v c d ht
  rcases ht.parts with h | h <;> rw [S.solve_two h] <;> simp [twoRes, hin, rpart]

theorem Good.consAt_target {v c d : Nat} (ht : S.P.IsTarget S.α S.key v c d) : S.consAt v = [] := by
  have hin := G.isIn_target v c d ht
  rcases ht.parts with h | h <;> simp [consAt, h, twoCons, hin]

/-- The result of a part satisfies the invariant. -/
theorem Good.rpart_inv {s0 : Nat → Bool} {v : Nat} {it : Item} (hit : it ∈ S.P.parts v)
    (hd : ∀ e, it = .dart e → S.α e ≠ e)
    (IH : ∀ c, it = .node c → S.Inv s0 (· ∈ openEnds S.α (S.P.D c)) (S.solve c)) :
    S.Inv s0 (· ∈ openEnds S.α (S.P.ID it)) (S.rpart it) := by
  cases it with
  | node c => exact IH c rfl
  | dart e =>
    have hb : S.key e + 1 < S.INF := G.bound v e (S.P.mem_D.mpr ⟨_, hit, (S.P.mem_ID_dart).mpr rfl⟩)
    exact (inv_dart s0 hb).congr fun x => ((S.P.openEnds_dart (hd e rfl)).symm)

/-- **The invariant of every node.** -/
theorem Good.solve_inv {s0 : Nat → Bool} (hs0 : ∀ v p q, S.P.IsFork S.α S.key v p q → S.P.ForkOK S.α S.key s0 p q) :
    ∀ v, S.Inv s0 (· ∈ openEnds S.α (S.P.D v)) (S.solve v) := by
  have main : ∀ k v, S.P.ht v = k → S.Inv s0 (· ∈ openEnds S.α (S.P.D v)) (S.solve v) := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro v hv
      have IH : ∀ c, Item.node c ∈ S.P.parts v → S.Inv s0 (· ∈ openEnds S.α (S.P.D c)) (S.solve c) :=
        fun c hc => ih _ (by rw [← hv]; exact S.P.ht_lt v c hc) c rfl
      cases G.kind v with
      | leaf h =>
        rw [S.solve_nil h]
        exact (inv_empty s0).congr fun e => ⟨False.elim, fun h' => S.P.openEnds_D_nil h h'⟩
      | out e h he =>
        rw [S.solve_one h]
        have hit : Item.dart e ∈ S.P.parts v := by rw [h]; simp
        exact (G.rpart_inv hit (fun e' h' => by cases h'; exact he) (fun c h' => by cases h')).congr
          fun x => (S.P.openEnds_D_one h).symm
      | single c h =>
        rw [S.solve_one h]
        exact (IH c (by rw [h]; simp)).congr fun x => (S.P.openEnds_D_one h).symm
      | target c d ht =>
        rw [G.solve_target ht]
        have hc : Item.node c ∈ S.P.parts v := by rcases ht.parts with h | h <;> rw [h] <;> simp
        have hx : S.α d ∈ openEnds S.α (S.P.D c) := mem_openEnds.mpr ⟨ht.mem, by rw [G.invol]; exact ht.not_mem⟩
        have hmax : ∀ y, y ∈ openEnds S.α (S.P.D c) → y ≠ S.α d → S.key y < S.key (S.α d) := by
          intro y hy hyd
          obtain ⟨h1, h2⟩ := mem_openEnds.mp hy
          exact ht.deep y h1 h2 hyd
        exact (inv_close (IH c hc) hx hmax).congr fun e => (S.P.openEnds_D_target G.invol ht e).symm
      | fork p q hf =>
        rw [S.solve_two hf.parts, G.twoRes_fork hf]
        have hp : p ∈ S.P.parts v := by rw [hf.parts]; simp
        have hq : q ∈ S.P.parts v := by rw [hf.parts]; simp
        have ip := G.rpart_inv hp hf.dp (fun c h => IH c (h ▸ hp))
        have iq := G.rpart_inv hq hf.dq (fun c h => IH c (h ▸ hq))
        exact (inv_fork v ip iq (fun a b ha hb => hf.keys a ha b hb) (forkOK_ab (hs0 v p q hf))).congr
          fun e => (S.P.openEnds_D_fork hf e).symm
  exact fun v => main _ v rfl

end good

/-- The fork condition for the part reaching higher. -/
theorem lrc_of_fork {s0 : Nat → Bool} {A B : Nat → Prop} {rp rq : Res} (hp : S.Inv s0 A rp)
    (hq : S.Inv s0 B rq) (hne : ∀ a b, A a → B b → S.key a ≠ S.key b)
    (hok : (∀ a b, A a → B b → VR s0 S.key a b) ∨ (∀ a b, A a → B b → VR s0 S.key b a)) :
    (rp.low < rq.low → S.LRC s0 A B) ∧ (¬ rp.low < rq.low → S.LRC s0 B A) := by
  refine ⟨fun hlt => ?_, fun hge => ?_⟩
  · refine lrc_of_vr ?_ hok
    have hpe : rp.seg ≠ [] := by
      intro h; have := hp.low_eq h; have := hq.low_le; omega
    obtain ⟨m, hmA, hlm, -, -⟩ := hp.low_lt hpe
    refine ⟨m, hmA, fun b hb => ?_⟩
    obtain ⟨m', hmB, hlm', hmin', -⟩ := hq.low_lt (fun h => hq.empty_of h b hb)
    have := hmin' b hb
    omega
  · by_cases hpe : rp.seg = []
    · exact ⟨true, fun a ha => absurd ha (hp.empty_of hpe a), fun b _ ⟨a, ha, _⟩ => absurd ha (hp.empty_of hpe a)⟩
    · obtain ⟨m, hmA, hlm, hmin, hbm⟩ := hp.low_lt hpe
      have hqe : rq.seg ≠ [] := by intro h; have := hq.low_eq h; omega
      obtain ⟨m', hmB, hlm', hmin', -⟩ := hq.low_lt hqe
      have hk : S.key m' < S.key m := by have := hne m m' hmA hmB; omega
      have hok' : (∀ b a, B b → A a → VR s0 S.key b a) ∨ (∀ b a, B b → A a → VR s0 S.key a b) := by
        rcases hok with h | h
        · exact Or.inr fun b a hb ha => h a b ha hb
        · exact Or.inl fun b a hb ha => h a b ha hb
      refine lrc_of_vr ⟨m', hmB, fun a ha => ?_⟩ hok'
      have := hmin a ha
      have := hne a m' ha hmB
      omega

section good

variable (G : S.Good)
include G

omit G in
theorem Good.rpart_oinv {o : Nat → Bool} {it : Item} (IH : ∀ c, it = .node c → OInv o (S.solve c).seg) :
    OInv o (S.rpart it).seg := by
  cases it with
  | node c => exact IH c rfl
  | dart e => exact oinv_dart o e

/-- **The orientation invariant of every node.** -/
theorem Good.solve_oinv {s0 : Nat → Bool} (hs0 : ∀ v p q, S.P.IsFork S.α S.key v p q → S.P.ForkOK S.α S.key s0 p q)
    {o : Nat → Bool} (ho : S.Consistent o) : ∀ v, OInv o (S.solve v).seg := by
  have hI := G.solve_inv hs0
  have main : ∀ k v, S.P.ht v = k → OInv o (S.solve v).seg := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro v hv
      have IH : ∀ c, Item.node c ∈ S.P.parts v → OInv o (S.solve c).seg :=
        fun c hc => ih _ (by rw [← hv]; exact S.P.ht_lt v c hc) c rfl
      cases G.kind v with
      | leaf h => rw [S.solve_nil h]; exact oinv_nil o
      | out e h he => rw [S.solve_one h]; exact oinv_dart o e
      | single c h => rw [S.solve_one h]; exact IH c (by rw [h]; simp)
      | target c d ht =>
        rw [G.solve_target ht]
        have hc : Item.node c ∈ S.P.parts v := by rcases ht.parts with h | h <;> rw [h] <;> simp
        exact oinv_close (IH c hc) _
      | fork p q hf =>
        rw [S.solve_two hf.parts, G.twoRes_fork hf]
        have hp : p ∈ S.P.parts v := by rw [hf.parts]; simp
        have hq : q ∈ S.P.parts v := by rw [hf.parts]; simp
        have ip := G.rpart_inv (s0 := s0) hp hf.dp (fun c h => hI c)
        have iq := G.rpart_inv (s0 := s0) hq hf.dq (fun c h => hI c)
        have op := Good.rpart_oinv (o := o) (it := p) (fun c h => IH c (h ▸ hp))
        have oq := Good.rpart_oinv (o := o) (it := q) (fun c h => IH c (h ▸ hq))
        have hne : ∀ a b, a ∈ openEnds S.α (S.P.ID p) → b ∈ openEnds S.α (S.P.ID q) → S.key a ≠ S.key b :=
          fun a b ha hb => hf.keys a ha b hb
        have hL := lrc_of_fork ip iq hne (forkOK_ab (hs0 v p q hf))
        have hc : ∀ x ∈ S.forkCons (S.rpart p) (S.rpart q), o x.1 = (o (S.gid v) ^^ x.2) := by
          intro x hx
          apply ho v x
          unfold consAt; rw [hf.parts]; simp only; rw [G.twoCons_fork hf]; exact hx
        unfold forkRes; unfold forkCons at hc
        split
        · rename_i hlt
          rw [ite_eq_left hlt] at hc
          exact (oinv_merge v ip iq hne (hL.1 hlt) op oq hc).1
        · rename_i hge
          rw [ite_eq_right hge] at hc
          exact (oinv_merge v iq ip (fun b a hb ha e => hne a b ha hb e.symm) (hL.2 hge) oq op hc).1
  exact fun v => main _ v rfl

omit G in
theorem Good.ord_bit_two {o : Nat → Bool} {v : Nat} {p q : Item} (h : S.P.parts v = [p, q]) :
    S.P.ord (S.bit o) v = if S.twoBit v o p q (S.rpart p) (S.rpart q) then [q, p] else [p, q] := by
  unfold Plan.ord bit; rw [h]; simp only
  split <;> simp

/-- **Correctness of the solver**: the sides `o` and the bits `bit o` place every part of every
node. -/
theorem Good.placed_all {s0 : Nat → Bool} (hs0 : ∀ v p q, S.P.IsFork S.α S.key v p q → S.P.ForkOK S.α S.key s0 p q)
    {o : Nat → Bool} (ho : S.Consistent o) : ∀ v, S.P.Placed S.α S.key o (S.bit o) v := by
  have hI := G.solve_inv hs0
  have hO := G.solve_oinv hs0 ho
  intro v
  refine ⟨fun c d ht => ?_, fun p q hf => ?_⟩
  · have hin := G.isIn_target v c d ht
    rcases ht.parts with h | h
    · rw [Good.ord_bit_two h]; cases hod : o (S.α d) <;> simp [twoBit, hin, hod]
    · rw [Good.ord_bit_two h]; cases hod : o (S.α d) <;> simp [twoBit, hin, hod]
  · rw [Good.ord_bit_two hf.parts, G.twoBit_fork hf]
    have hp : p ∈ S.P.parts v := by rw [hf.parts]; simp
    have hq : q ∈ S.P.parts v := by rw [hf.parts]; simp
    have ip := G.rpart_inv (s0 := s0) hp hf.dp (fun c h => hI c)
    have iq := G.rpart_inv (s0 := s0) hq hf.dq (fun c h => hI c)
    have op := Good.rpart_oinv (o := o) (it := p) (fun c h => hO c)
    have oq := Good.rpart_oinv (o := o) (it := q) (fun c h => hO c)
    have hne : ∀ a b, a ∈ openEnds S.α (S.P.ID p) → b ∈ openEnds S.α (S.P.ID q) → S.key a ≠ S.key b :=
      fun a b ha hb => hf.keys a ha b hb
    have hL := lrc_of_fork ip iq hne (forkOK_ab (hs0 v p q hf))
    have hc : ∀ x ∈ S.forkCons (S.rpart p) (S.rpart q), o x.1 = (o (S.gid v) ^^ x.2) := by
      intro x hx
      apply ho v x
      unfold consAt; rw [hf.parts]; simp only; rw [G.twoCons_fork hf]; exact hx
    unfold forkCons at hc
    unfold forkBit
    split
    · rename_i hlt
      rw [ite_eq_left hlt] at hc
      split
      · rename_i hqe
        exact Or.inl ⟨by simp, fun e he f hf' => absurd hf' (iq.empty_of hqe f)⟩
      · rename_i hqe
        obtain ⟨hB, hA⟩ := (oinv_merge v ip iq hne (hL.1 hlt) op oq hc).2 hqe
        have V := vr_of_lrc (σ := !o (S.gid v)) hne hB (fun a ha hr => by rw [hA a ha hr]; simp)
        cases hg : o (S.gid v)
        · exact Or.inl ⟨by simp, fun e he f hf' => V.1 (by simp [hg]) e f he hf'⟩
        · exact Or.inr ⟨by simp, fun e he f hf' => V.2 (by simp [hg]) e f he hf'⟩
    · rename_i hge
      rw [ite_eq_right hge] at hc
      split
      · rename_i hpe
        exact Or.inl ⟨by simp, fun e he f hf' => absurd he (ip.empty_of hpe e)⟩
      · rename_i hpe
        have hne' : ∀ b a, b ∈ openEnds S.α (S.P.ID q) → a ∈ openEnds S.α (S.P.ID p) → S.key b ≠ S.key a :=
          fun b a hb ha e => hne a b ha hb e.symm
        obtain ⟨hB, hA⟩ := (oinv_merge v iq ip hne' (hL.2 hge) oq op hc).2 hpe
        have V := vr_of_lrc (σ := !o (S.gid v)) hne' hB (fun a ha hr => by rw [hA a ha hr]; simp)
        cases hg : o (S.gid v)
        · exact Or.inr ⟨by simp, fun e he f hf' => V.1 (by simp [hg]) f e hf' he⟩
        · exact Or.inl ⟨by simp, fun e he f hf' => V.2 (by simp [hg]) f e hf' he⟩

/-- Every word is well nested for the bits of a consistent orientation. -/
theorem Good.wn_all {s0 : Nat → Bool} (hs0 : ∀ v p q, S.P.IsFork S.α S.key v p q → S.P.ForkOK S.α S.key s0 p q)
    {o : Nat → Bool} (ho : S.Consistent o) : ∀ v, WN S.α (S.P.W (S.bit o) v) :=
  fun v => (S.P.suff G.invol G.kind (G.placed_all hs0 ho) v).1

end good

end Sol

end STACS2027.Embed
