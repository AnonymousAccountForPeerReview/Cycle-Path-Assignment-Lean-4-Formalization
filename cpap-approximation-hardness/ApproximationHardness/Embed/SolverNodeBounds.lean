module

public import ApproximationHardness.Embed.SolverBounds

/-! # Bounds for node initialization and the full solver dispatch -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

theorem MemoryBounds.store {m : SMem} {width darts h : Nat}
    (H : MemoryBounds m width darts) (hh : h ≤ width) (v l : Nat) :
    MemoryBounds (m.store v h l) width darts := by
  refine ⟨H.successor, H.positiveHead, H.negativeHead, H.positiveTail,
    H.negativeTail, H.nextGroup, ?_⟩
  intro w; dsimp only [SMem.store]; unfold upd
  split; exact hh; exact H.resultHead w

theorem MemoryBounds.inf_frame {m : SMem} {width darts : Nat}
    (H : MemoryBounds m width darts) (v code : Nat) :
    MemoryBounds {m with inf := upd m.inf v code} width darts :=
  ⟨H.successor, H.positiveHead, H.negativeHead, H.positiveTail,
    H.negativeTail, H.nextGroup, H.resultHead⟩

theorem MemoryBounds.ia_frame {m : SMem} {width darts : Nat}
    (H : MemoryBounds m width darts) (v e : Nat) :
    MemoryBounds {m with ia := upd m.ia v e} width darts :=
  ⟨H.successor, H.positiveHead, H.negativeHead, H.positiveTail,
    H.negativeTail, H.nextGroup, H.resultHead⟩

theorem MemoryBounds.itRes (S : Sol) {m : SMem} {width darts : Nat}
    (H : MemoryBounds m width darts) (hdw : darts ≤ width) (it : Item)
    (hit : ∀ e, it = .dart e → e < darts) :
    MemoryBounds (S.itRes m it).1 width darts ∧ (S.itRes m it).2.1 ≤ width := by
  cases it with
  | node c => exact ⟨H, H.resultHead c⟩
  | dart e =>
    have he : e + 1 ≤ darts := Nat.add_one_le_iff.mpr (hit e rfl)
    refine ⟨⟨H.successor, ?_, ?_, ?_, H.negativeTail, ?_, H.resultHead⟩,
      by simpa [Sol.itRes] using he.trans hdw⟩
    · intro g; dsimp only [Sol.itRes]; unfold upd; split; exact he; exact H.positiveHead g
    · intro g; dsimp only [Sol.itRes]; unfold upd; split; exact Nat.zero_le _; exact H.negativeHead g
    · intro g; dsimp only [Sol.itRes]; unfold upd; split; exact he.trans hdw; exact H.positiveTail g
    · intro g; dsimp only [Sol.itRes]; unfold upd; split; exact Nat.zero_le _; exact H.nextGroup g

theorem MemoryBounds.closeM (S : Sol) {m : SMem} {width darts h : Nat}
    (H : MemoryBounds m width darts) (hh : h ≤ width) (e l : Nat) :
    MemoryBounds (S.closeM m e h l).1 width darts ∧ (S.closeM m e h l).2.1 ≤ width := by
  unfold Sol.closeM
  split
  · exact ⟨H, Nat.zero_le _⟩
  · split
    · refine ⟨⟨H.successor, ?_, H.negativeHead, H.positiveTail, H.negativeTail,
        H.nextGroup, H.resultHead⟩, ?_⟩
      · intro g; dsimp only; unfold upd; split
        · split; exact Nat.zero_le _; exact H.successor e
        · exact H.positiveHead g
      · dsimp only
        repeat first | exact H.nextGroup (h - 1) | exact hh | split
    · refine ⟨⟨H.successor, H.positiveHead, ?_, H.positiveTail, H.negativeTail,
        H.nextGroup, H.resultHead⟩, ?_⟩
      · intro g; dsimp only; unfold upd; split
        · split; exact Nat.zero_le _; exact H.successor e
        · exact H.negativeHead g
      · dsimp only
        repeat first | exact H.nextGroup (h - 1) | exact hh | split

theorem StateBounds.forkStart (S : Sol) {L : Layout} {s : SMS} {m : SMem} {darts : Nat}
    (H : StateBounds L s darts) (Hm : MemoryBounds m L.width darts)
    (v hx lx hy ly code : Nat) (hv : v < L.width) (hg : S.gid v < L.width)
    (hhx : hx ≤ L.width) (hhy : hy ≤ L.width) :
    StateBounds L (S.forkStart s m v hx lx hy ly code) darts := by
  unfold Sol.forkStart
  split
  · exact ⟨H.width, H.dartWidth, (Hm.store hhx v lx).inf_frame v 0,
      H.node, H.group, H.upper, H.lower, H.positiveHead, H.negativeHead,
      H.lowerClassHead, H.positiveTail, H.negativeTail, H.lowerClassTail⟩
  · exact ⟨H.width, H.dartWidth, Hm.inf_frame v code,
      hv, hg, hhx, hhy, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
      Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

theorem StateBounds.twoStep (S : Sol) {L : Layout} {s : SMS} {darts v : Nat} {p q : Item}
    (H : StateBounds L s darts) (hv : v < L.width) (hg : S.gid v < L.width)
    (hp : ∀ e, p = .dart e → e < darts) (hq : ∀ e, q = .dart e → e < darts) :
    StateBounds L (S.twoStep s v p q) darts := by
  unfold Sol.twoStep
  split
  · rename_i c d ht
    have Hclose := H.memory.closeM S (H.memory.resultHead c) (S.α d) (s.m.rl c)
    exact ⟨H.width, H.dartWidth,
      ((Hclose.1.store Hclose.2 v _).inf_frame v (Sol.tcode p)).ia_frame v (S.α d),
      H.node, H.group, H.upper, H.lower, H.positiveHead, H.negativeHead,
      H.lowerClassHead, H.positiveTail, H.negativeTail, H.lowerClassTail⟩
  · have Hr := H.memory.itRes S H.dartWidth p hp
    have Hq := Hr.1.itRes S H.dartWidth q hq
    apply H.forkStart S Hq.1 _ _ _ _ _ _ hv hg
    · split; exact Hr.2; exact Hq.2
    · split; exact Hq.2; exact Hr.2

theorem StateBounds.nodeStep (S : Sol) {L : Layout} {s : SMS} {darts v : Nat}
    (H : StateBounds L s darts) (hv : v < L.width) (hg : S.gid v < L.width)
    (hp : ∀ it ∈ S.P.parts v, ∀ e, it = .dart e → e < darts) :
    StateBounds L (S.nodeStep s v) darts := by
  unfold Sol.nodeStep
  split
  · exact ⟨H.width, H.dartWidth, (H.memory.store (Nat.zero_le _) v S.INF).inf_frame v 0,
      H.node, H.group, H.upper, H.lower, H.positiveHead, H.negativeHead,
      H.lowerClassHead, H.positiveTail, H.negativeTail, H.lowerClassTail⟩
  · rename_i it he
    have Hi := H.memory.itRes S H.dartWidth it (hp it (by rw [he]; simp))
    exact ⟨H.width, H.dartWidth, (Hi.1.store Hi.2 v _).inf_frame v 0,
      H.node, H.group, H.upper, H.lower, H.positiveHead, H.negativeHead,
      H.lowerClassHead, H.positiveTail, H.negativeTail, H.lowerClassTail⟩
  · rename_i p q he
    exact H.twoStep S hv hg (hp p (by rw [he]; simp)) (hp q (by rw [he]; simp))
  · exact ⟨H.width, H.dartWidth, H.memory, H.node, H.group, H.upper, H.lower,
      H.positiveHead, H.negativeHead, H.lowerClassHead, H.positiveTail, H.negativeTail,
      H.lowerClassTail⟩

theorem mstep_bounded {L : Layout} {c : RAM.Config} {S : Sol} {post : List Nat}
    {s : SMS} {vertices darts : Nat} (H : StateBounds L s darts)
    (Ht : Tables L c S post vertices darts) : StateBounds L (S.mstep post s) darts := by
  unfold Sol.mstep
  split
  · split
    · rename_i v hv
      have hvm : v ∈ post := List.mem_of_getElem? hv
      have hvb := Ht.nodeBound v hvm
      apply H.nodeStep S (lt_of_lt_of_le hvb Ht.vertices) (Ht.groupsBound v hvb)
      intro it hit e he
      have Hchild := Ht.children v hvb it hit
      simpa [he] using Hchild
    · exact H
  · split
    · exact popStep_bounded S H
    · exact consStep_bounded H

theorem nodeStep_index (S : Sol) (s : SMS) (v : Nat) : (S.nodeStep s v).k = s.k + 1 := by
  unfold Sol.nodeStep
  split
  · rfl
  · rfl
  · unfold Sol.twoStep
    split
    · rfl
    · unfold Sol.forkStart; dsimp only
      repeat first | rfl | split
  · rfl

theorem mstep_index_le (S : Sol) (post : List Nat) {s : SMS}
    (H : s.k ≤ post.length) : (S.mstep post s).k ≤ post.length := by
  unfold Sol.mstep
  split
  · split
    · rename_i v hv
      have hk : s.k < post.length := (List.getElem?_eq_some_iff.mp hv).1
      rw [nodeStep_index]; omega
    · exact H
  · split
    · have Hidx : (S.popStep s).k = s.k := by simp only [Sol.popStep]; split <;> rfl
      rw [Hidx]; exact H
    · rw [Sol.consStep_index]; exact H

theorem mstep_iterate_bounded {L : Layout} {c : RAM.Config} {S : Sol} {post : List Nat}
    {s : SMS} {vertices darts : Nat} (H : StateBounds L s darts)
    (Ht : Tables L c S post vertices darts) :
    ∀ n, StateBounds L ((S.mstep post)^[n] s) darts := by
  intro n
  induction n with
  | zero => exact H
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact mstep_bounded ih Ht

theorem mstep_iterate_index_le (S : Sol) (post : List Nat) {s : SMS}
    (H : s.k ≤ post.length) : ∀ n, ((S.mstep post)^[n] s).k ≤ post.length := by
  intro n
  induction n with
  | zero => exact H
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact mstep_index_le S post ih

end STACS2027.Embed.RAMSolver
