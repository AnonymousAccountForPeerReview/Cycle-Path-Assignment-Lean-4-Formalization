module

public import Outerplanar.TwoConnectedK23Cycles
import Mathlib.Tactic

/-!
# Lemma 19, third sentence: 2-connected `K_{2,3}`-minor-free graphs

**Lemma 19**, third sentence, in combinatorial form (`twoConnectedK23_structure : TwoConnectedK23Structure`): every
2-connected `K_{2,3}`-minor-free graph is a `K₄` or has a Hamiltonian cycle with respect to which
no two of its edges cross (`Outerplanar/OuterplanarCharacterization.lean` turns the Hamiltonian cycle into an
outerplanar drawing). The proof takes a longest cycle `C` (cycles as in
`Outerplanar/TwoConnectedK23Cycles.lean`):

1. A cycle exists (`exists_isCyc`): a vertex `u` has two neighbours `v ≠ w` (`g - v` connects
   `u` to a third vertex), and a path from `v` to `w` in `g - u` closes a cycle through `u`.
2. A longest cycle is Hamiltonian (`longer_or_minor`, `exists_ham`): a vertex `h` off the cycle
   `C` reaches `C` (connectivity) and reaches `C - x` in `g - x` (2-connectivity), which gives
   two attachments `x ≠ y` on `C`, neighbours of vertices `hx`, `hy` reachable from `h` off `C`,
   and a path `Q` from `hx` to `hy` off `C`. If `x` and `y` are consecutive on `C`, `Q` makes
   `C` longer (`IsCyc.extend`); otherwise `{x}`, `{y}`, `Q` and the interiors of the two arcs of
   `C` between `x` and `y` are the branch sets of a `K_{2,3}` minor.
3. Crossing chords `ac`, `bd` of the Hamiltonian cycle (`crossing`): if the arc from `a` to `b`
   has an inner vertex, `{a}`, `{b}`, its interior, `{c}` with the interior of the arc from `b`
   to `c`, and `{d}` with the interior of the arc from `d` to `a` are the branch sets of a
   `K_{2,3}` minor (`crossing_core`; the other arcs by rotation). Otherwise the cycle is
   `a, b, c, d`, and `g` is the `K₄` on these vertices (`isK4Graph_of`).
4. Otherwise no two edges cross with respect to the longest cycle: `OuterplanarHam`.
-/

@[expose] public section

namespace STACS2027

namespace K23Struct

/-! ### A cycle exists -/

theorem two_le_length {l : List ℕ} {a b : ℕ} (ha : l.head? = some a) (hb : l.getLast? = some b)
    (hab : a ≠ b) : 2 ≤ l.length := by
  match l, ha, hb with
  | [], ha, _ => simp at ha
  | [x], ha, hb =>
    simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at ha hb
    exact absurd (ha.symm.trans hb) hab
  | _ :: _ :: _, _, _ => simp

/-- A 2-connected graph has a cycle. -/
theorem exists_isCyc {g : Graph} (hg : TwoConnected g) : ∃ C, IsCyc g C := by
  obtain ⟨⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩, -, hcut⟩ := hg
  obtain ⟨v, hva⟩ := ha
  obtain ⟨z, hz, hza, hzv⟩ : ∃ z, IsVertex g z ∧ z ≠ a ∧ z ≠ v := by
    by_cases hbv : b = v
    · subst hbv
      exact ⟨c, hc, Ne.symm hac, Ne.symm hbc⟩
    · exact ⟨b, hb, Ne.symm hab, hbv⟩
  have r : Reach g (fun x => IsVertex g x ∧ x ≠ v) a z :=
    connectedWithin_iff.mp (hcut v) a z ⟨⟨v, hva⟩, hva.1.symm⟩ ⟨hz, hzv⟩
  obtain ⟨w, haw, hw, hwv⟩ : ∃ w, Adj g a w ∧ IsVertex g w ∧ w ≠ v := by
    cases r with
    | refl _ => exact absurd rfl hza
    | step _ hadj hr => exact ⟨_, hadj, hr.left⟩
  have r2 : Reach g (fun x => IsVertex g x ∧ x ≠ a) v w :=
    connectedWithin_iff.mp (hcut a) v w ⟨⟨a, hva.symm⟩, hva.1⟩ ⟨hw, haw.1.symm⟩
  obtain ⟨P, hPh, hPl, hPS, hPc, hPnd⟩ := r2.exists_path
  exact ⟨a :: P, isCyc_cons.mpr ⟨two_le_length hPh hPl (Ne.symm hwv),
    List.nodup_cons.mpr ⟨fun h => (hPS a h).2 rfl, hPnd⟩,
    isChain_cons_append_singleton hPc hPh hPl hva.symm haw.symm⟩⟩

/-! ### A longest cycle is Hamiltonian -/

theorem IsCyc.rotate_to {g : Graph} {C : List ℕ} (hC : IsCyc g C) {x : ℕ} (hx : x ∈ C) :
    ∃ T, IsCyc g (x :: T) ∧ (∀ z, z ∈ x :: T ↔ z ∈ C) ∧ T.length + 1 = C.length := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hx
  refine ⟨t ++ s, hC.append_comm, fun z => ?_, ?_⟩
  · simp only [List.mem_cons, List.mem_append]
    tauto
  · simp only [List.length_append, List.length_cons]
    omega

/-- A vertex `h` off a cycle `C` of a 2-connected graph gives a longer cycle or a `K_{2,3}`
minor. -/
theorem longer_or_minor {g : Graph} (hg : TwoConnected g) {C : List ℕ} (hC : IsCyc g C)
    {h : ℕ} (hh : IsVertex g h) (hhC : h ∉ C) :
    (∃ C', IsCyc g C' ∧ C.length < C'.length) ∨ HasMinor g 5 k23 := by
  have hCv := hC.isVertex
  obtain ⟨c0, c1, rest, hCe⟩ : ∃ c0 c1 rest, C = c0 :: c1 :: rest := by
    match C, hC.1 with
    | c0 :: c1 :: rest, _ => exact ⟨c0, c1, rest, rfl⟩
  have hc01 : c0 ≠ c1 := by
    have := hC.2.1
    rw [hCe, List.nodup_cons, List.mem_cons, not_or] at this
    exact this.1.1
  -- a first attachment `x`, neighbour of `hx`
  have r0 : Reach g (IsVertex g) h c0 :=
    connectedWithin_iff.mp hg.2.1 h c0 hh (hCv c0 (by simp [hCe]))
  obtain ⟨hx, x, hrx, hhxx, -, hxC⟩ := r0.exit (Q := (· ∉ C)) hhC (by simp [hCe])
  simp only [not_not] at hxC
  -- a second attachment `y ≠ x`, neighbour of `hy`
  obtain ⟨c, hcC, hcx⟩ : ∃ c ∈ C, c ≠ x := by
    by_cases h0 : c0 = x
    · exact ⟨c1, by simp [hCe], fun e => hc01 (h0.trans e.symm)⟩
    · exact ⟨c0, by simp [hCe], h0⟩
  have hhx : h ≠ x := fun e => hhC (e ▸ hxC)
  have r1 : Reach g (fun v => IsVertex g v ∧ v ≠ x) h c :=
    connectedWithin_iff.mp (hg.2.2 x) h c ⟨hh, hhx⟩ ⟨hCv c hcC, hcx⟩
  obtain ⟨hy, y, hry, hhyy, ⟨-, hyx⟩, hyC⟩ := r1.exit (Q := (· ∉ C)) hhC (by simpa using hcC)
  simp only [not_not] at hyC
  -- a path `Q` from `hx` to `hy` off `C`
  have hr : Reach g (fun v => IsVertex g v ∧ v ∉ C) hx hy :=
    (hrx.mono fun _ hv => hv).symm.trans (hry.mono fun _ hv => ⟨hv.1.1, hv.2⟩)
  obtain ⟨Q, hQh, hQl, hQS, hQc, hQnd⟩ := hr.exists_path
  have hQne : Q ≠ [] := by rintro rfl; simp at hQh
  have hQlen := List.length_pos_of_ne_nil hQne
  -- `C` from `x`: `x :: (T1 ++ y :: T2)`
  obtain ⟨T, hT, hTm, hTl⟩ := hC.rotate_to hxC
  have hyT : y ∈ T := by
    have := (hTm y).mpr hyC
    rw [List.mem_cons] at this
    exact this.resolve_left hyx
  obtain ⟨T1, T2, rfl⟩ := List.append_of_mem hyT
  have hQd : ∀ z ∈ Q, z ∉ x :: (T1 ++ y :: T2) := fun z hz hz' =>
    (hQS z hz).2 ((hTm z).mp hz')
  simp only [List.length_append, List.length_cons] at hTl
  by_cases hT1 : T1 = []
  · -- `x` and `y` consecutive: `Q` replaces the edge `xy`
    subst hT1
    left
    refine ⟨y :: (T2 ++ x :: Q), IsCyc.extend hT hQc hQnd hQd hQh hQl hhxx.symm hhyy, ?_⟩
    simp only [List.length_cons, List.length_append]
    simp only [List.length_nil] at hTl
    omega
  by_cases hT2 : T2 = []
  · -- `y` and `x` consecutive: the reversed `Q` replaces the edge `yx`
    subst hT2
    left
    have hT' : IsCyc g (y :: x :: T1) := by
      have := (show IsCyc g ((x :: T1) ++ [y]) by simpa using hT).append_comm
      simpa using this
    have hQd' : ∀ z ∈ Q.reverse, z ∉ y :: x :: T1 := by
      intro z hz hz'
      refine hQd z (List.mem_reverse.mp hz) ?_
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil] at hz' ⊢
      tauto
    refine ⟨x :: (T1 ++ y :: Q.reverse), IsCyc.extend hT'
      (List.isChain_reverse.mpr (hQc.imp fun _ _ h => h.symm)) (List.nodup_reverse.mpr hQnd)
      hQd' (by rw [List.head?_reverse, hQl]) (by rw [List.getLast?_reverse, hQh]) hhyy.symm
      hhxx, ?_⟩
    simp only [List.length_cons, List.length_append, List.length_reverse]
    simp only [List.length_nil] at hTl
    omega
  · -- `x` and `y` not consecutive: a `K_{2,3}` minor
    right
    have hch := (isCyc_cons.mp hT).2.2
    simp only [List.append_assoc, List.cons_append] at hch
    refine hasMinor_k23_of [x] [y] Q T1 T2 ?_ (connectedWithin_singleton g x)
      (connectedWithin_singleton g y) (connectedWithin_of_isChain hQc)
      (connectedWithin_of_isChain (hch.infix ⟨[x], y :: (T2 ++ [x]), by simp⟩))
      (connectedWithin_of_isChain (hch.infix ⟨x :: (T1 ++ [y]), [x], by simp⟩))
      ⟨x, by simp, hx, mem_of_head? hQh, hhxx.symm⟩
      (exists_adj_of_infix hch ⟨[], y :: (T2 ++ [x]), by simp⟩ (by simp) hT1)
      (exists_adj_of_infix_rev hch ⟨x :: (T1 ++ [y]), [], by simp⟩ hT2 (by simp))
      ⟨y, by simp, hy, mem_of_getLast? hQl, hhyy.symm⟩
      (exists_adj_of_infix_rev hch ⟨[x], T2 ++ [x], by simp⟩ hT1 (by simp))
      (exists_adj_of_infix hch ⟨x :: T1, [x], by simp⟩ (by simp) hT2)
    have hnd := hT.2.1
    intro v
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hv <;> (try refine ⟨?_, ?_, ?_, ?_⟩) <;>
      (try refine ⟨?_, ?_, ?_⟩) <;> (try refine ⟨?_, ?_⟩) <;> grind

/-- A 2-connected `K_{2,3}`-minor-free graph has a Hamiltonian cycle. -/
theorem exists_ham {g : Graph} (hg : TwoConnected g) (hk : K23MinorFree g) :
    ∃ C, IsCyc g C ∧ ∀ v, IsVertex g v → v ∈ C := by
  obtain ⟨C0, hC0⟩ := exists_isCyc hg
  suffices H : ∀ n C, IsCyc g C → (vertList g).length - C.length = n →
      ∃ C, IsCyc g C ∧ ∀ v, IsVertex g v → v ∈ C from H _ C0 hC0 rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C hC hn
    by_cases hh : ∀ v, IsVertex g v → v ∈ C
    · exact ⟨C, hC, hh⟩
    · obtain ⟨v, hv, hvC⟩ : ∃ v, IsVertex g v ∧ v ∉ C := by
        simpa only [not_forall, not_imp, exists_prop] using hh
      rcases longer_or_minor hg hC hv hvC with ⟨C', hC', hlt⟩ | hm
      · have := hC'.length_le
        exact ih _ (by omega) C' hC' rfl
      · exact absurd hm hk

/-! ### Crossing chords -/

theorem exists_split_getD {L : List ℕ} {i : ℕ} (hi : i < L.length) :
    ∃ X R, L = X ++ L.getD i 0 :: R ∧ X.length = i ∧
      ∀ j, i < j → L.getD j 0 = R.getD (j - i - 1) 0 := by
  refine ⟨L.take i, L.drop (i + 1), ?_, by simp only [List.length_take]; omega, ?_⟩
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
      List.getElem_cons_drop, List.take_append_drop]
  · intro j hij
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
    congr 2
    omega

/-- Four positions `i < j < k < l` cut a list into the entries at these positions and five
pieces. -/
theorem exists_split4 {L : List ℕ} {i j k l : ℕ} (hij : i < j) (hjk : j < k) (hkl : k < l)
    (hl : l < L.length) : ∃ X0 X1 X2 X3 X4, L = X0 ++ L.getD i 0 :: (X1 ++ L.getD j 0 ::
      (X2 ++ L.getD k 0 :: (X3 ++ L.getD l 0 :: X4))) := by
  obtain ⟨X0, R0, e0, l0, g0⟩ := exists_split_getD (L := L) (i := i) (by omega)
  have len0 : L.length = i + 1 + R0.length := by
    rw [e0]; simp only [List.length_append, List.length_cons]; omega
  obtain ⟨X1, R1, e1, l1, g1⟩ := exists_split_getD (L := R0) (i := j - i - 1) (by omega)
  have len1 : R0.length = j - i - 1 + 1 + R1.length := by
    rw [e1]; simp only [List.length_append, List.length_cons]; omega
  obtain ⟨X2, R2, e2, l2, g2⟩ := exists_split_getD (L := R1) (i := k - j - 1) (by omega)
  have len2 : R1.length = k - j - 1 + 1 + R2.length := by
    rw [e2]; simp only [List.length_append, List.length_cons]; omega
  obtain ⟨X3, R3, e3, -, -⟩ := exists_split_getD (L := R2) (i := l - k - 1) (by omega)
  refine ⟨X0, X1, X2, X3, R3, ?_⟩
  have hj : L.getD j 0 = R0.getD (j - i - 1) 0 := g0 j hij
  have hk : L.getD k 0 = R1.getD (k - j - 1) 0 := by
    rw [g0 k (by omega), g1 _ (by omega)]
    congr 1
    omega
  have hl' : L.getD l 0 = R2.getD (l - k - 1) 0 := by
    rw [g0 l (by omega), g1 _ (by omega), g2 _ (by omega)]
    congr 1
    omega
  rw [hj, hk, hl', ← e3, ← e2, ← e1, ← e0]

/-- Crossing chords `ac`, `bd` of a cycle `a, X1, b, X2, c, X3, d, X4` with `X1` nonempty give
a `K_{2,3}` minor with branch sets `{a}`, `{b}`, `X1`, `X2 ∪ {c}`, `{d} ∪ X4`. -/
theorem crossing_core {g : Graph} {a b c d : ℕ} {X1 X2 X3 X4 : List ℕ}
    (hC : IsCyc g (a :: (X1 ++ b :: (X2 ++ c :: (X3 ++ d :: X4))))) (hac : Adj g a c)
    (hbd : Adj g b d) (hX1 : X1 ≠ []) : HasMinor g 5 k23 := by
  obtain ⟨-, hnd, hch⟩ := isCyc_cons.mp hC
  simp only [List.append_assoc, List.cons_append] at hch
  refine hasMinor_k23_of [a] [b] X1 (X2 ++ [c]) (d :: X4) ?_ (connectedWithin_singleton g a)
    (connectedWithin_singleton g b)
    (connectedWithin_of_isChain
      (hch.infix ⟨[a], b :: (X2 ++ c :: (X3 ++ d :: (X4 ++ [a]))), by simp⟩))
    (connectedWithin_of_isChain
      (hch.infix ⟨a :: (X1 ++ [b]), X3 ++ d :: (X4 ++ [a]), by simp⟩))
    (connectedWithin_of_isChain
      (hch.infix ⟨a :: (X1 ++ b :: (X2 ++ c :: X3)), [a], by simp⟩))
    (exists_adj_of_infix hch ⟨[], b :: (X2 ++ c :: (X3 ++ d :: (X4 ++ [a]))), by simp⟩
      (by simp) hX1)
    ⟨a, by simp, c, by simp, hac⟩
    (exists_adj_of_infix_rev hch ⟨a :: (X1 ++ b :: (X2 ++ c :: X3)), [], by simp⟩ (by simp)
      (by simp))
    (exists_adj_of_infix_rev hch ⟨[a], X2 ++ c :: (X3 ++ d :: (X4 ++ [a])), by simp⟩ hX1
      (by simp))
    (exists_adj_of_infix hch ⟨a :: X1, X3 ++ d :: (X4 ++ [a]), by simp⟩ (by simp) (by simp))
    ⟨b, by simp, d, by simp, hbd⟩
  intro v
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hv <;> (try refine ⟨?_, ?_, ?_, ?_⟩) <;>
    (try refine ⟨?_, ?_, ?_⟩) <;> (try refine ⟨?_, ?_⟩) <;> grind

/-- Crossing chords `ac`, `bd` of a cycle `a, X1, b, X2, c, X3, d, X4` give a `K_{2,3}` minor
unless the cycle is `a, b, c, d`. -/
theorem crossing {g : Graph} {a b c d : ℕ} {X1 X2 X3 X4 : List ℕ}
    (hC : IsCyc g (a :: (X1 ++ b :: (X2 ++ c :: (X3 ++ d :: X4))))) (hac : Adj g a c)
    (hbd : Adj g b d) : HasMinor g 5 k23 ∨ (X1 = [] ∧ X2 = [] ∧ X3 = [] ∧ X4 = []) := by
  rcases eq_or_ne X1 [] with rfl | h1
  swap
  · exact .inl (crossing_core hC hac hbd h1)
  rcases eq_or_ne X2 [] with rfl | h2
  swap
  · have hC' : IsCyc g (b :: (X2 ++ c :: (X3 ++ d :: (X4 ++ [a])))) := by
      have := (show IsCyc g ([a] ++ b :: (X2 ++ c :: (X3 ++ d :: X4))) by
        simpa using hC).append_comm
      simpa using this
    exact .inl (crossing_core hC' hbd hac.symm h2)
  rcases eq_or_ne X3 [] with rfl | h3
  swap
  · have hC' : IsCyc g (c :: (X3 ++ d :: (X4 ++ a :: ([] ++ b :: [])))) := by
      have := (show IsCyc g ([a, b] ++ c :: (X3 ++ d :: X4)) by simpa using hC).append_comm
      simpa using this
    exact .inl (crossing_core hC' hac.symm hbd.symm h3)
  rcases eq_or_ne X4 [] with rfl | h4
  swap
  · have hC' : IsCyc g (d :: (X4 ++ a :: ([] ++ b :: ([] ++ c :: [])))) := by
      have := (show IsCyc g ([a, b, c] ++ d :: X4) by simpa using hC).append_comm
      simpa using this
    exact .inl (crossing_core hC' hbd.symm hac h4)
  exact .inr ⟨rfl, rfl, rfl, rfl⟩

/-- A Hamiltonian cycle `a, b, c, d` with chords `ac` and `bd`: `g` is a `K₄`. -/
theorem isK4Graph_of {g : Graph} {a b c d : ℕ} (hC : IsCyc g [a, b, c, d]) (hac : Adj g a c)
    (hbd : Adj g b d) (hham : ∀ v, IsVertex g v → v ∈ [a, b, c, d]) : IsK4Graph g := by
  have hch := (isCyc_cons.mp hC).2.2
  simp only [List.cons_append, List.nil_append, List.isChain_cons_cons,
    List.isChain_singleton, and_true] at hch
  obtain ⟨hab, hbc, hcd, hda⟩ := hch
  refine ⟨a, b, c, d, hab.1, hac.1, hda.1.symm, hbc.1, hbd.1, hcd.1, fun u v =>
    ⟨fun h => ⟨h.1, ?_, ?_⟩, ?_⟩⟩
  · simpa using hham u ⟨v, h.symm⟩
  · simpa using hham v ⟨u, h⟩
  · rintro ⟨hne, hu, hv⟩
    rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hne | assumption | exact Adj.symm ‹_›

end K23Struct

open K23Struct in
/-- **Lemma 19, third sentence** (ANONYMIZED, ANONYMIZED, ANONYMIZED, ANONYMIZED 2016, with the standard
structure of 2-connected outerplanar graphs), proved: every 2-connected `K_{2,3}`-minor-free
graph is a `K₄` or has a Hamiltonian cycle with respect to which no two edges cross. -/
theorem twoConnectedK23_structure : TwoConnectedK23Structure := by
  intro g hg hk
  obtain ⟨C, hC, hham⟩ := exists_ham hg hk
  by_cases hx : ∃ i j k l, i < j ∧ j < k ∧ k < l ∧ l < C.length ∧
      Adj g (C.getD i 0) (C.getD k 0) ∧ Adj g (C.getD j 0) (C.getD l 0)
  · left
    obtain ⟨i, j, k, l, hij, hjk, hkl, hl, hac, hbd⟩ := hx
    obtain ⟨X0, X1, X2, X3, X4, e⟩ := exists_split4 hij hjk hkl hl
    generalize C.getD i 0 = a at hac e
    generalize C.getD j 0 = b at hbd e
    generalize C.getD k 0 = c at hac e
    generalize C.getD l 0 = d at hbd e
    subst e
    have hD : IsCyc g (a :: (X1 ++ b :: (X2 ++ c :: (X3 ++ d :: (X4 ++ X0))))) := by
      simpa using hC.append_comm
    rcases crossing hD hac hbd with hm | ⟨rfl, rfl, rfl, h4⟩
    · exact absurd hm hk
    · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h4
      simp only [List.nil_append] at hC hham
      exact isK4Graph_of hC hac hbd hham
  · right
    exact ⟨C, hC.isCycle, hham, fun i j k l hij hjk hkl hl h =>
      hx ⟨i, j, k, l, hij, hjk, hkl, hl, h⟩⟩

end STACS2027
