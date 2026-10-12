module

public import NPHardness.PlanarAssemblySourceRule
public import NPHardness.PlanarAssemblyOccurrenceAddress
public import NPHardness.PlanarAssemblyComplete
public import ApproximationHardness.Planar.Skip
import Lean.Elab.Tactic.Omega

/-!
# The gadget orientation computed from a planar embedding of the incidence graph

Section 5 proves that *some* choice of endpoint orientations makes the oriented formula graph
planar (`orientedFormulaGraph_planar_exists`), by choosing the orientations from the cyclic
orders of a planar embedding of the incidence graph. This file computes them explicitly from
the node permutation `N` of such an embedding (given as a function on dart numbers):

* a variable `v` is *forward* when its positive occurrence's dart is followed by the dart of
  its second negative occurrence (`variableSign`);
* a three-literal clause `j` is *forward* when the dart of its first literal is followed by the
  dart of its third literal (`clauseSign`);
* occurrence `i` gets the bit `flipBit f N i`, a Boolean formula in its port, the sign of its
  variable and the sign of its clause.

`orientationChoices_planar` proves that the oriented formula graph built with these bits is
planar, for every embedding of the incidence graph whose node cycles are the vertices. The
local gadget embeddings are still proof witnesses (Section 5's profiles), but nothing in the
output depends on them: a variable gadget is mirrored according to its sign, a three-literal
clause gadget is mirrored according to its sign, and a node with fewer used ports is handled by
first-hit walks that skip the unused ports (`ApproximationHardness.Planar.Skip`).
-/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.SAT Complexity.Planar Comb PlanarGluing

/-! ### The explicit bits -/

/-- The allocated literal occurrences, in order. -/
def occList (f : CNF) : List PlacedLiteral := (placeFormula [] f).flatten

/-- The variable-gadget port of occurrence `i`. -/
def occPort (f : CNF) (i : Nat) : Nat := ((occList f)[i]?.map PlacedLiteral.port).getD 0

/-- The variable of occurrence `i`. -/
def occVar (f : CNF) (i : Nat) : Nat := ((occList f)[i]?.map fun p => p.literal.var).getD 0

/-- The index of the positive occurrence of `v` (the number of occurrences if there is none). -/
def positiveIndex (f : CNF) (v : Nat) : Nat :=
  (occList f).findIdx fun p => p.literal == ⟨v, true⟩

/-- Variable `v` is forward: the node permutation `N` sends the dart of its positive occurrence
to the dart of an occurrence on port 2. -/
def variableSign (f : CNF) (N : Nat → Nat) (v : Nat) : Bool :=
  decide (positiveIndex f v < (occList f).length) && occPort f (N (2 * positiveIndex f v) / 2) == 2

/-- Clause `j` has three literals and is forward: `N` sends the dart of its first literal to
the dart of its third literal. -/
def clauseSign (f : CNF) (N : Nat → Nat) (j : Nat) : Bool :=
  kl f j == 3 && N (2 * off f j + 1) == 2 * (off f j + 2) + 1

/-- The orientation bit of occurrence `i`. -/
def flipBit (f : CNF) (N : Nat → Nat) (i : Nat) : Bool :=
  ((occPort f i == 0) == !variableSign f N (occVar f i)) == !clauseSign f N (oj f i)

/-- The orientation bits of all occurrences, in order. -/
def orientationBits (f : CNF) (N : Nat → Nat) : List Bool :=
  (List.range (occList f).length).map (flipBit f N)

/-- The endpoint choices given by the orientation bits. -/
def orientationChoices (f : CNF) (N : Nat → Nat) : EndpointChoices :=
  fun p => flipBit f N ((occList f).idxOf p)

theorem orientationChoices_occurrence (f : CNF) (N : Nat → Nat) (i : OccurrenceIndex f) :
    orientationChoices f N (occurrence f i) = flipBit f N i.val := by
  unfold orientationChoices occurrence occList
  rw [List.Nodup.idxOf_getElem (placedOccurrences_nodup f)]

theorem orientationBits_getElem (f : CNF) (N : Nat → Nat) (i : OccurrenceIndex f) :
    (orientationBits f N)[i.val]? = some (orientationChoices f N (occurrence f i)) := by
  rw [orientationChoices_occurrence]
  have hi : i.val < (occList f).length := i.isLt
  unfold orientationBits
  rw [List.getElem?_map, List.getElem?_range hi]
  rfl

/-! ### Occurrence data -/

theorem occPort_eq (f : CNF) (i : OccurrenceIndex f) : occPort f i.val = (occurrence f i).port := by
  simp [occPort, occList, List.getElem?_eq_getElem i.isLt, occurrence]

theorem occVar_eq (f : CNF) (i : OccurrenceIndex f) :
    occVar f i.val = (occurrence f i).literal.var := by
  simp [occVar, occList, List.getElem?_eq_getElem i.isLt, occurrence]

theorem positiveIndex_eq {f : CNF} (hf : BoundedOccurrence f) (i : OccurrenceIndex f) {v : Nat}
    (hl : (occurrence f i).literal = ⟨v, true⟩) : positiveIndex f v = i.val := by
  have hex : ∃ x ∈ occList f, (fun p : PlacedLiteral => p.literal == ⟨v, true⟩) x = true :=
    ⟨occurrence f i, occurrence_mem f i, by simp [hl]⟩
  have hlt := List.findIdx_lt_length_of_exists hex
  have hp := @List.findIdx_getElem _ (fun p : PlacedLiteral => p.literal == ⟨v, true⟩) _ hlt
  simp only [beq_iff_eq] at hp
  let i' : OccurrenceIndex f := ⟨(occList f).findIdx fun p => p.literal == ⟨v, true⟩, hlt⟩
  have hkey : (occurrence f i').key = (occurrence f i).key := by
    have h1 : (occurrence f i').literal = ⟨v, true⟩ := hp
    simp [PlacedLiteral.key, PlacedLiteral.port, h1, hl]
  have he := hf.placement_key_injective (occurrence_mem f i') (occurrence_mem f i) hkey
  have := occurrence_injective f he
  exact congrArg Fin.val this

theorem occurrenceDart_val {f : CNF} (i : OccurrenceIndex f) (s : Bool) :
    (occurrenceDart i s).val = 2 * i.val + (if s then 1 else 0) := rfl

/-! ### The comparisons -/

/-- The variable sign compares the successor of the positive occurrence's dart with port 2. -/
theorem variableSign_spec {f : CNF} (hf : BoundedOccurrence f)
    (I : Hypermap (2 * (placeFormula [] f).flatten.length))
    (hnode : ∀ a b, Reaches I.node a b ↔ occurrenceVertex f a = occurrenceVertex f b)
    (N : Nat → Nat) (hN : ∀ d, N d.val = (I.node d).val)
    (i : OccurrenceIndex f) {v : Nat} (hl : (occurrence f i).literal = ⟨v, true⟩) :
    variableSign f N v = true ↔ sourcePortNumber f (I.node (occurrenceDart i false)) = 2 := by
  have hv := NodeDartIndex.node_vertex I hnode (occurrenceDart i false)
  obtain ⟨i', s, hd⟩ := occurrenceDart_cases (I.node (occurrenceDart i false))
  rw [hd, occurrenceVertex_even] at hv
  cases s
  · have hN' := hN (occurrenceDart i false)
    rw [hd, occurrenceDart_val, occurrenceDart_val] at hN'
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hN'
    unfold variableSign
    rw [positiveIndex_eq hf i hl, hN', hd, sourcePortNumber_even]
    have h2 : 2 * i'.val / 2 = i'.val := by omega
    rw [h2, occPort_eq]
    have hi : i.val < (occList f).length := i.isLt
    simp only [hi, decide_true, Bool.true_and, beq_iff_eq]
  · rw [occurrenceVertex_odd] at hv
    simp at hv

/-- The clause sign compares the successor of the first literal's dart with the third. -/
theorem clauseSign_spec {f : CNF}
    (I : Hypermap (2 * (placeFormula [] f).flatten.length))
    (hnode : ∀ a b, Reaches I.node a b ↔ occurrenceVertex f a = occurrenceVertex f b)
    (N : Nat → Nat) (hN : ∀ d, N d.val = (I.node d).val)
    {c : Nat} (hc : c < f.length) (h3 : kl f c = 3)
    (i : OccurrenceIndex f) (hi : i.val = off f c) :
    clauseSign f N c = true ↔ sourcePortNumber f (I.node (occurrenceDart i true)) = 2 := by
  have hpos := occurrencePosition_at_offset f i c 0 hc (by omega) (by omega)
  have hv := NodeDartIndex.node_vertex I hnode (occurrenceDart i true)
  obtain ⟨i', s, hd⟩ := occurrenceDart_cases (I.node (occurrenceDart i true))
  rw [hd, occurrenceVertex_odd] at hv
  cases s
  · rw [occurrenceVertex_even] at hv
    simp at hv
  · rw [occurrenceVertex_odd] at hv
    have hcl : (occurrencePosition f i').clause.val = c := by
      have := Sum.inr.inj hv
      rw [this, hpos.1]
    have hdec := occurrencePosition_decode f i'
    -- the occurrence `i'` is `off c + slot`
    have hoff : off f c + (occurrencePosition f i').slot.val = i'.val := by
      have he := occurrencePosition_offset f i'
      rw [placed_clause_lengths] at he
      rw [← hcl]
      exact he
    have hN' := hN (occurrenceDart i true)
    rw [hd, occurrenceDart_val, occurrenceDart_val] at hN'
    simp only [↓reduceIte] at hN'
    unfold clauseSign
    rw [hd, sourcePortNumber_odd, ← hi, hN', h3]
    simp only [BEq.rfl, Bool.true_and, beq_iff_eq]
    omega

/-! ### The profiles -/

/-- The direction of the profile of piece `j`. -/
def pieceForward (vs cs : Nat → Bool) (f : CNF) (j : Nat) : Bool :=
  if j < variableBound f then vs j else cs (j - variableBound f)

/-- The cyclic successor (forward) or predecessor of a port. -/
def pieceNextX {k : Nat} {f : CNF} (vs cs : Nat → Bool) (j : PieceIndex k f)
    (i : Fin (piecePorts k f j).length) : Fin (piecePorts k f j).length :=
  ⟨if pieceForward vs cs f j.val then (i.val + 1) % (piecePorts k f j).length
   else (i.val + (piecePorts k f j).length - 1) % (piecePorts k f j).length,
    by have hp : 0 < (piecePorts k f j).length := by have := i.isLt; omega
       split <;> exact Nat.mod_lt _ hp⟩

/-- The endpoint sides of the ports: the signed variable table, and the clause table, reflected
for a forward clause. -/
def pieceSideX {k : Nat} {f : CNF} (vs cs : Nat → Bool) (j : PieceIndex k f)
    (i : Fin (piecePorts k f j).length) : Bool :=
  if j.val < variableBound f then ((i.val == 0) == !(vs j.val)) else !(cs (j.val - variableBound f))

theorem pieceNextX_val {k : Nat} {f : CNF} (vs cs : Nat → Bool) (j : PieceIndex k f)
    (i : Fin (piecePorts k f j).length) :
    (pieceNextX vs cs j i).val = if pieceForward vs cs f j.val then (i.val + 1) % (piecePorts k f j).length
      else (i.val + (piecePorts k f j).length - 1) % (piecePorts k f j).length := rfl

theorem piece_length_variable {k : Nat} {f : CNF} (hf : BoundedOccurrence f) (j : PieceIndex k f)
    (hj : j.val < variableBound f) : (piecePorts k f j).length = 3 := by
  rw [piecePorts_length hf]
  simp only [pieceFullCount, hj, ↓reduceDIte]

theorem piece_clause_lt {k : Nat} {f : CNF} (j : PieceIndex k f) (hj : ¬ j.val < variableBound f) :
    j.val - variableBound f < f.length := by
  have h1 := (pieceClauseIndex k f j hj).isLt
  have h2 := placeFormula_length [] f
  have h3 : (pieceClauseIndex k f j hj).val = j.val - variableBound f := rfl
  omega

theorem piece_length_clause {k : Nat} {f : CNF} (hf : BoundedOccurrence f) (j : PieceIndex k f)
    (hj : ¬ j.val < variableBound f) : (piecePorts k f j).length = kl f (j.val - variableBound f) := by
  rw [piecePorts_length hf]
  simp only [pieceFullCount, hj, ↓reduceDIte, pieceClauseIndex]
  have hc := piece_clause_lt j hj
  rw [placed_clause_length f _ hc, kl_of_lt f _ hc]

theorem piece_length_bounds {k : Nat} {f : CNF} (hf : BoundedOccurrence f) (j : PieceIndex k f) :
    2 ≤ (piecePorts k f j).length ∧ (piecePorts k f j).length ≤ 3 := by
  by_cases hj : j.val < variableBound f
  · rw [piece_length_variable hf j hj]; omega
  · rw [piece_length_clause hf j hj]
    have hc := piece_clause_lt j hj
    rw [kl_of_lt f _ hc]
    rcases hf.1 _ (List.getElem_mem hc) with h | h <;> omega

/-- Every gadget piece admits its explicit profile: the Section 5 signed profile, reflected
for a forward three-literal clause. -/
theorem piece_explicit_profile {k : Nat} {f : CNF} (hf : BoundedOccurrence f)
    (vs cs : Nat → Bool) (hcs : ∀ c, cs c = true → kl f c = 3) (j : PieceIndex k f) :
    SphericalPortProfile (ungluedFormulaPieces k f)[j.val]
      (fun i => (piecePorts k f j)[i.val]) (pieceNextX vs cs j) (pieceSideX vs cs j) := by
  have hp := piece_signed_profile (k := k) hf vs j
  by_cases hj : j.val < variableBound f
  · have hn : pieceNextX vs cs j = pieceProfileNext vs j := by
      funext i
      apply Fin.ext
      rw [pieceNextX_val]
      simp only [pieceProfileNext, pieceForward, hj, ↓reduceIte, true_and]
    have hs : pieceSideX vs cs j = pieceProfileSide vs j := by
      funext i
      simp only [pieceSideX, pieceProfileSide, hj, ↓reduceIte]
    rw [hn, hs]
    exact hp
  · by_cases hc : cs (j.val - variableBound f) = true
    · have hl : (piecePorts k f j).length = 3 := by
        rw [piece_length_clause hf j hj]; exact hcs _ hc
      have hm := hp.mirror (pieceNextX vs cs j) (by
        intro i
        apply Fin.ext
        have hi := i.isLt
        simp only [pieceProfileNext, pieceNextX_val, pieceForward, hj, ↓reduceIte, hc, false_and]
        have key : ∀ a L : Nat, L = 3 → a < L → ((a + 1) % L + L - 1) % L = a := by
          intro a L h ha; subst h; omega
        exact key _ _ hl hi)
      have hs : pieceSideX vs cs j = fun i => !(pieceProfileSide vs j i) := by
        funext i
        simp only [pieceSideX, pieceProfileSide, hj, ↓reduceIte, hc]
      rw [hs]
      exact hm
    · have hn : pieceNextX vs cs j = pieceProfileNext vs j := by
        funext i
        apply Fin.ext
        rw [pieceNextX_val]
        simp only [pieceProfileNext, pieceForward, hj, ↓reduceIte, hc, false_and, Bool.false_eq_true]
      have hs : pieceSideX vs cs j = pieceProfileSide vs j := by
        funext i
        simp only [pieceSideX, pieceProfileSide, hj, ↓reduceIte]
        simp [hc]
      rw [hn, hs]
      exact hp

theorem clauseSign_three (f : CNF) (N : Nat → Nat) (c : Nat) (h : clauseSign f N c = true) :
    kl f c = 3 := by
  unfold clauseSign at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-! ### The source orders -/

/-- With all ports of a three-port piece used, the successor of its port-0 dart decides the
direction of its source order, and the explicit sign records it. -/
theorem piece_sign_witness {k : Nat} {f : CNF} (hf : BoundedOccurrence f)
    (I : Hypermap (2 * (placeFormula [] f).flatten.length))
    (hnode : ∀ a b, Reaches I.node a b ↔ occurrenceVertex f a = occurrenceVertex f b)
    (N : Nat → Nat) (hN : ∀ d, N d.val = (I.node d).val) (j : PieceIndex k f)
    (h3 : (piecePorts k f j).length = 3)
    (hfull : ∀ c : Fin (piecePorts k f j).length, ∃ t, piecePortIndex hf j t = c) :
    ∃ t t0, (piecePortIndex hf j t0).val = 0 ∧ (pieceNodeIndex k f j).order I hnode t = t0 ∧
      ((piecePortIndex hf j t).val = 2 ↔
        pieceForward (variableSign f N) (clauseSign f N) f j.val = true) := by
  let D := pieceNodeIndex k f j
  obtain ⟨t0, ht0⟩ := hfull ⟨0, by omega⟩
  have ht0v : (piecePortIndex hf j t0).val = 0 := by rw [ht0]
  have hvx : occurrenceVertex f (I.node (D.dart t0)) = pieceVertex k f j :=
    (NodeDartIndex.node_vertex I hnode _).trans (D.vertex t0)
  obtain ⟨t, ht⟩ := D.complete _ hvx
  have hqt : D.order I hnode t = t0 := D.order_of_node I hnode t0 t ht
  refine ⟨t, t0, ht0v, hqt, ?_⟩
  rw [piecePortIndex_number, ht]
  have hn0 := piecePortIndex_number hf j t0
  rw [ht0v] at hn0
  have hv0 := D.vertex t0
  obtain ⟨i0, s, hd0⟩ := occurrenceDart_cases (D.dart t0)
  change D.dart t0 = _ at hd0
  rw [hd0] at hn0 hv0 ⊢
  by_cases hj : j.val < variableBound f
  · simp only [pieceForward, hj, ↓reduceIte]
    cases s
    · rw [occurrenceVertex_even] at hv0
      simp only [pieceVertex, hj, ↓reduceIte, Sum.inl.injEq] at hv0
      rw [sourcePortNumber_even] at hn0
      have hpos : (occurrence f i0).literal = ⟨j.val, true⟩ := by
        have hz := placedLiteral_port_zero (occurrence f i0)
        rw [← hn0] at hz
        simp only [BEq.rfl] at hz
        cases hl : (occurrence f i0).literal with
        | mk w b =>
          rw [hl] at hv0 hz
          simp only at hv0 hz
          rw [hv0, ← hz]
      exact (variableSign_spec hf I hnode N hN i0 hpos).symm
    · rw [occurrenceVertex_odd] at hv0
      simp [pieceVertex, hj] at hv0
  · simp only [pieceForward, hj, ↓reduceIte]
    cases s
    · rw [occurrenceVertex_even] at hv0
      simp [pieceVertex, hj] at hv0
    · rw [occurrenceVertex_odd] at hv0
      simp only [pieceVertex, hj, ↓reduceIte, Sum.inr.injEq] at hv0
      rw [sourcePortNumber_odd] at hn0
      have hc := piece_clause_lt j hj
      have hoff : off f (j.val - variableBound f) + (occurrencePosition f i0).slot.val = i0.val := by
        have he := occurrencePosition_offset f i0
        rw [placed_clause_lengths] at he
        rw [← hv0]
        exact he
      have hk : kl f (j.val - variableBound f) = 3 := (piece_length_clause hf j hj).symm.trans h3
      exact (clauseSign_spec I hnode N hN hc hk i0 (by omega)).symm

/-- The explicit profiles realize every source order. -/
theorem explicit_source_orders {k : Nat} {f : CNF} (hf : BoundedOccurrence f)
    (I : Hypermap (2 * (placeFormula [] f).flatten.length))
    (hnode : ∀ a b, Reaches I.node a b ↔ occurrenceVertex f a = occurrenceVertex f b)
    (N : Nat → Nat) (hN : ∀ d, N d.val = (I.node d).val) (L : ChosenPieces k f)
    (hprof : L.HasProfiles (pieceNextX (variableSign f N) (clauseSign f N))
      (pieceSideX (variableSign f N) (clauseSign f N))) :
    L.HasSourceOrders I hnode (piecePortIndex hf) := by
  intro j i
  let D := pieceNodeIndex k f j
  let fw := pieceForward (variableSign f N) (clauseSign f N) f j.val
  have hb := piece_length_bounds hf j
  have hfull : (piecePorts k f j).length = 3 →
      (∀ c : Fin (piecePorts k f j).length, ∃ t, piecePortIndex hf j t = c) →
      ∀ i, piecePortIndex hf j (D.order I hnode i) =
        pieceNextX (variableSign f N) (clauseSign f N) j (piecePortIndex hf j i) := by
    intro h3 hall i
    obtain ⟨t, t0, ht0, hqt, hsign⟩ := piece_sign_witness hf I hnode N hN j h3 hall
    have hc := three_cycle_sign h3 (piecePortIndex hf j) (piecePortIndex_injective hf j)
      (D.order I hnode) (D.order_injective I hnode) (D.order_fixed I hnode) hall fw t t0 ht0 hqt
      hsign i
    apply Fin.ext
    rw [hc, pieceNextX_val]
    have hlt := (piecePortIndex hf j i).isLt
    have key : ∀ a L : Nat, L = 3 → a < L → ∀ b : Bool,
        (if b then (a + 1) % 3 else (a + 2) % 3) = (if b then (a + 1) % L else (a + L - 1) % L) := by
      intro a L h ha b; subst h; cases b <;> simp
    exact key _ _ h3 hlt fw
  obtain ⟨s, he, hskip⟩ := cyclic_skip hb.1 hb.2 fw (pieceNextX (variableSign f N) (clauseSign f N) j)
    (fun a => pieceNextX_val _ _ j a) (piecePortIndex hf j) (piecePortIndex_injective hf j)
    (D.order I hnode) (D.order_fixed I hnode) hfull i
  exact NextSelected.skip (hprof.1 j) (L j).injective (piecePortIndex hf j) i _ s he hskip

/-! ### Planarity -/

theorem explicit_sides {k : Nat} {f : CNF} {L : ChosenPieces k f} (hf : BoundedOccurrence f)
    (N : Nat → Nat)
    (hprof : L.HasProfiles (pieceNextX (variableSign f N) (clauseSign f N))
      (pieceSideX (variableSign f N) (clauseSign f N))) (i : OccurrenceIndex f) :
    orientationChoices f N (occurrence f i) =
      (dartSide ((L.choices hf).variableOccurrencePort hf i) ==
        dartSide ((L.choices hf).clauseOccurrencePort i)) := by
  obtain ⟨hv, hc⟩ := hprof.occurrence_sides hf i
  rw [hv, hc, orientationChoices_occurrence]
  have hvar := occurrence_variable_lt hf i
  have hdec := (occurrencePosition_decode f i).1
  have hcl : ¬ variableBound f + (occurrencePosition f i).clause.val < variableBound f := by omega
  unfold pieceSideX flipBit
  simp only [variablePieceIndex, occurrenceVariable, clausePieceIndex, hvar, hcl, ↓reduceIte,
    Nat.add_sub_cancel_left, variablePortIndex, occurrenceLocalPort]
  rw [occPort_eq, occVar_eq, hdec]
  rfl

/-- **The explicit orientation is planar.** For every planar embedding `I` of the incidence
graph (edge permutation the standard pairing, node cycles the vertices), the oriented formula
graph whose endpoint choices are computed from the node permutation `N` of `I` is planar. -/
theorem orientationChoices_planar (k : Nat) {f : CNF} (hf : BoundedOccurrence f)
    (I : Hypermap (2 * (placeFormula [] f).flatten.length))
    (hIedge : ∀ d, I.edge d = graphEdge d)
    (hnode : ∀ a b, Reaches I.node a b ↔ occurrenceVertex f a = occurrenceVertex f b)
    (hI : I.Planar) (N : Nat → Nat) (hN : ∀ d, N d.val = (I.node d).val) :
    PlanarGraph (orientedFormulaGraph (orientationChoices f N) k f) := by
  obtain ⟨L, hprofile⟩ := chosenPieces_with_profiles
    (pieceNextX (k := k) (f := f) (variableSign f N) (clauseSign f N))
    (pieceSideX (variableSign f N) (clauseSign f N))
    (piece_explicit_profile hf _ _ (clauseSign_three f N))
  let C := L.choices hf
  have horder := explicit_source_orders hf I hnode N hN L hprofile
  let O := L.orderedPorts hf I hIedge hnode (piecePortIndex hf) horder (L.sourcePort_piece_match hf)
  apply C.orientedFormulaGraph_planar_prescribed hf (orientationChoices f N)
    (explicit_sides hf N hprofile) (piecesMap (ungluedFormulaPieces k f) L.maps)
    L.embedding L.spherical I hI O
  intro a b hab
  exact (hnode a b).mpr (C.sourcePort_connected_vertex hf L.maps a b hab)

/-! ### From a rotation list -/

/-- `rot` lists, dart by dart, the node permutation of a planar embedding of `incidenceGraph f`. -/
def IsPlanarRotation (f : CNF) (rot : List Nat) : Prop :=
  ∃ G : Hypermap (2 * (incidenceGraph f).length),
    (∀ d, (G.edge d).val = cond (Nat.beq (d.val % 2) 0) (d.val + 1) (d.val - 1)) ∧
    (∀ d d', (∃ k, iterate G.node k d = d') ↔
      halfEdgeEnd (incidenceGraph f) d.val = halfEdgeEnd (incidenceGraph f) d'.val) ∧
    G.Planar ∧ rot.length = 2 * (incidenceGraph f).length ∧ ∀ d, rot[d.val]? = some (G.node d).val

/-- The incidence graph is planar exactly when it has a planar rotation list. -/
theorem planarGraph_iff_rotation (f : CNF) :
    PlanarGraph (incidenceGraph f) ↔ ∃ rot, IsPlanarRotation f rot := by
  constructor
  · rintro ⟨G, he, hn, hp⟩
    refine ⟨(List.finRange (2 * (incidenceGraph f).length)).map fun d => (G.node d).val,
      G, he, hn, hp, by simp, fun d => ?_⟩
    simp [d.isLt]
  · rintro ⟨rot, G, he, hn, hp, -, -⟩
    exact ⟨G, he, hn, hp⟩

/-- The endpoint choices read from a list of bits, one per occurrence. -/
def choicesOfBits (f : CNF) (bits : List Bool) : EndpointChoices :=
  fun p => bits.getD ((occList f).idxOf p) false

theorem choicesOfBits_orientationBits (k : Nat) (f : CNF) (N : Nat → Nat) :
    orientedFormulaGraph (choicesOfBits f (orientationBits f N)) k f =
      orientedFormulaGraph (orientationChoices f N) k f := by
  apply orientedFormulaGraph_congr_choices
  intro p hp
  have hi : (occList f).idxOf p < (occList f).length := List.idxOf_lt_length_of_mem hp
  unfold choicesOfBits orientationChoices orientationBits
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

/-- **Planarity from a rotation list.** If `rot` is a planar rotation list of the incidence
graph of a Definition 7 instance `f`, then the oriented formula graph whose endpoint choices are
the explicit bits `orientationBits f rot` is planar, for every gadget parameter `k`. -/
theorem orientationBits_planar (k : Nat) {f : CNF} (hf : BoundedOccurrence f) {rot : List Nat}
    (h : IsPlanarRotation f rot) :
    PlanarGraph (orientedFormulaGraph
      (choicesOfBits f (orientationBits f fun d => rot.getD d 0)) k f) := by
  rw [choicesOfBits_orientationBits]
  unfold IsPlanarRotation at h
  rw [← placed_occurrence_count f] at h
  obtain ⟨I, hIe, hIn, hIp, -, hrot⟩ := h
  have hIedge : ∀ d, I.edge d = graphEdge d := fun d => Fin.ext (hIe d)
  have hnode := occurrence_node_semantics f I hIn
  apply orientationChoices_planar k hf I hIedge hnode hIp
  intro d
  simp [List.getD_eq_getElem?_getD, hrot d]

end STACS2027.PlanarAssembly
