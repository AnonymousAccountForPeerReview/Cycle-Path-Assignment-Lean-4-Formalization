module

public import Outerplanar.RAM.PairIdsRank
import Mathlib.Tactic

/-!
# Leaders from a sorted order

For the relabelling without label-indexed memory: the indices of a key list
`keys` (e.g. the labels of the input, `L` keys at `rKY`), sorted by `(key, index)` by any stable
sort (`SQ` at `rSQ`, `ord` with `ord.Pairwise (KeyLt keys)`, containing every index), give the
leaders `LEAD = keys.map (keys.idxOf ·)` in one pass that only **compares** keys (no memory
indexed by keys):

`sortedLeads`: for `p < L`, `q = SQ[p]`: if `p = 0` or `KEY[q]` differs from the key of the
previous entry, the current leader becomes `q`; `LEAD[q] :=` the current leader
(`first_of_sorted`: in such an order the first entry of a group of equal keys is the first index
of its key).

Followed by `rankIds` (`PairIdsRank.lean`), it yields the identifiers in order of first
appearance, `EID[q] = keys.eraseDups.idxOf keys[q]` (for labels in input order: the ids of
the labels).
-/

@[expose] public section

namespace STACS2027.RAM.PairIds

open STACS2027.Algo

variable {S : ℕ}

/-! ### The abstract side -/

section abs

variable {keys ord : List ℕ}

/-- **The first entry of a group** in an order sorted by `(key, index)` that contains every
index: if `p = 0` or the entry before it has another key, the entry at `p` is the first index
of its key. -/
theorem first_of_sorted (hs : ord.Pairwise (KeyLt keys)) (hc : ∀ q < keys.length, q ∈ ord)
    {p : ℕ} (hp : p < ord.length) (hq : ord[p] < keys.length)
    (h : ∀ hp1 : p - 1 < ord.length, 0 < p → keys.getD ord[p - 1] 0 ≠ keys.getD ord[p] 0) :
    keys.idxOf (keys.getD ord[p] 0) = ord[p] := by
  rw [getD_eq_getElem' hq, idxOf_getElem_eq_self_iff keys hq]
  intro hm
  obtain ⟨j, hj, hjq⟩ := List.mem_take_iff_getElem.mp hm
  have hjL : j < keys.length := by omega
  obtain ⟨i, hi, hij⟩ := List.mem_iff_getElem.mp (hc j hjL)
  have hpw := List.pairwise_iff_getElem.mp hs
  have hkey : keys.getD j 0 = keys.getD ord[p] 0 := by
    rw [getD_eq_getElem' hjL, getD_eq_getElem' hq]; exact hjq
  rcases lt_trichotomy i p with hip | hip | hip
  · have hne := h (by omega) (by omega)
    rcases Nat.lt_or_ge i (p - 1) with hi1 | hi1
    · have h1 := hpw i (p - 1) hi (by omega) hi1
      have h2 := hpw (p - 1) p (by omega) hp (by omega)
      rw [hij] at h1
      unfold KeyLt at h1 h2
      omega
    · obtain rfl : i = p - 1 := by omega
      exact hne (by rw [hij]; exact hkey)
  · subst hip; omega
  · have h1 := hpw p i hp hi hip
    rw [hij] at h1
    unfold KeyLt at h1
    omega

/-- The leaders stored after `p` entries of the order. -/
def ldF (keys ord : List ℕ) (p q : ℕ) : ℕ := if q ∈ ord.take p then keys.idxOf (keys.getD q 0) else 0

theorem ldF_zero (keys ord : List ℕ) : ldF keys ord 0 = fun _ => 0 := by
  funext q; simp only [ldF, List.take_zero, List.not_mem_nil, ↓reduceIte]

theorem ldF_succ (hs : ord.Pairwise (KeyLt keys)) {p : ℕ} (hp : p < ord.length) :
    ldF keys ord (p + 1) = Function.update (ldF keys ord p) ord[p] (keys.idxOf (keys.getD ord[p] 0)) := by
  have hnot : ord[p] ∉ ord.take p := fun hm => keyLt_irrefl _ _ ((keyLt_split hs hp).1 _ hm)
  have ht : ord.take (p + 1) = ord.take p ++ [ord[p]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hp]; rfl
  funext q
  unfold ldF
  rw [ht]
  by_cases hq : q = ord[p]
  · rw [hq, Function.update_self]
    simp only [List.mem_append, List.mem_singleton, or_true, ↓reduceIte]
  · rw [Function.update_of_ne hq]
    simp only [List.mem_append, List.mem_singleton, hq, or_false]

end abs

/-! ### The program -/

/-- Input: base of the sorted indices `SQ` (`L` cells). -/
abbrev rSQ : ℕ := 128
/-- Input: base of the keys `KEY` (`L` cells). -/
abbrev rKY : ℕ := 129

/-- A new group: its first entry is the leader. -/
def sldNew : Stmt := mov rX rQ
/-- One entry `q = SQ[j]` of the order: the leader changes at a new key; `LEAD[q] :=` leader. -/
def sldBody : Stmt :=
  .seq (ld rQ rSQ rJ) (.seq (ld rU rKY rQ) (.seq (.ifz rJ sldNew (ifEq rU rV .skip sldNew))
    (.seq (mov rV rU) (st rLD rQ rX))))
/-- **The leaders from a sorted order.** -/
def sortedLeads : Stmt := .seq (alloc rLD rPL) (forUp rJ rPL sldBody)

/-! ### The specification -/

/-- The input of `sortedLeads`: the keys and their sorted indices below the free address. -/
structure SIn (keys ord : List ℕ) (c : Config) : Prop where
  pl : c.reg rPL = keys.length
  sq : Arr c.mem (c.reg rSQ) ord
  ky : Arr c.mem (c.reg rKY) keys
  below : c.reg rSQ + keys.length ≤ c.reg rFREE ∧ c.reg rKY + keys.length ≤ c.reg rFREE
  free : ZeroFrom c.mem (c.reg rFREE)

/-- The registers fixed by the pass (`c₀`: the configuration on entry). -/
@[mk_iff] structure SGlob (L : ℕ) (c₀ c : Config) : Prop where
  pl : c.reg rPL = L
  sq : c.reg rSQ = c₀.reg rSQ
  ky : c.reg rKY = c₀.reg rKY
  ld : c.reg rLD = c₀.reg rFREE
  free : c.reg rFREE = c₀.reg rFREE + L

/-- The invariant after `p` entries: the key and the leader of the previous entry in `rV`,
`rX`; the leaders of the entries so far. -/
def SldInv (keys ord : List ℕ) (c₀ : Config) (p : ℕ) (c : Config) : Prop :=
  SGlob keys.length c₀ c ∧
    (0 < p → c.reg rV = keys.getD (ord.getD (p - 1) 0) 0 ∧
      c.reg rX = keys.idxOf (keys.getD (ord.getD (p - 1) 0) 0)) ∧
    SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧ Tab c.mem (c₀.reg rFREE) keys.length (ldF keys ord p) ∧
    ZeroFrom c.mem (c₀.reg rFREE + keys.length)

theorem sldBody_spec {keys ord : List ℕ} (hs : ord.Pairwise (KeyLt keys))
    (hl : ord.length = keys.length) (hc : ∀ q < keys.length, q ∈ ord)
    (hb : ∀ q ∈ ord, q < keys.length) (c₀ : Config) (hIn : SIn keys ord c₀)
    (hS : c₀.reg rFREE + keys.length ≤ S) (p : ℕ) (hp : p < keys.length) :
    HTB S sldBody (fun c => SldInv keys ord c₀ p c ∧ c.reg rJ = p ∧ c.reg rPL = keys.length)
      (fun c => SldInv keys ord c₀ (p + 1) c ∧ c.reg rJ = p ∧ c.reg rPL = keys.length) 20 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hG, hprev, hsame, hT, hZ⟩, hj, hl'⟩ => ?_
  have hpo : p < ord.length := by omega
  have hqL : ord[p] < keys.length := hb _ (List.getElem_mem hpo)
  have hb' := hIn.below
  have hq : c.mem (c₀.reg rSQ + p) = ord[p] :=
    (hIn.sq.of_below hsame (by omega)).get hpo
  have hk : c.mem (c₀.reg rKY + ord[p]) = keys.getD ord[p] 0 :=
    (hIn.ky.of_below hsame (by omega)).getD hqL
  refine ⟨by addr_ok [sldBody, sldNew, hG.sq, hG.ky, hG.ld, hj, hq, hk], ?_⟩
  -- the leader of the entry
  have hgd : 0 < p → ord.getD (p - 1) 0 = ord[p - 1]'(by omega) := fun _ => getD_eq_getElem' (by omega)
  have hnew : (p = 0 ∨ keys.getD ord[p] 0 ≠ c.reg rV) → keys.idxOf (keys.getD ord[p] 0) = ord[p] := by
    intro h
    refine first_of_sorted hs hc hpo hqL fun hp1 hp0 he => ?_
    rcases h with h | h
    · omega
    · obtain ⟨hV, _⟩ := hprev hp0
      rw [hV, hgd hp0] at h
      exact h he.symm
  have hold : 0 < p → keys.getD ord[p] 0 = c.reg rV → c.reg rX = keys.idxOf (keys.getD ord[p] 0) := by
    intro hp0 he
    obtain ⟨hV, hX⟩ := hprev hp0
    rw [hX, he, hV]
  have hdis := hG.ld
  have hfr := hG.free
  simp +decide only [sldBody, sldNew, run_seq', run_ld, run_ifz', run_mov (show rQ ≠ rT by decide),
    run_mov (show rU ≠ rT by decide), run_ifEq (show rU ≠ rT by decide) (show rV ≠ rT by decide),
    run_skip, run_st (show rX ≠ rT by decide), setReg_reg, setReg_mem, ↓reduceIte, hG.sq, hG.ky,
    hj, hq, hk]
  have hv : keys.getD ord[p] 0 = keys.getD (ord.getD (p + 1 - 1) 0) 0 := by
    rw [Nat.add_sub_cancel, getD_eq_getElem' hpo]
  have hld := ldF_succ hs hpo
  have hT' : ∀ x, x = keys.idxOf (keys.getD ord[p] 0) →
      Tab (upd c.mem (c₀.reg rFREE + ord[p]) x) (c₀.reg rFREE) keys.length (ldF keys ord (p + 1)) := by
    intro x hx; rw [hld, hx]; exact hT.upd rfl
  have hX : ∀ x, x = keys.idxOf (keys.getD ord[p] 0) →
      x = keys.idxOf (keys.getD (ord.getD (p + 1 - 1) 0) 0) := fun x hx => by rw [hx, hv]
  split_ifs with h0 h1
  all_goals
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, fun _ => ⟨?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
    all_goals simp +decide only [setReg_reg, setReg_mem, setMem_reg, setMem_mem_upd, ↓reduceIte,
      hG.pl, hG.sq, hG.ky, hG.ld, hG.free, hj]
  all_goals first
    | exact hv
    | exact hsame.upd_of_ge (by omega) _
    | exact hZ.upd (by omega)
    | exact hX _ (hnew (Or.inl h0)).symm
    | exact hX _ (hold (by omega) h1)
    | exact hX _ (hnew (Or.inr h1)).symm
    | exact hT' _ (hnew (Or.inl h0)).symm
    | exact hT' _ (hold (by omega) h1)
    | exact hT' _ (hnew (Or.inr h1)).symm

/-- The leader pass, in `24 L + 3` steps. -/
theorem stepSld_spec {keys ord : List ℕ} (hs : ord.Pairwise (KeyLt keys))
    (hl : ord.length = keys.length) (hc : ∀ q < keys.length, q ∈ ord)
    (hb : ∀ q ∈ ord, q < keys.length) (c₀ : Config) (hIn : SIn keys ord c₀)
    (hS : c₀.reg rFREE + keys.length ≤ S) :
    HTB S (forUp rJ rPL sldBody) (fun c => SldInv keys ord c₀ 0 c ∧ c.reg rPL = keys.length)
      (fun c => SldInv keys ord c₀ keys.length c ∧ c.reg rJ = keys.length ∧ c.reg rPL = keys.length)
      (keys.length * 24 + 3) :=
  HTB.forUpC (i := rJ) (n := rPL) (N := keys.length) (body := sldBody) (SldInv keys ord c₀) 20
    (by decide) (by decide) (by decide) (fun j => by indep [SldInv, sGlob_iff])
    (fun j hj => sldBody_spec hs hl hc hb c₀ hIn hS j hj)

/-- **The leaders from a sorted order.** Given keys `keys` (`L` cells at `rKY`) and their indices
`ord` sorted by `(key, index)` (`L` cells at `rSQ`, every index once), both below the free
address `F`, `sortedLeads` stores the leaders `LEAD = keys.map (keys.idxOf ·)` at `rLD = F`
within `24 (L + 1)` steps, accessing only addresses below any `S ≥ F + L` and comparing keys
only. -/
theorem sortedLeads_spec (keys ord : List ℕ) (hs : ord.Pairwise (KeyLt keys))
    (hl : ord.length = keys.length) (hc : ∀ q < keys.length, q ∈ ord)
    (hb : ∀ q ∈ ord, q < keys.length) (c₀ : Config) (hS : c₀.reg rFREE + keys.length ≤ S) :
    HTB S sortedLeads (fun c => SIn keys ord c ∧ c = c₀)
      (fun c => (Arr c.mem (c.reg rLD) (keys.map (keys.idxOf ·)) ∧ c.reg rLD = c₀.reg rFREE ∧
        c.reg rFREE = c₀.reg rFREE + keys.length ∧ ZeroFrom c.mem (c.reg rFREE) ∧
        SameOn (· < c₀.reg rFREE) c₀.mem c.mem) ∧ Frame sortedLeads c₀ c)
      (24 * (keys.length + 1)) := by
  intro c ⟨hIn, hc₀⟩
  subst hc₀
  have h₀ : HTB S (alloc rLD rPL) (fun c' => c' = c)
      (fun c' => SldInv keys ord c 0 c' ∧ c'.reg rPL = keys.length) 3 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c' hc' => by
      subst hc'
      rw [run_alloc (by decide) (by decide)]
      refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, fun h => absurd h (by omega), ?_, ?_, ?_⟩, ?_⟩
      all_goals simp +decide only [setReg_reg, setReg_mem, ↓reduceIte, hIn.pl, ldF_zero]
      · exact SameOn.refl _ _
      · exact hIn.free.tab le_rfl _
      · exact hIn.free.mono (by omega)
  obtain ⟨c', t, he, ⟨⟨hG, -, hsame, hT, hZ⟩, -, -⟩, ht⟩ :=
    (h₀.seq (stepSld_spec hs hl hc hb c hIn hS)) c rfl
  refine ⟨c', t, he, ⟨⟨?_, hG.ld, hG.free, by rw [hG.free]; exact hZ, hsame⟩, he.frame⟩, by omega⟩
  intro i hi
  simp only [List.length_map] at hi
  have hm : i ∈ ord.take keys.length := by rw [List.take_of_length_le (by omega)]; exact hc i hi
  rw [hG.ld, hT.get hi, List.getElem_map, ldF]
  simp only [hm, ↓reduceIte, getD_eq_getElem' hi]

/-- The registers written by `sortedLeads`: `rT`, `rFREE`, `rLD` and scratch registers. -/
theorem sortedLeads_wregs : ∀ r ∈ wregs sortedLeads, r = rT ∨ r = rFREE ∨ (rLD ≤ r ∧ r < 138) := by
  decide

/-! ### First-appearance identifiers from a sorted order -/

/-- **First-appearance identifiers from a sorted order (leader and rank passes).** -/
def sortedIds : Stmt := .seq sortedLeads rankIds

/-- **First-appearance identifiers from a sorted order.** With the keys `keys` and their indices
sorted by `(key, index)` below the free address `F` (`SIn`), `sortedIds` stores the leaders at
`rLD`, the identifiers `EID = eids keys` (`EID[q] = keys.eraseDups.idxOf keys[q]`, the position
of the key of `q` in order of first appearance) at `rID`, the class sizes at `rCT` and
`NE = |keys.eraseDups|` in `rNE`, within `58 (L + 1)` steps, accessing only addresses below any
`S ≥ F + 3L`, comparing keys only (no memory indexed by keys). -/
theorem sortedIds_spec (keys ord : List ℕ) (hs : ord.Pairwise (KeyLt keys))
    (hl : ord.length = keys.length) (hc : ∀ q < keys.length, q ∈ ord)
    (hb : ∀ q ∈ ord, q < keys.length) (c₀ : Config)
    (hS : c₀.reg rFREE + keys.length + keys.length + keys.length ≤ S) :
    HTB S sortedIds (fun c => SIn keys ord c ∧ c = c₀)
      (fun c => Arr c.mem (c.reg rID) (eids keys) ∧
        Tab c.mem (c.reg rCT) keys.length (fun e => (eids keys).count e) ∧
        c.reg rNE = keys.eraseDups.length ∧
        c.reg rFREE = c₀.reg rFREE + keys.length + keys.length + keys.length ∧
        ZeroFrom c.mem (c.reg rFREE) ∧ SameOn (· < c₀.reg rFREE) c₀.mem c.mem ∧
        Frame sortedIds c₀ c)
      (58 * (keys.length + 1)) := by
  intro c ⟨hIn, hc₀⟩
  subst hc₀
  obtain ⟨c₁, t₁, he₁, ⟨⟨hld, hrld, hfree, hzero, hsame⟩, hfr₁⟩, ht₁⟩ :=
    sortedLeads_spec (S := S) keys ord hs hl hc hb c (by omega) c ⟨hIn, rfl⟩
  have hR : RIn keys c₁ :=
    ⟨(hfr₁.reg rPL (by decide)).trans hIn.pl, hld, by rw [hrld, hfree], hzero⟩
  obtain ⟨c₂, t₂, he₂, ⟨hO, -⟩, ht₂⟩ :=
    rankIds_spec (S := S) keys c₁ (by rw [hfree]; omega) c₁ ⟨hR, rfl⟩
  refine ⟨c₂, t₁ + t₂, ExecB.seq he₁ he₂, ⟨hO.id, hO.ct, hO.ne, by rw [hO.free, hfree],
    hO.zero, hsame.trans (hO.same.mono fun a (ha : a < _) => show a < _ by rw [hfree]; omega),
    (ExecB.seq he₁ he₂).frame⟩, ?_⟩
  simp only [CR] at ht₂
  omega

end STACS2027.RAM.PairIds
