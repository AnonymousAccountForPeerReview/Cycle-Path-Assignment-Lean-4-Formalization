module

public import Hardness.Decode.Selectors
public import Hardness.Decode.PoweringCore
public import OAI.Computability.UniqueGames.PCP.PoweringPortReindexLemmas

/-!
# Decoding the powering stage: least most-frequent opinion over walks

For a port table `P` on `vertices` vertices with `d` ports, a walk parameter `n` (walks of the
powered table have `n + 1` steps) and a sample length `N`, `powerDecode P n N labels` turns a
labeling of the powered table `PoweringTables.table P n` into a labeling of `P`:

* `decodeLabeling d n labels w` reads the label of `w` as a table of opinions, one `Fin 64`
  for every port word of length at most `n + 1`;
* the opinion of `w` about `u` is the entry at the first address (in the fixed list
  `allAddresses d (n + 1)`) whose walk from `w` ends in `u`, and `0` if there is none;
* `opinionCount P n N labels u a` is the number of port words `p : Fin N → Fin d` such that
  the opinion about `u` of the end point of the walk `p` from `u` is `a`;
* `powerDecode P n N labels u` is the least `a : Fin 64` maximising that count.

`powerDecode_bound` is the pointwise soundness statement for `P = lazy input`.
-/

@[expose] public section

namespace OAI.UniqueGamesTheorem.Foundations.PCP.Decode

noncomputable section

open scoped BigOperators
open PoweringWalks PoweringLabels PoweringOpinions PoweringTest PoweringReach
open SpectralReturn PoweringSoundness PoweringPortReindex

section Mass

variable {Ω A : Type*} [Fintype Ω]

theorem mass_eq_count [DecidableEq A] (opinion : Ω → A) (a : A) :
    PoweringDecoding.mass opinion a =
      ((Finset.univ.filter (fun ω => opinion ω = a)).card : ℝ) / (Fintype.card Ω : ℝ) := by
  unfold PoweringDecoding.mass
  rw [Fintype.expect_eq_sum_div_card]
  congr 1
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro ω _
  congr

/-- The least most frequent value of a `Fin n`-valued function has mass at least `1 / n`. -/
theorem leastArgMax_mass_lower [Nonempty Ω] {n : Nat} (h : 0 < n) (opinion : Ω → Fin n) :
    1 / (n : ℝ) ≤ PoweringDecoding.mass opinion
      (leastArgMax h (fun a => (Finset.univ.filter (fun ω => opinion ω = a)).card)) := by
  rw [mass_eq_count]
  have total : Fintype.card Ω =
      ∑ a : Fin n, (Finset.univ.filter (fun ω => opinion ω = a)).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  have hle := leastArgMax_mass h (fun a => (Finset.univ.filter (fun ω => opinion ω = a)).card)
  rw [← total] at hle
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr h
  have hΩ : (0 : ℝ) < Fintype.card Ω := Nat.cast_pos.mpr Fintype.card_pos
  rw [div_le_div_iff₀ hn hΩ, one_mul, mul_comm]
  exact_mod_cast hle

end Mass

section Reindex

variable {V D E A : Type*}

/-- Sampled opinions are invariant under a rotation-preserving change of ports. -/
theorem sampleOpinion_reindex (G : PortGraph V D) (H : PortGraph V E) (ports : D ≃ E)
    (rotation : ∀ v d, H.rot (v, ports d) = ((G.rot (v, d)).1, ports (G.rot (v, d)).2))
    (t N : Nat) (selectors : ∀ v, AddressSelector H t v)
    (labels : V → PaddedLabel E t A) (fallback : A) (u : V) (p : Fin N → D) :
    sampleOpinion G t N (fun v => pullSelector G H ports rotation (selectors v))
        (fun v => labelEquiv ports t (labels v)) fallback u p =
      sampleOpinion H t N selectors labels fallback u (wordEquiv ports N p) := by
  unfold sampleOpinion
  rw [opinionAt_pullSelector, wordEnd_map G H ports rotation]

theorem mass_reindex [Fintype D] [Fintype E] (G : PortGraph V D) (H : PortGraph V E)
    (ports : D ≃ E)
    (rotation : ∀ v d, H.rot (v, ports d) = ((G.rot (v, d)).1, ports (G.rot (v, d)).2))
    (t N : Nat) (selectors : ∀ v, AddressSelector H t v)
    (labels : V → PaddedLabel E t A) (fallback : A) (u : V) (a : A) :
    PoweringDecoding.mass (sampleOpinion G t N
        (fun v => pullSelector G H ports rotation (selectors v))
        (fun v => labelEquiv ports t (labels v)) fallback u) a =
      PoweringDecoding.mass (sampleOpinion H t N selectors labels fallback u) a := by
  classical
  unfold PoweringDecoding.mass
  apply Fintype.expect_equiv (wordEquiv ports N)
  intro p
  rw [sampleOpinion_reindex G H ports rotation]

/-- `PoweringPortReindex.uniform_count_gap` in pointwise form, for an arbitrary decoding whose
letters have mass at least `1 / q` among the sampled opinions. -/
theorem reindexed_count_bound
    [Fintype V] [Fintype D] [Fintype E] [Nonempty V] [Nonempty D]
    [Fintype A] [Nonempty A]
    (G : PortGraph V D) (H : PortGraph V E) (ports : (Bool × D) ≃ E)
    (rotation : ∀ v d, H.rot (v, ports d) =
      (((lazyGraph G).rot (v, d)).1, ports ((lazyGraph G).rot (v, d)).2))
    (lambda : ℝ) (certificate : SpectralCertificate (lazyGraph G) lambda)
    (accepts : Edge V E → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (q : Nat) (hq : Fintype.card A = q) (M : Nat) (hM : 1 ≤ M)
    (selectors : ∀ v, AddressSelector H (2 * center q M + 1) v)
    (labels : V → PaddedLabel E (2 * center q M + 1) A) (fallback : A) (dec : V → A)
    (hmass : ∀ u, 1 / (q : ℝ) ≤ PoweringDecoding.mass
      (sampleOpinion H (2 * center q M + 1) (center q M) selectors labels fallback u) (dec u)) :
    (gain q M lambda *
      min (((baseGraph H accepts reverse_accepts).rejectionCount dec : ℝ) /
          (Fintype.card (Edge V E) : ℝ))
        (1 / ((2 * center q M + 1 : Nat) : ℝ))) *
        (Fintype.card (Dart V E (2 * center q M)) : ℝ) ≤
      ((poweredGraph H accepts (2 * center q M) selectors).rejectionCount labels : ℝ) := by
  subst hq
  have bound := count_bound_of_mass G lambda certificate
    (pullAccepts ports accepts)
    (pullReverse (lazyGraph G) H ports rotation accepts reverse_accepts) M hM
    (fun v => pullSelector (lazyGraph G) H ports rotation (selectors v))
    (fun v => labelEquiv ports _ (labels v)) fallback dec (by
      intro u
      rw [mass_reindex (lazyGraph G) H ports rotation]
      exact hmass u)
  rw [base_rejectionCount_map (lazyGraph G) H ports rotation,
    Fintype.card_congr (Equiv.prodCongr (Equiv.refl V) ports),
    rejectionCount_map (lazyGraph G) H ports rotation,
    Fintype.card_congr (dartEquiv (V := V) ports (2 * center (Fintype.card A) M))] at bound
  exact bound

end Reindex

section Table

open PoweringAddresses PoweringTableSemantics

variable {vertices d : Nat}

/-- `scanWitness` returns the first element of the list satisfying the predicate. -/
theorem scanWitness_find {X : Type*} (p : X → Prop) [DecidablePred p] (xs : List X)
    (h : ∃ a ∈ xs, p a) :
    xs.find? (fun a => decide (p a)) = some (scanWitness p xs h).val := by
  induction xs with
  | nil => exact False.elim (by simp at h)
  | cons a xs ih =>
    by_cases ha : p a
    · simp only [scanWitness, ha, ↓reduceDIte, List.find?_cons, decide_true]
    · simp only [scanWitness, ha, ↓reduceDIte, List.find?_cons, decide_false]
      exact ih _

/-- Explicit form of the opinion of `w` about `u` under the first-match selector: the entry
of the label of `w` at the first address of `allAddresses d t` whose walk from `w` ends in
`u`, and the fallback letter if there is no such address. -/
theorem opinionAt_eq_find (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (lab : Fin vertices → PaddedLabel (Fin d) t (Fin 64)) (fallback : Fin 64)
    (u w : Fin vertices) :
    opinionAt G t (finitePortSelector G t) lab fallback u w =
      ((allAddresses d t).find? (fun a => decide (wordEnd G a.1.val w a.2 = u))).elim
        fallback (lab w) := by
  classical
  by_cases h : ∃ n, n ≤ t ∧ ∃ p : Fin n → Fin d, wordEnd G n w p = u
  · have hdec := opinionAt_eq_decode G t (finitePortSelector G t) lab fallback w ⟨u, h⟩
    have hfind := scanWitness_find
      (fun a : PortWords (Fin d) t => (wordToBall G t w a).val = u) (allAddresses d t) (by
        obtain ⟨a, ha⟩ := wordToBall_surjective G t w ⟨u, h⟩
        exact ⟨a, mem_allAddresses d t a, congrArg Subtype.val ha⟩)
    change (allAddresses d t).find? (fun a => decide (wordEnd G a.1.val w a.2 = u)) = _ at hfind
    rw [hfind]
    exact hdec
  · have hnone : (allAddresses d t).find? (fun a => decide (wordEnd G a.1.val w a.2 = u)) =
        none := by
      apply List.find?_eq_none.mpr
      intro a _
      simp only [decide_eq_true_eq]
      intro ha
      exact h ⟨a.1.val, Nat.le_of_lt_succ a.1.isLt, a.2, ha⟩
    rw [hnone]
    simp only [opinionAt, h, ↓reduceDIte, Option.elim]

/-- The opinion sampled by the port word `p` about its start vertex `u`: the opinion about `u`
stored in the label of the end point of the walk `p` from `u`. -/
def sampledOpinion (P : PortTables.Table vertices d) (n N : Nat)
    (labels : EncodedLabeling vertices d n) (u : Fin vertices) (p : Fin N → Fin d) : Fin 64 :=
  sampleOpinion (PortTables.portGraph P) (n + 1) N
    (finitePortSelector (PortTables.portGraph P) (n + 1))
    (decodeLabeling d n labels) (0 : Fin 64) u p

/-- Explicit form of `sampledOpinion`: with `w` the end point of the walk `p` from `u`, the
entry of the decoded label of `w` at the first address whose walk from `w` ends in `u`
(and `0` if there is none). -/
theorem sampledOpinion_eq_find (P : PortTables.Table vertices d) (n N : Nat)
    (labels : EncodedLabeling vertices d n) (u : Fin vertices) (p : Fin N → Fin d) :
    sampledOpinion P n N labels u p =
      ((allAddresses d (n + 1)).find? (fun a => decide
        (wordEnd (PortTables.portGraph P) a.1.val
          (wordEnd (PortTables.portGraph P) N u p) a.2 = u))).elim (0 : Fin 64)
        (decodeLabeling d n labels (wordEnd (PortTables.portGraph P) N u p)) :=
  opinionAt_eq_find (PortTables.portGraph P) (n + 1) (decodeLabeling d n labels) 0 u
    (wordEnd (PortTables.portGraph P) N u p)

/-- Number of port words of length `N` whose sampled opinion about `u` is `a`. -/
def opinionCount (P : PortTables.Table vertices d) (n N : Nat)
    (labels : EncodedLabeling vertices d n) (u : Fin vertices) (a : Fin 64) : Nat :=
  (Finset.univ.filter (fun p : Fin N → Fin d => sampledOpinion P n N labels u p = a)).card

/-- Stage decoder for powering: the least most frequent sampled opinion. -/
def powerDecode (P : PortTables.Table vertices d) (n N : Nat)
    (labels : EncodedLabeling vertices d n) : Fin vertices → Fin 64 :=
  fun u => leastArgMax (by decide : 0 < 64) (opinionCount P n N labels u)

theorem powerDecode_mass (P : PortTables.Table vertices d) (hd : 0 < d) (n N : Nat)
    (labels : EncodedLabeling vertices d n) (u : Fin vertices) :
    1 / ((64 : Nat) : ℝ) ≤ PoweringDecoding.mass
      (sampleOpinion (PortTables.portGraph P) (n + 1) N
        (finitePortSelector (PortTables.portGraph P) (n + 1))
        (decodeLabeling d n labels) (0 : Fin 64) u) (powerDecode P n N labels u) := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact leastArgMax_mass_lower (by decide : 0 < 64) (sampledOpinion P n N labels u)

/-- Pointwise soundness of powering a lazified port table, with the deterministic decoder:
the powered table rejects at least `gain · min(ε, 1 / (n + 1))` of its darts under `labels`,
where `ε` is the fraction of darts of the lazified table rejected by the decoded labeling. -/
theorem powerDecode_bound (input : PortTables.Table vertices d) (hv : 0 < vertices)
    (hd : 0 < d) (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph (PortTables.portGraph input)) lambda)
    (M : Nat) (hM : 1 ≤ M) (n : Nat) (hn : n = 2 * center 64 M)
    (labels : EncodedLabeling vertices (2 * d) n) :
    (gain 64 M lambda *
      min (((PortTables.baseGraph (PreprocessingOverlayTables.lazy input)).rejectionCount
            (powerDecode (PreprocessingOverlayTables.lazy input) n (center 64 M) labels) : ℝ) /
          ((vertices * (2 * d) : Nat) : ℝ))
        (1 / ((n + 1 : Nat) : ℝ))) *
      ((PoweringTables.table (PreprocessingOverlayTables.lazy input) n).darts : ℝ) ≤
      ((GenericGraphTables.semantics
        (PoweringTables.table (PreprocessingOverlayTables.lazy input) n)).rejectionCount
          labels : ℝ) := by
  subst n
  let : Nonempty (Fin vertices) := ⟨⟨0, hv⟩⟩
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hrot : ∀ v p,
      (PortTables.portGraph (PreprocessingOverlayTables.lazy input)).rot
          (v, PreprocessingOverlayTables.lazyPorts d p) =
        (((lazyGraph (PortTables.portGraph input)).rot (v, p)).1,
          PreprocessingOverlayTables.lazyPorts d
            ((lazyGraph (PortTables.portGraph input)).rot (v, p)).2) := by
    intro v p
    rw [PreprocessingTableSpectral.lazy_portGraph]
    exact GraphTransport.reindex_rot _ (Equiv.refl _) _ v p
  have bound := reindexed_count_bound (PortTables.portGraph input)
    (PortTables.portGraph (PreprocessingOverlayTables.lazy input))
    (PreprocessingOverlayTables.lazyPorts d) hrot lambda certificate
    (PortTables.accepts (PreprocessingOverlayTables.lazy input))
    (PortTables.accepts_rotation (PreprocessingOverlayTables.lazy input))
    64 (Fintype.card_fin 64) M hM
    (finitePortSelector (PortTables.portGraph (PreprocessingOverlayTables.lazy input)) _)
    (decodeLabeling (2 * d) (2 * center 64 M) labels) (0 : Fin 64)
    (powerDecode (PreprocessingOverlayTables.lazy input) (2 * center 64 M) (center 64 M) labels)
    (fun u => powerDecode_mass (PreprocessingOverlayTables.lazy input) (by omega)
      (2 * center 64 M) (center 64 M) labels u)
  rw [rejectionCount_decoded, ← card_darts_eq_table]
  have hcard : Fintype.card (Edge (Fin vertices) (Fin (2 * d))) = vertices * (2 * d) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
  rw [hcard] at bound
  exact bound

end Table

end

end OAI.UniqueGamesTheorem.Foundations.PCP.Decode
