module

public import Runtimes.ConvexQP.RAM.QPIface
import Mathlib.Tactic

/-!
# Lemma 15 on the RAM, the parser: the overlap matrix `H` on the abstract side

Flat indices `a = c k + j` (cycle `c`, option `j`). Option `j` of cycle `c` (the path
`selected C_c j`, which omits the vertex at position `j`) consists of the edges at the positions
`opos k j s = (j + 1 + s) % k`, `s < k − 2` (`mem_selected_iff`), i.e. of the occurrences
`occ k a s = (a/k) k + opos k (a % k) s` of Corollary 5's numbering, whose edge identifiers
`eidOf g k (occ k a s)` the RAM reads from `EID`.

The RAM computes `H` with a table `MARK` over the edge identifiers: `mk f b s v` is the table `f`
after writing `v` at the identifiers of the first `s` edges of option `b`; `mark g k b` is the
indicator of option `b` (from a zero table), and `mk (mark g k b) b (k − 2) 0` is zero again
(`mk_unmark`). The count `hc g k a b s = Σ_{s' < s} mark g k b (eidOf (occ k a s'))` after
`k − 2` steps is the entry of `H` (**`Hflat_instOf`**, for a duplicate-free `g`).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Parse

open STACS2027 STACS2027.RAM STACS2027.Runtimes.ConvexQP STACS2027.Runtimes.ZeroCost

/-! ### Positions and occurrences of an option -/

/-- Position `s` of option `j` on a cycle of length `k`: `(j + 1 + s) % k`. -/
def opos (k j s : ℕ) : ℕ := (j + 1 + s) % k

/-- The occurrence (Corollary 5's numbering) of the edge `s` of option `a = c k + j`. -/
def occ (k a s : ℕ) : ℕ := a / k * k + opos k (a % k) s

theorem opos_eq {k j s : ℕ} (hj : j < k) (hs : s < k) :
    opos k j s = if j + 1 + s < k then j + 1 + s else j + 1 + s - k := by
  unfold opos
  split
  · exact Nat.mod_eq_of_lt (by assumption)
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem opos_lt {k : ℕ} (hk : 0 < k) (j s : ℕ) : opos k j s < k := Nat.mod_lt _ hk

theorem opos_zero {k j : ℕ} (hj : j < k) : opos k j 0 = next k j := by
  rw [opos_eq hj (by omega)]
  unfold next
  split_ifs <;> omega

theorem opos_succ {k : ℕ} (hk : 0 < k) (j s : ℕ) : opos k j (s + 1) = next k (opos k j s) := by
  have h1 : opos k j (s + 1) = (opos k j s + 1) % k := by
    unfold opos
    rw [show j + 1 + (s + 1) = (j + 1 + s) + 1 by omega, Nat.add_mod (j + 1 + s) 1 k,
      Nat.add_mod ((j + 1 + s) % k) 1 k, Nat.mod_mod]
  have hp := opos_lt hk j s
  rw [h1]
  unfold next
  split
  · exact Nat.mod_eq_of_lt (by assumption)
  · rw [show opos k j s + 1 = k by omega, Nat.mod_self]

theorem opos_inj {k j s s' : ℕ} (hj : j < k) (hs : s < k) (hs' : s' < k)
    (h : opos k j s = opos k j s') : s = s' := by
  rw [opos_eq hj hs, opos_eq hj hs'] at h
  split at h <;> split at h <;> omega

theorem div_mul_lt {t k a : ℕ} (ha : a < t * k) : a / k * k + k ≤ k * t := by
  have h1 : a / k < t := div_lt_of_lt_tk ha
  have : (a / k + 1) * k ≤ t * k := Nat.mul_le_mul_right k h1
  rw [Nat.add_mul, one_mul] at this
  rw [Nat.mul_comm k t]; exact this

theorem occ_lt {t k a : ℕ} (ha : a < t * k) (s : ℕ) : occ k a s < k * t := by
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by simp [h] at ha
  have := div_mul_lt ha
  have := opos_lt hk (a % k) s
  unfold occ; omega

/-- **The edges of an option**: the path omitting the vertex at position `j` consists of the edges
at the positions `(j + 1 + s) % k`, `s < k − 2`. -/
theorem mem_selected_iff {g : Graph} {k : ℕ} {cy : Cycle} (hc : IsCycle g k cy) {j : ℕ}
    (hj : j < k) {e : Edge} :
    e ∈ selected cy j ↔ ∃ s < k - 2, (cycleEdges cy).getD (opos k j s) (0, 0) = e := by
  have hk : 3 ≤ k := hc.1
  constructor
  · intro he
    obtain ⟨p, hp, rfl⟩ := exists_position hc (selected_mem_cycleEdges he)
    have hnot := (mem_selected_iff_position hc hj hp).mp he
    unfold next at hnot
    by_cases hpj : j < p
    · refine ⟨p - j - 1, ?_, ?_⟩
      · split at hnot <;> omega
      · rw [opos_eq hj (by omega)]; split <;> [congr 1; omega]; omega
    · refine ⟨p + k - j - 1, ?_, ?_⟩
      · split at hnot <;> omega
      · rw [opos_eq hj (by split at hnot <;> omega)]; split <;> [omega; congr 1]; omega
  · rintro ⟨s, hs, rfl⟩
    have hp : opos k j s < k := opos_lt (by omega) j s
    rw [mem_selected_iff_position hc hj hp]
    have he := opos_eq hj (show s < k by omega)
    unfold next
    split <;> split at he <;> omega

/-! ### The mark table and the count -/

variable (g : Graph) (k : ℕ)

/-- The table `f` after writing `v` at the identifiers of the first `s` edges of option `b`. -/
def mk (f : ℕ → ℕ) (b s v : ℕ) (e : ℕ) : ℕ :=
  if (List.range s).any (fun s' => eidOf g k (occ k b s') == e) then v else f e

/-- The indicator of the edge identifiers of option `b`. -/
def mark (b : ℕ) : ℕ → ℕ := mk g k (fun _ => 0) b (k - 2) 1

/-- `Σ_{s' < s} [the edge s' of option a lies on option b]`. -/
def hc (a b s : ℕ) : ℕ := ∑ s' ∈ Finset.range s, mark g k b (eidOf g k (occ k a s'))

variable {g k}

theorem mk_zero (f : ℕ → ℕ) (b v : ℕ) : mk g k f b 0 v = f := by
  funext e; simp [mk]

theorem mk_succ (f : ℕ → ℕ) (b s v : ℕ) :
    mk g k f b (s + 1) v = Function.update (mk g k f b s v) (eidOf g k (occ k b s)) v := by
  funext e
  by_cases he : e = eidOf g k (occ k b s)
  · subst he; simp [mk, List.range_succ]
  · rw [Function.update_of_ne he]
    have : (eidOf g k (occ k b s) == e) = false := by simpa using Ne.symm he
    simp [mk, List.range_succ, this]

theorem mk_unmark (b : ℕ) : mk g k (mark g k b) b (k - 2) 0 = fun _ => 0 := by
  funext e
  unfold mk mark mk
  split <;> simp_all

theorem hc_zero (a b : ℕ) : hc g k a b 0 = 0 := by simp [hc]

theorem hc_succ (a b s : ℕ) :
    hc g k a b (s + 1) = hc g k a b s + mark g k b (eidOf g k (occ k a s)) := by
  simp [hc, Finset.sum_range_succ]

/-! ### `H` of the instance -/

theorem path_cycles {g : Graph} {k c j : ℕ} (hc : c < (cycles g k).length) (hj : j < k) :
    path ((cycles g k).map selectedOptions) c j = selected (kCycle g k c) j := by
  have hlen := cycles_length g k (List.getElem_mem hc)
  have h1 : ((cycles g k).map selectedOptions).getD c [] = selectedOptions (cycles g k)[c] := by
    rw [getD_of_lt _ _ (by simpa using hc), List.getElem_map]
  unfold path kCycle
  rw [h1, getD_of_lt (cycles g k) [] hc]
  unfold selectedOptions
  rw [getD_of_lt _ _ (by simp [hlen, hj])]
  simp

theorem cnt_instOf {g : Graph} {k : ℕ} (c : Fin (instOf g k).t) (j : Fin (instOf g k).k)
    (i : Fin (instOf g k).m) :
    (instOf g k).cnt c j i =
      if g[(i : ℕ)] ∈ selected (kCycle g k c) j then 1 else 0 := by
  have hc : (c : ℕ) < (cycles g k).length := by simpa using c.2
  have hj : (j : ℕ) < k := j.2
  have hcyc := kCycle_isCycle g hc
  have hp : (path ((cycles g k).map selectedOptions) c j).Nodup := by
    rw [path_cycles hc hj]; exact selected_nodup hcyc.2.2.1 _
  rw [show (instOf g k).cnt c j i = (ofOpts g k ((cycles g k).map selectedOptions)).cnt c j i
    from rfl, cnt_ofOpts g k _ c j i hp, path_cycles hc hj]
  split
  · exact List.count_eq_one_of_mem (path_cycles hc hj ▸ hp) (by assumption)
  · exact List.count_eq_zero_of_not_mem (by assumption)

/-- The entry `H(c, j; c', j')` of the instance of a duplicate-free graph: the number of edges of
option `j` of `C_c` lying on option `j'` of `C_{c'}`. -/
theorem H_instOf {g : Graph} (hg : g.Nodup) {k : ℕ} (c : Fin (instOf g k).t)
    (j : Fin (instOf g k).k) (c' : Fin (instOf g k).t) (j' : Fin (instOf g k).k) :
    (instOf g k).H c j c' j' = ∑ s ∈ Finset.range (k - 2),
      if cycleEdgeAt g k c (opos k j s) ∈ selected (kCycle g k c') j' then 1 else 0 := by
  have hc : (c : ℕ) < (cycles g k).length := by simpa using c.2
  have hjk : (j : ℕ) < k := j.2
  have hcyc := kCycle_isCycle g hc
  have hk : 3 ≤ k := hcyc.1
  set P := selected (kCycle g k c) j
  set P' := selected (kCycle g k c') j'
  let F : Edge → ℕ := fun x => (if x ∈ P then 1 else 0) * (if x ∈ P' then 1 else 0)
  have h1 : (instOf g k).H c j c' j' = (g.map F).sum := by
    rw [← Fin.sum_univ_fun_getElem g F]
    unfold Inst.H
    exact Finset.sum_congr rfl fun i _ => by rw [cnt_instOf, cnt_instOf]
  rw [h1]
  rw [← List.sum_toFinset _ hg]
  have hsub : P.toFinset ⊆ g.toFinset := fun x hx => by
    rw [List.mem_toFinset] at hx ⊢
    exact selected_mem_graph hcyc _ hx
  rw [← Finset.sum_subset hsub (fun x _ hx => by simp [List.mem_toFinset.not.mp hx] at hx ⊢)]
  have h2 : ∑ x ∈ P.toFinset, (if x ∈ P then 1 else 0) * (if x ∈ P' then 1 else 0) =
      ∑ x ∈ P.toFinset, if x ∈ P' then 1 else 0 :=
    Finset.sum_congr rfl fun x hx => by simp [List.mem_toFinset.mp hx]
  have himg : P.toFinset = (Finset.range (k - 2)).image fun s => cycleEdgeAt g k c (opos k j s) := by
    ext x
    simp only [List.mem_toFinset, Finset.mem_image, Finset.mem_range]
    rw [mem_selected_iff hcyc hjk]
    rfl
  have hinj : Set.InjOn (fun s => cycleEdgeAt g k c (opos k j s)) (Finset.range (k - 2) : Set ℕ) := by
    intro s hs s' hs' h
    simp only [Finset.coe_range, Set.mem_Iio] at hs hs'
    exact opos_inj hjk (by omega) (by omega)
      (edgeAt_inj hcyc (opos_lt (by omega) _ _) (opos_lt (by omega) _ _) h)
  rw [h2, himg, Finset.sum_image hinj]

/-- The mark of an edge of option `a`, by the edge itself. -/
theorem mark_occ {g : Graph} {k a b s : ℕ} (ha : a < (cycles g k).length * k)
    (hb : b < (cycles g k).length * k) :
    mark g k b (eidOf g k (occ k a s)) =
      if cycleEdgeAt g k (a / k) (opos k (a % k) s) ∈ selected (kCycle g k (b / k)) (b % k)
      then 1 else 0 := by
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by simp [h] at ha
  have hcb : b / k < (cycles g k).length := div_lt_of_lt_tk hb
  have hca : a / k < (cycles g k).length := div_lt_of_lt_tk ha
  have hcyc := kCycle_isCycle g hcb
  have hocc : ∀ x, x < (cycles g k).length * k → ∀ s',
      (occs g k).getD (occ k x s') (0, 0) = cycleEdgeAt g k (x / k) (opos k (x % k) s') :=
    fun x hx s' => occs_getD_cycleEdgeAt (div_lt_of_lt_tk hx) (opos_lt hk _ _)
  unfold mark mk
  congr 1
  rw [mem_selected_iff hcyc (Nat.mod_lt _ hk)]
  simp only [List.any_eq_true, List.mem_range, beq_iff_eq, eq_iff_iff]
  refine exists_congr fun s' => and_congr_right fun hs' => ?_
  rw [eidOf_eq_iff (occ_lt hb s'), hocc b hb, hocc a ha]
  rfl

/-- **`H` of the instance, as the RAM counts it**: for a duplicate-free graph,
`H(a, b) = Σ_{s < k−2} mark b (EID[occ a s])`. -/
theorem Hflat_instOf {g : Graph} (hg : g.Nodup) {k a b : ℕ} (ha : a < (cycles g k).length * k)
    (hb : b < (cycles g k).length * k) :
    Hflat (instOf g k) a b = (hc g k a b (k - 2) : ℤ) := by
  have hab : a < (instOf g k).t * (instOf g k).k ∧ b < (instOf g k).t * (instOf g k).k := by
    simp only [List.length_map]; exact ⟨ha, hb⟩
  unfold Hflat
  rw [dite_eq_left_of_eq_true (eq_true hab), H_instOf hg]
  push_cast
  unfold hc
  push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mark_occ ha hb]
  push_cast
  rfl

end STACS2027.Runtimes.QPRam.Parse
