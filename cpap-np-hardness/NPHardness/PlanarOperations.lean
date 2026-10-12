module

public import Complexity.Planar.Subdivide
import Lean.Elab.Tactic.Omega

/-!Plain edge subdivision for the registered `Complexity.PlanarGraph` predicate.
Adapted from `Complexity/Planar/Subdivide.lean` at registered commit
`3e603e795b44fedcf7d6dd65b7d1e30547ead925` (Apache-2.0).
The orbit-counting and reachability lemmas are reused from the pinned registered
foundation; the local four-dart construction removes the pendant branch present
in the upstream six-dart construction.
-/

@[expose] public section
namespace STACS2027.PlanarOperations.Subdivision
open Complexity Complexity.Planar
open Complexity.Planar.Subdiv (gN gNi gF ed gN_lt gNi_lt gF_lt gN_gNi ed_ed ed_lt edge_val
  gNi_ed cycleCount_ge_labels cminN cminF cminN_step cminF_step compMin compMin_false
  lk_of_step lk_trans halfEdgeEnd_mem iterate_gN_val)

section maps

variable (A : Nat)

/-- The new dart of an old dart. -/
def iota (y : Nat) : Nat := if y < A then y else A + 4 * ((y - A) / 2) + 2 * ((y - A) % 2)

/-- The old dart of a dart of the old class. -/
def sig (x : Nat) : Nat :=
  if x < A then x else A + 2 * ((x - A) / 4) + (if (x - A) % 4 = 2 then 1 else 0)

/-- The old class. -/
abbrev IsOld (x : Nat) : Prop := x < A ∨ (x - A) % 4 = 0 ∨ (x - A) % 4 = 2

theorem sig_iota (y : Nat) : sig A (iota A y) = y := by
  unfold iota sig
  by_cases h : y < A
  · simp [h]
  · rw [ite_eq_right h, ite_eq_right (by omega)]
    rcases Nat.mod_two_eq_zero_or_one (y - A) with h2 | h2
    · rw [ite_eq_right (by omega)]; omega
    · rw [ite_eq_left (by omega)]; omega

theorem isOld_iota (y : Nat) : IsOld A (iota A y) := by
  unfold iota
  by_cases h : y < A
  · rw [ite_eq_left h]; exact Or.inl h
  · rw [ite_eq_right h]
    rcases Nat.mod_two_eq_zero_or_one (y - A) with h2 | h2 <;> omega

theorem iota_sig {x : Nat} (hx : IsOld A x) : iota A (sig A x) = x := by
  unfold iota sig
  by_cases h : x < A
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h]
    rcases hx with hx | hx | hx
    · omega
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; omega
    · rw [ite_eq_left hx, ite_eq_right (by omega)]; omega

theorem iota_lt {T y : Nat} (hy : y < A + 2 * T) : iota A y < A + 4 * T := by
  unfold iota; split <;> omega

theorem sig_lt {T x : Nat} (hx : x < A + 4 * T) : sig A x < A + 2 * T := by
  unfold sig; split
  · omega
  · split <;> omega

theorem iota_mono {y y' : Nat} (h : y < y') : iota A y < iota A y' := by
  unfold iota; split <;> split <;> omega

end maps

section perms
variable {n : Nat} (G : Hypermap n) (A : Nat)
def nd (x : Nat) : Nat :=
  if IsOld A x then iota A (gN G (sig A x))
  else if (x-A)%4 = 1 then x+2 else x-2
def ndi (x : Nat) : Nat :=
  if IsOld A x then iota A (gNi G (sig A x))
  else if (x-A)%4 = 1 then x+2 else x-2
def fc (x : Nat) : Nat := ndi G A (ed x)
def tau (x : Nat) : Nat :=
  if IsOld A x then sig A x
  else if (x-A)%4 = 3 then A+2*((x-A)/4) else A+2*((x-A)/4)+1
end perms
section eval
variable {n : Nat} (G : Hypermap n) {A x : Nat}
theorem nd_old (h : IsOld A x) : nd G A x = iota A (gN G (sig A x)) := by
  unfold nd; rw [ite_eq_left h]
theorem nd_r1 (hx : A ≤ x) (h : (x-A)%4 = 1) : nd G A x = x+2 := by
  unfold nd; rw [ite_eq_right (by omega), ite_eq_left h]
theorem nd_r3 (hx : A ≤ x) (h : (x-A)%4 = 3) : nd G A x = x-2 := by
  unfold nd; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
theorem ndi_old (h : IsOld A x) : ndi G A x = iota A (gNi G (sig A x)) := by
  unfold ndi; rw [ite_eq_left h]
theorem ndi_r1 (hx : A ≤ x) (h : (x-A)%4 = 1) : ndi G A x = x+2 := by
  unfold ndi; rw [ite_eq_right (by omega), ite_eq_left h]
theorem ndi_r3 (hx : A ≤ x) (h : (x-A)%4 = 3) : ndi G A x = x-2 := by
  unfold ndi; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
omit G in
theorem dart_cases (x : Nat) : x < A ∨ (A ≤ x ∧ ((x-A)%4 = 0 ∨ (x-A)%4 = 1 ∨
  (x-A)%4 = 2 ∨ (x-A)%4 = 3)) := by omega
omit G in
theorem sig_new {u r : Nat} (hr : r = 0 ∨ r = 2) :
    sig A (A + 4 * u + r) = A + 2 * u + (if r = 2 then 1 else 0) := by
  unfold sig
  rw [ite_eq_right (by omega), show A + 4 * u + r - A = 4 * u + r by omega,
    show (4 * u + r) / 4 = u by omega, show (4 * u + r) % 4 = r by omega]

end eval

section newmap
variable {n : Nat} {G : Hypermap n} {A T : Nat} (hn : n = A + 2*T)
include hn
theorem nd_lt {x : Nat} (hx : x < A+4*T) : nd G A x < A+4*T := by
  rcases dart_cases (A := A) x with h | ⟨h, h0 | h1 | h2 | h3⟩
  · rw [nd_old G (Or.inl h)]
    exact iota_lt A (by rw [← hn]; exact gN_lt G (by rw [hn]; exact sig_lt A hx))
  · rw [nd_old G (Or.inr (Or.inl h0))]
    exact iota_lt A (by rw [← hn]; exact gN_lt G (by rw [hn]; exact sig_lt A hx))
  · rw [nd_r1 G h h1]; omega
  · rw [nd_old G (Or.inr (Or.inr h2))]
    exact iota_lt A (by rw [← hn]; exact gN_lt G (by rw [hn]; exact sig_lt A hx))
  · rw [nd_r3 G h h3]; omega
theorem ndi_lt {x : Nat} (hx : x < A+4*T) : ndi G A x < A+4*T := by
  rcases dart_cases (A := A) x with h | ⟨h, h0 | h1 | h2 | h3⟩
  · rw [ndi_old G (Or.inl h)]
    exact iota_lt A (by rw [← hn]; exact gNi_lt G (by rw [hn]; exact sig_lt A hx))
  · rw [ndi_old G (Or.inr (Or.inl h0))]
    exact iota_lt A (by rw [← hn]; exact gNi_lt G (by rw [hn]; exact sig_lt A hx))
  · rw [ndi_r1 G h h1]; omega
  · rw [ndi_old G (Or.inr (Or.inr h2))]
    exact iota_lt A (by rw [← hn]; exact gNi_lt G (by rw [hn]; exact sig_lt A hx))
  · rw [ndi_r3 G h h3]; omega
theorem nd_ndi {x : Nat} (hx : x < A+4*T) : nd G A (ndi G A x) = x := by
  have old : ∀ x, x < A+4*T → IsOld A x → nd G A (ndi G A x) = x := by
    intro x hx ho
    rw [ndi_old G ho, nd_old G (isOld_iota A _), sig_iota,
      gN_gNi G (by rw [hn]; exact sig_lt A hx), iota_sig A ho]
  rcases dart_cases (A := A) x with h | ⟨h, h0 | h1 | h2 | h3⟩
  · exact old x hx (Or.inl h)
  · exact old x hx (Or.inr (Or.inl h0))
  · rw [ndi_r1 G h h1, nd_r3 G (by omega) (by omega)]; omega
  · exact old x hx (Or.inr (Or.inr h2))
  · rw [ndi_r3 G h h3, nd_r1 G (by omega) (by omega)]; omega
omit hn in
theorem ed_lt' {x : Nat} (hx : x < A + 4 * T) (hA : A % 2 = 0) : ed x < A + 4 * T :=
  ed_lt (by omega) hx

/-- The subdivided hypermap. -/
def newMap {N : Nat} (hN : N = A + 4 * T) (hA : A % 2 = 0) : Hypermap N where
  edge d := ⟨ed d.val, by
    have := ed_lt' (T := T) (x := d.val) (by have := d.isLt; omega) hA; omega⟩
  node d := ⟨nd G A d.val, by
    have := nd_lt (G := G) hn (x := d.val) (by have := d.isLt; omega); omega⟩
  face d := ⟨fc G A d.val, by
    have := ndi_lt (G := G) hn (x := ed d.val) (ed_lt' (T := T) (x := d.val) (by have := d.isLt; omega) hA)
    unfold fc; omega⟩
  edgeK x := by
    apply Fin.ext
    simp only [fc, ed_ed]
    exact nd_ndi (G := G) hn (x := x.val) (by have := x.isLt; omega)

end newmap

section count
variable {E0 E1 : Nat} (G : Hypermap (2 * E0)) {A T : Nat} (hn : 2 * E0 = A + 2 * T)
  (hN : 2 * E1 = A + 4 * T) (hA : A % 2 = 0)
  (hedge : ∀ d, (G.edge d).val = cond (Nat.beq (d.val % 2) 0) (d.val + 1) (d.val - 1))
abbrev G' := newMap (G := G) hn hN hA
noncomputable def nodeLabel (A : Nat) (x : Nat) : Nat × Nat :=
  if IsOld A x then (0, cminN G (sig A x)) else (1, (x-A)/4)
include hn hN hA
theorem graphEdge_new : IsGraphEdge (G' G hn hN hA).edge := by
  intro d
  show ed d.val = _
  unfold ed
  rcases Nat.mod_two_eq_zero_or_one d.val with h | h <;> simp [h]

theorem nodeLabel_old {x : Nat} (hx : x < 2 * E1) (ho : IsOld A x) :
    nodeLabel G A (nd G A x) = nodeLabel G A x := by
  rw [nd_old G ho]
  unfold nodeLabel
  rw [ite_eq_left (isOld_iota A _), ite_eq_left ho, sig_iota,
    cminN_step G (by rw [hn]; exact sig_lt A (by omega))]

theorem nodeLabel_step (x : Fin (2 * E1)) :
    nodeLabel G A ((G' G hn hN hA).node x).val = nodeLabel G A x.val := by
  show nodeLabel G A (nd G A x.val) = _
  have hx := x.isLt
  rcases dart_cases (A := A) x.val with h | ⟨h, h0 | h1 | h2 | h3⟩
  · exact nodeLabel_old G hn hN hA hx (Or.inl h)
  · exact nodeLabel_old G hn hN hA hx (Or.inr (Or.inl h0))
  · rw [nd_r1 G h h1]; unfold nodeLabel
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    congr 1; omega
  · exact nodeLabel_old G hn hN hA hx (Or.inr (Or.inr h2))
  · rw [nd_r3 G h h3]; unfold nodeLabel
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    congr 1; omega

theorem nodes_ge : cycleCount G.node + T ≤ cycleCount (G' G hn hN hA).node := by
  let Ls : List (Nat × Nat) :=
    ((List.finRange (2 * E0)).filter (CycleMin G.node)).map (fun y => (0, y.val)) ++
      (List.range T).map (fun u => (1, u))
  have hlen : Ls.length = cycleCount G.node + T := by
    simp only [Ls, List.length_append, List.length_map, List.length_range, cycleCount_eq,
      List.countP_eq_length_filter]
  have hnd : Ls.Nodup := by
    simp only [Ls]
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · apply nodup_map_of_injOn' _ (List.Pairwise.filter _ (List.nodup_finRange _))
      intro a _ b _ hab
      exact Fin.ext (by simpa using hab)
    · apply nodup_map_of_injOn' _ List.nodup_range
      intro a _ b _ hab; simpa using hab
    · intro a ha b hb hab
      simp only [List.mem_map] at ha hb
      obtain ⟨u, _, rfl⟩ := ha
      obtain ⟨u', _, rfl⟩ := hb
      simp at hab
  have hatt : ∀ l ∈ Ls, ∃ x : Fin (2 * E1), nodeLabel G A x.val = l := by
    intro l hl
    simp only [Ls, List.mem_append, List.mem_map, List.mem_filter, List.mem_range] at hl
    rcases hl with ⟨y, ⟨_, hy⟩, rfl⟩ | ⟨u, hu, rfl⟩
    · refine ⟨⟨iota A y.val, by have := iota_lt A (T := T) (y := y.val) (by omega); omega⟩, ?_⟩
      unfold nodeLabel
      rw [ite_eq_left (isOld_iota A _), sig_iota]
      unfold cminN
      rw [dite_eq_left y.isLt]
      simp only [Fin.eta]
      rw [(cmin_eq_iff (hm_node_inj G) y).mpr hy]
    · refine ⟨⟨A + 4 * u + 1, by omega⟩, ?_⟩
      show nodeLabel G A (A + 4 * u + 1) = _
      unfold nodeLabel
      rw [ite_eq_right (by omega)]
      congr 1; omega
  have := cycleCount_ge_labels (G' G hn hN hA).node (fun x => nodeLabel G A x.val)
    (nodeLabel_step G hn hN hA) Ls hnd hatt
  omega
end count
section faces
variable {E0 : Nat} (G : Hypermap (2 * E0)) {A T : Nat} (hn : 2 * E0 = A + 2 * T) (hA : A % 2 = 0)
  (hedge : ∀ d, (G.edge d).val = cond (Nat.beq (d.val % 2) 0) (d.val + 1) (d.val - 1))
include hn hA hedge
theorem fc_low {x : Nat} (hx : x < A) : fc G A x = iota A (gF G x) := by
  unfold fc
  have he : ed x < A := by unfold ed; split <;> omega
  rw [ndi_old G (Or.inl he), show sig A (ed x) = ed x by unfold sig; rw [ite_eq_left he],
    gNi_ed hedge (by omega) (by omega)]

omit hedge in
theorem fc_r0 (u : Nat) : fc G A (A + 4 * u) = A + 4 * u + 3 := by
  unfold fc
  rw [show ed (A + 4 * u) = A + 4 * u + 1 by unfold ed; rw [ite_eq_left (by omega)],
    ndi_r1 G (by omega) (by omega)]

theorem fc_r1 {u : Nat} (hu : u < T) : fc G A (A + 4 * u + 1) = iota A (gF G (A + 2 * u + 1)) := by
  unfold fc
  rw [show ed (A + 4 * u + 1) = A + 4 * u by unfold ed; rw [ite_eq_right (by omega)]; omega,
    ndi_old G (Or.inr (Or.inl (by omega))),
    show sig A (A + 4 * u) = ed (A + 2 * u + 1) by
      unfold sig ed
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      omega,
    gNi_ed hedge (by omega) (by omega)]

omit hedge in
theorem fc_r2 (u : Nat) : fc G A (A + 4 * u + 2) = A + 4 * u + 1 := by
  unfold fc
  rw [show ed (A + 4 * u + 2) = A + 4 * u + 3 by unfold ed; rw [ite_eq_left (by omega)],
    ndi_r3 G (by omega) (by omega)]
  omega

theorem fc_r3 {u : Nat} (hu : u < T) : fc G A (A + 4 * u + 3) = iota A (gF G (A + 2 * u)) := by
  unfold fc
  rw [show ed (A + 4 * u + 3) = A + 4 * u + 2 by unfold ed; rw [ite_eq_right (by omega)]; omega,
    ndi_old G (Or.inr (Or.inr (by omega))),
    show sig A (A + 4 * u + 2) = ed (A + 2 * u) by
      unfold sig ed
      rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
      omega,
    gNi_ed hedge (by omega) (by omega)]

omit hn hA hedge in
theorem tau_old {x : Nat} (h : IsOld A x) : tau A x = sig A x := by
  unfold tau; rw [ite_eq_left h]

omit hn hA hedge in
theorem tau_new {u r : Nat} (hr : r = 1) :
    tau A (A + 4*u+r) = A+2*u+1 := by
  unfold tau
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  omega
omit hn hA hedge in
theorem tau_r3 (u : Nat) : tau A (A + 4 * u + 3) = A + 2 * u := by
  unfold tau
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  omega

omit hn hA hedge in
theorem tau_r0 (u : Nat) : tau A (A + 4 * u) = A + 2 * u := by
  rw [tau_old (Or.inr (Or.inl (by omega)))]
  unfold sig
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  omega

omit hn hA hedge in
theorem tau_r2 (u : Nat) : tau A (A + 4 * u + 2) = A + 2 * u + 1 := by
  rw [tau_old (Or.inr (Or.inr (by omega)))]
  unfold sig
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  omega

omit hn hA hedge in
theorem tau_iota (y : Nat) : tau A (iota A y) = y := by
  rw [tau_old (isOld_iota A y), sig_iota]

theorem tau_fc {x : Nat} (hx : x < A + 4 * T) :
    tau A (fc G A x) = gF G (tau A x) ∨ tau A (fc G A x) = tau A x := by
  rcases dart_cases (A := A) x with h | ⟨h, h0 | h1 | h2 | h3⟩
  · left
    rw [fc_low G hn hA hedge h, tau_iota, tau_old (Or.inl h)]
    unfold sig; rw [ite_eq_left h]
  all_goals
    obtain ⟨u, r, rfl, hu, hr⟩ : ∃ u r, x = A + 4*u+r ∧ u < T ∧ r < 4 :=
      ⟨(x-A)/4, (x-A)%4, by omega, by omega, by omega⟩
  · right
    rw [show A+4*u+r = A+4*u by omega, fc_r0 G hn hA, tau_r3, tau_r0]
  · left
    rw [show A+4*u+r = A+4*u+1 by omega, fc_r1 G hn hA hedge hu, tau_iota,
      tau_new (by omega)]
  · right
    rw [show A+4*u+r = A+4*u+2 by omega, fc_r2 G hn hA, tau_new (by omega), tau_r2]
  · left
    rw [show A+4*u+r = A+4*u+3 by omega, fc_r3 G hn hA hedge hu, tau_iota, tau_r3]
omit hn hA hedge in
theorem tau_lt {x : Nat} (hx : x < A + 4 * T) : tau A x < A + 2 * T := by
  unfold tau
  split
  · exact sig_lt A hx
  · split <;> omega

end faces

/-- An old dart as a new dart. -/
def iotaF {E0 E1 A T : Nat} (hn : 2 * E0 = A + 2 * T) (hN : 2 * E1 = A + 4 * T)
    (y : Fin (2 * E0)) : Fin (2 * E1) :=
  ⟨iota A y.val, by have := iota_lt A (T := T) (y := y.val) (by omega); omega⟩

/-- An old-class dart as an old dart. -/
def sigF {E0 E1 A T : Nat} (hn : 2 * E0 = A + 2 * T) (hN : 2 * E1 = A + 4 * T)
    (x : Fin (2 * E1)) : Fin (2 * E0) :=
  ⟨sig A x.val, by have := sig_lt A (T := T) (x := x.val) (by omega); omega⟩

section planar

variable {E0 E1 : Nat} (G : Hypermap (2 * E0)) {A T : Nat} (hn : 2 * E0 = A + 2 * T)
  (hN : 2 * E1 = A + 4 * T) (hA : A % 2 = 0)
  (hedge : ∀ d, (G.edge d).val = cond (Nat.beq (d.val % 2) 0) (d.val + 1) (d.val - 1))
include hn hN hA hedge

theorem faces_ge : cycleCount G.face ≤ cycleCount (G' G hn hN hA).face := by
  let φ : Fin (2 * E1) → Nat := fun x => cminF G (tau A x.val)
  have hφ : ∀ x, φ ((G' G hn hN hA).face x) = φ x := by
    intro x
    show cminF G (tau A (fc G A x.val)) = cminF G (tau A x.val)
    have hx := x.isLt
    rcases tau_fc G hn hA hedge (x := x.val) (by omega) with h | h
    · rw [h, cminF_step G (by rw [hn]; exact tau_lt (by omega))]
    · rw [h]
  let Ls : List Nat := ((List.finRange (2 * E0)).filter (CycleMin G.face)).map Fin.val
  have hnd : Ls.Nodup := by
    apply nodup_map_of_injOn' _ (List.Pairwise.filter _ (List.nodup_finRange _))
    intro a _ b _ hab
    exact Fin.ext hab
  have hatt : ∀ l ∈ Ls, ∃ x, φ x = l := by
    intro l hl
    simp only [Ls, List.mem_map, List.mem_filter] at hl
    obtain ⟨y, ⟨_, hy⟩, rfl⟩ := hl
    refine ⟨⟨iota A y.val, by have := iota_lt A (T := T) (y := y.val) (by omega); omega⟩, ?_⟩
    show cminF G (tau A (iota A y.val)) = y.val
    rw [tau_iota]
    unfold cminF
    rw [dite_eq_left y.isLt]
    simp only [Fin.eta]
    rw [(cmin_eq_iff (hm_face_inj G) y).mpr hy]
  have := cycleCount_ge_labels _ φ hφ Ls hnd hatt
  have hl : Ls.length = cycleCount G.face := by
    simp only [Ls, List.length_map, cycleCount_eq, List.countP_eq_length_filter]
  omega

omit hn hN hA hedge in
theorem iota_r (u : Nat) (s : Nat) (hs : s < 2) : iota A (A + 2 * u + s) = A + 4 * u + 2 * s := by
  unfold iota
  rw [ite_eq_right (by omega)]
  have h1 : (A + 2 * u + s - A) / 2 = u := by omega
  have h2 : (A + 2 * u + s - A) % 2 = s := by omega
  rw [h1, h2]

theorem step_transfer {w z : Fin (2 * E0)} (hs : Linked.Step G w z) :
    ∃ k, (G' G hn hN hA).linked k (iotaF hn hN w) (iotaF hn hN z) = true := by
  have hw := w.isLt
  have hz := z.isLt
  have stepE : ∀ a b : Fin (2 * E1), ed a.val = b.val →
      ∃ k, (G' G hn hN hA).linked k a b = true := fun a b h => lk_of_step (Or.inl (Fin.ext h))
  have stepN : ∀ a b : Fin (2 * E1), nd G A a.val = b.val →
      ∃ k, (G' G hn hN hA).linked k a b = true :=
    fun a b h => lk_of_step (Or.inr (Or.inl (Fin.ext h)))
  have stepF : ∀ a b : Fin (2 * E1), fc G A a.val = b.val →
      ∃ k, (G' G hn hN hA).linked k a b = true :=
    fun a b h => lk_of_step (Or.inr (Or.inr (Fin.ext h)))
  have hiv : ∀ y : Fin (2 * E0), (iotaF hn hN y).val = iota A y.val := fun _ => rfl
  rcases hs with h | h | h
  · have he : z.val = ed w.val := by rw [← h]; exact edge_val hedge w
    rcases Nat.lt_or_ge w.val A with hlt | hge
    · apply stepE
      have : ed w.val < A := by unfold ed; split <;> omega
      rw [hiv, hiv]
      unfold iota
      rw [ite_eq_left hlt, ite_eq_left (by omega), he]
    · obtain ⟨u, s, hws, hu, hs⟩ : ∃ u s, w.val = A + 2*u+s ∧ u < T ∧ s < 2 :=
        ⟨(w.val-A)/2, (w.val-A)%2, by omega, by omega, by omega⟩
      have hiw : (iotaF hn hN w).val = A+4*u+2*s := by rw [hiv, hws, iota_r u s hs]
      rcases Nat.lt_or_ge s 1 with hs0 | hs1
      · have hzs : z.val = A+2*u+1 := by
          rw [he,hws]; unfold ed; rw [ite_eq_left (by omega)]; omega
        have hiz : (iotaF hn hN z).val = A+4*u+2 := by rw [hiv,hzs,iota_r u 1 (by omega)]
        have n1 := nd_r1 G (A := A) (x := A+4*u+1) (by omega) (by omega)
        refine lk_trans (stepE _ ⟨A+4*u+1,by omega⟩ ?_)
          (lk_trans (stepN ⟨A+4*u+1,by omega⟩ ⟨A+4*u+3,by omega⟩ ?_)
          (stepE ⟨A+4*u+3,by omega⟩ _ ?_))
        · rw [hiw]; change ed (A+4*u+2*s) = A+4*u+1
          unfold ed; rw [ite_eq_left (by omega)]; omega
        · show nd G A (A+4*u+1) = A+4*u+3; omega
        · rw [hiz]; show ed (A+4*u+3) = _; unfold ed; rw [ite_eq_right (by omega)]; omega
      · have hzs : z.val = A+2*u := by
          rw [he,hws]; unfold ed; rw [ite_eq_right (by omega)]; omega
        have hiz : (iotaF hn hN z).val = A+4*u := by
          rw [hiv,hzs]; simpa using iota_r (A := A) u 0 (by omega)
        have n3 := nd_r3 G (A := A) (x := A+4*u+3) (by omega) (by omega)
        refine lk_trans (stepE _ ⟨A+4*u+3,by omega⟩ ?_)
          (lk_trans (stepN ⟨A+4*u+3,by omega⟩ ⟨A+4*u+1,by omega⟩ ?_)
          (stepE ⟨A+4*u+1,by omega⟩ _ ?_))
        · rw [hiw]; change ed (A+4*u+2*s) = A+4*u+3
          unfold ed; rw [ite_eq_left (by omega)]; omega
        · show nd G A (A+4*u+3) = A+4*u+1; omega
        · rw [hiz]; show ed (A+4*u+1) = _; unfold ed; rw [ite_eq_right (by omega)]; omega
  · apply stepN
    rw [hiv,hiv,nd_old G (isOld_iota A _),sig_iota,← h]
    unfold gN; rw [dite_eq_left hw]
  · have hf : z.val = gF G w.val := by rw [← h]; unfold gF; rw [dite_eq_left hw]
    rcases Nat.lt_or_ge w.val A with hlt | hge
    · apply stepF
      rw [hiv,hiv,show iota A w.val = w.val by unfold iota; rw [ite_eq_left hlt],
        fc_low G hn hA hedge hlt,hf]
    · obtain ⟨u,s,hws,hu,hs⟩ : ∃ u s, w.val = A+2*u+s ∧ u<T ∧ s<2 :=
        ⟨(w.val-A)/2,(w.val-A)%2,by omega,by omega,by omega⟩
      have hiw : (iotaF hn hN w).val = A+4*u+2*s := by rw [hiv,hws,iota_r u s hs]
      rcases Nat.lt_or_ge s 1 with hs0 | hs1
      · refine lk_trans (stepF _ ⟨A+4*u+3,by omega⟩ ?_) (stepF ⟨A+4*u+3,by omega⟩ _ ?_)
        · rw [hiw,show A+4*u+2*s = A+4*u by omega]; exact fc_r0 G hn hA u
        · show fc G A (A+4*u+3) = iota A z.val
          rw [fc_r3 G hn hA hedge hu,hf,hws,show A+2*u+s = A+2*u by omega]
      · refine lk_trans (stepF _ ⟨A+4*u+1,by omega⟩ ?_) (stepF ⟨A+4*u+1,by omega⟩ _ ?_)
        · rw [hiw,show A+4*u+2*s = A+4*u+2 by omega]; exact fc_r2 G hn hA u
        · show fc G A (A+4*u+1) = iota A z.val
          rw [fc_r1 G hn hA hedge hu,hf,hws,show A+2*u+s = A+2*u+1 by omega]
theorem linked_transfer (k : Nat) (y : Fin (2 * E0)) :
    ∀ z, G.linked k y z = true →
      ∃ k', (G' G hn hN hA).linked k' (iotaF hn hN y)
        (iotaF hn hN z) = true := by
  induction k with
  | zero =>
    intro z hz
    have := (Linked.linked_zero G y z).mp hz
    subst this
    exact ⟨0, Linked.linked_refl _ 0 _⟩
  | succ k ih =>
    intro z hz
    rcases (Linked.linked_succ G k y z).mp hz with h | ⟨w, hw, hs⟩
    · exact ih z h
    · exact lk_trans (ih w hw) (step_transfer G hn hN hA hedge hs)

theorem components_le : (G' G hn hN hA).componentCount ≤ G.componentCount := by
  let R : Fin (2 * E1) → Bool := fun x =>
    decide (IsOld A x.val) && compMin G (sigF hn hN x)
  have h1 := componentCount_le (G' G hn hN hA) R ?roots
  · have h2 : (List.finRange (2 * E1)).countP R ≤ G.componentCount := by
      rw [List.countP_eq_length_filter]
      have hlen := length_le_countP (compMin G)
        (((List.finRange (2 * E1)).filter R).map (sigF hn hN)) ?nd ?all
      · rw [List.length_map] at hlen
        exact hlen
      · apply nodup_map_of_injOn' _ (List.Pairwise.filter _ (List.nodup_finRange _))
        intro a ha b hb hab
        simp only [List.mem_filter, R, Bool.and_eq_true, decide_eq_true_eq] at ha hb
        apply Fin.ext
        have e := congrArg (fun y : Fin (2 * E0) => iota A y.val) hab
        simp only [sigF] at e
        rw [iota_sig A ha.2.1, iota_sig A hb.2.1] at e
        exact e
      · intro y hy
        simp only [List.mem_map, List.mem_filter, R, Bool.and_eq_true] at hy
        obtain ⟨x, ⟨_, _, hx⟩, rfl⟩ := hy
        exact hx
    omega
  · intro x hx
    have hxl := x.isLt
    by_cases ho : IsOld A x.val
    · have hc : compMin G (sigF hn hN x) = false := by
        simp only [R, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hx
        rcases hx with hx | hx
        · exact absurd ho hx
        · exact hx
      obtain ⟨z, hz, hlk⟩ := compMin_false hc
      obtain ⟨k, hk⟩ := linked_transfer G hn hN hA hedge _ _ z hlk
      have hx' : iotaF hn hN (sigF hn hN x) = x :=
        Fin.ext (iota_sig A ho)
      rw [hx'] at hk
      refine ⟨iotaF hn hN z, ?_, k, hk⟩
      show iota A z.val < x.val
      have := iota_mono A hz
      simp only [sigF] at this
      rw [iota_sig A ho] at this
      exact this
    · refine ⟨⟨x.val-1,by omega⟩,by show x.val-1<x.val; omega,?_⟩
      exact lk_of_step (Or.inl (Fin.ext (by
        show ed x.val = x.val-1
        unfold ed
        rw [ite_eq_right (by omega)])))
/-- **The subdivided hypermap is planar** when the old one is. -/
theorem newMap_planar (hP : G.Planar) : (G' G hn hN hA).Planar := by
  rw [planar_iff] at hP
  unfold Hypermap.eulerRhs at hP
  have hE := cycleCount_graphEdge_le (E := E0) (edge := G.edge) hedge
  have hE' := cycleCount_graphEdge_ge (E := E1) (edge := (G' G hn hN hA).edge)
    (graphEdge_new G hn hN hA)
  have hV := nodes_ge G hn hN hA
  have hF := faces_ge G hn hN hA hedge
  have hC := components_le G hn hN hA hedge
  apply planar_of_bounds _ E1 (cycleCount G.node + T) (cycleCount G.face) G.componentCount
    hE' hV hF hC
  omega

end planar

/-- Replace each selected edge `(p,q)` by `(p,c u)` and `(q,c u)`. -/
def splitEdges {V : Type} (ts : List (V × V)) (c : Nat → V) : List (V × V) :=
  ts.zipIdx.flatMap fun p => [(p.1.1,c p.2),(p.1.2,c p.2)]
theorem flatMap_two_length {α β : Type} (L : List α) (g : α → List β)
    (hg : ∀ a, (g a).length = 2) : (L.flatMap g).length = 2 * L.length := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.flatMap_cons, List.length_append, hg, ih, List.length_cons]
    omega

theorem getElem?_flatMap_two {α β : Type} (L : List α) (g : α → List β)
    (hg : ∀ a, (g a).length = 2) :
    ∀ u i, (hu : u < L.length) → i < 2 → (L.flatMap g)[2 * u + i]? = (g L[u])[i]? := by
  induction L with
  | nil => intro u i hu; simp at hu
  | cons a L ih =>
    intro u i hu hi
    cases u with
    | zero =>
      simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getElem?_append_left (by rw [hg]; omega)]
    | succ u =>
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [List.getElem?_append_right (by rw [hg]; omega), hg,
        show 2 * (u + 1) + i - 2 = 2 * u + i by omega]
      exact ih u i (by simp at hu; omega) hi

theorem splitEdges_length {V : Type} (ts : List (V × V)) (c : Nat → V) :
    (splitEdges ts c).length = 2 * ts.length := by
  unfold splitEdges
  rw [flatMap_two_length _ _ (fun _ => rfl), List.length_zipIdx]

theorem splitEdges_get {V : Type} (ts : List (V × V)) (c : Nat → V) {u i : Nat}
    (hu : u < ts.length) (hi : i < 2) :
    (splitEdges ts c)[2 * u + i]? =
      [(ts[u].1, c u), (ts[u].2, c u)][i]? := by
  unfold splitEdges
  rw [getElem?_flatMap_two _ _ (fun _ => rfl) u i (by simpa using hu) hi]
  simp

section final
variable {V : Type} {es ts : List (V × V)} {c : Nat → V}
theorem end_split {u r : Nat} (hu : u < ts.length) (hr : r < 4) :
    halfEdgeEnd (es ++ splitEdges ts c) (2*es.length+4*u+r) =
      ([(ts[u].1,c u),(ts[u].2,c u)][r/2]?).map
        (fun e => cond (Nat.beq (r%2) 0) e.1 e.2) := by
  rw [halfEdgeEnd_append_right _ _ _ (by omega),
    show 2*es.length+4*u+r-2*es.length = 4*u+r by omega]
  unfold halfEdgeEnd
  rw [show (4*u+r)/2 = 2*u+r/2 by omega, splitEdges_get ts c hu (by omega),
    show (4*u+r)%2 = r%2 by omega]
theorem end_c {u r : Nat} (hu : u < ts.length) (hr : r = 1 ∨ r = 3) :
    halfEdgeEnd (es ++ splitEdges ts c) (2*es.length+4*u+r) = some (c u) := by
  rw [end_split hu (by omega)]
  rcases hr with rfl | rfl <;> rfl
theorem end_old {x : Nat} (hx : x < 2 * es.length + 4 * ts.length)
    (ho : IsOld (2 * es.length) x) :
    halfEdgeEnd (es ++ splitEdges ts c) x = halfEdgeEnd (es ++ ts) (sig (2 * es.length) x) := by
  rcases Nat.lt_or_ge x (2 * es.length) with h | h
  · rw [halfEdgeEnd_append_left _ _ _ h, show sig (2 * es.length) x = x by
      unfold sig; rw [ite_eq_left h], halfEdgeEnd_append_left _ _ _ h]
  · obtain ⟨u, r, rfl, hu, hr⟩ : ∃ u r, x = 2 * es.length + 4 * u + r ∧ u < ts.length ∧
        (r = 0 ∨ r = 2) :=
      ⟨(x - 2 * es.length) / 4, (x - 2 * es.length) % 4, by omega, by omega, by omega⟩
    rw [end_split hu (by omega), sig_new hr,
      halfEdgeEnd_append_right _ _ _ (by split <;> omega)]
    unfold halfEdgeEnd
    rcases hr with rfl | rfl
    · simp only [Nat.zero_div, Nat.zero_mod]
      rw [show 2 * es.length + 2 * u + (if (0 : Nat) = 2 then 1 else 0) - 2 * es.length = 2 * u by
        simp]
      rw [show 2 * u / 2 = u by omega, show 2 * u % 2 = 0 by omega,
        List.getElem?_eq_getElem hu]
      rfl
    · rw [show 2 * es.length + 2 * u + (if (2 : Nat) = 2 then 1 else 0) - 2 * es.length =
        2 * u + 1 by simp only [ite_true]; omega]
      rw [show (2 * u + 1) / 2 = u by omega, show (2 * u + 1) % 2 = 1 by omega,
        List.getElem?_eq_getElem hu]
      rfl

end final

/-! ## Node cycles of the subdivided hypermap -/

theorem iterate_node_val {E0 E1 A T : Nat} (G : Hypermap (2 * E0)) (hn : 2 * E0 = A + 2 * T)
    (hN : 2 * E1 = A + 4 * T) (hA : A % 2 = 0) (k : Nat) (d : Fin (2 * E1)) :
    (iterate (G' G hn hN hA).node k d).val = iterate (nd G A) k d.val := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih => simp only [iterate]; rw [ih]; rfl

theorem iterate_nd_old {n A T : Nat} (G : Hypermap n) (hn : n = A + 2 * T) (k : Nat) :
    ∀ x, x < A + 4 * T → IsOld A x →
      iterate (nd G A) k x = iota A (iterate (gN G) k (sig A x)) := by
  induction k with
  | zero => intro x _ ho; exact (iota_sig A ho).symm
  | succ k ih =>
    intro x hx ho
    simp only [iterate]
    rw [ih _ (nd_lt hn hx) (by rw [nd_old G ho]; exact isOld_iota A _), nd_old G ho, sig_iota]

theorem reach_c {n A : Nat} (G : Hypermap n) {u r r' : Nat} (hr : r = 1 ∨ r = 3)
    (hr' : r' = 1 ∨ r' = 3) : ∃ k, iterate (nd G A) k (A+4*u+r) = A+4*u+r' := by
  have s1 := nd_r1 G (A := A) (x := A+4*u+1) (by omega) (by omega)
  have s3 := nd_r3 G (A := A) (x := A+4*u+3) (by omega) (by omega)
  have e1 : nd G A (A+4*u+1) = A+4*u+3 := by omega
  have e3 : nd G A (A+4*u+3) = A+4*u+1 := by omega
  rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,by simp only [iterate]; rw [e1]⟩
  · exact ⟨1,by simp only [iterate]; rw [e3]⟩
  · exact ⟨0,rfl⟩

/-- Subdivision by distinct fresh internal vertices preserves registered planarity.
The edge list may contain loops, parallel edges, or multiple components. -/
theorem planar_subdivide {V : Type} (es ts : List (V × V)) (c : Nat → V)
    (hc : ∀ u, u < ts.length → ∀ u', u' < ts.length → c u = c u' → u = u')
    (hfresh : ∀ e ∈ es ++ ts, ∀ u, u < ts.length → e.1 ≠ c u ∧ e.2 ≠ c u)
    (h : PlanarGraph (es ++ ts)) : PlanarGraph (es ++ splitEdges ts c) := by
  obtain ⟨G,hedge,hnode,hP⟩ := h
  have hn : 2*(es++ts).length = 2*es.length+2*ts.length := by
    simp only [List.length_append]; omega
  have hN : 2*(es++splitEdges ts c).length = 2*es.length+4*ts.length := by
    simp only [List.length_append,splitEdges_length]; omega
  have hA : (2*es.length)%2 = 0 := by omega
  refine ⟨G' G hn hN hA,graphEdge_new G hn hN hA,?_,newMap_planar G hn hN hA hedge hP⟩
  have endOld : ∀ x, x < 2*es.length+4*ts.length → IsOld (2*es.length) x →
      halfEdgeEnd (es++splitEdges ts c) x = halfEdgeEnd (es++ts) (sig (2*es.length) x) :=
    fun x hx ho => end_old hx ho
  have nodeEnd : ∀ y : Fin (2*(es++ts).length),
      halfEdgeEnd (es++ts) (gN G y.val) = halfEdgeEnd (es++ts) y.val := by
    intro y
    have := (hnode y (G.node y)).mp ⟨1,rfl⟩
    unfold gN; rw [dite_eq_left y.isLt]
    exact this.symm
  have inv : ∀ x, x < 2*es.length+4*ts.length →
      halfEdgeEnd (es++splitEdges ts c) (nd G (2*es.length) x) =
        halfEdgeEnd (es++splitEdges ts c) x := by
    intro x hx
    by_cases ho : IsOld (2*es.length) x
    · rw [nd_old G ho, endOld _ (by have := nd_lt (G := G) hn hx; rw [nd_old G ho] at this; exact this)
        (isOld_iota _ _),sig_iota,endOld x hx ho]
      have hs := sig_lt (2*es.length) hx
      exact nodeEnd ⟨sig (2*es.length) x,by omega⟩
    · obtain ⟨u,r,rfl,hu,hr⟩ : ∃ u r, x = 2*es.length+4*u+r ∧ u<ts.length ∧ (r=1 ∨ r=3) :=
        ⟨(x-2*es.length)/4,(x-2*es.length)%4,by omega,by omega,by omega⟩
      rcases hr with rfl | rfl
      · rw [nd_r1 G (by omega) (by omega),show 2*es.length+4*u+1+2 = 2*es.length+4*u+3 by omega,
          end_c hu (by omega),end_c hu (by omega)]
      · rw [nd_r3 G (by omega) (by omega),show 2*es.length+4*u+3-2 = 2*es.length+4*u+1 by omega,
          end_c hu (by omega),end_c hu (by omega)]
  intro d d'
  have hd : d.val < 2*es.length+4*ts.length := by have := d.isLt; omega
  have hd' : d'.val < 2*es.length+4*ts.length := by have := d'.isLt; omega
  constructor
  · rintro ⟨k,rfl⟩
    rw [iterate_node_val]
    have invk : ∀ k x, x < 2*es.length+4*ts.length →
        halfEdgeEnd (es++splitEdges ts c) (iterate (nd G (2*es.length)) k x) =
          halfEdgeEnd (es++splitEdges ts c) x := by
      intro k
      induction k with
      | zero => intro x _; rfl
      | succ k ih =>
        intro x hx
        simp only [iterate]
        rw [ih _ (nd_lt (G := G) hn hx), inv x hx]
    exact (invk k d.val hd).symm
  · intro he
    have classify : ∀ x, x < 2*es.length+4*ts.length →
        IsOld (2*es.length) x ∨
        (∃ u, u<ts.length ∧ ∃ r, (r=1 ∨ r=3) ∧ x=2*es.length+4*u+r) := by
      intro x hx
      by_cases ho : IsOld (2*es.length) x
      · exact Or.inl ho
      · exact Or.inr ⟨(x-2*es.length)/4,by omega,(x-2*es.length)%4,by omega,by omega⟩
    have oldEnd : ∀ x, x < 2*es.length+4*ts.length → IsOld (2*es.length) x →
        ∀ v, halfEdgeEnd (es++splitEdges ts c) x = some v → ∀ u, u<ts.length → v ≠ c u := by
      intro x hx ho v hv u hu
      rw [endOld x hx ho] at hv
      obtain ⟨e,he,hve⟩ := halfEdgeEnd_mem hv
      rcases hve with rfl | rfl
      · exact (hfresh e he u hu).1
      · exact (hfresh e he u hu).2
    have toFin : ∀ k, iterate (nd G (2*es.length)) k d.val = d'.val →
        ∃ k, iterate (G' G hn hN hA).node k d = d' :=
      fun k hk => ⟨k,Fin.ext (by rw [iterate_node_val]; exact hk)⟩
    rcases classify d.val hd with ho | ⟨u,hu,r,hr,hdr⟩ <;>
      rcases classify d'.val hd' with ho' | ⟨u',hu',r',hr',hdr'⟩
    · rw [endOld _ hd ho,endOld _ hd' ho'] at he
      have hs := sig_lt (2*es.length) hd
      have hs' := sig_lt (2*es.length) hd'
      obtain ⟨k,hk⟩ := (hnode ⟨sig (2*es.length) d.val,by omega⟩
        ⟨sig (2*es.length) d'.val,by omega⟩).mpr he
      apply toFin k
      rw [iterate_nd_old G hn k _ hd ho]
      have := congrArg Fin.val hk
      rw [iterate_gN_val] at this
      have e : iterate (gN G) k (sig (2*es.length) d.val) = sig (2*es.length) d'.val := this
      rw [e,iota_sig _ ho']
    · rw [hdr',end_c hu' hr'] at he
      exact absurd rfl (oldEnd _ hd ho _ he u' hu')
    · rw [hdr,end_c hu hr] at he
      exact absurd rfl (oldEnd _ hd' ho' _ he.symm u hu)
    · rw [hdr,end_c hu hr,hdr',end_c hu' hr'] at he
      have := hc u hu u' hu' (Option.some.inj he)
      subst this
      obtain ⟨k,hk⟩ := reach_c G (A := 2*es.length) (u := u) hr hr'
      exact toFin k (by rw [hdr,hk,hdr'])

section faceOrbits
variable {E0 E1 : Nat} (G : Hypermap (2 * E0)) {A T : Nat}
  (hn : 2*E0 = A+2*T) (hN : 2*E1 = A+4*T) (hA : A%2 = 0)
  (hedge : ∀ d, (G.edge d).val = cond (Nat.beq (d.val%2) 0) (d.val+1) (d.val-1))

theorem iterate_face_val (k : Nat) (d : Fin (2*E1)) :
    (iterate (G' G hn hN hA).face k d).val = iterate (fc G A) k d.val := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih => simp only [iterate]; rw [ih]; rfl

include hedge

/-- An original face step becomes either one or two steps after subdivision. -/
theorem face_step_transfer (y : Fin (2*E0)) :
    ∃ k, 1 ≤ k ∧ k ≤ 2 ∧
      iterate (G' G hn hN hA).face k (iotaF hn hN y) = iotaF hn hN (G.face y) := by
  have hy := y.isLt
  have hf : (G.face y).val = gF G y.val := by unfold gF; rw [dite_eq_left hy]
  have hiv : ∀ x : Fin (2*E0), (iotaF hn hN x).val = iota A x.val := fun _ => rfl
  rcases Nat.lt_or_ge y.val A with hlt | hge
  · refine ⟨1,by omega,by omega,Fin.ext ?_⟩
    rw [iterate_face_val,hiv,hiv,hf]
    change fc G A (iota A y.val) = _
    rw [show iota A y.val = y.val by unfold iota; rw [ite_eq_left hlt],fc_low G hn hA hedge hlt]
  · obtain ⟨u,s,hys,hu,hs⟩ : ∃ u s, y.val = A+2*u+s ∧ u<T ∧ s<2 :=
      ⟨(y.val-A)/2,(y.val-A)%2,by omega,by omega,by omega⟩
    refine ⟨2,by omega,by omega,Fin.ext ?_⟩
    rw [iterate_face_val,hiv,hiv,hf,hys,iota_r u s hs]
    change fc G A (fc G A (A+4*u+2*s)) = iota A (gF G (A+2*u+s))
    rcases Nat.lt_or_ge s 1 with hs0 | hs1
    · have hs : s = 0 := by omega
      subst s
      simp only [Nat.mul_zero,Nat.add_zero]
      rw [fc_r0 G hn hA,fc_r3 G hn hA hedge hu]
    · have hs : s = 1 := by omega
      subst s
      simp only [Nat.mul_one]
      rw [fc_r2 G hn hA,fc_r1 G hn hA hedge hu]

/-- Subdivision preserves every original face orbit, with at most twice as many
steps. In particular, designated attachment darts remain on their common face. -/
theorem face_orbit_transfer (k : Nat) (y : Fin (2*E0)) :
    ∃ k', k ≤ k' ∧ k' ≤ 2*k ∧
      iterate (G' G hn hN hA).face k' (iotaF hn hN y) =
        iotaF hn hN (iterate G.face k y) := by
  induction k generalizing y with
  | zero => exact ⟨0,by omega,by omega,rfl⟩
  | succ k ih =>
    obtain ⟨s,hs1,hs2,hs⟩ := face_step_transfer G hn hN hA hedge y
    obtain ⟨t,ht1,ht2,ht⟩ := ih (G.face y)
    refine ⟨s+t,by omega,by omega,?_⟩
    rw [iterate_add,hs,ht]
    rfl
end faceOrbits

end STACS2027.PlanarOperations.Subdivision
