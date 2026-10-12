module

public import NPHardness.PlanarAssemblyOccurrencePorts
public import NPHardness.PlanarAssemblyRouting

/-! Construct the global matching from the actual injected source darts.
Unselected darts are fixed. Every marked dart has exactly the source edge
partner prescribed by the occurrence incidence list. -/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.SAT Complexity.Planar PlanarGluing

namespace SelectedPairing
variable {n m : Nat} (port : Fin m → Fin n)

noncomputable def marked (d : Fin n) : Bool := by
  classical
  exact decide (∃ i, port i=d)

noncomputable def pair (partner : Fin m → Fin m) (d : Fin n) : Fin n := by
  classical
  exact if h : ∃ i, port i=d then port (partner (Classical.choose h)) else d

theorem marked_iff (d : Fin n) : marked port d=true ↔ ∃ i, port i=d := by
  classical
  simp only [marked,decide_eq_true_eq]

theorem pair_port (hinj : ∀ i j, port i=port j → i=j)
    (partner : Fin m → Fin m) (i : Fin m) : pair port partner (port i)=port (partner i) := by
  classical
  have hi : ∃ j, port j=port i := ⟨i,rfl⟩
  simp only [pair,dite_eq_left hi]
  rw [hinj _ _ (Classical.choose_spec hi)]

theorem pair_unmarked (partner : Fin m → Fin m) (d : Fin n)
    (hd : marked port d=false) : pair port partner d=d := by
  classical
  have hn : ¬∃ i, port i=d := by
    intro hi
    have hm := (marked_iff port d).mpr hi
    rw [hd] at hm
    contradiction
  simp only [pair,dite_eq_right hn]

/-- Separation of the selected port darts is the only geometric input to the
matching constructor; its source involution and all fibers are explicit. -/
noncomputable def toPortPairing (G : Hypermap n)
    (hinj : ∀ i j, port i=port j → i=j)
    (partner : Fin m → Fin m) (hpartner : ∀ i, partner (partner i)=i)
    (hne : ∀ i, partner i≠i)
    (hsep : ∀ i j, G.face (port i)≠port j) : PortPairing G where
  marked := marked port
  pair := pair port partner
  pair_pair d := by
    cases hm : marked port d with
    | false => rw [pair_unmarked port partner d hm,pair_unmarked port partner d hm]
    | true =>
      obtain ⟨i,rfl⟩ := (marked_iff port d).mp hm
      rw [pair_port port hinj,pair_port port hinj,hpartner]
  pair_marked d := by
    cases hm : marked port d with
    | false => rw [pair_unmarked port partner d hm]; exact hm
    | true =>
      obtain ⟨i,rfl⟩ := (marked_iff port d).mp hm
      rw [pair_port port hinj]
      exact (marked_iff port _).mpr ⟨partner i,rfl⟩
  pair_ne d hd := by
    obtain ⟨i,rfl⟩ := (marked_iff port d).mp hd
    rw [pair_port port hinj]
    intro he
    exact hne i (hinj _ _ he)
  face_separated d hd := by
    obtain ⟨i,rfl⟩ := (marked_iff port d).mp hd
    cases hm : marked port (G.face (port i)) with
    | false => rfl
    | true =>
      obtain ⟨j,hj⟩ := (marked_iff port _).mp hm
      exact False.elim (hsep i j hj.symm)

end SelectedPairing

theorem graphEdge_ne {E : Nat} (d : Fin (2*E)) : graphEdge d≠d := by
  intro h
  have hv := congrArg Fin.val h
  change ed d.val=d.val at hv
  rcases Nat.mod_two_eq_zero_or_one d.val with hm | hm <;> simp [ed,hm] at hv <;> omega

/-- The actual global occurrence matching, before its node and face surgery. -/
noncomputable def LocalPortChoices.pairing {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f)
    (G : Hypermap (2*(ungluedFormulaPieces k f).flatten.length))
    (hsep : ∀ i j, G.face (C.sourcePort hf i)≠C.sourcePort hf j) : PortPairing G :=
  SelectedPairing.toPortPairing (C.sourcePort hf) G (C.sourcePort_injective hf)
    graphEdge graphEdge_twice graphEdge_ne hsep

theorem LocalPortChoices.pairing_marked {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f)
    (G : Hypermap (2*(ungluedFormulaPieces k f).flatten.length))
    (hsep : ∀ i j, G.face (C.sourcePort hf i)≠C.sourcePort hf j)
    (d : Fin (2*(ungluedFormulaPieces k f).flatten.length)) :
    (C.pairing hf G hsep).marked d=true ↔ ∃ i, C.sourcePort hf i=d :=
  SelectedPairing.marked_iff _ d

theorem LocalPortChoices.pairing_pair {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f)
    (G : Hypermap (2*(ungluedFormulaPieces k f).flatten.length))
    (hsep : ∀ i j, G.face (C.sourcePort hf i)≠C.sourcePort hf j)
    (i : Fin (2*(placeFormula [] f).flatten.length)) :
    (C.pairing hf G hsep).pair (C.sourcePort hf i)=C.sourcePort hf (graphEdge i) :=
  SelectedPairing.pair_port _ (C.sourcePort_injective hf) _ i

theorem LocalPortChoices.pairing_variable {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f)
    (G : Hypermap (2*(ungluedFormulaPieces k f).flatten.length))
    (hsep : ∀ i j, G.face (C.sourcePort hf i)≠C.sourcePort hf j) (i : OccurrenceIndex f) :
    (C.pairing hf G hsep).pair (C.variableOccurrencePort hf i)=C.clauseOccurrencePort i := by
  have h := C.pairing_pair hf G hsep (occurrenceDart i false)
  simpa only [sourcePort_even,occurrenceDart_graphEdge,Bool.not_false,sourcePort_odd] using h

theorem LocalPortChoices.pairing_clause {k : Nat} {f : CNF}
    (C : LocalPortChoices k f) (hf : BoundedOccurrence f)
    (G : Hypermap (2*(ungluedFormulaPieces k f).flatten.length))
    (hsep : ∀ i j, G.face (C.sourcePort hf i)≠C.sourcePort hf j) (i : OccurrenceIndex f) :
    (C.pairing hf G hsep).pair (C.clauseOccurrencePort i)=C.variableOccurrencePort hf i := by
  have h := C.pairing_pair hf G hsep (occurrenceDart i true)
  simpa only [sourcePort_odd,occurrenceDart_graphEdge,Bool.not_true,sourcePort_even] using h

end STACS2027.PlanarAssembly
