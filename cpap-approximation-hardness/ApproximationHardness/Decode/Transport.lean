module

public import ApproximationHardness.LReduction
import Lean.Elab.Tactic.Omega

/-!
# From an assignment of the enumerated cycles to the gadget family

A cycle-path assignment `τ` of the Theorem 8 graph is a list `ps` of chosen paths, one for each
enumerated cycle (`cycles (formulaGraph k f) k`). The analysis of Theorem 11 works on the gadget
family `formulaFamily k hk f`, with one omitted vertex per gadget cycle. `decoder_transport`
gives an omitted-vertex choice on the family whose chosen paths are those of `ps` up to the
order of the paths and of their edges: every path statistic invariant under reordering the
edges has the same sum, and the costs agree.
-/

@[expose] public section
namespace STACS2027
open Complexity.SAT

theorem PathsPerm.sum_map {ps qs : List (List Edge)} (h : PathsPerm ps qs) (Φ : List Edge → Nat)
    (hΦ : ∀ p q : List Edge, p.Perm q → Φ p = Φ q) : (ps.map Φ).sum = (qs.map Φ).sum := by
  induction ps generalizing qs with
  | nil => cases qs with
    | nil => rfl
    | cons _ _ => exact False.elim h
  | cons p ps ih => cases qs with
    | nil => exact False.elim h
    | cons q qs =>
      obtain ⟨hpq, hrest⟩ := h
      simp only [List.map_cons, List.sum_cons, hΦ p q hpq, ih hrest]

theorem decoder_transport {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : BoundedOccurrence f)
    (hd : ClauseVariablesDistinct f) {ps : List (List Edge)}
    (hps : ValidChoices ((cycles (formulaGraph k f) k).map selectedOptions) ps) :
    ∃ pick : Cycle → Nat, (∀ c ∈ formulaFamily k hk f, pick c ∈ c) ∧
      cost (chosenFamily (formulaFamily k hk f) pick) = cost ps ∧
      ∀ Φ : List Edge → Nat, (∀ p q : List Edge, p.Perm q → Φ p = Φ q) →
        (ps.map Φ).sum = ((chosenFamily (formulaFamily k hk f) pick).map Φ).sum := by
  classical
  let g := formulaGraph k f
  let ds := cycles g k
  let cs := formulaFamily k hk f
  have hdv : ∀ d ∈ ds, IsCycle g d.length d := by
    intro d hd'
    have h := enumerated_isCycle hd'
    simpa only [h.2.1] using h
  obtain ⟨choose, hchoose, hpp⟩ := validChoices_vertex_function (cycles_nodup g k) hdv hps
  have hc : ∀ c ∈ cs, IsCycle g k c := formulaFamily_valid hk hf
  have hcself : ∀ c ∈ cs, IsCycle g c.length c := by
    intro c hcm; have h := hc c hcm; simpa only [h.2.1] using h
  have hcn := formulaFamily_distinct hk hf hd
  have hdn := cycles_pairwise_different g k
  have hcd : ∀ c ∈ cs, ∃ d ∈ ds, SameCycle c d := fun c hcm => isCycle_represented (hc c hcm)
  have hdc : ∀ d ∈ ds, ∃ c ∈ cs, SameCycle d c := fun d hdm =>
    formulaFamily_complete hk hf hd (enumerated_isCycle hdm)
  let pick := fun c => choose (representativeIn ds c)
  have hs := fun c hc => representativeIn_spec (hcd c hc)
  have hsel : ∀ c ∈ cs, (selectedAt c (pick c)).Perm
      (selectedAt (representativeIn ds c) (choose (representativeIn ds c))) := by
    intro c hcm
    exact (hs c hcm).2.selectedAt_perm (hcself c hcm) (hdv _ (hs c hcm).1) (pick c)
  have hrep := representatives_perm hcn hdn hcd hdc
  refine ⟨pick, ?_, ?_, ?_⟩
  · intro c hcm
    exact ((hs c hcm).2.vertices (hcself c hcm) (hdv _ (hs c hcm).1) (pick c)).mpr (hchoose _ (hs c hcm).1)
  · have heq : cost (cs.map fun c => selectedAt c (pick c)) =
        cost (cs.map fun c => selectedAt (representativeIn ds c) (choose (representativeIn ds c))) := by
      apply cost_map_eq
      apply List.pairwise_of_forall_mem_list
      intro c hcm d hdm
      exact overlap_perm (hsel c hcm) (hsel d hdm)
    have hp := hrep.map (fun c => selectedAt c (choose c))
    have hperm : cost (cs.map fun c => selectedAt (representativeIn ds c) (choose (representativeIn ds c))) =
        cost (ds.map fun c => selectedAt c (choose c)) := by
      simpa only [List.map_map, Function.comp_def] using cost_perm hp
    show cost (cs.map fun c => selectedAt c (pick c)) = cost ps
    rw [heq, hperm, hpp.cost_eq]
  · intro Φ hΦ
    rw [hpp.sum_map Φ hΦ]
    have h1 : ((ds.map fun c => selectedAt c (choose c)).map Φ).sum =
        (((cs.map (representativeIn ds)).map fun c => selectedAt c (choose c)).map Φ).sum :=
      ((hrep.map (fun c => selectedAt c (choose c))).map Φ).sum_nat.symm
    have h2 : (((cs.map (representativeIn ds)).map fun c => selectedAt c (choose c)).map Φ) =
        ((cs.map fun c => selectedAt c (pick c)).map Φ) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro c hcm
      exact (hΦ _ _ (hsel c hcm)).symm
    rw [h1, h2]
    rfl

end STACS2027
