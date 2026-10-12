module

public import NPHardness.GadgetRelabel
public import NPHardness.CPAP

/-! CPAP is independent of the orientation and ordering of its complete,
duplicate-free cycle representative family. -/

@[expose] public section
namespace STACS2027

theorem cost_perm {ps qs : List (List Edge)} (h : ps.Perm qs) : cost ps = cost qs := by
  induction h with
  | nil => rfl
  | cons p h ih => simp only [cost,ih,(h.map (overlap p)).sum_nat]
  | swap p q ps =>
    simp only [cost,List.map_cons,List.sum_cons,overlap_comm q p]
    omega
  | trans h h' ih ih' => exact ih.trans ih'

theorem SameCycle.vertices {g h : Graph} {r s : Nat} {c d : Cycle}
    (he : SameCycle c d) (hc : IsCycle g r c) (hd : IsCycle h s d) :
    ∀ x, x ∈ c ↔ x ∈ d := by
  intro x
  constructor
  · intro hx
    obtain ⟨y,_,hxy⟩ := hc.vertex_incident hx
    exact (cycleEdge_vertices (he.1 _ hxy)).1
  · intro hx
    obtain ⟨y,_,hxy⟩ := hd.vertex_incident hx
    exact (cycleEdge_vertices (he.2 _ hxy)).1

theorem distinctCycles_eq {cs : List Cycle}
    (hn : cs.Pairwise (fun c d => ¬ SameCycle c d))
    {c d : Cycle} (hc : c ∈ cs) (hd : d ∈ cs) (he : SameCycle c d) : c = d := by
  induction cs with
  | nil => simp at hc
  | cons a cs ih =>
    obtain ⟨hh,ht⟩ := List.pairwise_cons.mp hn
    rcases List.mem_cons.mp hc with hca | hct
    · subst c
      rcases List.mem_cons.mp hd with hda | hdt
      · exact hda.symm
      · exact False.elim (hh d hdt he)
    · rcases List.mem_cons.mp hd with hda | hdt
      · subst d
        exact False.elim (hh c hct he.symm)
      · exact ih ht hct hdt

theorem distinctCycles_nodup {cs : List Cycle}
    (hn : cs.Pairwise (fun c d => ¬ SameCycle c d)) : cs.Nodup :=
  hn.imp (fun {c d} h he => by subst d; exact h (SameCycle.refl c))

def FamilyAssignment (cs : List Cycle) (budget : Nat) : Prop :=
  ∃ choose : Cycle → Nat, (∀ c ∈ cs, choose c ∈ c) ∧
    cost (cs.map fun c => selectedAt c (choose c)) ≤ budget

theorem validChoices_vertex_function {cs : List Cycle} {ps : List (List Edge)}
    (hn : cs.Nodup) {g : Graph} (hc : ∀ c ∈ cs, IsCycle g c.length c)
    (hp : ValidChoices (cs.map selectedOptions) ps) :
    ∃ choose : Cycle → Nat, (∀ c ∈ cs, choose c ∈ c) ∧
      PathsPerm ps (cs.map fun c => selectedAt c (choose c)) := by
  induction cs generalizing ps with
  | nil => cases ps with
    | nil => exact ⟨fun _ => 0,by simp,trivial⟩
    | cons _ _ => exact False.elim hp
  | cons c cs ih => cases ps with
    | nil => exact False.elim hp
    | cons p ps =>
      obtain ⟨hcn,hcs⟩ := List.nodup_cons.mp hn
      obtain ⟨v,hv,hpv⟩ := selected_option_has_vertex (hc c (by simp)) hp.1
      obtain ⟨choose,hchoose,hpaths⟩ := ih hcs (fun d hd => hc d (by simp [hd])) hp.2
      let pick := fun d => if d = c then v else choose d
      have hpick : ∀ d ∈ cs, pick d = choose d := by
        intro d hd
        have hne : d ≠ c := fun he => hcn (he ▸ hd)
        simp [pick,hne]
      refine ⟨pick,?_,?_⟩
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · simpa [pick] using hv
        · rw [hpick d hd]; exact hchoose d hd
      · change p.Perm (selectedAt c (pick c)) ∧ PathsPerm ps (cs.map fun d => selectedAt d (pick d))
        refine ⟨by simpa [pick] using hpv,?_⟩
        have hm : (cs.map fun d => selectedAt d (pick d)) = (cs.map fun d => selectedAt d (choose d)) :=
          List.map_congr_left (fun d hd => congrArg (selectedAt d) (hpick d hd))
        rw [hm]
        exact hpaths

theorem hasAssignment_iff_enumerated_family (g : Graph) (k budget : Nat) :
    HasAssignment g k budget ↔ FamilyAssignment (cycles g k) budget := by
  have hv : ∀ c ∈ cycles g k, IsCycle g c.length c := by
    intro c hc
    have h := enumerated_isCycle hc
    simpa only [h.2.1] using h
  constructor
  · rintro ⟨ps,hps,hcost⟩
    obtain ⟨choose,hchoose,hp⟩ := validChoices_vertex_function (cycles_nodup g k) hv hps
    exact ⟨choose,hchoose,by rw [← hp.cost_eq]; exact hcost⟩
  · rintro ⟨choose,hchoose,hcost⟩
    obtain ⟨ps,hps,hp⟩ := vertex_choices_have_options hv choose hchoose
    exact ⟨ps,hps,by rw [hp.cost_eq]; exact hcost⟩

noncomputable def representativeIn (ds : List Cycle) (c : Cycle) : Cycle :=
  if h : ∃ d ∈ ds, SameCycle c d then Classical.choose h else []

theorem representativeIn_spec {ds : List Cycle} {c : Cycle}
    (h : ∃ d ∈ ds, SameCycle c d) :
    representativeIn ds c ∈ ds ∧ SameCycle c (representativeIn ds c) := by
  simpa only [representativeIn,dite_eq_left h] using Classical.choose_spec h

theorem representatives_perm {cs ds : List Cycle}
    (hc : cs.Pairwise (fun c d => ¬ SameCycle c d))
    (hd : ds.Pairwise (fun c d => ¬ SameCycle c d))
    (hcd : ∀ c ∈ cs, ∃ d ∈ ds, SameCycle c d)
    (hdc : ∀ d ∈ ds, ∃ c ∈ cs, SameCycle d c) :
    (cs.map (representativeIn ds)).Perm ds := by
  have hs := fun c hc => representativeIn_spec (hcd c hc)
  have hn : (cs.map (representativeIn ds)).Nodup := by
    rw [List.nodup_iff_pairwise_ne,List.pairwise_map]
    apply hc.imp_of_mem
    intro c d hcm hdm hne he
    exact hne ((hs c hcm).2.trans (he ▸ (hs d hdm).2.symm))
  apply (List.perm_ext_iff_of_nodup hn (distinctCycles_nodup hd)).mpr
  intro d
  constructor
  · intro h
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp h
    exact (hs c hc).1
  · intro h
    obtain ⟨c,hc,he⟩ := hdc d h
    have hr := hs c hc
    exact List.mem_map.mpr ⟨c,hc,(distinctCycles_eq hd h hr.1 (he.trans hr.2)).symm⟩

theorem familyAssignment_transport {cs ds : List Cycle} {g h : Graph}
    (hc : ∀ c ∈ cs, IsCycle g c.length c) (hd : ∀ d ∈ ds, IsCycle h d.length d)
    (hcn : cs.Pairwise (fun c d => ¬ SameCycle c d))
    (hdn : ds.Pairwise (fun c d => ¬ SameCycle c d))
    (hcd : ∀ c ∈ cs, ∃ d ∈ ds, SameCycle c d)
    (hdc : ∀ d ∈ ds, ∃ c ∈ cs, SameCycle d c) {budget : Nat}
    (ha : FamilyAssignment ds budget) : FamilyAssignment cs budget := by
  obtain ⟨choose,hchoose,hcost⟩ := ha
  let pick := fun c => choose (representativeIn ds c)
  have hs := fun c hc => representativeIn_spec (hcd c hc)
  have hsel : ∀ c ∈ cs, (selectedAt c (pick c)).Perm
      (selectedAt (representativeIn ds c) (choose (representativeIn ds c))) := by
    intro c hcm
    exact (hs c hcm).2.selectedAt_perm (hc c hcm) (hd _ (hs c hcm).1) (pick c)
  have heq : cost (cs.map fun c => selectedAt c (pick c)) =
      cost (cs.map fun c => selectedAt (representativeIn ds c) (choose (representativeIn ds c))) := by
    apply cost_map_eq
    apply List.pairwise_of_forall_mem_list
    intro c hcm d hdm
    exact overlap_perm (hsel c hcm) (hsel d hdm)
  have hp := (representatives_perm hcn hdn hcd hdc).map (fun c => selectedAt c (choose c))
  have hperm : cost (cs.map fun c => selectedAt (representativeIn ds c) (choose (representativeIn ds c))) =
      cost (ds.map fun c => selectedAt c (choose c)) := by
    simpa only [List.map_map,Function.comp_def] using cost_perm hp
  refine ⟨pick,?_,by rw [heq,hperm]; exact hcost⟩
  intro c hcm
  exact ((hs c hcm).2.vertices (hc c hcm) (hd _ (hs c hcm).1) (pick c)).mpr (hchoose _ (hs c hcm).1)

theorem hasAssignment_iff_complete_family {g : Graph} {k budget : Nat} {cs : List Cycle}
    (hc : ∀ c ∈ cs, IsCycle g k c)
    (hn : cs.Pairwise (fun c d => ¬ SameCycle c d))
    (hcover : ∀ c, IsCycle g k c → ∃ d ∈ cs, SameCycle c d) :
    HasAssignment g k budget ↔ FamilyAssignment cs budget := by
  rw [hasAssignment_iff_enumerated_family]
  have hcself : ∀ c ∈ cs, IsCycle g c.length c := by
    intro c hcm; have h := hc c hcm; simpa only [h.2.1] using h
  have heself : ∀ c ∈ cycles g k, IsCycle g c.length c := by
    intro c hcm; have h := enumerated_isCycle hcm; simpa only [h.2.1] using h
  exact ⟨familyAssignment_transport hcself heself hn (cycles_pairwise_different g k)
    (fun c hcm => isCycle_represented (hc c hcm)) (fun c hcm => hcover c (enumerated_isCycle hcm)),
    familyAssignment_transport heself hcself (cycles_pairwise_different g k) hn
      (fun c hcm => hcover c (enumerated_isCycle hcm)) (fun c hcm => isCycle_represented (hc c hcm))⟩

end STACS2027
