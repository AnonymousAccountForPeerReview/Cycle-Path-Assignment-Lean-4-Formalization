module

public import NPHardness.FamilyCost

/-! Exact port loads for original-vertex choices, and monotone port loads
under normalization of arbitrary choices. -/

@[expose] public section
namespace STACS2027

theorem expandedEdges_unchanged_mem {g : Graph} {ss : List SubdivisionStep}
    (hv : validSubdivision g ss) {as : List Edge} (ha : as ⊆ g)
    {e : Edge} (he : e ∈ g) (hz : expandedEdge ss e = [e]) :
    e ∈ as.flatMap (expandedEdge ss) ↔ e ∈ as := by
  have hee : e ∈ expandedEdge ss e := by rw [hz]; simp
  constructor
  · intro hm
    obtain ⟨d, hd, hed⟩ := List.mem_flatMap.mp hm
    have heq := expandedEdge_unique_parent hv he (ha hd) hee hed
    exact heq ▸ hd
  · intro hm
    exact List.mem_flatMap.mpr ⟨e, hm, hee⟩

theorem expanded_selectedAt_port_mem {g : Graph} {r : Nat} {c d : Cycle}
    {ss : List SubdivisionStep} (hv : validSubdivision g ss) (hc : IsCycle g r c)
    (hp : (cycleEdges d).Perm ((cycleEdges c).flatMap (expandedEdge ss)))
    {e : Edge} (he : e ∈ g) (hz : expandedEdge ss e = [e]) (v : Nat) :
    e ∈ selectedAt d v ↔ e ∈ selectedAt c v := by
  simp only [selectedAt_mem, hp.mem_iff, expandedEdges_unchanged_mem hv hc.2.2.2 he hz]

theorem expanded_selectedAt_port_count {g h : Graph} {r k : Nat} {c d : Cycle}
    {ss : List SubdivisionStep} (hv : validSubdivision g ss)
    (hc : IsCycle g r c) (hd : IsCycle h k d)
    (hp : (cycleEdges d).Perm ((cycleEdges c).flatMap (expandedEdge ss)))
    {e : Edge} (he : e ∈ g) (hz : expandedEdge ss e = [e]) (v : Nat) :
    (selectedAt d v).count e = (selectedAt c v).count e := by
  rw [(selectedAt_nodup hd v).count, (selectedAt_nodup hc v).count]
  simp only [expanded_selectedAt_port_mem hv hc hp he hz v]

theorem expanded_selectedAt_port_normalizes {g h : Graph} {r k : Nat} {c d : Cycle}
    {ss : List SubdivisionStep} (hv : validSubdivision g ss)
    (hc : IsCycle g r c) (hd : IsCycle h k d)
    (hp : (cycleEdges d).Perm ((cycleEdges c).flatMap (expandedEdge ss)))
    {e : Edge} (he : e ∈ g) (hz : expandedEdge ss e = [e]) (v : Nat) :
    (selectedAt c (originalChoice c v)).count e ≤ (selectedAt d v).count e := by
  rw [(selectedAt_nodup hd v).count, (selectedAt_nodup hc _).count]
  by_cases hm : e ∈ selectedAt c (originalChoice c v)
  · obtain ⟨hec, hav⟩ := List.mem_filter.mp hm
    have hv' : e ∈ selectedAt c v := List.mem_filter.mpr ⟨hec, originalChoice_avoids v hec hav⟩
    have hd' := (expanded_selectedAt_port_mem hv hc hp he hz v).mpr hv'
    simp [hm, hd']
  · simp [hm]

theorem expanded_family_port_eq {g h : Graph} {k : Nat} {ss : List SubdivisionStep}
    (hv : validSubdivision g ss) (cs : List Cycle) (expand : Cycle → Cycle)
    (hc : ∀ c ∈ cs, IsCycle g c.length c)
    (hd : ∀ c ∈ cs, IsCycle h k (expand c))
    (hp : ∀ c ∈ cs, (cycleEdges (expand c)).Perm ((cycleEdges c).flatMap (expandedEdge ss)))
    {e : Edge} (he : e ∈ g) (hz : expandedEdge ss e = [e]) (choose : Cycle → Nat) :
    load (cs.map fun c => selectedAt (expand c) (choose c)) e =
      load (cs.map fun c => selectedAt c (choose c)) e := by
  simp only [load, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hcm
  exact expanded_selectedAt_port_count hv (hc c hcm) (hd c hcm) (hp c hcm) he hz (choose c)

theorem expanded_family_port_normalizes {g h : Graph} {k : Nat} {ss : List SubdivisionStep}
    (hv : validSubdivision g ss) (cs : List Cycle) (expand : Cycle → Cycle)
    (hc : ∀ c ∈ cs, IsCycle g c.length c)
    (hd : ∀ c ∈ cs, IsCycle h k (expand c))
    (hp : ∀ c ∈ cs, (cycleEdges (expand c)).Perm ((cycleEdges c).flatMap (expandedEdge ss)))
    {e : Edge} (he : e ∈ g) (hz : expandedEdge ss e = [e]) (choose : Cycle → Nat) :
    load (cs.map fun c => selectedAt c (originalChoice c (choose c))) e ≤
      load (cs.map fun c => selectedAt (expand c) (choose c)) e := by
  simp only [load, List.map_map]
  apply sum_map_le
  intro c hcm
  exact expanded_selectedAt_port_normalizes hv (hc c hcm) (hd c hcm) (hp c hcm) he hz (choose c)

theorem overlap_singleton (p : List Edge) (e : Edge) : overlap p [e] = p.count e := by
  rw [overlap_cons_right, overlap_nil_right, Nat.add_zero]

theorem cost_append_ports (ps : List (List Edge)) (ports : List Edge) :
    cost (ps ++ ports.map (fun e => [e])) =
      cost ps + cost (ports.map (fun e => [e])) + (ports.map (load ps)).sum := by
  induction ps with
  | nil =>
    simp only [List.nil_append, cost, Nat.zero_add]
    have hz : (ports.map (load [])).sum = 0 := sum_map_zero ports
    rw [hz, Nat.add_zero]
  | cons p ps ih =>
    simp only [List.cons_append, cost, List.map_append, List.map_map, List.sum_append, ih,
      Function.comp_def]
    have hp : (ports.map (fun e => overlap p [e])).sum = (ports.map (fun e => p.count e)).sum := by
      congr 1
      exact List.map_congr_left (fun e _ => overlap_singleton p e)
    rw [hp]
    have hl : (ports.map (load (p :: ps))).sum =
        (ports.map (fun e => p.count e)).sum + (ports.map (load ps)).sum := by
      change (ports.map (fun e => p.count e + load ps e)).sum = _
      exact sum_map_add ports _ _
    rw [hl]
    omega

theorem load_reverse (ps : List (List Edge)) (e : Edge) : load ps.reverse e = load ps e := by
  simp [load]

def costWithPorts (ps : List (List Edge)) (ports : List Edge) : Nat :=
  cost ps + (ports.map (load ps)).sum

theorem costWithPorts_eq_append (ps : List (List Edge)) (ports : List Edge)
    (hz : cost (ports.map (fun e => [e])) = 0) :
    costWithPorts ps ports = cost (ps.reverse ++ ports.map (fun e => [e])) := by
  rw [cost_append_ports, cost_reverse, hz, Nat.add_zero]
  unfold costWithPorts
  congr 2
  exact List.map_congr_left (fun e _ => (load_reverse ps e).symm)

theorem PathsPerm.costWithPorts_eq {ps qs : List (List Edge)} (hp : PathsPerm ps qs)
    (ports : List Edge) : costWithPorts ps ports = costWithPorts qs ports := by
  unfold costWithPorts
  rw [hp.cost_eq]
  congr 2
  exact List.map_congr_left (fun e _ => hp.load_eq e)

theorem expanded_family_costWithPorts_normalizes {g h : Graph} {k : Nat} {ss : List SubdivisionStep}
    (hv : validSubdivision g ss) (cs : List Cycle) (expand : Cycle → Cycle)
    (hc : ∀ c ∈ cs, IsCycle g c.length c)
    (hd : ∀ c ∈ cs, IsCycle h k (expand c))
    (hp : ∀ c ∈ cs, (cycleEdges (expand c)).Perm ((cycleEdges c).flatMap (expandedEdge ss)))
    (hu : cs.Pairwise (fun c d => ∀ e ∈ cycleEdges c,
      e ∈ cycleEdges d → expandedEdge ss e = [e]))
    (ports : List Edge) (hports : ∀ e ∈ ports, e ∈ g ∧ expandedEdge ss e = [e])
    (choose : Cycle → Nat) :
    costWithPorts (cs.map fun c => selectedAt c (originalChoice c (choose c))) ports ≤
      costWithPorts (cs.map fun c => selectedAt (expand c) (choose c)) ports := by
  apply Nat.add_le_add (expanded_family_normalizes hv cs expand hc hd hp hu choose)
  apply sum_map_le
  intro e he
  exact expanded_family_port_normalizes hv cs expand hc hd hp
    (hports e he).1 (hports e he).2 choose

end STACS2027
