module

public import NPHardness.OccurrencePorts
public import NPHardness.GadgetProjection

/-! Concrete vertex names for gluing clause-port endpoints onto the allocated
variable-port endpoints. Private clause vertices occupy a separate block. -/

@[expose] public section
namespace STACS2027

def blockVertex (width tag v : Nat) : Nat := tag * width + v

theorem blockVertex_injective {width a b u v : Nat} (hu : u < width) (hv : v < width)
    (he : blockVertex width a u = blockVertex width b v) : a = b ∧ u = v := by
  have hw : 0 < width := by omega
  have hd := congrArg (fun x => x / width) he
  have hf : ∀ t x, x < width → blockVertex width t x / width = t := by
    intro t x hx
    rw [blockVertex, Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hx, Nat.zero_add]
  rw [hf a u hu, hf b v hv] at hd
  refine ⟨hd, ?_⟩
  subst b
  unfold blockVertex at he
  omega

def variableEndpoint (port : Nat) (right : Bool) : Nat :=
  if port = 0 then (if right then 6 else 2)
  else if port = 1 then (if right then 5 else 4)
  else (if right then 3 else 0)

def clauseEndpoint (slot : Nat) (right : Bool) : Nat :=
  if slot = 0 then (if right then 1 else 0)
  else if slot = 1 then (if right then 5 else 4)
  else (if right then 11 else 10)

def clausePortAt (v : Nat) : Option (Nat × Bool) :=
  if v = 0 then some (0,false) else if v = 1 then some (0,true)
  else if v = 4 then some (1,false) else if v = 5 then some (1,true)
  else if v = 10 then some (2,false) else if v = 11 then some (2,true) else none

def attachmentAt (c : List PlacedLiteral) (v : Nat) : Option (PlacedLiteral × Bool) :=
  (clausePortAt v).bind fun ib => (c[ib.1]?).map fun p => (p, ib.2)

def clauseVertex (width n j : Nat) (c : List PlacedLiteral) (v : Nat) : Nat :=
  match attachmentAt c v with
  | some (p, side) => blockVertex width p.literal.var (variableEndpoint p.port side)
  | none => blockVertex width (n + j) v

theorem variableEndpoint_bound (port : Nat) (side : Bool) : variableEndpoint port side < 7 := by
  simp only [variableEndpoint]
  split <;> split <;> cases side <;> decide

theorem variableEndpoint_injective {p q : Nat} (hp : p < 3) (hq : q < 3) (b c : Bool)
    (h : variableEndpoint p b = variableEndpoint q c) : p = q ∧ b = c := by
  have ht : ∀ p q : Fin 3, ∀ b c : Bool,
      variableEndpoint p.val b = variableEndpoint q.val c → p = q ∧ b = c := by decide
  obtain ⟨h₁, h₂⟩ := ht ⟨p,hp⟩ ⟨q,hq⟩ b c h
  exact ⟨congrArg Fin.val h₁, h₂⟩

theorem clausePortAt_spec {v i : Nat} {side : Bool} (h : clausePortAt v = some (i,side)) :
    i < 3 ∧ v = clauseEndpoint i side := by
  unfold clausePortAt at h
  split at h <;> try split at h <;> try split at h <;> try split at h <;>
    try split at h <;> try split at h
  all_goals simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals obtain ⟨hi, hs⟩ := h
  all_goals subst i; subst side; simp_all [clauseEndpoint]

theorem clausePortAt_endpoint {i : Nat} (hi : i < 3) (side : Bool) :
    clausePortAt (clauseEndpoint i side) = some (i,side) := by
  have ht : ∀ i : Fin 3, ∀ side : Bool,
      clausePortAt (clauseEndpoint i.val side) = some (i.val,side) := by decide
  exact ht ⟨i,hi⟩ side

theorem attachmentAt_spec {c : List PlacedLiteral} {v : Nat} {p : PlacedLiteral} {side : Bool} :
    attachmentAt c v = some (p,side) ↔
      ∃ i, i < 3 ∧ c[i]? = some p ∧ v = clauseEndpoint i side := by
  constructor
  · intro h
    unfold attachmentAt at h
    cases hv : clausePortAt v with
    | none => simp [hv] at h
    | some ib =>
      cases ib with | mk i b =>
        cases hp : c[i]? with
        | none => simp [hv, hp] at h
        | some q =>
          have he : q = p ∧ b = side := by simpa [hv, hp] using h
          obtain ⟨rfl, rfl⟩ := he
          obtain ⟨hi, he⟩ := clausePortAt_spec hv
          exact ⟨i, hi, hp, he⟩
  · rintro ⟨i, hi, hp, rfl⟩
    simp [attachmentAt, clausePortAt_endpoint hi side, hp]

theorem clauseVertex_attachment {width n j : Nat} {c : List PlacedLiteral}
    {i : Nat} (hi : i < 3) {p : PlacedLiteral} (hp : c[i]? = some p) (side : Bool) :
    clauseVertex width n j c (clauseEndpoint i side) =
      blockVertex width p.literal.var (variableEndpoint p.port side) := by
  have h : attachmentAt c (clauseEndpoint i side) = some (p,side) :=
    attachmentAt_spec.mpr ⟨i, hi, hp, rfl⟩
  simp only [clauseVertex, h]

theorem clauseVertex_injective {width n j : Nat} {c : List PlacedLiteral}
    (hw : 7 ≤ width) (hc : (c.map PlacedLiteral.key).Nodup)
    (hb : ∀ p ∈ c, p.literal.var < n ∧ p.port < 3)
    {u v : Nat} (hu : u < width) (hv : v < width)
    (he : clauseVertex width n j c u = clauseVertex width n j c v) : u = v := by
  cases hau : attachmentAt c u with
  | none =>
    cases hav : attachmentAt c v with
    | none => exact (blockVertex_injective hu hv (by simpa [clauseVertex, hau, hav] using he)).2
    | some ps =>
      obtain ⟨p, side⟩ := ps
      obtain ⟨i, _, hip, _⟩ := attachmentAt_spec.mp hav
      have hpm : p ∈ c := List.mem_of_getElem? hip
      have hpv := (hb p hpm).1
      have hep : variableEndpoint p.port side < width := Nat.lt_of_lt_of_le (variableEndpoint_bound _ _) hw
      have htag := (blockVertex_injective hu hep (by simpa [clauseVertex, hau, hav] using he)).1
      omega
  | some ps =>
    obtain ⟨p, side⟩ := ps
    obtain ⟨i, _, hip, hui⟩ := attachmentAt_spec.mp hau
    have hpm : p ∈ c := List.mem_of_getElem? hip
    have hpv := (hb p hpm).1
    have hep : variableEndpoint p.port side < width := Nat.lt_of_lt_of_le (variableEndpoint_bound _ _) hw
    cases hav : attachmentAt c v with
    | none =>
      have htag := (blockVertex_injective hep hv (by simpa [clauseVertex, hau, hav] using he)).1
      omega
    | some qs =>
      obtain ⟨q, side'⟩ := qs
      obtain ⟨i', _, hiq, hvi⟩ := attachmentAt_spec.mp hav
      have hqm : q ∈ c := List.mem_of_getElem? hiq
      have heq : variableEndpoint q.port side' < width := Nat.lt_of_lt_of_le (variableEndpoint_bound _ _) hw
      obtain ⟨hvar, hend⟩ := blockVertex_injective hep heq (by simpa [clauseVertex, hau, hav] using he)
      obtain ⟨hport, hside⟩ := variableEndpoint_injective (hb p hpm).2 (hb q hqm).2 _ _ hend
      have hkey : p.key = q.key := Prod.ext hvar hport
      have hlen : i < (c.map PlacedLiteral.key).length := by
        have h := (List.getElem?_eq_some_iff.mp hip).1
        simpa using h
      have hidx : i = i' := hc.eq_of_getElem?_eq hlen (by simp [List.getElem?_map, hip, hiq, hkey])
      rw [hui, hvi, hidx, hside]

end STACS2027
