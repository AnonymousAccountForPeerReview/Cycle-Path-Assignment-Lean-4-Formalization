module
public import NPHardness.PlanarBoundedMembershipProgram
import Lean.Elab.Tactic.Omega
@[expose] public section
namespace STACS2027.PlanarBoundedMembership
open Complexity Complexity.SAT Complexity.Planar Complexity.Planar.Vf Complexity.Planar.Chk
open Complexity.StackTableauEmitter

/-- The registered planar verifier plus the finite signed-occurrence checks. -/
def boundedVerifier : C := .both (verifier false) (readScalars extraCheck)

def boundedProgram : ClauseProgram 1 := checkedProgram boundedVerifier

/-- Exact acceptance semantics, retaining rejection of malformed input words. -/
theorem boundedProgram_accepts (x w : SAT.Word) :
    boundedProgram.emit (pairWords x w) (fun _ => (pairWords x w).length) = [[]] ↔
      (program false).emit (pairWords x w) (fun _ => (pairWords x w).length) = [[]] ∧
      BoundedOccurrence (decodeCert (pairWords x w) x.length).pt.fml := by
  rw [boundedProgram,checkedProgram_emit,program_emit]
  constructor
  · rintro ⟨L,hL,hbase,hextra⟩
    have hv := (holds_verifier false x w L _ (by simp) hL.symm).mp hbase
    obtain ⟨rfl,hw,hv⟩ := hv
    have hg := globalWF_of _ _ hL.symm hw
    refine ⟨⟨x.length,hL,hbase⟩,?_⟩
    rw [holds_readScalars (by simp) hg, s_extra hg (envOK_scal (by simp))] at hextra
    exact (tableCaps_iff hv.parse hv.three).mp hextra
  · rintro ⟨⟨L,hL,hbase⟩,hb⟩
    have hv := (holds_verifier false x w L _ (by simp) hL.symm).mp hbase
    obtain ⟨rfl,hw,hv⟩ := hv
    have hg := globalWF_of _ _ hL.symm hw
    refine ⟨x.length,hL,hbase,?_⟩
    rw [holds_readScalars (by simp) hg, s_extra hg (envOK_scal (by simp))]
    exact (tableCaps_iff hv.parse hv.three).mpr hb

theorem boundedProgram_sound (x w : SAT.Word)
    (h : boundedProgram.emit (pairWords x w) (fun _ => (pairWords x w).length) = [[]]) :
    PlanarBoundedSATLanguage x := by
  obtain ⟨hbase,hb⟩ := (boundedProgram_accepts x w).mp h
  have hv := ((accepts_iff false x w).mp hbase).2.2
  obtain ⟨f,hf,_,hs,hp⟩ := verifier_sound false x w hbase
  have he : f=(decodeCert (pairWords x w) x.length).pt.fml :=
    encode_injective _ _ (hf.trans hv.parse.encode_eq.symm)
  rw [←he] at hb
  refine ⟨f,?_,hb,?_,hs⟩
  · rw [SAT.decode_eq_some_iff]
    exact hf.symm
  · simpa only [targetGraph,Bool.false_eq_true,ite_false,List.append_nil] using hp

theorem boundedProgram_complete {f : CNF} (hb : BoundedOccurrence f)
    (hp : PlanarGraph (incidenceGraph f)) (hs : Satisfiable f) :
    ∃w,w.length=certLen (encode f).length ∧
      boundedProgram.emit (pairWords (encode f) w)
        (fun _ => (pairWords (encode f) w).length)=[[]] := by
  obtain ⟨w,hw,hbase⟩ := verifier_complete false hb.isThreeCNF hs
    (by simpa only [targetGraph,Bool.false_eq_true,ite_false,List.append_nil] using hp)
  refine ⟨w,hw,(boundedProgram_accepts (encode f) w).mpr ⟨hbase,?_⟩⟩
  have hv := ((accepts_iff false (encode f) w).mp hbase).2.2
  have he : (decodeCert (pairWords (encode f) w) (encode f).length).pt.fml=f :=
    encode_injective _ _ hv.parse.encode_eq
  simpa only [he] using hb

end STACS2027.PlanarBoundedMembership

namespace STACS2027
open Complexity Complexity.SAT Complexity.Planar

/-- Definition 7 with actual incidence planarity belongs to the registered NP
class. The verifier is finite code compiled by the registered single-tape
compiler; malformed encodings fail its parser. -/
theorem planarBoundedSAT_inNP : InNP PlanarBoundedSATLanguage := by
  apply inNP_of_emitter PlanarBoundedMembership.boundedProgram 704 2
  intro x
  constructor
  · rintro ⟨f,hd,hb,hp,hs⟩
    have hx := (SAT.decode_eq_some_iff _ _).mp hd
    subst x
    obtain ⟨w,hw,he⟩ := PlanarBoundedMembership.boundedProgram_complete hb hp hs
    exact ⟨w,hw ▸ Vf.certLen_le _,he⟩
  · rintro ⟨w,_,he⟩
    exact PlanarBoundedMembership.boundedProgram_sound x w he

end STACS2027
