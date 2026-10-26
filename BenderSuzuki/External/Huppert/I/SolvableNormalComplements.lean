module

public import Mathlib.GroupTheory.GroupAction.OfQuotient
public import FeitThompson.HallSubgroups.Conjugacy
public import FeitThompson.SubgroupConjAction

namespace BenderSuzuki.External
open scoped Pointwise
universe u

/-- The solvable-normal-subgroup branch of Huppert I.18.2. -/
public theorem huppert_I_18_2_a_complements_conjugate_of_solvable_normal
    {G : Type u} [Group G] [Finite G]
    (N H K : Subgroup G) [N.Normal]
    (hcoprime : Nat.Coprime (Nat.card N) (Nat.card (G ⧸ N)))
    (hsolvable : IsSolvable N)
    (hH : N.IsComplement' H) (hK : N.IsComplement' K) :
    ∃ n : N, K = H.map (MulAut.conj (n : G)).toMonoidHom := by
  classical
  have hH_normalizes_N : H ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.le_normalizer_of_normal (H := N)
  letI : MulDistribMulAction H N :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (G := G) H N hH_normalizes_N
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let eK : G ⧸ N ≃* K := hK.symm.QuotientMulEquiv
  let sectionK : H → K := fun h => eK (q (h : G))
  have hsectionK_q : ∀ h : H, q (sectionK h : G) = q (h : G) := by
    intro h
    dsimp [sectionK, eK, q]
    exact Subgroup.IsComplement.quotientGroupMk_leftQuotientEquiv hK.symm
      (QuotientGroup.mk' N (h : G))
  let cocycle : H → N := fun h =>
    ⟨(sectionK h : G) * (h : G)⁻¹, by
      rw [← QuotientGroup.eq_one_iff (N := N)]
      change q ((sectionK h : G) * (h : G)⁻¹) = 1
      rw [map_mul, map_inv, hsectionK_q h]
      simp⟩
  have hsectionK_mul : ∀ a b : H, sectionK (a * b) = sectionK a * sectionK b := by
    intro a b
    dsimp [sectionK]
    exact eK.map_mul (q (a : G)) (q (b : G))
  have hsectionK_eq : ∀ h : H, (sectionK h : G) = (cocycle h : G) * (h : G) := by
    intro h
    dsimp [cocycle]
    simp [mul_assoc]
  have hcocycle : ∀ a b : H, cocycle (a * b) = cocycle a * (a • cocycle b) := by
    intro a b
    ext
    have hsG : (sectionK (a * b) : G) = (sectionK a : G) * (sectionK b : G) :=
      congrArg Subtype.val (hsectionK_mul a b)
    dsimp [cocycle]
    rw [hsG]
    simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
  have hcardH : Nat.card H = Nat.card (G ⧸ N) := by
    calc
      Nat.card H = N.index := hH.symm.index_eq_card.symm
      _ = Nat.card (G ⧸ N) := Subgroup.index_eq_card N
  have hcoprimeHN : Nat.Coprime (Nat.card H) (Nat.card N) := by
    simpa [hcardH] using hcoprime.symm
  obtain ⟨n, hn⟩ :=
    exists_principal_cocycle_of_solvable_coprime
      (A := H) (N := N) hsolvable hcoprimeHN cocycle hcocycle
  have hHn_le_K : H.map (MulAut.conj (n : G)).toMonoidHom ≤ K := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨h, hhH, rfl⟩
    let hH' : H := ⟨h, hhH⟩
    have hnG :
        (cocycle hH' : G) = (n : G) * (((hH' : H) • n : N) : G)⁻¹ := by
      simpa using congrArg Subtype.val (hn hH')
    have hsection_eq : (sectionK hH' : G) = (n : G) * h * (n : G)⁻¹ := by
      calc
        (sectionK hH' : G) = (cocycle hH' : G) * (hH' : G) := hsectionK_eq hH'
        _ = ((n : G) * (((hH' : H) • n : N) : G)⁻¹) * (hH' : G) := by rw [hnG]
        _ = (n : G) * h * (n : G)⁻¹ := by
          simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hH', mul_assoc]
    simpa [MulAut.conj_apply, hH', hsection_eq] using (sectionK hH').property
  have hcardK : Nat.card K = Nat.card H :=
    hK.symm.index_eq_card.symm.trans hH.symm.index_eq_card
  have hcardHn : Nat.card (H.map (MulAut.conj (n : G)).toMonoidHom) = Nat.card H := by
    exact Subgroup.card_map_of_injective
      (K := H) (f := (MulAut.conj (n : G)).toMonoidHom) (MulAut.conj (n : G)).injective
  have hcard_le : Nat.card K ≤ Nat.card (H.map (MulAut.conj (n : G)).toMonoidHom) := by
    rw [hcardK, hcardHn]
  exact ⟨n, (Subgroup.eq_of_le_of_card_ge hHn_le_K hcard_le).symm⟩

end BenderSuzuki.External
