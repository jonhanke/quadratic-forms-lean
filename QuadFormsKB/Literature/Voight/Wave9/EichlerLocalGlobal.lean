/-
# Being an Eichler order is a local property (Voight, Proposition 23.4.2)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Proposition 23.4.2 (p. 382).

**Setting.** $F$ a number field, $B = (a,b)_F$ with $a, b \in \mathbb Z_F$ nonzero, $\mathcal O \subseteq B$ an order, $\mathcal O_v$
its completion at a finite place $v$ (`QuatOrder.localOrder`).

**Theorem** (`eichlerIsLocal`, the proposition `Wave4.EichlerIsLocal F` proved for every number field):
$\mathcal O$ is an Eichler order (the intersection of two maximal orders) iff $\mathcal O_v$ is an Eichler $\mathfrak o_v$-order of $B_v$
for every finite place $v$.

*Proof.* ($\Rightarrow$) Completion commutes with intersection (`localOrder_inf`) and completions of maximal orders are maximal
(`isMaximalOrder_localOrder_nf`). ($\Leftarrow$) Choose a maximal order $M \supseteq \mathbb Z_F\langle i,j,k\rangle$. The orders $\mathcal O$ and
$M$ are lattices in $F^4$, so $\mathcal O_v = M_v$ for almost all $v$. Choose local maximal orders $\Lambda_{1,v}, \Lambda_{2,v}$ with
$\mathcal O_v = \Lambda_{1,v} \cap \Lambda_{2,v}$, and replace them by $M_v$ where $\mathcal O_v = M_v$. By gluing of orders
(`exists_order_localOrder_eq`) these are the completions of global orders $\mathcal O_1, \mathcal O_2$, maximal because their completions
are (`order_eq_of_localOrder_eq`), and $\mathcal O = \mathcal O_1 \cap \mathcal O_2$ since both sides have the same completions.
-/
import QuadFormsKB.Literature.Voight.Wave9.LocalLattice

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain

noncomputable section

namespace QuadFormsKB.Voight.Wave9

open QuadFormsKB.Quat QuadFormsKB.QuatOrder QuadFormsKB.Lattices QuadFormsKB.Voight QuadFormsKB.Voight.Wave3
  QuadFormsKB.Voight.Wave4

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}

/-- A global maximal order is determined by maximality of its completions: if every completion $\mathcal O_v$ of an order is a
maximal $\mathfrak o_v$-order then $\mathcal O$ is maximal. -/
theorem isMaximalOrder_of_forall_localOrder {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), IsMaximalOrder (v.adicCompletionIntegers F) (v.adicCompletion F)
      (localOrder (v := v) a b O)) : IsMaximalOrder (𝓞 F) F O := by
  refine ⟨hO, fun O' hO' hle => ?_⟩
  refine (order_eq_of_localOrder_eq hO hO' fun v => ?_).symm
  exact ((h v).2 _ (Gen.isOrder_localOrder_gen v hO') (localOrder_mono' v hle)).symm

/-- **Being an Eichler order is a local property** (Voight 2021, Proposition 23.4.2), for every number field: an order
$\mathcal O \subseteq (a,b)_F$ ($a, b \ne 0$) is an Eichler order iff every completion $\mathcal O_v$ is an Eichler order of $B_v$. -/
@[kb "voight2021" "Proposition 23.4.2, p. 382"]
theorem eichlerIsLocal (F : Type) [Field F] [NumberField F] : EichlerIsLocal F := by
  intro a b ha hb O hO
  constructor
  · rintro ⟨O₁, O₂, h₁, h₂, rfl⟩ v
    exact ⟨_, _, isMaximalOrder_localOrder_nf h₁, isMaximalOrder_localOrder_nf h₂, localOrder_inf h₁.1 h₂.1 v⟩
  · intro h
    have h2ab : algebraMap (𝓞 F) F (2 * a * b) ≠ 0 := by
      simpa [ha, hb] using
        mul_ne_zero (mul_ne_zero (two_ne_zero) ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 ha))
          ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hb)
    obtain ⟨M, hM, -⟩ := exists_isMaximalOrder_ge_stdOrder (R := 𝓞 F) (K := F) h2ab
    choose Λ₁ Λ₂ hΛ₁ hΛ₂ hΛ using h
    have hev : ∀ᶠ v in Filter.cofinite, localOrder (v := v) a b O = localOrder (v := v) a b M := by
      filter_upwards [loc_eventually_std (isLattice_latOf hO), loc_eventually_std (isLattice_latOf hM.1)] with v h1 h2
      exact (loc_latOf_eq_iff v).1 (h1.trans h2.symm)
    classical
    let Λ' : Fin 2 → ∀ v : HeightOneSpectrum (𝓞 F), Subalgebra (v.adicCompletionIntegers F) (QuatV v a b) :=
      fun i v => if localOrder (v := v) a b O = localOrder (v := v) a b M then localOrder (v := v) a b M
        else (![Λ₁ v, Λ₂ v] i)
    have hmax : ∀ i v, IsMaximalOrder (v.adicCompletionIntegers F) (v.adicCompletion F) (Λ' i v) := by
      intro i v
      by_cases hv : localOrder (v := v) a b O = localOrder (v := v) a b M
      · simp only [Λ', if_pos hv]; exact isMaximalOrder_localOrder_nf hM
      · simp only [Λ', if_neg hv]; fin_cases i
        · exact hΛ₁ v
        · exact hΛ₂ v
    have hevi : ∀ i, ∀ᶠ v in Filter.cofinite, Λ' i v = localOrder (v := v) a b M := by
      intro i
      filter_upwards [hev] with v hv
      simp only [Λ', if_pos hv]
    have hglue : ∀ i, ∃ Oi : Subalgebra (𝓞 F) (QuatF F a b), IsOrder (𝓞 F) F Oi ∧
        ∀ v, localOrder (v := v) a b Oi = Λ' i v :=
      fun i => exists_order_localOrder_eq hM.1 (Λ' i) (fun v => (hmax i v).1) (hevi i)
    obtain ⟨O₁, hO₁, hl₁⟩ := hglue 0
    obtain ⟨O₂, hO₂, hl₂⟩ := hglue 1
    have hm₁ : IsMaximalOrder (𝓞 F) F O₁ :=
      isMaximalOrder_of_forall_localOrder hO₁ fun v => by rw [hl₁ v]; exact hmax 0 v
    have hm₂ : IsMaximalOrder (𝓞 F) F O₂ :=
      isMaximalOrder_of_forall_localOrder hO₂ fun v => by rw [hl₂ v]; exact hmax 1 v
    -- the local intersection: O_v = Λ₁' ⊓ Λ₂'
    have hloc : ∀ v, localOrder (v := v) a b O = Λ' 0 v ⊓ Λ' 1 v := by
      intro v
      by_cases hv : localOrder (v := v) a b O = localOrder (v := v) a b M
      · simp only [Λ', if_pos hv, inf_idem]; exact hv
      · simp only [Λ', if_neg hv]; exact hΛ v
    refine ⟨O₁, O₂, hm₁, hm₂, le_antisymm ?_ ?_⟩
    · refine le_inf ?_ ?_
      · exact order_le_of_localOrder_le hO₁ fun v => by rw [hl₁ v, hloc v]; exact inf_le_left
      · exact order_le_of_localOrder_le hO₂ fun v => by rw [hl₂ v, hloc v]; exact inf_le_right
    · refine order_le_of_localOrder_le hO fun v => ?_
      rw [hloc v, ← hl₁ v, ← hl₂ v]
      exact le_inf (localOrder_mono' v inf_le_left) (localOrder_mono' v inf_le_right)

end QuadFormsKB.Voight.Wave9
