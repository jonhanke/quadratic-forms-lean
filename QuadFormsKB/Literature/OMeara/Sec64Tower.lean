/-
# O'Meara §64: the norm of an idèle in a tower, $N_{H/F} = N_{E/F} \circ N_{H/E}$

**Setting.** $F \subseteq E \subseteq H$ is a tower of number fields (`IsScalarTower F E H`). Idèle norms are
`ideleNorm` (`Sec64Norm.lean`), built from the local norms `localNormFin` and `localNormInf`.

**Proves** (§64, p. 173)
* `ideleNorm_tower`: $N_{H/F}\mathfrak J = N_{E/F}(N_{H/E}\mathfrak J)$ for $\mathfrak J \in J_H$ (componentwise:
  transitivity of the local norms $N_{\mathfrak U|\mathfrak p} = N_{\mathfrak P|\mathfrak p} \circ N_{\mathfrak U|\mathfrak P}$,
  and $\{\mathfrak U \mid \mathfrak p\} = \bigsqcup_{\mathfrak P|\mathfrak p}\{\mathfrak U \mid \mathfrak P\}$ at finite and
  infinite spots);
* `range_ideleNorm_tower_le`: $N_{H/F} J_H \subseteq N_{E/F} J_E$.
-/
import QuadFormsKB.Literature.OMeara.Sec64Norm

open NumberField IsDedekindDomain InfinitePlace

open scoped NumberField.LiesOver

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {F E H : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Field H] [NumberField H]
  [Algebra F E] [Algebra E H] [Algebra F H] [IsScalarTower F E H]

/-! ### Finite spots -/

section Fin

variable (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 H))

/-- $\mathfrak U \mid \mathfrak P \mid \mathfrak p$ implies $\mathfrak U \mid \mathfrak p$. -/
theorem liesOver_trans_fin [w.asIdeal.LiesOver v.asIdeal] [u.asIdeal.LiesOver w.asIdeal] :
    u.asIdeal.LiesOver v.asIdeal :=
  Ideal.LiesOver.trans u.asIdeal w.asIdeal v.asIdeal

/-- $\mathfrak U \mid \mathfrak p$ implies that the spot of $E$ below $\mathfrak U$ lies over $\mathfrak p$. -/
theorem liesOver_spotBelow_fin [h : u.asIdeal.LiesOver v.asIdeal] :
    (spotBelow (F := E) u).asIdeal.LiesOver v.asIdeal := by
  refine ⟨?_⟩
  rw [h.over]
  show _ = Ideal.comap _ (Ideal.comap _ _)
  rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]

/-- Transitivity of the embeddings of completions. -/
theorem localMap_comp [w.asIdeal.LiesOver v.asIdeal] [u.asIdeal.LiesOver w.asIdeal]
    [u.asIdeal.LiesOver v.asIdeal] (x : v.adicCompletion F) :
    localMap w u (localMap v w x) = localMap v u x := by
  have key : (localMap w u).comp (localMap v w) = localMap v u := by
    refine RingHom.ext fun x => ?_
    have := DenseRange.equalizer (HeightOneSpectrum.denseRange_algebraMap F v)
      (g := ⇑((localMap w u).comp (localMap v w))) (h := ⇑(localMap v u))
      (((continuous_localMap w u).comp (continuous_localMap v w)))
      (continuous_localMap v u) (by
        funext c
        simp only [Function.comp_apply, RingHom.coe_comp, localMap_algebraMap,
          ← IsScalarTower.algebraMap_apply F E H])
    exact congrFun this x
  exact RingHom.congr_fun key x

instance [w.asIdeal.LiesOver v.asIdeal] [u.asIdeal.LiesOver w.asIdeal] [u.asIdeal.LiesOver v.asIdeal] :
    IsScalarTower (v.adicCompletion F) (w.adicCompletion E) (u.adicCompletion H) :=
  .of_algebraMap_eq fun x => (localMap_comp v w u x).symm

/-- Transitivity of the local norm. -/
theorem localNormFin_tower [w.asIdeal.LiesOver v.asIdeal] [u.asIdeal.LiesOver w.asIdeal]
    [u.asIdeal.LiesOver v.asIdeal] (y : u.adicCompletion H) :
    localNormFin v w (localNormFin w u y) = localNormFin v u y := by
  simp only [localNormFin_apply]
  exact Algebra.norm_norm

/-- The reindexing $\{\mathfrak U \mid \mathfrak p\} \simeq \bigsqcup_{\mathfrak P|\mathfrak p}\{\mathfrak U \mid
\mathfrak P\}$. -/
def spotsOverSigma : SpotsOver H v ≃ Σ w : SpotsOver E v, SpotsOver H w.1 where
  toFun u :=
    have := u.2
    ⟨⟨spotBelow (F := E) u.1, liesOver_spotBelow_fin v u.1⟩, ⟨u.1, inferInstance⟩⟩
  invFun p :=
    have := p.1.2
    have := p.2.2
    ⟨p.2.1, liesOver_trans_fin v p.1.1 p.2.1⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨w, hw⟩, ⟨u, hu⟩⟩
    have : spotBelow (F := E) u = w := (eq_spotBelow_of_liesOver w u).symm
    subst this
    rfl

/-- The finite component of the norm is transitive. -/
theorem finNormComp_tower (x : (u : HeightOneSpectrum (𝓞 H)) → u.adicCompletion H) :
    finNormComp (F := F) x v =
      finNormComp (F := F) (fun w : HeightOneSpectrum (𝓞 E) => finNormComp (F := E) x w) v := by
  unfold finNormComp
  simp only [map_prod]
  rw [← Fintype.prod_sigma' (fun (w : SpotsOver E v) (u : SpotsOver H w.1) =>
    localNormFin v w.1 (localNormFin w.1 u.1 (x u.1)))]
  refine Fintype.prod_equiv (spotsOverSigma v) _ _ fun u => ?_
  have := u.2
  have := liesOver_spotBelow_fin (E := E) v u.1
  change _ = localNormFin v (spotBelow (F := E) u.1) (localNormFin (spotBelow (F := E) u.1) u.1 (x u.1))
  rw [localNormFin_tower]

end Fin

/-! ### Infinite spots -/

section Inf

variable (v : InfinitePlace F) (w : InfinitePlace E) (u : InfinitePlace H)

theorem liesOver_of_comap_eq {K L : Type} [Field K] [Field L] [Algebra K L] (w : InfinitePlace L)
    (v : InfinitePlace K) (h : w.comap (algebraMap K L) = v) : w.LiesOver v :=
  ⟨by
    ext x
    have := congrArg (fun p : InfinitePlace K => p x) h
    exact this⟩

/-- $\mathfrak U \mid \mathfrak P \mid \mathfrak p$ implies $\mathfrak U \mid \mathfrak p$. -/
theorem liesOver_trans_inf [w.LiesOver v] [u.LiesOver w] : u.LiesOver v := by
  refine liesOver_of_comap_eq u v ?_
  rw [IsScalarTower.algebraMap_eq F E H, InfinitePlace.comap_comp (w := u),
    InfinitePlace.LiesOver.comap_eq u w, InfinitePlace.LiesOver.comap_eq w v]

/-- $\mathfrak U \mid \mathfrak p$ implies that the spot of $E$ below $\mathfrak U$ lies over $\mathfrak p$. -/
theorem liesOver_comap_inf [h : u.LiesOver v] : (u.comap (algebraMap E H)).LiesOver v := by
  refine liesOver_of_comap_eq _ v ?_
  rw [← InfinitePlace.LiesOver.comap_eq u v, IsScalarTower.algebraMap_eq F E H, InfinitePlace.comap_comp]

theorem denseRange_algebraMap_completion {K : Type} [Field K] (v : InfinitePlace K) :
    DenseRange (algebraMap K v.Completion) :=
  (InfinitePlace.Completion.denseRange_coe v).mono (by
    rintro _ ⟨x, rfl⟩
    exact ⟨WithAbs.ofAbs x, rfl⟩)

omit [NumberField F] [NumberField E] [NumberField H] in
theorem algebraMap_tower_completion (u : InfinitePlace H) (c : F) :
    algebraMap E u.Completion (algebraMap F E c) = algebraMap F u.Completion c := by
  apply (InfinitePlace.Completion.equiv u).injective
  change (algebraMap E u.Completion (algebraMap F E c)).toCompletion =
    (algebraMap F u.Completion c).toCompletion
  rw [InfinitePlace.Completion.algebraMap_toCompletion, InfinitePlace.Completion.algebraMap_toCompletion,
    ← IsScalarTower.algebraMap_apply]

theorem completionMap_comp [w.LiesOver v] [u.LiesOver w] [u.LiesOver v] (x : v.Completion) :
    algebraMap w.Completion u.Completion (algebraMap v.Completion w.Completion x) =
      algebraMap v.Completion u.Completion x := by
  have key : (algebraMap w.Completion u.Completion).comp (algebraMap v.Completion w.Completion) =
      algebraMap v.Completion u.Completion := by
    refine RingHom.ext fun x => ?_
    have := DenseRange.equalizer (denseRange_algebraMap_completion v)
      (g := ⇑((algebraMap w.Completion u.Completion).comp (algebraMap v.Completion w.Completion)))
      (h := ⇑(algebraMap v.Completion u.Completion))
      (((NumberField.LiesOver.continuous_completionMap w u).comp
        (NumberField.LiesOver.continuous_completionMap v w)))
      (NumberField.LiesOver.continuous_completionMap v u) (by
        funext c
        simp only [Function.comp_apply, RingHom.coe_comp]
        rw [← IsScalarTower.algebraMap_apply F v.Completion w.Completion c,
          ← IsScalarTower.algebraMap_apply F v.Completion u.Completion c,
          IsScalarTower.algebraMap_apply F E w.Completion c,
          ← IsScalarTower.algebraMap_apply E w.Completion u.Completion,
          algebraMap_tower_completion u c])
    exact congrFun this x
  exact RingHom.congr_fun key x

instance [w.LiesOver v] [u.LiesOver w] [u.LiesOver v] :
    IsScalarTower v.Completion w.Completion u.Completion :=
  .of_algebraMap_eq fun x => (completionMap_comp v w u x).symm

/-- Transitivity of the local norm at infinite spots. -/
theorem localNormInf_tower [w.LiesOver v] [u.LiesOver w] [u.LiesOver v] (y : u.Completion) :
    localNormInf E v w (localNormInf H w u y) = localNormInf H v u y := by
  simp only [localNormInf_apply]
  exact Algebra.norm_norm

/-- The reindexing $\{\mathfrak U \mid \mathfrak p\} \simeq \bigsqcup_{\mathfrak P|\mathfrak p}\{\mathfrak U \mid
\mathfrak P\}$ at infinite spots. -/
def infSpotsOverSigma : InfSpotsOver H v ≃ Σ w : InfSpotsOver E v, InfSpotsOver H w.1 where
  toFun u :=
    have := u.2
    ⟨⟨u.1.comap (algebraMap E H), liesOver_comap_inf v u.1⟩, ⟨u.1, liesOver_of_comap_eq _ _ rfl⟩⟩
  invFun p :=
    have := p.1.2
    have := p.2.2
    ⟨p.2.1, liesOver_trans_inf v p.1.1 p.2.1⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨w, hw⟩, ⟨u, hu⟩⟩
    have : u.comap (algebraMap E H) = w := InfinitePlace.LiesOver.comap_eq u w
    subst this
    rfl

/-- The infinite component of the norm is transitive. -/
theorem infNormComp_tower (x : (u : InfinitePlace H) → u.Completion) :
    infNormComp (F := F) x v =
      infNormComp (F := F) (fun w : InfinitePlace E => infNormComp (F := E) x w) v := by
  unfold infNormComp
  simp only [map_prod]
  rw [← Fintype.prod_sigma' (fun (w : InfSpotsOver E v) (u : InfSpotsOver H w.1) =>
    localNormInf E v w.1 (localNormInf H w.1 u.1 (x u.1)))]
  refine Fintype.prod_equiv (infSpotsOverSigma v) _ _ fun u => ?_
  have := u.2
  have := liesOver_comap_inf (E := E) v u.1
  have : u.1.LiesOver (u.1.comap (algebraMap E H)) := liesOver_of_comap_eq _ _ rfl
  change _ = localNormInf E v (u.1.comap (algebraMap E H))
    (localNormInf H (u.1.comap (algebraMap E H)) u.1 (x u.1))
  rw [localNormInf_tower]

end Inf

/-- **The norm of an idèle in a tower** (O'Meara 1963, §64, p. 173): for $F \subseteq E \subseteq H$,
$N_{H/F}\mathfrak J = N_{E/F}(N_{H/E}\mathfrak J)$. -/
@[kb "omeara1963" "§64, p. 173 (tower F ⊆ E ⊆ H: N_{H/F} 𝔍 = N_{E/F}(N_{H/E} 𝔍))"]
theorem ideleNorm_tower (i : IdeleGroup (𝓞 H) H) :
    ideleNorm (F := F) (E := H) i = ideleNorm (F := F) (E := E) (ideleNorm (F := E) (E := H) i) := by
  apply Units.ext
  refine Prod.ext ?_ ?_
  · funext v
    exact infNormComp_tower v _
  · apply RestrictedProduct.ext
    intro v
    exact finNormComp_tower v _

/-- **$N_{H/F} J_H \subseteq N_{E/F} J_E$** (O'Meara 1963, §64, p. 173). -/
@[kb "omeara1963" "§64, p. 173 (N_{H/F} J_H ⊆ N_{E/F} J_E)"]
theorem range_ideleNorm_tower_le :
    (ideleNorm (F := F) (E := H)).range ≤ (ideleNorm (F := F) (E := E)).range := by
  rintro _ ⟨i, rfl⟩
  exact ⟨ideleNorm (F := E) (E := H) i, (ideleNorm_tower i).symm⟩

end QuadFormsKB.OMeara
