import QuadFormsKB.Tamagawa.Measure.Weil.BinaryTorusAdelic

/-!
# Splitting $T(\mathbb A) = T(F_\infty)\times T(\mathbb A_f)\cong G_\infty\times SO(V)(\mathbb A_f)$
**Layer:** number fields. $F$ is a number field, $D\in\mathcal O_F\setminus0$, $Q_0 = \langle1,D\rangle$ = `diagForm1 D`, $d = -D$ = `dD D`,
$E\otimes F_\infty$ = `QuadInf F d`, $E\otimes\mathbb A_f$ = `QuadFin F d`. Template: `PDMeasure`, for the
torus $T = R_{E/F}\mathbb G_m/\mathbb G_m$ in place of $PD^\times$.

**Defines**
* `TorInf D` $= (E\otimes F_\infty)^\times/F_\infty^\times$ and `TorFin D` $= (E\otimes\mathbb A_f)^\times/\mathbb A_f^\times$
  (quotient groups, quotient topology);
* **`torInfEquiv`** $: T(F_\infty)\cong_{\mathrm{top.\ grp.}} G_\infty$ (`GInfSO (diagForm1 D)`) and
  **`torFinEquiv`** $: T(\mathbb A_f)\cong SO(V)(\mathbb A_f)$ (`SOAf (diagForm1 D)`), from `torInf`, `torFin`
  (generic `quotientContinuousMulEquiv`);
* **`torSplit`** $: T(\mathbb A)\cong T(F_\infty)\times T(\mathbb A_f)$, and `torGammaSplit`, the image of $T(F)$.

**Proves**
* `torProdEquiv_torSplit` / `torAdeleEquiv_eq_prod_torSplit`: `torAdeleEquiv` $=$ (`torInfEquiv` $\times$ `torFinEquiv`) $\circ$ `torSplit`
  (on elements), and `torSplit_mk`: $\mathrm{torSplit}([z]) = ([z_\infty], [z_f])$;
* `map_torGammaSplit`: the product isomorphism carries `torGammaSplit` onto `GammaSOAdele (diagForm1 D)`.

Source: Weil 1982, §2.4 and §2.3 (product decomposition of the adelic points) [unverified locator]; Ono 1963 [unverified].
-/

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding IsDedekindDomain Topology Matrix

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.HilbertModular QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F : Type} [Field F] [NumberField F] (D : 𝓞 F)

/-- $T(F_\infty) = (E\otimes F_\infty)^\times/F_\infty^\times$ (quotient group with the quotient topology). -/
abbrev TorInf : Type := (QuadInf F (dD D))ˣ ⧸ (infScalarQ (dD D)).range

/-- $T(\mathbb A_f) = (E\otimes\mathbb A_f)^\times/\mathbb A_f^\times$ (quotient group with the quotient topology). -/
abbrev TorFin : Type := (QuadFin F (dD D))ˣ ⧸ (finScalarQ (dD D)).range

/-! ### Kernels of `torInf` and `torFin` -/

/-- $\mathrm{tor}_\infty(z) = 1$ iff $\mathrm{im}\,z = 0$. -/
theorem torInf_eq_one_iff (z : (QuadInf F (dD D))ˣ) : torInf D z = 1 ↔ (z : QuadInf F (dD D)).im = 0 := by
  constructor
  · intro h
    have h1 := h
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · have : torGLK (dD_map D (embedding_of_isReal w.2)) (Units.map (projQR (dD D) w).toMonoidHom z) = 1 :=
        congrArg (fun g : GInfSO (diagForm1 D) => ArchSO.incl _ (g.1 w)) h1
      exact (torGLK_eq_one_iff _ _).1 this
    · have : torGLK (dD_map D w.1.embedding) (Units.map (projQC (dD D) w).toMonoidHom z) = 1 :=
        congrArg (fun g : GInfSO (diagForm1 D) => ArchSOC.incl _ (g.2 w)) h1
      exact (torGLK_eq_one_iff _ _).1 this
  · intro h
    refine Prod.ext (funext fun w => archSO_ext ?_) (funext fun w => archSOC_ext' ?_)
    · exact (torGLK_eq_one_iff (dD_map D (embedding_of_isReal w.2)) _).2 (by
        show (z : QuadInf F (dD D)).im.1 w = 0
        rw [h]; rfl)
    · exact (torGLK_eq_one_iff (dD_map D w.1.embedding) _).2 (by
        show (z : QuadInf F (dD D)).im.2 w = 0
        rw [h]; rfl)

/-- $\mathrm{tor}_f(z) = 1$ iff $\mathrm{im}\,z = 0$. -/
theorem torFin_eq_one_iff (z : (QuadFin F (dD D))ˣ) : torFin D z = 1 ↔ (z : QuadFin F (dD D)).im = 0 := by
  constructor
  · intro h
    refine Subtype.ext (funext fun v => ?_)
    have : torGLK (dD_algebraMap D (v.adicCompletion F)) (unitAtD (dD D) v z) = 1 :=
      congrArg (fun g : SOAf (diagForm1 D) =>
        (((g : OAf (formF (diagForm1 D))) v : orthGroup (formF (diagForm1 D)) (v.adicCompletion F)) :
          GL (Fin 2) (v.adicCompletion F))) h
    exact (torGLK_eq_one_iff _ _).1 this
  · intro h
    ext v : 2
    refine Subtype.ext ((torGLK_eq_one_iff (dD_algebraMap D (v.adicCompletion F)) _).2 ?_)
    show (z : QuadFin F (dD D)).im v = 0
    rw [h]; rfl

theorem ker_torInf : (torInf D).ker = (infScalarQ (dD D)).range := by
  ext z
  rw [MonoidHom.mem_ker, torInf_eq_one_iff]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := exists_scalar_of_im_eq_zero z h
    exact ⟨c, hc⟩
  · rintro ⟨c, rfl⟩
    rfl

theorem ker_torFin : (torFin D).ker = (finScalarQ (dD D)).range := by
  ext z
  rw [MonoidHom.mem_ker, torFin_eq_one_iff]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := exists_scalar_of_im_eq_zero z h
    exact ⟨c, hc⟩
  · rintro ⟨c, rfl⟩
    rfl

/-! ### $T(F_\infty)\cong G_\infty$ and $T(\mathbb A_f)\cong SO(V)(\mathbb A_f)$ -/

/-- **$T(F_\infty) = (E\otimes F_\infty)^\times/F_\infty^\times\cong G_\infty = \prod_wSO(Q^w)(F_w)$** as topological groups
($D\ne0$). -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
def torInfEquiv (hD : D ≠ 0) : TorInf D ≃ₜ* GInfSO (diagForm1 D) :=
  quotientContinuousMulEquiv (torInf D) _ (ker_torInf D) (torInf_surjective D hD) (continuous_torInf D)
    (MonoidHom.isOpenMap_of_sigmaCompact _ (torInf_surjective D hD) (continuous_torInf D))

/-- **$T(\mathbb A_f) = (E\otimes\mathbb A_f)^\times/\mathbb A_f^\times\cong SO(V)(\mathbb A_f)$** as topological groups
($D\ne0$). -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
def torFinEquiv (hD : D ≠ 0) : TorFin D ≃ₜ* SOAf (diagForm1 D) :=
  quotientContinuousMulEquiv (torFin D) _ (ker_torFin D) (torFin_surjective D hD) (continuous_torFin D)
    (MonoidHom.isOpenMap_of_sigmaCompact _ (torFin_surjective D hD) (continuous_torFin D))

theorem torInfEquiv_mk (hD : D ≠ 0) (z : (QuadInf F (dD D))ˣ) :
    torInfEquiv D hD (QuotientGroup.mk z) = torInf D z := rfl

theorem torFinEquiv_mk (hD : D ≠ 0) (z : (QuadFin F (dD D))ˣ) :
    torFinEquiv D hD (QuotientGroup.mk z) = torFin D z := rfl

/-- The product isomorphism $T(F_\infty)\times T(\mathbb A_f)\cong SO(V)(\mathbb A)$. -/
def torProdEquiv (hD : D ≠ 0) : TorInf D × TorFin D ≃ₜ* SOAdele (diagForm1 D) where
  toMulEquiv := (torInfEquiv D hD).toMulEquiv.prodCongr (torFinEquiv D hD).toMulEquiv
  continuous_toFun := (torInfEquiv D hD).continuous.prodMap (torFinEquiv D hD).continuous
  continuous_invFun := (torInfEquiv D hD).symm.continuous.prodMap (torFinEquiv D hD).symm.continuous

/-- **$T(\mathbb A)\cong T(F_\infty)\times T(\mathbb A_f)$** as topological groups ($D\ne0$). -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
def torSplit (hD : D ≠ 0) : TorA D ≃ₜ* TorInf D × TorFin D :=
  (torAdeleEquiv D hD).trans (torProdEquiv D hD).symm

/-- **Compatibility:** `torAdeleEquiv` $=$ (`torInfEquiv` $\times$ `torFinEquiv`) $\circ$ `torSplit`, on elements. -/
theorem torProdEquiv_torSplit (hD : D ≠ 0) (x : TorA D) :
    torProdEquiv D hD (torSplit D hD x) = torAdeleEquiv D hD x :=
  (torProdEquiv D hD).apply_symm_apply _

/-- **Compatibility, in the form stated in the plan:** $\Phi = (\Phi_\infty\times\Phi_f)\circ\mathrm{torSplit}$. -/
theorem torAdeleEquiv_eq_prod_torSplit (hD : D ≠ 0) (x : TorA D) :
    torAdeleEquiv D hD x =
      ((torInfEquiv D hD).toMulEquiv.prodCongr (torFinEquiv D hD).toMulEquiv) (torSplit D hD x) :=
  (torProdEquiv_torSplit D hD x).symm

/-- $\mathrm{torSplit}([z]) = ([z_\infty], [z_f])$ for $z\in(E\otimes\mathbb A_F)^\times$. -/
theorem torSplit_mk (hD : D ≠ 0) (z : (QuadAdele F (dD D))ˣ) :
    torSplit D hD (torMk D z) =
      (QuotientGroup.mk (quadUnitsSplit (dD D) z).1, QuotientGroup.mk (quadUnitsSplit (dD D) z).2) := by
  apply (torProdEquiv D hD).injective
  rw [torProdEquiv_torSplit]
  rfl

/-- **$T(F)$ inside $T(F_\infty)\times T(\mathbb A_f)$.** -/
def torGammaSplit (hD : D ≠ 0) : Subgroup (TorInf D × TorFin D) :=
  (torGamma D).map (torSplit D hD).toMulEquiv.toMonoidHom

/-- **The product isomorphism carries $T(F)$ onto $SO(V)(F)$** (`GammaSOAdele`). -/
@[kb "weil1982" "§2.4, p. 23 [unverified]"]
theorem map_torGammaSplit (hD : D ≠ 0) :
    (torGammaSplit D hD).map ((torInfEquiv D hD).toMulEquiv.prodCongr (torFinEquiv D hD).toMulEquiv).toMonoidHom =
      GammaSOAdele (diagForm1 D) := by
  rw [torGammaSplit, Subgroup.map_map, ← map_torGamma D hD]
  congr 1
  refine MonoidHom.ext fun x => ?_
  exact (torProdEquiv D hD).apply_symm_apply _

end QuadFormsKB.Tamagawa.Measure.Weil
