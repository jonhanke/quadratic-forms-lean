/-
# Conway–Sloane, Ch. 15, §9: the spinor operators and the one-spinor-genus criterion

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9, pp. 388–393
(`conwaysloane1999`).

**Layer.** An integer-valued form $f$ = `f : QuadForm ℤ n`, $n \ge 3$, the rational space $V = (\mathbb Q^n, f)$
(`f.map (Int.castRingHom ℚ)`), the lattice $\Lambda = \mathbb Z^n$ (`stdLat`), and a finite set $P$ of primes of
$\mathbb Q$ (as `HeightOneSpectrum (𝓞 ℚ)`) containing every prime dividing $2\det H$, where $H$ is the Hessian of $f$
(`hPd`). Conway–Sloane's set $\Pi$ (§9.4, p. 390: "any finite set of primes that contains $-1$, $2$ and all primes
dividing $d$") is $P \cup \{-1\}$; for a classically integral form with Gram matrix $A$, $\det H = 2^n\det A$, so the
primes dividing $2\det H$ are $2$ and the primes dividing $d = \det A$.

The spinor genera of Conway–Sloane are Cassels' (proper) spinor genera `SameProperSpinorGenus` (§9.1, p. 388:
Conway–Sloane follow Cassels, Ch. 11; Cassels' spinor genus uses the rotation group $O^+$). Their spinor operators are
the elements of Cassels' group $G = R/ST$ (`CasselsG`, Cassels Ch. 11, (3.15)), which acts simply transitively on the
spinor genera of the genus (Cassels, Thm. 3.1, `casselsAct_*`); see `Section9Kernel.lean` for the names
$\Delta(r)$, $\Delta_p(A)$ of (37), (38) and the spinor kernel.

**Proves**
* `mem_localSpinorNormGroup_std_iff_of_not_mem`: for $p \notin P$, $\theta(\Lambda_p) = U_p\mathbb Q_p^{\times2}$
  (Cassels' condition (3.7) on $P$; $\Lambda_p$ is unimodular at $p \nmid 2\det H$).
* `sameProperSpinorGenus_of_casselsX_le`: if every family $(x_p)_{p \in P}$ of $p$-adic units lies in $ST$ (that is,
  every spinor operator named by units is in the spinor kernel, Cassels' $Y = X$), then the genus of $\Lambda$ is a
  single spinor genus.
* `intEquiv_of_sameGenus_of_casselsX_le`: if moreover $f$ is indefinite, every form in the (Siegel) genus of $f$ is
  integrally equivalent to $f$ (Eichler's theorem, Conway–Sloane's Thm. 14, in the form of Cassels Ch. 11, Thm. 1.4).
-/
import QuadFormsKB.Literature.ConwaySloane.Spinor
import QuadFormsKB.Literature.Cassels.Ch11Sec3Thm
import QuadFormsKB.Literature.Cassels.Ch11Sec3GroupY
import QuadFormsKB.Literature.Cassels.Ch11Sec6Subst
import QuadFormsKB.Literature.Cassels.Ch9Examples

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices



variable {n : ℕ}

/-- The prime number $p$ of a finite place $v$ of $\mathbb Q$. -/
abbrev primeOf (v : HeightOneSpectrum (𝓞 ℚ)) : ℕ := Rat.HeightOneSpectrum.natGenerator v

/-- **Cassels' condition (3.7) for $\Lambda = \mathbb Z^n$**: at a prime $p \nmid 2\det H$ the lattice $\Lambda_p$ is
unimodular and $\theta(\Lambda_p) = U_p\mathbb Q_p^{\times 2}$ (Cassels, Ch. 11, (3.7), p. 208; Lemma 3.7). -/
@[kb "conwaysloane1999" "Ch. 15, §9.6, p. 392 (irrelevant primes: the p-adically automorphous numbers are exactly the unit classes)"]
theorem mem_localSpinorNormGroup_std_iff_of_not_dvd (hn : 2 ≤ n) (f : QuadForm ℤ n)
    (hQ : (f.map (Int.castRingHom ℚ)).Nondegenerate) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ¬ ((primeOf v : ℕ) : ℤ) ∣ 2 * f.hessian.det) (u : (v.adicCompletion ℚ)ˣ) :
    u ∈ localSpinorNormGroup (f.map (Int.castRingHom ℚ)) hQ v stdLat ↔ IsUnitSqClass v (SqClass.mk u) := by
  have h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal := by
    rw [two_mem_iff_natGenerator]
    intro h
    apply hv
    rw [show primeOf v = 2 from h]
    exact dvd_mul_right _ _
  have hd : ¬ ((primeOf v : ℕ) : ℤ) ∣ f.hessian.det := fun h => hv (dvd_mul_of_dvd_right h _)
  have hL : loc v (stdLat : Lat ℚ n).1 = std v := loc_intVec v
  have hγ : loc v (stdLat : Lat ℚ n).1 = locAct v (1 : GL (Fin n) (v.adicCompletion ℚ)) (std v) := by
    rw [locAct_one]; exact hL
  have hint : ∀ x ∈ loc v (stdLat : Lat ℚ n).1,
      Valued.v ((f.map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) x) ≤ 1 := by
    intro x hx; rw [hL] at hx; exact valued_evalIn_le_one_int v f hx
  have hdet : Valued.v (locGram (f.map (Int.castRingHom ℚ)) v 1).det = 1 := by
    rw [locGram_one_int_det]
    exact valued_intCast_eq_one v _ hd
  exact mem_localSpinorNormGroup_iff_of_unimodular (f.map (Int.castRingHom ℚ)) v hQ h2 hn stdLat 1 hγ
    (by convert hint; exact Subsingleton.elim _ _) hdet u

/-- Cassels' condition (3.7) for $\Lambda = \mathbb Z^n$ and a set $P$ containing the primes dividing $2\det H$
(Conway–Sloane's $\Pi$, §9.4: "any finite set of primes that contains $-1$, $2$ and all primes dividing $d$"; the
primes outside $\Pi$ are irrelevant). -/
@[kb "conwaysloane1999" "Ch. 15, §9.4, p. 390 (the set Π of primes)"]
theorem casselsCond_std (hn : 2 ≤ n) (f : QuadForm ℤ n) (hQ : (f.map (Int.castRingHom ℚ)).Nondegenerate)
    (P : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hPd : ∀ v, v ∉ P → ¬ ((primeOf v : ℕ) : ℤ) ∣ 2 * f.hessian.det) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ P → ∀ u : (v.adicCompletion ℚ)ˣ,
      u ∈ localSpinorNormGroup (f.map (Int.castRingHom ℚ)) hQ v stdLat ↔ IsUnitSqClass v (SqClass.mk u) :=
  fun v hv u => mem_localSpinorNormGroup_std_iff_of_not_dvd hn f hQ v (hPd v hv) u

section Criterion

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (L : Lat ℚ n) (P : Finset (HeightOneSpectrum (𝓞 ℚ)))

/-- If every element of $X = \prod_{p\in P}U_p$ lies in $ST$, then $ST = R$ (by $R = XT$), i.e. $G$ is trivial. -/
theorem casselsST_eq_top_of_casselsX_le (hn : 3 ≤ n) (hX : casselsX P ≤ casselsST Q hQ L P) :
    casselsST Q hQ L P = ⊤ := by
  refine eq_top_iff.mpr fun r _ => ?_
  obtain ⟨x, hx, t, ht, rfl⟩ := exists_casselsX_mul_casselsT Q hQ P hn r
  exact (casselsST Q hQ L P).mul_mem (hX hx) (Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩))

/-- **One spinor genus when the spinor kernel contains every unit operator** (Conway–Sloane §9.6–9.7; Cassels Ch. 11,
(3.35) and Lemma 3.5, Cor.): if every family of $p$-adic units $(x_p)_{p \in P}$ lies in $ST$ (Cassels' $Y = X$), then
every lattice in the genus of $L$ is in the (proper) spinor genus of $L$. -/
theorem sameProperSpinorGenus_of_casselsX_le (hn : 3 ≤ n)
    (hP : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ P → ∀ u : (v.adicCompletion ℚ)ˣ,
      u ∈ localSpinorNormGroup Q hQ v L ↔ IsUnitSqClass v (SqClass.mk u))
    (hX : casselsX P ≤ casselsST Q hQ L P) {M : Lat ℚ n} (hM : SameGenus Q L.1 M.1) :
    SameProperSpinorGenus Q L M := by
  classical
  let _ : MulAction (OAf Q) (Lat ℚ n) := latAction Q
  obtain ⟨Γ, hMΓ, β, rfl, hβ, -, hβ1, -⟩ := exists_sameProperSpinorGenus_casselsForm_rat Q hQ hn L P hP hM
  have hx : ∀ v : P, ∃ x : (v.1.adicCompletion ℚ)ˣ,
      SqClass.mk x = spinorNorm Q (v.1.adicCompletion ℚ) (β v) := fun v =>
    QuotientGroup.mk_surjective _
  choose x hx using hx
  have htop := casselsST_eq_top_of_casselsX_le Q hQ L P hn hX
  have hxx : (QuotientGroup.mk x : CasselsG Q hQ L P) = QuotientGroup.mk 1 := by
    rw [QuotientGroup.eq, htop]; trivial
  have h1 : ∀ v : P, SqClass.mk ((1 : CasselsR P) v) = spinorNorm Q (v.1.adicCompletion ℚ) ((1 : OAf Q) v) := by
    intro v
    rw [show ((1 : OAf Q) v) = 1 from rfl, ← spinorNormHom_apply Q _ hQ, map_one]
    rfl
  have key := sameProperSpinorGenus_casselsShift Q hQ L P hP (SameGenus.refl Q L.1) (fun _ _ => rfl)
    (fun _ _ => rfl) (SameProperSpinorGenus.refl Q L) β 1 hβ (fun v => (Tamagawa.soSub Q _).one_mem) hβ1
    (fun _ _ => rfl) x 1 hx h1 hxx
  have e : latSMul Q (1 : OAf Q) L = L := one_smul (OAf Q) L
  rw [e] at key
  exact SameProperSpinorGenus.trans Q (SameProperSpinorGenus.symm Q key) (SameProperSpinorGenus.symm Q hMΓ)

end Criterion

/-- **From one spinor genus to one class, for forms** (Eichler's theorem, Conway–Sloane's Thm. 14, as Cassels Ch. 11,
Thm. 1.4, `isProperIsometric_of_sameProperSpinorGenus`; transport as in Cassels Ch. 11, Lemma 1.1, Cor. 2): if $f$ is an
indefinite integer-valued form in $n \ge 3$ variables and every lattice in the genus of $\mathbb Z^n$ is in its spinor
genus, then every form of the genus of $f$ is integrally equivalent to $f$. -/
theorem intEquiv_of_sameGenus_of_oneSpinorGenus (hn : 3 ≤ n) (f : QuadForm ℤ n) (hf : f.hessian.det ≠ 0)
    (hind : IsIndefinite (f.map (Int.castRingHom ℚ)))
    (hone : ∀ M : Lat ℚ n, SameGenus (f.map (Int.castRingHom ℚ)) (stdLat : Lat ℚ n).1 M.1 →
      SameProperSpinorGenus (f.map (Int.castRingHom ℚ)) stdLat M)
    (f' : QuadForm ℤ n) (h : Siegel.SameGenus f f') : Siegel.IntEquiv f f' := by
  have hd := h.hessian_det_eq
  have hQ := isometricGL_rat_of_sameGenus f f' hd hf h
  obtain ⟨γ, hγ1, hFγ⟩ := exists_pos_det_one f f' (by omega) hd hf hQ
  have hgen := sameGenus_latOf_of_sameGenus hFγ h
  have e1 : latOf (1 : GL (Fin n) ℚ) = (stdLat : Lat ℚ n).1 := by
    rw [latOf, glImage_one]; rfl
  rw [e1] at hgen
  have hQnd := nondegenerate_map_of_det_ne_zero f hf
  obtain ⟨σ, hσ, hσL⟩ := isProperIsometric_of_sameProperSpinorGenus (f.map (Int.castRingHom ℚ)) hn hQnd hind
    (hone ⟨latOf γ, latOf_isLattice γ⟩ hgen)
  have hσ1 : ((σ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det = 1 := hσ
  have hlat : latOf γ = latOf (σ : GL (Fin n) ℚ) := by
    rw [latOf]
    exact hσL.symm
  obtain ⟨U, hUdet, hU⟩ := exists_unimod_of_latOf_eq (γ := γ) (δ := (σ : GL (Fin n) ℚ))
    (by rw [hγ1]; exact one_pos) (by rw [hσ1]; exact one_pos) hlat
  have hFσ : FormOf f (σ : GL (Fin n) ℚ) f := fun x => by
    have := evalIn_mulVec_of_mem (f.map (Int.castRingHom ℚ)) σ.2 x
    rw [map_evalIn_rat, map_evalIn_rat] at this
    exact this.symm
  have key := eval_eq_of_latOf_eq f hFγ hFσ hU
  exact (Siegel.isometricGL_iff_isometricIn _ _).mpr
    ⟨U, by rw [hUdet]; exact isUnit_one, fun x => (key x).symm⟩

/-- **One class in the genus when the spinor kernel contains every unit operator**: for an indefinite integer-valued
form $f$ in $n \ge 3$ variables and a finite set $P$ of primes containing those dividing $2\det H$, if every family of
units $(x_p)_{p \in P}$ lies in Cassels' $ST$, then every form of the genus of $f$ is integrally equivalent to $f$. -/
theorem intEquiv_of_sameGenus_of_casselsX_le (hn : 3 ≤ n) (f : QuadForm ℤ n) (hf : f.hessian.det ≠ 0)
    (hind : IsIndefinite (f.map (Int.castRingHom ℚ))) (P : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hPd : ∀ v, v ∉ P → ¬ ((primeOf v : ℕ) : ℤ) ∣ 2 * f.hessian.det)
    (hX : casselsX P ≤ casselsST (f.map (Int.castRingHom ℚ)) (nondegenerate_map_of_det_ne_zero f hf) stdLat P)
    (f' : QuadForm ℤ n) (h : Siegel.SameGenus f f') : Siegel.IntEquiv f f' :=
  intEquiv_of_sameGenus_of_oneSpinorGenus hn f hf hind (fun _ hM =>
    sameProperSpinorGenus_of_casselsX_le _ _ _ P hn
      (casselsCond_std (by omega) f (nondegenerate_map_of_det_ne_zero f hf) P hPd) hX hM) f' h

end QuadFormsKB.ConwaySloane
