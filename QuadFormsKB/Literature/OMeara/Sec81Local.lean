/-
# O'Meara §81E: the laws of localization for ideals and lattices

**Setting.** As in `Sec82Local.lean`: $R$ is a Dedekind domain with fraction field $F$, $V$ a finite-dimensional
vector space over $F$, and for a prime $\mathfrak p$ of $R$ the localizations $\mathfrak a_{\mathfrak p}$
(`locIdeal p a`) and $L_{\mathfrak p}$ (`locLat p L`) are taken at the localization $\mathfrak o_{\mathfrak p}$ of $R$
inside $F$ (`locRing F p`), not at the completion $F_{\mathfrak p}$ as in O'Meara (§81E, pp. 216–218); see the module
docstring of `Sec82Local.lean` for this deviation. Fractional ideals are non-zero finitely generated $R$-submodules of
$F$; the laws below hold for all $R$-submodules of $F$.

**Proves** (O'Meara 1963, §81E, pp. 217–218):
* `locIdeal_span_singleton_mul`, `locIdeal_mul` (in `Sec82Local.lean`), `locIdeal_inf`, `locIdeal_sup`: the laws
  $(\alpha\mathfrak a)_{\mathfrak p} = \alpha\mathfrak a_{\mathfrak p}$,
  $(\mathfrak a\mathfrak b)_{\mathfrak p} = \mathfrak a_{\mathfrak p}\mathfrak b_{\mathfrak p}$,
  $(\mathfrak a \cap \mathfrak b)_{\mathfrak p} = \mathfrak a_{\mathfrak p} \cap \mathfrak b_{\mathfrak p}$,
  $(\mathfrak a + \mathfrak b)_{\mathfrak p} = \mathfrak a_{\mathfrak p} + \mathfrak b_{\mathfrak p}$ (p. 217).
  O'Meara's last law $|\mathfrak a_{\mathfrak p}|_{\mathfrak p} = |\mathfrak a|_{\mathfrak p}$ concerns the valuation of
  the completion and is not stated here.
* `subset_locIdeal`, `eq_iInf_locIdeal`, `le_iff_forall_locIdeal_le`, `eq_iff_forall_locIdeal_eq`:
  $\mathfrak a \subseteq \mathfrak a_{\mathfrak p}$, $\mathfrak a = \bigcap_{\mathfrak p}(F \cap \mathfrak a_{\mathfrak p})$,
  and inclusion and equality of ideals are local (p. 217).
* `locLat_sup` ($(L + K)_{\mathfrak p} = L_{\mathfrak p} + K_{\mathfrak p}$), `locLat_smul_span_singleton`
  ($(\mathfrak ax)_{\mathfrak p} = \mathfrak a_{\mathfrak p}x$); the formula for
  $(\mathfrak a_1z_1 + \cdots + \mathfrak a_rz_r)_{\mathfrak p}$ is `locLat_iSup_smul` of `Sec82Local.lean` (p. 218).
-/
import QuadFormsKB.Literature.OMeara.Sec82Local

open Submodule Module

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace QuadFormsKB.OMeara

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]

variable (p : Ideal R) [p.IsPrime]

/-- **$(\alpha\mathfrak a)_{\mathfrak p} = \alpha\mathfrak a_{\mathfrak p}$** (O'Meara 1963, §81E, p. 217), for
$\alpha \in F$ and an $R$-submodule $\mathfrak a$ of $F$; localization at $\mathfrak o_{\mathfrak p} \subseteq F$. -/
@[kb "omeara1963" "§81E, p. 217 ((αa)_p = α a_p; here at the localization of o)"]
theorem locIdeal_span_singleton_mul (α : F) (a : Submodule R F) :
    locIdeal p (span R {α} * a) = span (locRing F p) {α} * locIdeal p a := by
  rw [locIdeal_mul, locIdeal_span_singleton]

/-- **$(\mathfrak a + \mathfrak b)_{\mathfrak p} = \mathfrak a_{\mathfrak p} + \mathfrak b_{\mathfrak p}$**
(O'Meara 1963, §81E, p. 217); localization at $\mathfrak o_{\mathfrak p} \subseteq F$. -/
@[kb "omeara1963" "§81E, p. 217 ((a + b)_p = a_p + b_p; here at the localization of o)"]
theorem locIdeal_sup (a b : Submodule R F) : locIdeal p (a ⊔ b) = locIdeal p a ⊔ locIdeal p b := by
  have h : a ⊔ b = span R ((a : Set F) ∪ b) := by rw [Submodule.span_union, span_eq, span_eq]
  unfold locIdeal
  rw [h, span_locRing_span, Submodule.span_union]

/-- **$(\mathfrak a \cap \mathfrak b)_{\mathfrak p} = \mathfrak a_{\mathfrak p} \cap \mathfrak b_{\mathfrak p}$**
(O'Meara 1963, §81E, p. 217); localization at $\mathfrak o_{\mathfrak p} \subseteq F$. -/
@[kb "omeara1963" "§81E, p. 217 ((a ∩ b)_p = a_p ∩ b_p; here at the localization of o)"]
theorem locIdeal_inf (a b : Submodule R F) : locIdeal p (a ⊓ b) = locIdeal p a ⊓ locIdeal p b := by
  refine le_antisymm (le_inf (locIdeal_mono p inf_le_left) (locIdeal_mono p inf_le_right)) ?_
  rintro x ⟨hxa, hxb⟩
  obtain ⟨t, ht⟩ := exists_smul_mem_of_mem_locSpan p hxa
  obtain ⟨t', ht'⟩ := exists_smul_mem_of_mem_locSpan p hxb
  refine mem_locLat_of_smul_mem (V := F) p (t * t') ⟨?_, ?_⟩
  · rw [Submonoid.coe_mul, mul_comm, mul_smul]; exact a.smul_mem _ ht
  · rw [Submonoid.coe_mul, mul_smul]; exact b.smul_mem _ ht'

/-- **$\mathfrak a \subseteq \mathfrak a_{\mathfrak p}$** (O'Meara 1963, §81E, p. 217). -/
@[kb "omeara1963" "§81E, p. 217 (a ⊆ a_p; here at the localization of o)"]
theorem subset_locIdeal (a : Submodule R F) : (a : Set F) ⊆ locIdeal p a :=
  subset_span

omit [p.IsPrime] in
/-- **$\mathfrak a = \bigcap_{\mathfrak p}(F \cap \mathfrak a_{\mathfrak p})$** (O'Meara 1963, §81E, p. 217): an
$R$-submodule of $F$ is the intersection of its localizations at the maximal ideals $\mathfrak p$ of $R$ (here the
localizations already lie in $F$, so "$F \cap$" is not needed). -/
@[kb "omeara1963" "§81E, p. 217 (a = ∩ (F ∩ a_p); here at the localization of o)"]
theorem eq_iInf_locIdeal (a : Submodule R F) :
    a = ⨅ (q : Ideal R) (_ : q.IsMaximal), (locIdeal (F := F) q a).restrictScalars R := by
  refine le_antisymm (le_iInf₂ fun q _ => subset_locIdeal q a) fun x hx => ?_
  by_contra hxa
  let I : Ideal R := a.comap (LinearMap.toSpanSingleton R F x)
  have hI : I ≠ ⊤ := by
    intro h1
    apply hxa
    have : (1 : R) ∈ I := h1 ▸ Submodule.mem_top
    simpa [I] using this
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  have hx' : x ∈ locIdeal (F := F) m a := by
    have := (Submodule.mem_iInf _).1 hx m
    exact (Submodule.mem_iInf _).1 this hm
  obtain ⟨t, ht⟩ := exists_smul_mem_of_mem_locSpan m hx'
  exact t.2 (hIm ht)

omit [p.IsPrime] in
/-- **$\mathfrak a \subseteq \mathfrak b$ if and only if $\mathfrak a_{\mathfrak p} \subseteq \mathfrak b_{\mathfrak p}$
for all $\mathfrak p$** (O'Meara 1963, §81E, p. 217), $\mathfrak p$ running over the maximal ideals of $R$. -/
@[kb "omeara1963" "§81E, p. 217 (a ⊆ b iff a_p ⊆ b_p for all p; here at the localization of o)"]
theorem le_iff_forall_locIdeal_le {a b : Submodule R F} :
    a ≤ b ↔ ∀ (q : Ideal R) [q.IsMaximal], locIdeal (F := F) q a ≤ locIdeal q b :=
  ⟨fun h q _ => locIdeal_mono q h, le_of_forall_locIdeal_le⟩

omit [p.IsPrime] in
/-- **$\mathfrak a = \mathfrak b$ if and only if $\mathfrak a_{\mathfrak p} = \mathfrak b_{\mathfrak p}$ for all
$\mathfrak p$** (O'Meara 1963, §81E, p. 217), $\mathfrak p$ running over the maximal ideals of $R$. -/
@[kb "omeara1963" "§81E, p. 217 (a = b iff a_p = b_p for all p; here at the localization of o)"]
theorem eq_iff_forall_locIdeal_eq {a b : Submodule R F} :
    a = b ↔ ∀ (q : Ideal R) [q.IsMaximal], locIdeal (F := F) q a = locIdeal q b :=
  ⟨fun h _ _ => h ▸ rfl, eq_of_forall_locIdeal_eq⟩

/-- **$(L + K)_{\mathfrak p} = L_{\mathfrak p} + K_{\mathfrak p}$** (O'Meara 1963, §81E, p. 218) for $R$-submodules
(in particular lattices) $L$, $K$ of $V$; localization at $\mathfrak o_{\mathfrak p} \subseteq F$. -/
@[kb "omeara1963" "§81E, p. 218 ((L + K)_p = L_p + K_p; here at the localization of o)"]
theorem locLat_sup (L K : Submodule R V) :
    locLat (F := F) p (L ⊔ K) = locLat p L ⊔ locLat p K := by
  have h : L ⊔ K = span R ((L : Set V) ∪ K) := by rw [Submodule.span_union, span_eq, span_eq]
  unfold locLat
  rw [h, span_locRing_span, Submodule.span_union]

/-- **$(\mathfrak ax)_{\mathfrak p} = \mathfrak a_{\mathfrak p}x$** (O'Meara 1963, §81E, p. 218) for an
$R$-submodule $\mathfrak a$ of $F$ and $x \in V$; localization at $\mathfrak o_{\mathfrak p} \subseteq F$. -/
@[kb "omeara1963" "§81E, p. 218 ((ax)_p = a_p x; here at the localization of o)"]
theorem locLat_smul_span_singleton (a : Submodule R F) (x : V) :
    locLat (F := F) p (a • span R {x}) = locIdeal p a • span (locRing F p) {x} := by
  have h := locLat_iSup_smul (F := F) p (fun _ : Unit => a) (fun _ => x)
  simpa using h

end QuadFormsKB.OMeara
