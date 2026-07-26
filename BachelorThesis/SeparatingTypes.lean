import Mathlib

set_option linter.style.header false
set_option linter.style.whitespace false

namespace FirstOrder
namespace Language
namespace Theory

open FirstOrder
open FirstOrder.Language
open Formula

noncomputable section SeparatingTypes

universe u v w u' v' w'
variable {L : Language.{u,v}} {α : Type*}

/-- If `T` is an L-theory and `φ` and `ψ` are L-formulas and `T` models `φ ⊓ ψ`,
then `T` models `ψ ⊓ φ`. -/
lemma modelsBoundedFormula_inf_symm₁ [Finite α] (T : L.Theory)
   (φ ψ : L.Formula α) :
  T ⊨ᵇ (φ ⊓ ψ) → T ⊨ᵇ (ψ ⊓ φ) := by {
    unfold ModelsBoundedFormula
    simp_all only [BoundedFormula.realize_inf, Fin.forall_fin_zero_pi, and_self, implies_true]
  }

/-- If `T` is an L-theory and `φ` and `ψ` are L-formulas,
`T` models `φ ⊓ ψ` if and only if `T` models `ψ ⊓ φ`. -/
lemma modelsFormula_inf_symm {α : Type*} [Finite α] (T : L.Theory) (φ ψ : L.Formula α) :
  T ⊨ᵇ (φ ⊓ ψ) ↔ T ⊨ᵇ (ψ ⊓ φ) :=
    ⟨ modelsBoundedFormula_inf_symm₁ T φ ψ, modelsBoundedFormula_inf_symm₁ T ψ φ ⟩

/-- If `T` is an L-theory and `φ` and `ψ` are L-formulas and `T` models `φ.iff ψ`,
then `T` models `ψ.iff φ`. -/
lemma modelsBoundedFormula_iff_symm₁ {α : Type*} [Finite α] (T : L.Theory) (φ ψ : L.Formula α) :
  T ⊨ᵇ φ.iff ψ → T ⊨ᵇ ψ.iff φ := by {
    unfold Formula.iff; unfold BoundedFormula.iff
    exact fun a => modelsBoundedFormula_inf_symm₁ T (φ ⟹ ψ) (ψ ⟹ φ) a
  }

/-- If `T` is an L-Theory and `φ` and `ψ` are L-formulas,
then `T` models `φ.iff ψ` if and only if `T` models `ψ.iff φ`. -/
lemma modelsBoundedFormula_iff_symm {α : Type*} [Finite α] (T : L.Theory) (φ ψ : L.Formula α) :
  T ⊨ᵇ (φ.iff ψ) ↔ T ⊨ᵇ (ψ.iff φ) :=
    ⟨ modelsBoundedFormula_iff_symm₁ T φ ψ,  modelsBoundedFormula_iff_symm₁ T ψ φ ⟩

#check Sentence.realize_imp

/-- If `T` is an L-theory and `φ` an L-sentence,
`T ∪ {φ}` models `ψ` if and only if `T` models `φ → ψ`. -/
-- Note: This is Lemma 3.4 in the Thesis
lemma exist_models_iff_models_imp (T : L.Theory) (φ : L.Sentence) (ψ : L.Sentence) :
  (T ∪ {φ}) ⊨ᵇ ψ ↔ T ⊨ᵇ (φ.imp ψ) := by
    constructor
    · -- Suppose `T ∪ {φ} ⊨ᵇ ψ`.
      intro hTφ
      -- Let `M` be a model of `T`.
      apply models_sentence_iff.2
      intro M
      -- Suppose `M ⊨ φ`. We need to show `M ⊨ ψ`.
      apply (Sentence.realize_imp M).2
      intro hM
      -- Since `M ⊨ T` and `M ⊨ φ`, we have `M ⊨ (T ∪ {φ})`.
      have hM' : M ⊨ T ∪ {φ} := {
        realize_of_mem := by {
          intro φ' hφ'
          obtain hφ'₁ | hφ'₂ := hφ'
          · exact M.is_model.realize_of_mem φ' hφ'₁
          · have this : φ' = φ := ((fun a ↦ hφ'₂) ∘ T) φ
            rwa [this]
        }
      }
      -- Hence, by assumption, it follows that `M ⊨ ψ`.
      exact ModelsBoundedFormula.realize_sentence hTφ M
    · -- Now, suppose `T ⊨ᵇ (φ → ψ)`
      intro hT
      -- Let `M` be a model of `T ∪ {φ}`. We need to prove `M ⊨ ψ`.
      apply models_sentence_iff.2; apply models_sentence_iff.1 at hT
      intro M
      -- By assumption, we have `M ⊨ T`...
      have hM : M ⊨ T := {
        realize_of_mem := by
          intro φ' hφ'
          exact M.is_model.realize_of_mem φ' (Set.mem_union_left {φ} hφ')
      }
      -- ...and `M ⊨ φ`.
      have hM' : M ⊨ φ := by
        have hφ : φ ∈ T ∪ {φ} := Set.mem_union_right T rfl
        exact Model.realize_of_mem φ hφ
      -- Therefore, since `T ⊨ᵇ (φ → ψ)`, it follows that `M ⊨ ψ`.
      let M' : T.ModelType := {
        Carrier := M.Carrier
      }
      exact (ElementarilyEquivalent.realize_sentence rfl ψ).mp (hT M' hM')

theorem equivSentence_sup (φ ψ : L.Formula α) :
    equivSentence (φ ⊔ ψ) = equivSentence φ ⊔ equivSentence ψ :=
  rfl

theorem equivSentence_imp (φ ψ : L.Formula α) :
    equivSentence (φ.imp ψ) = (equivSentence φ).imp (equivSentence ψ) :=
  rfl

/-- `equivSentence` commutes with taking the conjunction of finitely many formulas. -/
lemma equivSentence_iInf [Finite α] {β : Type*} (M : Type*)
[L[[β]].Structure M] (f : α → L.Formula β) :
  M ⊨ equivSentence (iInf f) ↔ ∀ x : α, M ⊨ equivSentence (f x) := by {
    haveI := LHom.isExpansionOn_reduct (L.lhomWithConstants β) M
    letI := (L.lhomWithConstants β).reduct M
    constructor
    · intro hM x
      apply (realize_equivSentence M (iInf f)).1 at hM
      apply realize_iInf.1 at hM
      specialize hM x
      apply (realize_equivSentence M (f x)).2 at hM
      assumption
    · intro hM
      apply (realize_equivSentence M (iInf f)).2
      apply realize_iInf.2
      intro x
      apply (realize_equivSentence M (f x)).1
      exact hM x
  }
/-- `equivSentence` commutes with taking the disjunction of finitely many formulas. -/
lemma equivSentence_iSup [Finite α] {β : Type*} (M : Type*)
[L[[β]].Structure M] (f : α → L.Formula β) :
  M ⊨ equivSentence (iSup f) ↔ ∃ x : α, M ⊨ equivSentence (f x) := by {
    haveI := LHom.isExpansionOn_reduct (L.lhomWithConstants β) M
    letI := (L.lhomWithConstants β).reduct M
    constructor
    · intro hM
      apply (realize_equivSentence M (iSup f)).1 at hM
      apply realize_iSup.1 at hM
      obtain ⟨ x, hM ⟩ := hM
      use x
      apply (realize_equivSentence M (f x)).2 at hM
      assumption
    · intro hM
      apply (realize_equivSentence M (iSup f)).2
      apply realize_iSup.2
      obtain ⟨ x, hM ⟩ := hM
      apply (realize_equivSentence M (f x)).1 at hM
      use x
  }

/-- A theory `T` models the conjunction of finitely many formulas
if and only if it models the negation of the disjunction of their negations. -/
lemma iInf_iff_not_iSup_not (T : L.Theory) [Finite α] {β : Type*}
  (f : α → L.Formula β) : T.Iff (iInf f) (iSup (fun x ↦ (f x).not)).not := by {
    intro M v xs
    have hxs : xs = default := List.ofFn_inj.mp rfl
    rw [hxs]
    apply realize_iff.2
    constructor
    · intro hf
      apply realize_iInf.1 at hf
      apply realize_not.2
      by_contra hf'
      apply realize_iSup.1 at hf'
      obtain ⟨ b, hb ⟩ := hf'
      apply realize_not.1 at hb
      specialize hf b
      contradiction
    · intro hf
      apply realize_not.1 at hf
      apply realize_iInf.2
      by_contra hf'
      push Not at hf'
      apply hf
      apply realize_iSup.2
      obtain ⟨ b, hb⟩ := hf'
      use b
      apply realize_not.2
      assumption
  }

/-- A theory `T` models the disjunction of finitely many formulas
if and only if it models the negation of the conjunction of their negations. -/
lemma iSup_iff_not_iInf_not (T : L.Theory) [Finite α] {β : Type*}
  (f : α → L.Formula β) : T.Iff (iSup f) (iInf (fun x ↦ (f x).not)).not := by {
    intro M v xs
    have hxs : xs = default := List.ofFn_inj.mp rfl
    rw [hxs]
    apply realize_iff.2
    constructor
    · intro hf
      apply realize_iSup.1 at hf
      apply realize_not.2
      by_contra hf'
      apply realize_iInf.1 at hf'
      obtain ⟨ b, hb ⟩ := hf
      specialize hf' b
      apply realize_not.1 at hf'
      contradiction
    · intro hf
      apply realize_iSup.2
      apply realize_not.1 at hf
      by_contra hf'
      apply hf
      apply realize_iInf.2
      push Not at hf'
      intro b
      specialize hf' b
      apply realize_not.2
      assumption
  }

/-- For two `L`-formulas `φ` and `ψ`, `T ⊨ᵇ (φ ↔ ψ)` if and only if
`T ⊨ᵇ φ` is equivalent to `T ⊨ᵇ ψ`. -/
lemma iff_iff_modelsBoundedFormula_iff {T : L.Theory} (φ ψ : L.Formula α) :
  (T.Iff φ ψ) → (T ⊨ᵇ φ ↔ T ⊨ᵇ ψ) := by {
    intro hφψ
    constructor
    · intro hφ M v xs
      specialize hφ M v xs; specialize hφψ M v xs
      simp_all only [BoundedFormula.realize_iff, true_iff]
    · intro hψ M v xs
      specialize hψ M v xs; specialize hφψ M v xs
      simp_all only [BoundedFormula.realize_iff, iff_true]
  }

/-- A theory `T` models the negation of the disjunction of finitely many formulas
if and only if it models the conjunction of their negations. -/
lemma not_iSup_iff_iInf_not (T : L.Theory) [Finite α] {β : Type*}
  (f : α → L.Formula β) : T.Iff (iSup f).not (iInf (fun x ↦ (f x).not)) := by {
    intro M v xs
    have h := (iSup_iff_not_iInf_not T f)
    specialize h M v xs
    simp_all only [BoundedFormula.realize_iff, BoundedFormula.realize_not, not_not]
  }

/-- A theory `T` models the negation of the conjunction of finitely many formulas
if and only if it models the disjunction of their negations. -/
lemma not_iInf_iff_iSup_not {T : L.Theory} [Finite α] {β : Type*}
  (f : α → L.Formula β) : T.Iff (iInf f).not (iSup (fun x ↦ (f x).not)) := by {
    intro M v xs
    have h := (iInf_iff_not_iSup_not T f)
    specialize h M v xs
    simp_all only [BoundedFormula.realize_iff, BoundedFormula.realize_not, not_not]
  }

/-- Modulo a theory `T`, the formulas `φ.imp ψ` and `(ψ.not).imp (φ.not)` are equivalent. -/
lemma contraposition {T : L.Theory} (φ ψ : L.Formula α) :
  T.Iff (φ.imp ψ) ((ψ.not).imp (φ.not)) := by {
    intro M v xs
    simp only [BoundedFormula.realize_iff, BoundedFormula.realize_imp]
    constructor
    · intro hφψ hψ
      simp_all only [BoundedFormula.realize_not, imp_false, not_false_eq_true]
    · intro hφψ hφ
      simp_all only [BoundedFormula.realize_not, not_true_eq_false, imp_false, not_not]
  }

/-- Let `T` be an `L`-theory, `φ` an `L`-formula and `Sigma` a collection of `L`-formulas s.t.
for every `M ⊨ T` and `a : α → M` that realizes `φ`, there exists an `L`-formula `ψ ∈ Sigma`
such that `ψ` realizes `Sigma`. Then, there is a finite set of `L`-formulas in `Sigma` s.t.
in every model of `T`, `φ` implies their disjunction. -/
lemma impliesfinitedisj_if {α : Type w} [Finite α]
  (T : L.Theory) (φ : L.Formula α) (Sigma : Set (L.Formula α))
  (hSigma : ∀ (M : ModelType.{u, v, max (max u v) w} T) (a : α → M.Carrier),
  φ.Realize a → ∃ ψ ∈ Sigma, ψ.Realize a) :
    ∃ (β : Finset L[[α]].Sentence) (f : β → Sigma), T ⊨ᵇ φ.imp (iSup (Subtype.val ∘ f)) := by
      let T_φ : L[[α]].Theory := ((L.lhomWithConstants α).onTheory T) ∪ { equivSentence φ  }
      let Delta : L[[α]].Theory := { (equivSentence ψ).not | ψ ∈ Sigma }
      -- Now, we are going to show that `T_φ ∪ Delta` is not satisfiable:
      have hTφDelta : ¬ (T_φ ∪ Delta).IsSatisfiable := by
        -- Suppose `M` is a model of `T_φ ∪ Delta`.
        by_contra M
        apply Classical.choice at M
        let _ := M.leftStructure
        have _ : (L.lhomWithConstants α).IsExpansionOn M := {
          map_onFunction := by tauto
          map_onRelation := by tauto
        }
        -- Then, by definition of `T_φ`, `M ⊨ T`.
        have hM : M ⊨ T := {
          realize_of_mem := by
            intro φ' hφ'
            have hφ'₁ : ((L.lhomWithConstants α).onFormula φ') ∈ T_φ ∪ Delta := by {
              unfold T_φ
              aesop
            }
            apply (LHom.realize_onBoundedFormula (L.lhomWithConstants α) φ').1
            exact M.is_model.realize_of_mem ((L.lhomWithConstants α).onFormula φ') hφ'₁
        }
        let M' : T.ModelType := {
          Carrier := M.Carrier
        }
        -- similarly, `M ⊨ φ`, if `φ` is considered as an `L[[α]]`-sentence.
        have hMφ : M ⊨ (equivSentence φ) := by
          have h₁ : (equivSentence φ) ∈ T_φ ∪ Delta := by unfold T_φ; norm_num
          exact M.is_model.realize_of_mem (equivSentence φ) h₁
        -- in particular, there exists a tuple in `M` that realize `φ`.
        apply (realize_equivSentence M.Carrier φ).1 at hMφ
        -- Hence, by our assumptions on Sigma,
        -- there is `ψ ∈ Sigma` that is realized by the same tuple as `φ`.
        specialize hSigma M' (fun a ↦ (L.con a)) hMφ
        obtain ⟨ ψ, hψ₁, hψ₂ ⟩ := hSigma
        -- On the other hand, the negation of `ψ` (considered as an `L[[α]]`-sentence)
        -- is contained in `Delta`.
        have hψDelta : (equivSentence ψ).not ∈ Delta := by
          unfold Delta
          simp only [Set.mem_ofPred_eq]
          use ψ
        -- Hence, `M` models the negation of `ψ` as an `L[[α]]`-sentence.
        have hMψ : M ⊨ (equivSentence ψ).not :=
          M.is_model.realize_of_mem (equivSentence ψ).not (Set.mem_union_right T_φ hψDelta)
        -- This is a contradiction.
        apply (realize_equivSentence M ψ).2 at hψ₂
        exact (iff_false_intro hMψ).mp hψ₂
      -- By the compactness theorem, there is a finite subset `T0` of `T_φ ∪ Delta`
      -- that is not satisfiable.
      by_contra h'
      apply hTφDelta
      apply isSatisfiable_iff_isFinitelySatisfiable.2
      unfold IsFinitelySatisfiable
      by_contra h₂
      push Not at h₂
      obtain ⟨ T0, hT0_1, hT0_2 ⟩ := h₂
      -- Let Delta'' be the intersection of `T0` and `Delta`.
      -- Note: We want Delta'' to have the type `Finset L[[α]].Sentence`,
      -- therefore, we need to prove that it is finite.
      let Delta' := (T0 : Set L[[α]].Sentence) ∩ Delta
      have hDelta' : Finite Delta' := Finite.Set.finite_inter_of_left T0 Delta
      let Delta'' := Set.Finite.toFinset hDelta'
      have hDelta'Delta'' : (Delta'' : Set L[[α]].Sentence) = Delta' := by
        unfold Delta''
        exact Set.Finite.coe_toFinset hDelta'
      -- By definition, `T0` (considered as an `L[[α]]`-theory) is a subset of `T_φ ∪ Delta''`.
      have hT0TφDelta'' : (T0 : L[[α]].Theory) ⊆ (T_φ ∪ Delta'') := by
        rw [hDelta'Delta'']
        unfold Delta'
        intro φ' hφ'
        specialize hT0_1 hφ'
        obtain hφ'₁ | hφ'₂ := hT0_1
        · left
          exact hφ'₁
        · right
          exact ⟨ hφ', hφ'₂ ⟩
      -- Since `T0` is not satisfiable, neither is `T_φ ∪ Delta''`.
      have hDelta'' : ¬ (T_φ ∪ Delta'').IsSatisfiable := by
        by_contra h
        have h' := IsSatisfiable.mono h hT0TφDelta''
        apply hT0_2
        exact h'
      -- Now, we define `χ` to be the conjunction of all formulas in `Delta''`.
      have hDelta''₁ : Finite Delta'' := by exact Finite.of_fintype Delta''
      let f : Delta'' → L.Formula α := fun x ↦ equivSentence.invFun (x : L[[α]].Sentence)
      let χ : L.Formula α := iInf f
      -- Now, we are going to prove that `T_φ ∪ {χ}` is not satisfiable.
      -- Here, we consider `χ` as an `L[[α]]`-sentence.
      have hχ : ¬(T_φ ∪ {equivSentence χ}).IsSatisfiable := by
        -- Suppose `M ⊨ (T_φ ∪ {equivSentence χ})`
        by_contra M
        unfold IsSatisfiable at M
        apply Classical.choice at M
        have hM := M.is_model.realize_of_mem
        unfold χ at hM
        -- Then, by definition of `χ`, this implies `M ⊨ T_φ ∪ Delta''`
        have hM' : M ⊨ (T_φ ∪ Delta'') := {
          realize_of_mem := by
            intro φ' hφ'
            obtain hφ'₁ | hφ'₂ := hφ'
            · have hφ'₂ : φ' ∈ T_φ ∪ {equivSentence (Formula.iInf f)} :=
                Set.mem_union_left {equivSentence (Formula.iInf f)} hφ'₁
              exact hM φ' hφ'₂
            · have hM' : M ⊨ equivSentence (Formula.iInf f) := by
                specialize hM (equivSentence (Formula.iInf f))
                simp_all
              apply (equivSentence_iInf M f).1 at hM'
              specialize hM' ⟨ φ', hφ'₂ ⟩
              unfold f at hM'
              simp_all
        }
        let M' : (T_φ ∪ Delta'').ModelType := {
          Carrier := M.Carrier
        }
        -- This is a contradiction since `T_φ ∪ Delta''` is not satisfiable.
        apply hDelta''
        unfold IsSatisfiable
        exact Nonempty.intro M'
      -- Next, we are going to prove `T_φ ⊨ᵇ (equivSentence χ).not`:
      have hχ₁ : T_φ ⊨ᵇ (equivSentence χ).not := by
        -- Suppose there is an `L[[α]]`-structure `M` s.t. `M ⊨ T_φ`
        -- and `M ⊨ ((equivSentence χ).not).not`.
        apply (@models_iff_not_satisfiable L[[α]] T_φ (equivSentence χ).not).2
        unfold IsSatisfiable
        by_contra hχ₂
        apply Classical.choice at hχ₂
        let M := hχ₂.Carrier
        have hM := hχ₂.is_model
        have hM₁ : M ⊨ T_φ := by simp_all [T_φ, Delta, Delta'', Delta', χ, f, M]
        have hM₂ : M ⊨ ((equivSentence χ).not).not := by simp_all [T_φ, Delta, Delta'',
          Delta', χ, f, M]
        -- Then, `M ⊨ equivSentence χ`
        have hM₂' : M ⊨ equivSentence χ := by simp_all
        -- Hence, `M ⊨ (T_φ ∪ {equivSentence χ})`, which is a contradiction to the fact that
        -- `(T_φ ∪ {equivSentence χ})` is not satisfiable.
        have hM' : M ⊨ (T_φ ∪ {equivSentence χ}) := by simp_all
        apply hχ
        unfold IsSatisfiable
        refine Nonempty.intro ?_
        let M' : (T_φ ∪ {equivSentence χ}).ModelType := {
          Carrier := M
        }
        gcongr
      -- Since the bijection `equivSentence` is compatible with negation,
      -- implication and conjunction of formulas, it follows by Lemma 3.4 from the thesis that
      -- `T ⊨ᵇ (φ → χ.not)`.
      rw [← equivSentence_not] at hχ₁
      unfold T_φ at hχ₁
      apply (exist_models_iff_models_imp ((L.lhomWithConstants α).onTheory T)
        (equivSentence φ) (equivSentence χ.not)).1 at hχ₁
      unfold χ at hχ₁
      rw [← equivSentence_imp] at hχ₁
      apply (models_formula_iff_onTheory_models_equivSentence).2 at hχ₁
      -- Now, note that every formula in `Delta''` (considered as an `L`-formula)
      -- is equal to the negation of some formula in `Sigma`:
      have hf : ∀ x : Delta'', ∃ y : Sigma, f x = (y : L.Formula α).not := by
        intro x
        have hx₁ : (x : L[[α]].Sentence) ∈ Delta'' := Finset.coe_mem x
        unfold Delta'' at hx₁
        have hx₂ : (x : L[[α]].Sentence) ∈ Delta' := (Set.Finite.mem_toFinset hDelta').mp hx₁
        unfold Delta' at hx₂
        obtain ⟨ hx₃, hx₄ ⟩ := hx₂
        unfold Delta at hx₄
        simp only [Set.mem_ofPred_eq] at hx₄
        obtain ⟨ ψ, hψ₁, hψ₂ ⟩ := hx₄
        use ⟨ ψ, by exact Set.mem_of_subset_of_mem (fun ⦃a⦄ a_1 ↦ a_1) hψ₁ ⟩
        unfold f
        rw [← hψ₂, ← equivSentence_not]
        simp
      -- Hence, we can define a function `f'` from `Delta''` to `Sigma`
      -- s.t. `φ` is the negation of `f'(φ)`.
      let f' : Delta'' → Sigma := fun x ↦ Classical.choose (hf x)
      have hf' : f = fun x ↦ ((Subtype.val ∘ f') x).not := by
        ext x
        unfold f'
        simp only [Function.comp_apply]
        grind
      apply h'
      -- Now, we are going to prove that modulo `T`, `φ` implies
      -- the conjunction over `f'`
      use Delta''; use f'
      intro M v xs
      -- We distinguish between two cases:
      by_cases hφ : BoundedFormula.Realize φ v xs
      · -- If `v : α → M` is a tuple realizing `φ`,
        -- it also realizes the negation of the disjunction of formulas in `Delta''`.
        specialize hχ₁ M v xs
        rw [hf'] at hχ₁
        apply BoundedFormula.realize_imp.1 at hχ₁
        apply hχ₁ at hφ
        -- This is equivalent to realizing the conjunction over `f'`.
        have hφ' :=  @iSup_iff_not_iInf_not L ↥Delta'' T hDelta''₁ α (Subtype.val ∘ f')
        specialize hφ' M v xs
        apply BoundedFormula.realize_iff.1 at hφ'
        apply hφ'.2 at hφ
        apply BoundedFormula.realize_imp.2
        finiteness
      · -- On the other hand, if `v : α → M` does not realize `φ`, there is nothing to prove.
        apply BoundedFormula.realize_imp.2
        by_contra h'
        simp only [Classical.not_imp] at h'
        apply hφ
        exact h'.1


/-- Two complete types `p`, `q` over `T` with variables indexed by `α` are not equal
if and only if there is an `L[[α]].Sentence` that is contained in `p`, but not in `q`. -/
lemma types_neq_iff (T : L.Theory) (p q : T.CompleteType α) :
  p.toTheory ≠ q.toTheory ↔ ∃ φ, (φ ∈ p.toTheory ∧ ¬ φ ∈ q.toTheory) := by {
    constructor
    · intro hpq
      by_contra h
      push Not at h
      have hp : p.toTheory ⊆ q.toTheory := by trivial
      have hq : q.toTheory ⊆ p.toTheory := by {
        intro φ hφ
        have hp' := p.isMaximal'.2
        specialize hp' φ
        obtain hp'₁ | hp'₂ := hp'
        · assumption
        · apply hp at hp'₂
          have hq := q.isMaximal'
          unfold IsMaximal at hq
          obtain ⟨ hq₁, hq₂ ⟩ := hq
          apply Classical.choice at hq₁
          have hq₃ := hq₁.is_model
          have hq₄ : hq₁.Carrier ⊨ φ := by simp_all
          have hq₅ : hq₁.Carrier ⊨ (φ.not) := by simp_all
          trivial
      }
      have hpq' : p.toTheory = q.toTheory := Set.Subset.antisymm h hq
      contradiction
    · intro hpq
      obtain ⟨ φ, hφ ⟩ := hpq
      by_contra h
      have h₁ : φ ∈ p.toTheory := by tauto
      have h₂ : ¬ φ ∈ q.toTheory := by tauto
      simp_all
  }

/-- If a set `Sigma` with values in `α` is closed under some two-valued operation `f`,
`l` is a list with values in `Sigma` and `Sigma` contains the initial value of folding `l`
along `f` in reverse order, it contains the result of folding the list. -/
lemma closed_contains_foldr {α : Type*} (Sigma : Set α) (f : α → α → α)
  (init : α) (l : List α) (hl : ∀ i : Fin (l.length), l.get i ∈ Sigma)
  (closed_f : ∀ a b, a ∈ Sigma ∧ b ∈ Sigma → f a b ∈ Sigma)
  (contains_init : init ∈ Sigma) : List.foldr f init l ∈ Sigma := by
    induction l with
    | nil => simpa
    | cons head tail ih =>
      simp only [List.foldr_cons]
      have h_head : head ∈ Sigma := by
        specialize hl 0
        simpa
      have h_tail : ∀ i : Fin (tail.length), tail.get i ∈ Sigma := by
        intro i
        specialize hl ⟨i+1, by norm_num ⟩
        finiteness
      apply ih at h_tail
      specialize closed_f head (List.foldr f init tail)
      simp_all

/-- If `Sigma` is a set of `L`-formulas that is closed under conjunction
and contains `⊤`, it contains the conjunction of finitely many formulas from `Sigma`. -/
lemma closed_inf_contains_iInf {β : Type*} [Finite β] (Sigma : Set (L.Formula α))
  (closed_inf : ∀ φ ψ, (φ ∈ Sigma) ∧ (ψ ∈ Sigma) → (φ ⊓ ψ) ∈ Sigma)
  (contains_top : ⊤ ∈ Sigma) (f : β → Sigma) :
  iInf (Subtype.val ∘ f) ∈ Sigma := by
    unfold Formula.iInf; unfold BoundedFormula.iInf
    simp only
    let l := List.map (Subtype.val ∘ f) (@Finset.univ β (Fintype.ofFinite β)).toList
    have hl : ∀ i : Fin (l.length), l.get i ∈ Sigma := by
      intro i
      unfold l
      norm_num
    have h' := closed_contains_foldr Sigma (fun x1 x2 ↦ x1 ⊓ x2) ⊤ l hl closed_inf contains_top
    unfold l at h'
    assumption

/-- If `Sigma` is a set of `L`-formulas that is closed under disjunction and contains `⊥`,
it contains the disjunction of finitely many formulas from `Sigma`. -/
lemma closed_sup_contains_iSup {β : Type*} [Finite β] (Sigma : Set (L.Formula α))
  (closed_sup : ∀ φ ψ, (φ ∈ Sigma) ∧ (ψ ∈ Sigma) → (φ ⊔ ψ) ∈ Sigma)
  (contains_bot : ⊥ ∈ Sigma) (f : β → Sigma) :
  iSup (Subtype.val ∘ f) ∈ Sigma := by
    unfold Formula.iSup; unfold BoundedFormula.iSup
    simp only
    let l := List.map (Subtype.val ∘ f) (@Finset.univ β (Fintype.ofFinite β)).toList
    have hl : ∀ i : Fin (l.length), l.get i ∈ Sigma := by
      intro i
      unfold l
      norm_num
    have h' := closed_contains_foldr Sigma (fun x1 x2 ↦ x1 ⊔ x2) ⊥ l hl closed_sup contains_bot
    unfold l at h'
    assumption

namespace CompleteType

/-- If `T` models `φ` for some L-formulas `φ`,
then every complete type `p` over `T` contains `φ`. -/
lemma contains_modeled_formulas {α : Type*} [Finite α] (T : L.Theory)
  (p : T.CompleteType α) (φ : L.Formula α) (hφ : T ⊨ᵇ φ) :
  φ.equivSentence ∈ p.toTheory := by {
    have hp := p.isMaximal'
    unfold IsMaximal at hp
    obtain ⟨ M, hp₁ ⟩ := hp
    apply Classical.choice at M
    have hp₂ := p.subset'
    apply (models_formula_iff_onTheory_models_equivSentence).1 at hφ
    have hM₁ := M.is_model
    have hM₂ : ((L.lhomWithConstants α).onTheory T).Model M := Model.mono hM₁ hp₂
    unfold LHom.onTheory at hM₂; unfold LHom.onSentence at hM₂
    have hM₃ : M ⊨ {x | ∃ φ' ∈ T, (L.lhomWithConstants α).onFormula φ' = x} := by {
      simp only [model_iff, Set.mem_ofPred_eq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro φ hφ'
      simp only [model_iff, Set.mem_image, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂] at hM₂
      specialize hM₂ φ hφ'
      assumption
    }
    let M' : ModelType {x | ∃ φ' ∈ T, (L.lhomWithConstants α).onFormula φ' = x} := {
      Carrier := M.Carrier
    }
    specialize hφ M'
    specialize hp₁ (equivSentence φ)
    by_contra h'
    have h'' : (equivSentence φ).not ∈ p := (not_mem_iff p (equivSentence φ)).mpr h'
    simp only [model_iff] at hM₁
    have h''' : (equivSentence φ).not ∈ p.toTheory := by exact Set.mem_preimage.mp h''
    specialize hM₁ (equivSentence φ).not h'''
    unfold Sentence.Realize at hM₁; unfold Formula.Realize at hM₁
    specialize hφ default default
    exact (iff_false_intro hM₁).mp hφ
  }

/-- If `φ` and `ψ` are L-formulas with variables indexed by a finite type `α`
and `T` models `φ.iff ψ`, then every type containing `φ` also contains `ψ` -/
lemma contains_equiv_if {α : Type*} [Finite α] (T : L.Theory)
  (p : T.CompleteType α) (φ ψ : L.Formula α) (hφψ : T ⊨ᵇ (φ.iff ψ)) :
  φ.equivSentence ∈ p.toTheory → ψ.equivSentence ∈ p.toTheory := by {
    intro hφ
    have hφψ' := contains_modeled_formulas T p (φ.iff ψ) hφψ
    by_contra h
    have hp' := p.isMaximal'
    unfold IsMaximal at hp'
    obtain ⟨ hp'₁, hp'₂ ⟩ := hp'
    have hψ : equivSentence (ψ.not) ∈ p := by {
      specialize hp'₂ (equivSentence ψ)
      obtain hp'₃ | hp'₄ := hp'₂
      · contradiction
      · exact (mem_typesWith_iff (equivSentence ψ.not) p).mp hp'₄
    }
    apply Classical.choice at hp'₁
    have hp'₃ : hp'₁.Carrier ⊨ (equivSentence φ) := Model.realize_of_mem (equivSentence φ) hφ
    have hp'₄ : hp'₁.Carrier ⊨ (equivSentence ψ.not) :=
      Model.realize_of_mem (equivSentence ψ.not) hψ
    have hp'₅ : hp'₁.Carrier ⊨ equivSentence (φ.iff ψ) :=
      Model.realize_of_mem (equivSentence (φ.iff ψ)) hφψ'
    unfold Formula.iff at hp'₅; unfold BoundedFormula.iff at hp'₅
    rw [equivSentence_inf] at hp'₅
    simp only [Sentence.realize_inf] at hp'₅
    obtain ⟨ hp'₆, hp'₇ ⟩ := hp'₅
    exact (iff_false_intro hp'₄).mp (hp'₆ hp'₃)
  }

/-- If `φ` and `ψ` are L-formulas with variables indexed by a finite type `α`
and `T` models `φ.iff ψ`, then every complete type `p` over `T` with variables indexed by `α`
contains `φ` if and only if it contains `ψ`. -/
lemma contains_equiv {α : Type*} [Finite α] (T : L.Theory)
  (p : T.CompleteType α) (φ ψ : L.Formula α) (hφψ : T ⊨ᵇ (φ.iff ψ)) :
  φ.equivSentence ∈ p.toTheory ↔ ψ.equivSentence ∈ p.toTheory :=
    ⟨ contains_equiv_if T p φ ψ hφψ,
    contains_equiv_if T p ψ φ (modelsBoundedFormula_iff_symm₁ T φ ψ hφψ)⟩

/-- Complete types are closed under conjunction of formulas. -/
lemma closed_inf {α : Type*} {T : L.Theory} (p : CompleteType T α) {φ ψ : L[[α]].Sentence} :
  (φ ⊓ ψ) ∈ (p.toTheory) ↔ (φ ∈ (p.toTheory) ∧ ψ ∈ (p.toTheory)) := by {
    have hp := p.isMaximal
    obtain ⟨ M, hp₂⟩ := hp
    apply Classical.choice at M
    constructor
    · intro hφψ
      have hM := M.is_model.realize_of_mem (φ ⊓ ψ) hφψ
      apply realize_inf.1 at hM
      obtain ⟨ hM₁, hM₂ ⟩ := hM
      constructor
      · specialize hp₂ φ
        by_contra hφ
        have hφ' : φ.not ∈ (p.toTheory) := by tauto
        have hM := M.is_model.realize_of_mem φ.not hφ'
        contradiction
      · specialize hp₂ ψ
        by_contra hψ
        have hψ' : ψ.not ∈ (p.toTheory) := by tauto
        have hM := M.is_model.realize_of_mem ψ.not hψ'
        contradiction
    · intro hφψ
      have hMφ := M.is_model.realize_of_mem φ hφψ.1
      have hMψ := M.is_model.realize_of_mem ψ hφψ.2
      specialize hp₂ (φ ⊓ ψ)
      by_contra hφψ'
      have hφψ'' : (φ ⊓ ψ).not ∈ (p.toTheory) := by tauto
      have hM := M.is_model.realize_of_mem (φ ⊓ ψ).not hφψ''
      apply realize_not.1 at hM
      apply hM
      apply realize_inf.2
      constructor
      · exact hMφ
      · exact hMψ
  }

/-- Complete types are closed under disjunction of formulas. -/
lemma closed_sup {α : Type*} {T : L.Theory} (p : CompleteType T α) {φ ψ : L[[α]].Sentence} :
  (φ ⊔ ψ) ∈ (p.toTheory) ↔ (φ ∈ p.toTheory ∨ ψ ∈ p.toTheory) := by {
    have hp := p.isMaximal
    obtain ⟨ M, hp ⟩ := hp
    apply Classical.choice at M
    constructor
    · intro hφψ
      have hφψ' := M.is_model.realize_of_mem (φ ⊔ ψ) hφψ
      apply realize_sup.1 at hφψ'
      obtain hφ | hψ := hφψ'
      · left
        specialize hp φ
        by_contra hφ'
        have hφ'' : φ.not ∈ p.toTheory := by tauto
        have hM' := M.is_model.realize_of_mem φ.not hφ''
        contradiction
      · right
        specialize hp ψ
        by_contra hψ'
        have hψ'' : ψ.not ∈ p.toTheory := by tauto
        have hM' := M.is_model.realize_of_mem ψ.not hψ''
        contradiction
    · intro hφψ
      specialize hp (φ ⊔ ψ)
      obtain hφ | hψ := hφψ
      · have hMφ := M.is_model.realize_of_mem φ hφ
        by_contra hφ'
        have hφψ' : (φ ⊔ ψ).not ∈ p.toTheory := by tauto
        have hMφψ := M.is_model.realize_of_mem (φ ⊔ ψ).not hφψ'
        apply realize_not.1 at hMφψ
        apply hMφψ
        apply realize_sup.2
        left
        assumption
      · have hMψ := M.is_model.realize_of_mem ψ hψ
        by_contra hψ'
        have hφψ' : (φ ⊔ ψ).not ∈ p.toTheory := by tauto
        have hMφψ := M.is_model.realize_of_mem (φ ⊔ ψ).not hφψ'
        apply realize_not.1 at hMφψ
        apply hMφψ
        apply realize_sup.2
        right
        assumption
  }

/-- **Separating Types Theorem**

If `Sigma` is a set of `L`-formulas with variables in `α`
that is closed under conjunction and disjunction
and contains `⊤` and `⊥`, every `L`-formula with variables in `α`
is equivalent to a formula from `Sigma`
if and only if all distinct complete types are separated by a formula in `Sigma`. -/
theorem ContainsEquivForumulas_iff_SeparatesTypes {α : Type w} [Finite α] (T : L.Theory)
  (Sigma : Set (L.Formula α)) (closed_sup : ∀ φ ψ, (φ ∈ Sigma) ∧ (ψ ∈ Sigma) →  (φ ⊔ ψ) ∈ Sigma)
  (closed_inf : ∀ φ ψ, (φ ∈ Sigma) ∧ (ψ ∈ Sigma) → (φ ⊓ ψ) ∈ Sigma)
  (contains_top : ⊤ ∈ Sigma) (contains_bot : ⊥ ∈ Sigma) :
  (∀ φ : L.Formula α, ∃ ψ ∈ Sigma, T.Iff φ ψ) ↔
  (∀ p q : T.CompleteType α, p.toTheory ≠ q.toTheory →
  ∃ ψ : L.Formula α, ψ ∈ Sigma ∧ equivSentence ψ ∈ p.toTheory ∧
  ¬equivSentence ψ ∈ q.toTheory) := by {
    constructor
    · intro hSigma p q hpq
      apply (types_neq_iff T p q).1 at hpq
      obtain ⟨ φ, hφ₁, hφ₂ ⟩ := hpq
      let φ' := equivSentence.invFun φ
      specialize hSigma φ'
      obtain ⟨ ψ, hψ ⟩ := hSigma
      use ψ
      have hφ' : equivSentence φ' = φ := (Equiv.apply_eq_iff_eq_symm_apply equivSentence).mpr rfl
      rw [← hφ'] at hφ₁; rw [← hφ'] at hφ₂
      apply (contains_equiv T p φ' ψ hψ.2).1 at hφ₁
      constructor
      · exact hψ.1
      · constructor
        · gcongr
        · by_contra h'
          apply hφ₂
          apply (contains_equiv T q φ' ψ hψ.2).2
          gcongr
    · intro hSigma φ
      have hSigma₁ : ∀ p : T.CompleteType α, (equivSentence φ) ∈ p.toTheory →
        ∃ χ_p ∈ Sigma, (equivSentence χ_p) ∈ p.toTheory ∧ T ⊨ᵇ χ_p.imp φ := by {
          intro p hp₁
          let Sigma' := {(ψ' : L.Formula α) |
            ∃ ψ, ψ ∈ Sigma ∧ (equivSentence ψ) ∈ p.toTheory ∧ T.Iff ψ' ψ.not}
          have hSigma' : ∀ (M : ModelType.{u, v, max (max u v) w} T) (a : α → M.Carrier),
            (φ.not).Realize a → ∃ ψ ∈ Sigma', ψ.Realize a := by {
              intro M a hφ
              by_cases hM : Nonempty M
              · let q := T.typeOf a
                have hq : equivSentence φ.not ∈ q.toTheory := by {
                  unfold q
                  apply formula_mem_typeOf.2
                  assumption
                }
                have hpq : p.toTheory ≠ q.toTheory := by {
                  by_contra hpq'
                  rw [← hpq'] at hq
                  rw [equivSentence_not] at hq
                  have hp := p.isMaximal
                  obtain ⟨ M, hp₂ ⟩ := hp
                  apply Classical.choice at M
                  have hM₁ := M.is_model.realize_of_mem (equivSentence φ) hp₁
                  have hM₂ := M.is_model.realize_of_mem (equivSentence φ).not hq
                  apply realize_not.1 at hM₂
                  contradiction
                }
                specialize hSigma p q hpq
                obtain ⟨ ψ, hψ₁, hψ₂, hψ₃ ⟩ := hSigma
                use ψ.not
                constructor
                · unfold Sigma'
                  simp only [Set.mem_ofPred_eq]
                  use ψ
                · have hq' := q.isMaximal
                  unfold IsMaximal at hq'
                  obtain ⟨ hq₁, hq₂ ⟩ := hq'
                  specialize hq₂ (equivSentence ψ)
                  have hq₃ : (equivSentence ψ).not ∈ q.toTheory := Set.mem_preimage.mp hψ₃
                  rw [← equivSentence_not] at hq₃
                  unfold q at hq₃
                  exact formula_mem_typeOf.mp hq₃
              · simp only [not_nonempty_iff, not_isEmpty_of_nonempty] at hM
            }
          have hφ := impliesfinitedisj_if T φ.not Sigma' hSigma'
          have closed_inf' : ∀ (φ ψ : L.Formula α),
          φ ∈ Sigma' ∧ ψ ∈ Sigma' → (φ ⊓ ψ) ∈ Sigma' := by {
            intro φ' ψ' hφ'ψ'
            unfold Sigma' at hφ'ψ'
            simp only [Set.mem_ofPred_eq] at hφ'ψ'
            obtain ⟨ hφ', ψ'', hψ''₁, hψ''₂, hψ'⟩ := hφ'ψ'
            obtain ⟨ φ'', hφ''₁, hφ''₂, hφ'⟩ := hφ'
            unfold Sigma'
            use φ'' ⊔ ψ''
            constructor
            · specialize closed_sup φ'' ψ''
              apply closed_sup
              exact ⟨ hφ''₁, hψ''₁ ⟩
            · constructor
              · rw [equivSentence_sup]
                apply (p.closed_sup).2
                left
                assumption
              · intro M v xs
                specialize hφ' M v xs; specialize hψ' M v xs
                simp_all only [and_imp, ne_eq, realize_not, BoundedFormula.realize_iff,
                  BoundedFormula.realize_not, BoundedFormula.realize_inf,
                  BoundedFormula.realize_sup, not_or]
          }
          obtain ⟨ β, f, hφ ⟩ := hφ
          have h₁ := @not_iSup_iff_iInf_not L β T _ α (Subtype.val ∘ f)
          have h₂ : ∀ x : β, ∃ ψ ∈ Sigma,
            equivSentence ψ ∈ p.toTheory ∧ T.Iff ((Subtype.val ∘ f) x).not ψ := by {
              intro x
              have hx : ((Subtype.val ∘ f) x) ∈ Sigma' := by norm_num
              unfold Sigma' at hx
              simp only [Set.mem_ofPred_eq] at hx
              obtain ⟨ ψ, hψ₁, hψ₂, hψ₃ ⟩ := hx
              use ψ
              constructor
              · exact hψ₁
              · constructor
                · exact hψ₂
                · intro M v xs
                  specialize hψ₃ M v default
                  have hxs : xs = default := List.ofFn_inj.mp rfl
                  rw [hxs]
                  apply realize_iff.2
                  apply realize_iff.1 at hψ₃
                  constructor
                  · intro hf
                    by_contra hψ₄
                    apply realize_not.2 at hψ₄
                    apply hψ₃.2 at hψ₄
                    apply realize_not.1 at hf
                    contradiction
                  · intro hψ
                    apply realize_not.2
                    by_contra hf
                    apply hψ₃.1 at hf
                    apply realize_not.1 at hf
                    contradiction
          }
          let f' : β → Sigma := fun x ↦ ⟨ Classical.choose (h₂ x), by grind ⟩
          use (Formula.iInf (Subtype.val ∘ f'))
          constructor
          · exact closed_inf_contains_iInf Sigma closed_inf contains_top f'
          · constructor
            · have hp := p.isMaximal
              obtain ⟨ M, hp ⟩ := hp
              apply Classical.choice at M
              by_contra hp'
              specialize hp (equivSentence (Formula.iInf (Subtype.val ∘ f')))
              have hp'' : (equivSentence (Formula.iInf (Subtype.val ∘ f'))).not ∈ p.toTheory := by
                tauto
              have hM :=
                M.is_model.realize_of_mem (equivSentence (Formula.iInf (Subtype.val ∘ f'))).not hp''
              apply realize_not.1 at hM
              apply hM
              apply (equivSentence_iInf M (Subtype.val ∘ f')).2
              intro b
              have hb : equivSentence (f' b) ∈ p.toTheory := by unfold f'; grind
              have hb' := M.is_model.realize_of_mem (equivSentence (f' b)) hb
              simpa only [Function.comp_apply]
            · intro M v xs
              have hxs : xs = default := List.ofFn_inj.mp rfl
              rw [hxs]
              apply realize_imp.1
              intro hf'
              have h₃ : Realize (Formula.iInf (fun x ↦ ((Subtype.val ∘ f) x).not)) v := by {
                apply realize_iInf.1 at hf'
                apply realize_iInf.2
                intro b
                specialize hf' b
                have hb : T.Iff (((Subtype.val ∘ f) b).not) (f' b) := by {
                  unfold f'
                  simp only [Function.comp_apply]
                  grind
                }
                simp only [Function.comp_apply] at hf'
                specialize hb M v default
                apply realize_iff.1 at hb
                apply hb.2
                assumption
              }
              have h₄ := not_iSup_iff_iInf_not T (Subtype.val ∘ f)
              specialize h₄ M v default
              apply realize_iff.1 at h₄
              apply h₄.2 at h₃
              specialize hφ M v default
              apply realize_imp.1 at hφ
              by_contra h₅
              apply realize_not.2 at h₅
              apply hφ at h₅
              apply realize_not.1 at h₃
              contradiction
      }
      let Delta : Set (L.Formula α) := {χ_p | ∃ p : T.CompleteType α,
        ∃ (hp :(equivSentence φ) ∈ p.toTheory), χ_p = Classical.choose (hSigma₁ p hp)}
      have hDelta : ∀ (M : ModelType.{u, v, max (max u v) w} T) (a : α → M.Carrier), φ.Realize a →
      ∃ ψ ∈ Delta, ψ.Realize a := by {
        intro M a hφ
        let q := T.typeOf a
        have hq : equivSentence φ ∈ q.toTheory := by {
          unfold q
          apply formula_mem_typeOf.2
          assumption
        }
        let ψ := Classical.choose (hSigma₁ q hq)
        use ψ
        constructor
        · unfold Delta
          simp only [Set.mem_ofPred_eq]
          use q
          use hq
        · have hψ : (equivSentence ψ) ∈ q.toTheory := by unfold ψ; grind
          unfold q at hψ
          exact formula_mem_typeOf.mp hψ
      }
      have hDelta'' := impliesfinitedisj_if T φ Delta hDelta
      obtain ⟨ β, f, hDelta'' ⟩ := hDelta''
      let ψ := Formula.iSup (Subtype.val ∘ f)
      have hDelta₁ : Delta ⊆ Sigma := by {
          intro χ_p hχ_p
          unfold Delta at hχ_p
          simp only [Set.mem_ofPred_eq] at hχ_p
          obtain ⟨ p, hp, hχ_p ⟩ := hχ_p
          grind only [usr Exists.choose_spec]
        }
      have hψ₁ : ψ ∈ Sigma := by {
        unfold ψ
        let f' : β → Sigma := fun x ↦ ⟨ f x , by grind ⟩
        let f'' : β → L.Formula α := Subtype.val ∘ f
        let f''' : β → L.Formula α := Subtype.val ∘ f'
        have hf' : f''' = f'' := by {
          unfold f'''; unfold f''; unfold f'
          ext x
          simp only [Function.comp_apply]
        }
        unfold f'' at hf'
        rw [← hf']
        unfold f'''
        exact closed_sup_contains_iSup Sigma closed_sup contains_bot f'
      }
      have hψ₂ : T ⊨ᵇ ψ.imp φ := by {
        intro M v xs
        have hxs : xs = default := List.ofFn_inj.mp rfl
        rw [hxs]
        apply realize_imp.2
        intro hψ
        unfold ψ at hψ
        apply realize_iSup.1 at hψ
        obtain ⟨ x, hx ⟩ := hψ
        have hx' : (@Function.comp β {x // x ∈ Delta} (L.Formula α) Subtype.val f) x ∈ Delta := by
          norm_num
        unfold Delta at hx'
        simp only [Set.mem_ofPred_eq] at hx'
        obtain ⟨ p, hp, hx' ⟩ := hx'
        have hx'':
          T ⊨ᵇ ((@Function.comp β {x // x ∈ Delta} (L.Formula α) Subtype.val f) x).imp φ := by
            grind
        specialize hx'' M v default
        apply realize_imp.1 at hx''
        apply hx'' at hx
        assumption
      }
      use ψ
      constructor
      · exact hψ₁
      · unfold Theory.Iff
        tauto
  }


end CompleteType

end SeparatingTypes

end Theory

end Language

end FirstOrder

#min_imports
