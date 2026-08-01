import Mathlib
import BachelorThesis.QuantifierElimination

set_option linter.style.whitespace false

open FirstOrder
open Language
open Theory

#check Language.order

namespace FirstOrder
namespace Language
namespace Theory
namespace dlo

universe u v
variable (L : Language.{u, v}) [L.IsOrdered]

def le (M : Type*) [L.Structure M] [M ⊨ L.dlo] : M → M → Prop := by
  rename_i _ struc _
  intro m₁ m₂
  let v : Fin 2 → M := fun x ↦ if h : x = 0 then m₁ else m₂
  use struc.RelMap leSymb v

lemma le_refl (M : Type*) [L.Structure M] [M ⊨ L.dlo] :
  ∀ (a : M), (Theory.dlo.le L M) a a := by
    rename_i _ _ is_model
    unfold dlo at is_model; unfold linearOrderTheory at is_model
    unfold partialOrderTheory at is_model; unfold preorderTheory at is_model
    have h : Sentence.Realize M (@leSymb L _).reflexive := by simp_all
    unfold Relations.reflexive at h; unfold Sentence.Realize at h; unfold Formula.Realize at h
    rw [BoundedFormula.realize_all] at h
    intro m
    specialize h m
    unfold le
    simp_all only [Set.union_insert, Set.union_singleton, model_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, Relations.realize_total,
      Relations.realize_antisymmetric, Relations.realize_reflexive, Relations.realize_transitive,
      forall_eq, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Function.comp_apply,
      BoundedFormula.realize_rel₂, Term.realize_var, Sum.elim_inr, dite_eq_ite, ite_self]
    have this : @Matrix.vecCons (↑M) 1 (@Fin.snoc 0 (fun a ↦ ↑M) default m 0 )
      ![@Fin.snoc 0 (fun a ↦ ↑M) default m 0 ] = fun (x : Fin (Nat.succ 1)) ↦ m :=
        List.ofFn_inj.mp rfl
    rwa [← this]

lemma le_trans (M : Type*) [L.Structure M] [M ⊨ L.dlo] :
  ∀ a b c : M, (Theory.dlo.le L M a b) → (Theory.dlo.le L M b c) → (Theory.dlo.le L M a c) := by
    rename_i _ _ is_model
    unfold le
    intro m₁ m₂ m₃ hm₁m₂ hm₂m₃
    have h : Sentence.Realize M (@leSymb L _).transitive := by
      unfold dlo at is_model; unfold linearOrderTheory at is_model
      unfold partialOrderTheory at is_model; unfold preorderTheory at is_model
      simp_all
    simp_all only [Fin.isValue, dite_eq_ite]
    unfold Relations.transitive at h; unfold Sentence.Realize at h; unfold Formula.Realize at h
    rw [BoundedFormula.realize_all] at h
    specialize h m₁
    rw [BoundedFormula.realize_all] at h
    specialize h m₂
    rw [BoundedFormula.realize_all] at h
    specialize h m₃
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Function.comp_apply,
      BoundedFormula.realize_imp, BoundedFormula.realize_rel₂, Term.realize_var, Sum.elim_inr,
      Fin.snoc_apply_zero] at h
    have this₁ : ![@Fin.snoc 0 (fun a ↦ ↑M) default m₁ 0,
      @Fin.snoc 2 (fun a ↦ ↑M) (Fin.snoc (Fin.snoc default m₁) m₂) m₃ 1]
      = fun (x : Fin (Nat.succ 1)) ↦ if x = 0 then m₁ else m₂ := List.ofFn_inj.mp rfl
    have this₂ : ![@Fin.snoc 2 (fun a ↦ ↑M) (Fin.snoc (Fin.snoc default m₁) m₂) m₃ 1,
      @Fin.snoc 2 (fun a ↦ ↑M) (Fin.snoc (Fin.snoc default m₁) m₂) m₃ 2 ]
      = fun x ↦ if x = 0 then m₂ else m₃ := List.ofFn_inj.mp rfl
    have this₃ : ![@Fin.snoc 0 (fun a ↦ ↑M) default m₁ 0,
      @Fin.snoc 2 (fun a ↦ ↑M) (Fin.snoc (Fin.snoc default m₁) m₂) m₃ 2]
      = fun x ↦ if x = 0 then m₁ else m₃ := List.ofFn_inj.mp rfl
    rw [this₁, this₂, this₃] at h
    exact h hm₁m₂ hm₂m₃

lemma le_antisymm (M : Type*) [L.Structure M] [M ⊨ L.dlo] :
  ∀ (a b : M), dlo.le L M a b → dlo.le L M b a → a = b := by
    unfold dlo.le
    intro a b hab hba
    rename_i _ _ is_model
    unfold dlo at is_model; unfold linearOrderTheory at is_model;
    unfold partialOrderTheory at is_model
    have hM : M ⊨ (@leSymb L _).antisymmetric := by simp_all
    unfold Relations.antisymmetric at hM; unfold Sentence.Realize at hM
    unfold Formula.Realize at hM
    rw [BoundedFormula.realize_all] at hM
    specialize hM a
    rw [BoundedFormula.realize_all] at hM
    specialize hM b
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Function.comp_apply,
      BoundedFormula.realize_imp, BoundedFormula.realize_rel₂, Term.realize_var, Sum.elim_inr,
      Fin.snoc_apply_zero, BoundedFormula.realize_bdEqual] at hM
    have this₁ : ![@Fin.snoc 0 (fun a ↦ M) default a 0,
      @Fin.snoc 1 (fun a ↦ M) (Fin.snoc default a) b 1]
      = fun x ↦ if h : x = 0 then a else b := List.ofFn_inj.mp rfl
    have this₂ : ![@Fin.snoc 1 (fun a ↦ M) (Fin.snoc default a) b 1,
    @Fin.snoc 0 (fun a ↦ M) default a 0]
    = fun x ↦ if h : x = 0 then b else a := List.ofFn_inj.mp rfl
    rw [this₁, this₂] at hM
    simp_all only [Set.union_insert, Set.union_singleton, model_iff, Set.mem_insert_iff,
      forall_eq_or_imp, Relations.realize_total, Relations.realize_antisymmetric, Fin.isValue,
      dite_eq_ite, Nat.succ_eq_add_one, Nat.reduceAdd, forall_const]
    exact ((fun a ↦ hM) ∘ fun a ↦ L) L

lemma le_total (M : Type*)  [L.Structure M] [M ⊨ L.dlo] :
  ∀ a b : M, dlo.le L M a b ∨ dlo.le L M b a := by
    intro a b
    unfold dlo.le
    rename_i _ _ is_model
    unfold dlo at is_model; unfold linearOrderTheory at is_model
    have hM : M ⊨ (@leSymb L _).total := by simp_all
    unfold Relations.total at hM
    unfold Sentence.Realize at hM; unfold Formula.Realize at hM
    rw [BoundedFormula.realize_all] at hM
    specialize hM a
    rw [BoundedFormula.realize_all] at hM
    specialize hM b
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Function.comp_apply,
      BoundedFormula.realize_sup, BoundedFormula.realize_rel₂, Term.realize_var, Sum.elim_inr,
      Fin.snoc_apply_zero] at hM
    obtain hM₁ | hM₂ := hM
    · left
      have this : ![@Fin.snoc 0 (fun a ↦ M) default a 0,
      @Fin.snoc 1 (fun a ↦ M) (Fin.snoc default a) b 1] = fun x ↦ if h : x = 0 then a else b :=
        List.ofFn_inj.mp rfl
      rwa [← this]
    · right
      have this : ![@Fin.snoc 1 (fun a ↦ M) (Fin.snoc default a) b 1,
      @Fin.snoc 0 (fun a ↦ M) default a 0] = fun x ↦ if h : x = 0 then b else a :=
        List.ofFn_inj.mp rfl
      rwa [← this]

end dlo
end Theory

namespace order

lemma dlo_PartialIso_extends_lt_of_finite_source {M : Type*} {N : Type*}
  [Nonempty M] [Nonempty N] [LinearOrder M] [LinearOrder N]
  [Language.order.Structure M] [Language.order.Structure N]
  [Language.order.OrderedStructure M] [Language.order.OrderedStructure N]
  [DenselyOrdered M] [DenselyOrdered N] [M ⊨ Language.order.dlo] [N ⊨ Language.order.dlo]
  (f : Language.order.PartialIso M N) (hf₁ : Nonempty f.source) (hf₂ : Finite f.source) (m : M)
  (hm : ∀ m' ∈ f.source, m < m') :
    ∃ g : PartialIso M N, m ∈ g.source ∧ f ≤ g := by
      let source_set : Finset M := Set.Finite.toFinset hf₂
      let m_min := source_set.min
      have hf₃ : Finset.Nonempty source_set := by
        apply Classical.choice at hf₁
        use hf₁
        unfold source_set
        sorry
      have h_m_min := Finset.min_of_nonempty hf₃
      obtain ⟨ m_min', h_m_min' ⟩ := h_m_min

      sorry


theorem dlo_HasQE : HasQE (Language.order.dlo) := by
  apply HasQE_if_BackAndForth_of_finite
  intro M N
  let _ : LE M := {
    le := dlo.le Language.order M
  }
  let _ : LE N := {
    le := dlo.le Language.order N
  }
  let _ : LinearOrder M := {
    le := dlo.le Language.order M
    le_refl := dlo.le_refl Language.order M
    le_trans := dlo.le_trans Language.order M
    lt_iff_le_not_ge := by intros; rfl
    le_antisymm := dlo.le_antisymm Language.order M
    le_total := dlo.le_total Language.order M
    toDecidableLE := Classical.decRel LE.le
    min_def := by intros; rfl
    max_def := by intros; rfl
    compare_eq_compareOfLessAndEq := by intros; rfl
  }
  let _ : LinearOrder N := {
    le := dlo.le Language.order N
    le_refl := dlo.le_refl Language.order N
    le_trans := dlo.le_trans Language.order N
    lt_iff_le_not_ge := by intros; rfl
    le_antisymm := dlo.le_antisymm Language.order N
    le_total := dlo.le_total Language.order N
    toDecidableLE := Classical.decRel LE.le
    min_def := by intros; rfl
    max_def := by intros; rfl
    compare_eq_compareOfLessAndEq := by intros; rfl
  }
  let _ : Language.order.OrderedStructure M := {
    relMap_leSymb := by
      intro v
      have hv₁ : v = fun x ↦ if h : x = 0 then (v 0) else (v 1) := by
        ext x
        grind
      constructor
      · intro hv₂
        rw [hv₁] at hv₂
        finiteness
      · intro hv₂
        rw [hv₁]
        finiteness
  }
  let _ : Language.order.OrderedStructure N := {
    relMap_leSymb := by
      intro v
      have hv₁ : v = fun x ↦ if h : x = 0 then (v 0) else (v 1) := by
        ext x
        grind
      constructor
      · intro hv₂
        rw [hv₁] at hv₂
        finiteness
      · intro hv₂
        rw [hv₁]
        finiteness
  }
  have hM := denselyOrdered_of_dlo Language.order M
  have hN := denselyOrdered_of_dlo Language.order N
  have hM' : Nonempty M := M.nonempty'
  have hN' : Nonempty N := N.nonempty'
  unfold IsBackAndForthSystem
  constructor
  · intro f hf m
    simp only [Set.mem_ofPred_eq] at hf
    let lt_set : Set M := {x | x ∈ f.source ∧ x < m}
    let gt_set : Set M := {x | x ∈ f.source ∧ m < x}
    let lt_finset : Finset M := Set.Finite.toFinset (Finite.Set.finite_sep f.source fun a ↦ a < m)
    let gt_finset : Finset M := Set.Finite.toFinset (Finite.Set.finite_sep f.source (LT.lt m))
    by_cases hm : m ∈ f.source
    · use f
      constructor
      · exact hf
      · constructor
        · exact hm
        · exact PartialIso.le_refl M N f
    · by_cases h₁ : Nonempty lt_finset
      · by_cases h₂ : Nonempty gt_finset
        · sorry
        · sorry
      · by_cases h₃ : Nonempty gt_finset
        · sorry
        · apply Classical.choice at hN'
          let g : Language.order.PartialIso M N := {
            source := {m}
            target := {hN'}
            toFun := fun x ↦ hN'
            invFun := fun x ↦ m
            map_source' := by intros; simp
            map_target' := by intros; simp
            left_inv' := by intros; simp_all
            right_inv' := by intros; simp_all
            map_fun' := by intros; trivial
            map_rel' := by
              intro n r a ha
              unfold Language.order at r
              let r' : orderRel n := r
              cases r'
              have hr : r = @IsOrdered.leSymb Language.order _ := by
                cases r
                exact ((fun a ↦ a) ∘ fun a ↦ a) rfl
              rw [hr]
              simp_all only [nonempty_subtype, not_exists, Set.mem_singleton_iff,
                Fin.forall_fin_two, Fin.isValue, relMap_leSymb, Std.le_refl, Function.comp_apply]
          }
          use g
          constructor
          · simp only [Set.mem_ofPred_eq]
            unfold g
            exact Finite.of_subsingleton
          constructor
          · unfold g
            exact Set.mem_singleton m
          · apply (PartialIso.le_def M N f g).2
            have hf : ¬ ∃ x, x ∈ f.source := by
              by_contra h
              obtain ⟨ x, hx ⟩ := h
              by_cases hx₁ : x < m
              · have hx₁' : x ∈ lt_set := by
                  unfold lt_set
                  sorry
                sorry
              sorry
            sorry
  · sorry
end order
end Language
end FirstOrder

#min_imports
