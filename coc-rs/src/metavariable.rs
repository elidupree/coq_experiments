pub enum MetavariableKind {
    Term,
    HasType,
    SingleSubstitution,
}

pub enum TermConstructor {}

macro_rules! constructor {
    ($($a:tt)*) => {};
}

constructor! {
    Lambda () -> AbstractionKind;
    ForAll () -> AbstractionKind;
    Type () -> Term;
    Prop () -> Term;
    VariableUsage () -> Term;
    Abstraction (kind: AbstractionKind, argument_type: Term, body: Term, bindings: BindingTree) -> Term;
    Apply (m: Term, n: Term) -> Term;

    BindNothing () -> BindingTree;
    BindVariable () -> BindingTree;
    BindBranch (m: BindingTree, n: BindingTree) -> BindingTree;

    BetaReductionHere (replaced_bindings: Binding3) -> WhichBetaReduction;
    BetaReductionL (reduction: WhichBetaReduction) -> WhichBetaReduction;
    BetaReductionR (reduction: WhichBetaReduction) -> WhichBetaReduction;

    ContextHole ()-> Context;
    ContextKnownVariable (binding_term: Term, binding_context: Context)-> Context;
    ContextBranch(m: Context,n: Context)-> Context;

    // Note: implicitly prevents binding the same thing a second time, by requiring ContextHole
    AddBindingsNothing(context: Context, inserted_context: Context) -> AddBindings BindNothing inserted_context context context;
    AddBindingsVariable(inserted_context: Context) -> AddBindings BindVariable inserted_context ContextHole inserted_context;
    AddBindingsBranch (lb: BindingTree,rb: BindingTree,lc: Context, rc: Context,lc2: Context, rc2: Context,inserted_context: Context,
        _: AddBindings lb inserted_context lc lc2,
        _: AddBindings rb inserted_context rc rc2,
      )
      -> AddBindings (BindBranch lb rb) inserted_context (ContextBranch lc rc) (ContextBranch lc2 rc2);

    GrowFromLeaf(inserted_bindings: BindingTree)-> GrowFromLeaves inserted_bindings BindVariable inserted_bindings;
    GrowNothing(inserted_bindings: BindingTree)-> GrowFromLeaves inserted_bindings BindNothing BindNothing;
    GrowFromBranch(m: BindingTree, n: BindingTree, inserted_bindings: BindingTree,
        m2, BindingTree, n2: BindingTree,
        _:GrowFromLeaves m m2 inserted_bindings,
        _:GrowFromLeaves n n2 inserted_bindings,
    )-> GrowFromLeaves inserted_bindings (BindBranch m n) (BindBranch m2 n2);

    // Note: implicitly requires disjointness, by not having a constructor for BindVariable other than next to BindNothing
    UnionBindingsNothingL(bindings: BindingTree) -> UnionBindings BindNothing bindings bindings;
    UnionBindingsNothingR(bindings: BindingTree) -> UnionBindings bindings BindNothing bindings;
    UnionBindingsBranch(m: BindingTree, n: BindingTree, m2: BindingTree, n2: BindingTree, m3: BindingTree, n3: BindingTree,
        _:UnionBindings m m2 m3,
        _:UnionBindings n n2 n3,
    ) -> UnionBindings (BindBranch m n) (BindBranch m2 n2) (BindBranch m3 n3);

    PortBindingsNothing(
        reduction: WhichBetaReduction,
    ) -> PortBindings reduction BindNothing BindNothing;
    PortBindingsHere(
        replaced_bindings: BindingTree,
        bindings_in_argument_type: BindingTree, bindings_in_body: BindingTree,
        bindings_in_argument: BindingTree,
        bindings_in_new_copies_of_argument: BindingTree,
        new_bindings: BindingTree,
        _: GrowFromLeaves bindings_in_argument replaced_bindings bindings_in_new_copies_of_argument,
        _:UnionBindings(bindings_in_body,bindings_in_new_copies_of_argument),
    ) -> PortBindings
      (BetaReductionHere replaced_bindings)
      (BindBranch (BindBranch bindings_in_argument_type bindings_in_body) bindings_in_argument)
      new_bindings;

    PortBindingsL (
        reduction: WhichBetaReduction,
        m: BindingTree, n: BindingTree, m2: BindingTree,
        _: PortBindings reduction m m2,
    )->PortBindings
      (BetaReductionL reduction)
      (BindBranch m n)
      (BindBranch m2 n);
    PortBindingsR (
        reduction: WhichBetaReduction,
        m: BindingTree, n: BindingTree, n2: BindingTree,
        _: PortBindings reduction n n2,
    )->PortBindings
      (BetaReductionR reduction)
      (BindBranch m n)
      (BindBranch m n2);

    SingleSubstitutionNothing (
        term: Term, replacement: Term
    ) -> SingleSubstitution BindNothing replacement term term;

    SingleSubstitutionBoundVariable (
        term: Term, replacement: Term
    ) -> SingleSubstitution BindVariable replacement term replacement;

    SingleSubstitutionAbstraction (
        kind: AbstractionKind, argument_type: Term, body: Term, bindings: BindingTree,
        argument_type2: Term, body2: Term,
        argument_replaced_bindings: BindingTree, body_replaced_bindings: BindingTree,
        replacement: Term,
        _ : SingleSubstitution argument_replaced_bindings replacement argument_type argument_type2,
        _ : SingleSubstitution body_replaced_bindings replacement body body2,
    ) -> SingleSubstitution
        (BindBranch argument_replaced_bindings body_replaced_bindings)
        replacement
        (Abstraction kind argument_type body bindings)
        (Abstraction kind argument_type2 body2 bindings);

    SingleSubstitutionApply (
        repl: Term, m: Term, n: Term, m2: Term, n2: Term, mb: BindingTree, nb: BindingTree,
        _ : SingleSubstitution mb repl m m2,
        _ : SingleSubstitution nb repl n n2,
    ) -> SingleSubstitution bindings repl (Apply m n) (Apply m2 n2);


    BetaReduction (
        argument_type: Term, body: Term, bindings: BindingTree,
        argument: Term,
        result: Term,
        _:SingleSubstitution bindings argument body result,
    )-> BetaReductionOneStep BetaReductionHere (Apply (Abstraction Lambda argument_type body bindings) argument) result;

    BetaCompatibilityApplyLeft (
        m: Term, n: Term, m2: Term,
        reduction: WhichBetaReduction,
        _ : BetaReductionOneStep reduction m m2,
    )-> BetaReductionOneStep (BetaReductionL reduction) (Apply m n) (Apply m2 n);

    BetaCompatibilityApplyRight (
        m: Term, n: Term, n2: Term,
        reduction: WhichBetaReduction,
        _ : BetaReductionOneStep reduction n n2,
    )-> BetaReductionOneStep (BetaReductionR reduction) (Apply m n) (Apply m n2);

    BetaCompatibilityAbstractionArgType (
        kind: AbstractionKind, argument_type: Term, body: Term, bindings: BindingTree,
        argument_type2: Term,
        reduction: WhichBetaReduction,
        _ : BetaReductionOneStep reduction argument_type argument_type2,
    )-> BetaReductionOneStep (BetaReductionL reduction) (Abstraction kind argument_type body bindings) (Abstraction kind argument_type2 body bindings);

    BetaCompatibilityAbstractionBody (
        kind: AbstractionKind, argument_type: Term, body: Term, bindings: BindingTree, bindings2: BindingTree,
        body2: Term,
        reduction: WhichBetaReduction,
        _ : PortBindings reduction bindings bindings2,
        _ : BetaReductionOneStep reduction body body2,
    )-> BetaReductionOneStep (BetaReductionR reduction) (Abstraction kind argument_type body bindings) (Abstraction kind argument_type body2 bindings2);


    BetaReductionIsConversion (reduction: WhichBetaReduction, a: Term, b: Term,
        _:BetaReductionOneStep reduction a b) -> BetaConversion a b;
    BetaReflexive (term: Term) -> BetaConversion term term;
    BetaSymmetric (x: Term, y: Term, _:BetaConversion x y)-> BetaConversion y x;
    BetaTransitive (x: Term, y: Term, z: Term,_:BetaConversion x y,_:BetaConversion y z)-> BetaConversion x z;

    TypeIsSort () -> IsSort Type;
    PropIsSort () -> IsSort Prop;

    // HasTypeThatIsSortCons (term: Term, context: Context, sort: Term,
    //   _: HasType term context sort ContextHole) -> HasTypeThatIsSort term context;

    TypeOfProp() -> HasType Prop ContextHole Type ContextHole;
    TypeOfVariableUsage(
        kind: AbstractionKind, argument_type: Term, body: Term, bindings: BindingTree,
        argument_context: Context, body_context: Context,
    ) -> HasType
      VariableUsage (ContextKnownVariable (Abstraction kind argument_type body bindings) (ContextBranch argument_context body_context))
      argument_type argument_context;

    TypeOfForAll (
        argument_type: Term, return_type: Term, argument_context: Context, return_context: Context, return_context_before_bindings: Context, bindings: BindingTree,
        s1 : Term, s2 : Term,
        _ : HasType argument_type argument_context s1 ContextHole,
        _ : HasType return_type return_context s2 ContextHole,
        _ : IsSort s1,
        _ : IsSort s2,
        _ : BindingsMinimal bindings,
        _ : AddBindings bindings (ContextKnownVariable (Abstraction ForAll argument_type return_type bindings) (ContextBranch argument_context return_context_before_bindings)) return_context_before_bindings return_context
    ) -> HasType
        (Abstraction ForAll argument_type return_type bindings)
        (ContextBranch argument_context return_context)
        s2 ContextHole;

    TypeOfLambda (
        argument_type: Term, argument_context: Context,
        body: Term, body_context: Context, body_context_before_bindings: Context,
        return_type: Term, return_context: Context, return_context_before_bindings: Context,
        lambda_bindings: BindingTree, forall_bindings: BindingTree,
        s : Term,
        _ : HasType (Abstraction ForAll argument_type return_type forall_bindings) (ContextBranch argument_context return_context_before_bindings) s ContextHole,
        _ : HasType body body_context return_type return_context,
        _ : BindingsMinimal lambda_bindings,
        _ : AddBindings lambda_bindings (ContextKnownVariable (Abstraction Lambda argument_type body lambda_bindings) (ContextBranch argument_context body_context_before_bindings)) body_context_before_bindings body_context
    ) -> HasType
        (Abstraction Lambda argument_type body lambda_bindings)
        (ContextBranch argument_context body_context_before_bindings)
        (Abstraction ForAll argument_type return_type forall_bindings)
        (ContextBranch argument_context return_context_before_bindings);

    TypeBetaConversion (
        value: Term, value_context: Context,
        ty: Term, type_context: Context,
        ty2: Term,
        s: Term,
        _ : HasType value value_context ty type_context,
        _ : HasType ty2 type_context s ContextHole,
        _ : IsSort s,
        _ : BetaConversion ty ty2,
    ) -> HasType value value_context ty2 type_context;
}
