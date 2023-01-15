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

    DescendantHere () -> WhichDescendant;
    DescendantL (descendant: WhichDescendant) -> WhichDescendant;
    DescendantR (descendant: WhichDescendant) -> WhichDescendant;

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

    // Note: implicitly requires disjointness, not having a constructor for BindVariable other than next to BindNothing
    UnionBindingsNothingL(bindings: BindingTree) -> UnionBindings BindNothing bindings bindings;
    UnionBindingsNothingR(bindings: BindingTree) -> UnionBindings bindings BindNothing bindings;
    UnionBindingsBranch(m: BindingTree, n: BindingTree, m2, BindingTree, n2: BindingTree, m3, BindingTree, n3: BindingTree,
        _:UnionBindings m m2 m3,
        _:UnionBindings n n2 n3,
    ) -> UnionBindings (BindBranch m n) (BindBranch m2 n2) (BindBranch m3 n3);

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


    TypeIsSort (t = Type) -> IsSort [t];
    PropIsSort (p = Prop) -> IsSort [p];

    TypeOfProp(
        p = Prop, t = Type,
    ) -> HasType [p t];

    TypeOfVariable (
        var, usage = VariableUsage [var],
    ) -> HasType [usage var];

    TypeOfForAll (
        var, ret, s1, s2,
        f = ForAll [var ret],
        _ : HasType [var s1],
        _ : HasType [ret s2],
        _ : IsSort [s1],
        _ : IsSort [s2],
    ) -> HasType [f s2];

    TypeOfLambda (
        var, body, ret, s,
        l = Lambda [var body],
        f = ForAll [var ret],
        _ : HasType [body ret],
        _ : HasType [f s],
        _ : IsSort [s],
    ) -> HasType [l f];

    TypeOfApply (
        m, n, var, ret, ret2,
        mn = Apply [m n],
        f = ForAll [var ret],
        _ : HasType [m f],
        _ : HasType [n var],
        _ : SingleSubstitution [ret var n ret2],
    ) -> HasType [mn ret2];

    TypeBetaConversion (
        x, ty, ty2, s,
        _ : HasType [x ty],
        _ : HasType [ty2 s],
        _ : IsSort [s],
        _ : BetaConversion [ty ty2],
    ) -> HasType [x ty2];


    BindNothing () -> BindingTree;
    BindVariable () -> BindingTree;
    BindBranch (m, n) -> BindingTree;


    SingleSubstitutionNothing (
        term, bindings = BindNothing, repl
    ) -> SingleSubstitution [term bindings repl term];

    SingleSubstitutionBoundVariable (
        term, bindings = BindVariable, repl
    ) -> SingleSubstitution [term bindings repl repl];

    SingleSubstitutionForAll (
        var, ret, f_ret_b, f = ForAll [var ret f_ret_b]
        var2, ret2, f2 = ForAll [var2 ret2 f_ret_b]
        varb, retb, bindings = BindBranch [varb retb],
        repl,
        _ : SingleSubstitution [var varb repl var2],
        _ : SingleSubstitution [ret retb repl ret2],
    ) -> SingleSubstitution [f bindings repl f2];

    SingleSubstitutionApply (
        repl, m, n, mn, m2, n2, mn2, mb, nb, bindings = BindBranch [mb nb],
        _ : SingleSubstitution [m mb repl m2],
        _ : SingleSubstitution [n nb repl n2],
    ) -> SingleSubstitution [mn bindings repl mn2];


    BetaRefl ()-> BetaConversion [t t];

    BetaReduction (
        l = Lambda [argument_type body bindings],
        argument,
        application = Apply [l argument],
        result,
        _:SingleSubstitution [body,bindings,argument, result], ?????????
    )-> BetaReductionOneStep [application result];

    BetaCompatibilityApplyLeft (
        mn = Apply [m n],
        mn2 = Apply [m2 n],
        b : BetaReductionOneStep [m m2],
    )-> BetaReductionOneStep [mn mn2];

    BetaCompatibilityApplyRight (
        mn = Apply [m n],
        mn2 = Apply [m n2],
        b : BetaReductionOneStep [n n2],
    )-> BetaReductionOneStep [mn mn2];

    BetaCompatibilityLambdaArgType (
        l = Lambda [argument_type body bindings],
        l2 = Lambda [argument_type2 body bindings],
        b : BetaReductionOneStep [argument_type argument_type2],
    )-> BetaReductionOneStep [l l2];

    BetaCompatibilityLambdaBody (
        l = Lambda [argument_type body bindings],
        l2 = Lambda [argument_type body2 bindings],
        b : BetaReductionOneStep [body body2],
    )-> BetaReductionOneStep [l l2];

    PortBindingsBetaReduction (
        b = BetaReductionOneStep [l argument application result],
        bindings = BindBranch [argument_bindings body_bindings],
        new_body_bindings,
        _: SpliceBindings [body_bindings, l_bindings, new_body_bindings]
        new_bindings = BindBranch [argument_bindings body_bindings],
    )->PortBindings [bindings b new_bindings]

    PortBindNothing (
        b, bindings = BindNothing,
    )->PortBindings [bindings b bindings]

    PortBindVariable (
        b, bindings = BindNothing,
    )->PortBindings [bindings b bindings]
}
