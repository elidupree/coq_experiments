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
    Type () -> Term;
    Prop () -> Term;
    VariableUsage (var: Term) -> Term;
    ForAll (var: Term, ret: Term) -> Term;
    Lambda (var: Term, body: Term) -> Term;
    Apply (m: Term, n: Term) -> Term;

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


    SingleSubstitutionSort (
        s, _ : IsSort [s],
    ) -> SingleSubstitution [s var repl s];

    SingleSubstitutionSameVariable (
        var, repl, usage = VariableUsage [var],
    ) -> SingleSubstitution [usage var repl repl];

    SingleSubstitutionDifferentVariable (
        var, repl, var2 != var, usage = VariableUsage [var2],
    ) -> SingleSubstitution [usage var repl usage];

    SingleSubstitutionApply (
        var, repl, m, n, mn, m2, n2, mn2,
        _ : SingleSubstitution [m var repl m2],
        _ : SingleSubstitution [n var repl n2],
    ) -> SingleSubstitution [mn var repl mn2]
}
