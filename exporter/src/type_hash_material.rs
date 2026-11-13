//! Exact raw syntax domain consumed by Lean WorldTypeHash. No compiler query
//! result is inspected, and no child's final TypeId replaces constructor syntax.
use rustc_middle::ty;
use rustc_middle::ty::inherent::IntoKind;

pub(super) fn eligible(input: ty::Ty<'_>) -> bool {
    type_in_binder(input, false)
}
fn arguments_in_binder(arguments: ty::GenericArgsRef<'_>, bound: bool) -> bool {
    arguments.iter().all(|argument| match argument.kind() {
        ty::GenericArgKind::Type(child) => type_in_binder(child, bound),
        ty::GenericArgKind::Lifetime(_) => true,
        ty::GenericArgKind::Const(value) => constant_in_binder(value, bound),
    })
}
fn region_variables(variables: &[ty::BoundVariableKind<'_>]) -> bool {
    variables.iter().all(|value| matches!(value, ty::BoundVariableKind::Region(_)))
}
fn type_in_binder(input: ty::Ty<'_>, bound: bool) -> bool {
    match *input.kind() {
        ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Never | ty::Str
        | ty::Foreign(_) => true,
        ty::Slice(child) | ty::RawPtr(child, _) => type_in_binder(child, bound),
        ty::Array(child, length) => type_in_binder(child, bound) && constant_in_binder(length, bound),
        ty::Ref(_, child, _) => type_in_binder(child, bound),
        ty::Pat(base, pattern) => type_in_binder(base, bound) && pattern_in_binder(pattern, bound),
        ty::Dynamic(predicates, _) => predicates.iter().all(|predicate| {
            let binder = predicate.bound_vars().iter().all(|variable| matches!(variable, ty::BoundVariableKind::Region(_)));
            binder && match predicate.skip_binder() {
                ty::ExistentialPredicate::Trait(value) => arguments_in_binder(value.args, true),
                ty::ExistentialPredicate::Projection(value) => arguments_in_binder(value.args, true) && match value.term.kind() {
                    ty::TermKind::Ty(value) => type_in_binder(value, true),
                    ty::TermKind::Const(value) => constant_in_binder(value, true),
                },
                ty::ExistentialPredicate::AutoTrait(_) => true,
            }
        }),
        ty::Tuple(children) => children.iter().all(|child| type_in_binder(child, bound)),
        ty::Adt(_, arguments) | ty::Closure(_, arguments) => arguments_in_binder(arguments, bound),
        ty::FnDef(_, arguments) => region_variables(arguments.bound_vars()) &&
            arguments_in_binder(arguments.skip_binder(), bound || !arguments.bound_vars().is_empty()),
        ty::FnPtr(signature, _) => region_variables(signature.bound_vars()) &&
            signature.skip_binder().inputs_and_output.iter().all(|child| type_in_binder(child, true)),
        _ => false,
    }
}
fn constant_in_binder(input: ty::Const<'_>, bound: bool) -> bool {
    let ty::ConstKind::Value(value) = input.kind() else { return false; };
    type_in_binder(value.ty, bound) && match **value.valtree {
        ty::ValTreeKind::Leaf(_) => true,
        ty::ValTreeKind::Branch(children) => children.iter().all(|child| constant_in_binder(child, bound)),
    }
}

fn pattern_in_binder(pattern: ty::Pattern<'_>, bound: bool) -> bool {
    match pattern.kind() {
        ty::PatternKind::Range {start, end} => constant_in_binder(start, bound) && constant_in_binder(end, bound),
        ty::PatternKind::Or(patterns) => !patterns.is_empty() && patterns.iter().all(|pattern| pattern_in_binder(pattern, bound)),
        ty::PatternKind::NotNull => true,
    }
}
