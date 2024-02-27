use std::collections::{HashMap, HashSet};

use powdr_ast::analyzed::types::Type;

use crate::type_builtins::elementary_type_bounds;

#[derive(Default, Clone)]
pub struct Unifier {
    /// Inferred type constraints (traits) on type variables.
    type_var_bounds: HashMap<String, HashSet<String>>,
    /// Substitutions for type variables
    substitutions: HashMap<String, Type>,
}

impl Unifier {
    pub fn substitutions(&self) -> &HashMap<String, Type> {
        &self.substitutions
    }

    pub fn type_var_bounds(&self, type_var: &String) -> HashSet<String> {
        self.type_var_bounds
            .get(type_var)
            .cloned()
            .unwrap_or_default()
    }

    pub fn add_type_var_bound(&mut self, type_var: String, bound: String) {
        self.type_var_bounds
            .entry(type_var)
            .or_default()
            .insert(bound);
    }

    pub fn add_substitution(&mut self, type_var: String, ty: Type) -> Result<(), String> {
        if ty.contains_type_var(&type_var) {
            Err(format!(
                "Cannot unify types {ty} and {type_var}: They depend on each other"
            ))?
        }
        let subs = [(type_var.clone(), ty.clone())].into();

        for bound in self.type_var_bounds(&type_var) {
            self.ensure_bound(&ty, bound)?;
        }

        self.substitutions
            .values_mut()
            .for_each(|t| t.substitute_type_vars(&subs));
        self.substitutions.insert(type_var, ty);
        Ok(())
    }

    pub fn unify_types(&mut self, mut inner: Type, mut expected: Type) -> Result<(), String> {
        if let (Type::TypeVar(n1), Type::TypeVar(n2)) = (&inner, &expected) {
            if n1 == n2 {
                return Ok(());
            }
        }

        inner.substitute_type_vars(&self.substitutions);
        expected.substitute_type_vars(&self.substitutions);

        if inner == expected {
            return Ok(());
        }
        match (inner, expected) {
            (Type::Bottom, _) | (_, Type::Bottom) => Ok(()),
            (Type::TypeVar(n1), Type::TypeVar(n2)) if n1 == n2 => Ok(()),
            (Type::TypeVar(name), ty) | (ty, Type::TypeVar(name)) => {
                // TODO this is the reason why we have to re-substitute for each
                // recursive call.
                // Maybe it would be better to store those and only apply them?
                self.add_substitution(name, ty)
            }
            (Type::Function(f1), Type::Function(f2)) => {
                if f1.params.len() != f2.params.len() {
                    Err(format!(
                        "Function types have different number of parameters: {f1} and {f2}"
                    ))?;
                }
                for (p1, p2) in f1.params.into_iter().zip(f2.params.into_iter()) {
                    self.unify_types(p1, p2)?;
                }
                self.unify_types(*f1.value, *f2.value)
            }
            (Type::Array(a1), Type::Array(a2)) => {
                if a1.length != a2.length {
                    Err(format!("Array types have different lengths: {a1} and {a2}"))?;
                }
                self.unify_types(*a1.base, *a2.base)
            }
            (Type::Tuple(t1), Type::Tuple(t2)) => {
                if t1.items.len() != t2.items.len() {
                    Err(format!(
                        "Tuple types have different number of items: {t1} and {t2}"
                    ))?;
                }
                t1.items
                    .into_iter()
                    .zip(t2.items.into_iter())
                    .try_for_each(|(i1, i2)| self.unify_types(i1, i2))
            }

            (ty1, ty2) => Err(format!("Cannot unify types {ty1} and {ty2}")),
        }
    }

    pub fn ensure_bound(&mut self, ty: &Type, bound: String) -> Result<(), String> {
        if let Type::TypeVar(n) = ty {
            self.add_type_var_bound(n.clone(), bound);
            Ok(())
        } else {
            let bounds = elementary_type_bounds(ty);
            if bounds.contains(&bound.as_str()) {
                Ok(())
            } else {
                Err(format!(
                    "Type {ty} is required to satisfy trait {bound}, but does not."
                ))
            }
        }
    }
}
