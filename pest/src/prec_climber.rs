// pest. The Elegant Parser
// Copyright (c) 2018 Dragoș Tiselice
//
// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. All files in the project carrying such notice may not be copied,
// modified, or distributed except according to those terms.

//! Constructs useful in infix operator parsing with the precedence climbing method.

use std::collections::HashMap;
use std::iter::Peekable;
use std::ops::BitOr;
use std::marker::PhantomData;

use RuleType;
use iterators::Pair;

/// Associativity of an [`Operator`].
///
/// [`Operator`]: struct.Operator.html
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Assoc {
    /// Left `Operator` associativity
    Left,
    /// Right `Operator` associativity
    Right
}

type Prec = u32;
type OpNeighbor<R> = Option<Box<Op<R>>>;

pub struct Op<R: RuleType> {
    rule: R,
    kind: OpKind,
    next: OpNeighbor<R>
}

pub enum OpKind {
    Prefix,
    Suffix,
    Infix(Assoc)
}

impl<R: RuleType> Op<R> {

    pub fn prefix(rule: R) -> Self {
        Self {
            rule: rule,
            kind: OpKind::Prefix,
            next: None
        }
    }

    pub fn suffix(rule: R) -> Self {
        Self {
            rule: rule,
            kind: OpKind::Suffix,
            next: None
        }
    }

    pub fn infix(rule: R, assoc: Assoc) -> Self {
        Self {
            rule: rule,
            kind: OpKind::Infix(assoc),
            next: None
        }
    }
}

impl<R: RuleType> BitOr for Op<R> {
    type Output = Self;

    fn bitor(mut self, rhs: Self) -> Self {
        fn assign_next<R: RuleType>(op: &mut Op<R>, next: Op<R>) {
            if let Some(ref mut child) = op.next {
                assign_next(child, next);
            } else {
                op.next = Some(Box::new(next));
            }
        }

        assign_next(&mut self, rhs);
        self
    }
}

/// List of operators and precedences, which can perform [precedence climbing][1] on infix
/// expressions contained in a [`Pairs`]. The token pairs contained in the `Pairs` should start
/// with a *primary* pair and then alternate between an *operator* and a *primary*.
///
/// [1]: https://en.wikipedia.org/wiki/Operator-precedence_parser#Precedence_climbing_method
/// [`Pairs`]: ../iterators/struct.Pairs.html
pub struct PrecClimber<R: RuleType> {
    prec: Prec,
    ops: HashMap<R, (OpKind, Prec)>
}

type PrefixFn<'a, R, T> = Box<Fn(Pair<'a, R>, T) -> T + 'a>;
type SuffixFn<'a, R, T> = Box<Fn(T, Pair<'a, R>) -> T + 'a>;
type InfixFn<'a, R, T> = Box<Fn(T, Pair<'a, R>, T) -> T + 'a>;

pub struct PrecClimberMap<'a, R, F, T>
    where
    R: RuleType + 'static,
    F: Fn(Pair<'a, R>) -> T,
{
    ops: &'static HashMap<R, (OpKind, Prec)>,
    primary: F,
    prefix: Option<PrefixFn<'a, R, T>>,
    suffix: Option<SuffixFn<'a, R, T>>,
    infix: Option<InfixFn<'a, R, T>>,
    phantom: PhantomData<T>,
}

impl<R: RuleType> PrecClimber<R> {
    /// Creates a new `PrecClimber` from the `Operator`s contained in `ops`. Every entry in the
    /// `Vec` has precedence *index + 1*. In order to have operators with same precedence, they need
    /// to be chained with `|` between them.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pest::prec_climber::{Assoc, Operator, PrecClimber};
    /// # #[allow(non_camel_case_types)]
    /// # #[allow(dead_code)]
    /// # #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    /// # enum Rule {
    /// #     plus,
    /// #     minus,
    /// #     times,
    /// #     divide,
    /// #     power,
    /// #     negate,
    /// # }
    /// PrecClimber::new()
    ///     .op(Op::infix(Rule::plus, Assoc::Left) | Op::infix(Rule::minus, Assoc::Left)),
    ///     .op(Op::infix(Rule::times, Assoc::Left) | Op::infix(Rule::divide, Assoc::Left)),
    ///     .op(Op::infix(Rule::power, Assoc::Right))
    ///     .op(Op::prefix(Rule::negate))
    /// ```

    pub fn new() -> Self {
        Self {
            prec: 1,
            ops: HashMap::new(),
        }
    }

    pub fn op(mut self, op: Op<R>) -> Self {
        self.prec += 1;
        let mut iter = Some(op);
        while let Some( Op { rule, kind, next } ) = iter.take() {
            self.ops.insert(rule, (kind, self.prec));
            iter = next.map(|op| *op);
        }
        self
    }

    pub fn map_primary<'a, F, T>(&'static self, primary: F) -> PrecClimberMap<'a, R, F, T>
        where F: Fn(Pair<'a, R>) -> T
    {
        PrecClimberMap {
            ops: &self.ops,
            primary: primary,
            prefix: None,
            suffix: None,
            infix: None,
            phantom: PhantomData
        }
    }

}

impl<'a, R: RuleType, F: Fn(Pair<'a, R>) -> T, T> PrecClimberMap<'a, R, F, T> {

    pub fn map_prefix<X>(mut self, prefix: X) -> Self
        where X: Fn(Pair<'a, R>, T) -> T + 'a
    {
        self.prefix = Some(Box::new(prefix));
        self
    }

    pub fn map_suffix<X>(mut self, suffix: X) -> Self
        where X: Fn(T, Pair<'a, R>) -> T + 'a 
    {
        self.suffix = Some(Box::new(suffix));
        self
    }

    pub fn map_infix<X>(mut self, infix: X) -> Self
        where X: Fn(T, Pair<'a, R>, T) -> T + 'a
    {
        self.infix = Some(Box::new(infix));
        self
    }

    pub fn climb<P: Iterator<Item = Pair<'a, R>>>(
        &self,
        pest: P
    ) -> T {
        let peekable = &mut pest.peekable();
        let lhs = self.climb_unary(peekable);
        let expr = if let Some(ref infix) = self.infix {
            self.climb_binary(lhs, 0, peekable, infix)
        } else {
            lhs
        };
        expr
    }


    fn climb_unary<P: Iterator<Item = Pair<'a, R>>>(
        &self,
        pest: &mut Peekable<P>
    ) -> T {
        let expr = if let Some(ref prefix) = self.prefix {
            self.climb_prefix(pest, prefix)
        } else {
            (self.primary)(pest.next().unwrap())
        };
        let expr = if let Some(ref suffix) = self.suffix {
            self.climb_suffix(pest, expr, suffix)
        } else {
            expr
        };
        expr
    }

    // Climb the prefix of a unary expression
    fn climb_prefix<P: Iterator<Item = Pair<'a, R>>>(
        &self,
        pest: &mut Peekable<P>,
        prefix: &PrefixFn<'a, R, T>
    ) -> T {
        let pair = pest.next().unwrap();
        if let Some((OpKind::Prefix, _)) = self.ops.get(&pair.as_rule()) {
            let expr = self.climb_prefix(pest, prefix);
            prefix(pair, expr)
        } else {
            (self.primary)(pair)
        }
    }

    // Climb the suffix of a unary expression
    fn climb_suffix<P: Iterator<Item = Pair<'a, R>>>(
        &self,
        pest: &mut Peekable<P>,
        mut expr: T,
        suffix: &SuffixFn<'a, R, T>
    ) -> T {
        while pest.peek().is_some() {
            let rule = pest.peek().unwrap().as_rule();
            if let Some((OpKind::Suffix, _)) = self.ops.get(&rule) {
                expr = suffix(expr, pest.next().unwrap());
            } else {
                break;
            }
        }
        expr
    }

    // Climb a binary expression
    fn climb_binary<P: Iterator<Item = Pair<'a, R>>>(
        &self,
        mut lhs: T,
        min_prec: Prec,
        pest: &mut Peekable<P>,
        infix: &InfixFn<'a, R, T>,
    ) -> T {
        while pest.peek().is_some() {
            let rule = pest.peek().unwrap().as_rule();
            if let Some(&(OpKind::Infix(_), prec)) = self.ops.get(&rule) {
                if prec >= min_prec {
                    let op = pest.next().unwrap();
                    let mut rhs = self.climb_unary(pest);

                    while pest.peek().is_some() {
                        let rule = pest.peek().unwrap().as_rule();
                        if let Some(&(OpKind::Infix(assoc), new_prec)) = self.ops.get(&rule) {
                            if new_prec > prec || assoc == Assoc::Right && new_prec == prec {
                                rhs = self.climb_binary(rhs, new_prec, pest, infix);
                            } else {
                                break;
                            }
                        } else {
                            break;
                        }
                    }

                    lhs = infix(lhs, op, rhs);
                } else {
                    break;
                }
            } else {
                break;
            }
        }

        lhs
    }
}
