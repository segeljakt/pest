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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Position {
    /// Prefix unary `Operator`
    Prefix,
    /// Suffix unary `Operator`
    Suffix,
}

    #[derive(Debug)]
pub struct UnaryOperator<R: RuleType> {
    rule: R,
    pos: Position,
    next: Option<Box<UnaryOperator<R>>>
}

/// Infix operator used in [`PrecClimber`].
///
/// [`PrecClimber`]: struct.PrecClimber.html
#[derive(Debug)]
pub struct BinaryOperator<R: RuleType> {
    rule: R,
    assoc: Assoc,
    next: Option<Box<BinaryOperator<R>>>
}

impl<R: RuleType> UnaryOperator<R> {
    /// Creates a new `Operator` from a `Rule` and `Assoc`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pest::prec_climber::{Assoc, Operator};
    /// # #[allow(non_camel_case_types)]
    /// # #[allow(dead_code)]
    /// # #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    /// # enum Rule {
    /// #     plus,
    /// #     minus
    /// # }
    /// Operator::new(Rule::plus, Assoc::Left) | Operator::new(Rule::minus, Assoc::Right);
    /// ```
    pub fn new(rule: R, pos: Position) -> UnaryOperator<R> {
        UnaryOperator {
            rule,
            pos,
            next: None
        }
    }
}

impl<R: RuleType> BinaryOperator<R> {
    /// Creates a new `Operator` from a `Rule` and `Assoc`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pest::prec_climber::{Assoc, Operator};
    /// # #[allow(non_camel_case_types)]
    /// # #[allow(dead_code)]
    /// # #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    /// # enum Rule {
    /// #     plus,
    /// #     minus
    /// # }
    /// Operator::new(Rule::plus, Assoc::Left) | Operator::new(Rule::minus, Assoc::Right);
    /// ```
    pub fn new(rule: R, assoc: Assoc) -> BinaryOperator<R> {
        BinaryOperator {
            rule,
            assoc,
            next: None
        }
    }
}

impl<R: RuleType> BitOr for BinaryOperator<R> {
    type Output = Self;

    fn bitor(mut self, rhs: Self) -> Self {
        fn assign_next<R: RuleType>(op: &mut BinaryOperator<R>, next: BinaryOperator<R>) {
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

pub struct PrecClimberBuilder<R: RuleType> {
    unops: Option<Vec<UnaryOperator<R>>>,
    binops: Option<Vec<BinaryOperator<R>>>,
}

impl<R: RuleType> PrecClimberBuilder<R> {
  pub fn new() -> PrecClimberBuilder<R> {
    Self {
      unops: None,
      binops: None,
    }
  }
}

impl<R: RuleType> PrecClimberBuilder<R> {

    pub fn with_unary_operators(self, unops: Vec<UnaryOperator<R>>) -> Self {
      Self {
        unops: Some(unops),
        binops: self.binops,
      }
    }

    pub fn with_binary_operators(self, binops: Vec<BinaryOperator<R>>) -> Self {
      Self {
        unops: self.unops,
        binops: Some(binops),
      }
    }

    pub fn build(self) -> PrecClimber<R> {
      let unops = self.unops.unwrap_or(vec![]).into_iter()
        .fold(HashMap::new(), |mut map, unop| {
          let mut next = Some(unop);

          while let Some(unop) = next.take() {
            match unop {
              UnaryOperator {
                rule,
                pos,
                next: unop_next,
              } => {
                map.insert(rule, pos);
                next = unop_next.map(|op| *op);
              }
            }
          }

          map
        });
      let binops = self.binops.unwrap_or(vec![]).into_iter()
        .zip(1..)
        .fold(HashMap::new(), |mut map, (binop, prec)| {
          let mut next = Some(binop);

          while let Some(binop) = next.take() {
            match binop {
              BinaryOperator {
                rule,
                assoc,
                next: binop_next
              } => {
                map.insert(rule, (prec, assoc));
                next = binop_next.map(|op| *op);
              }
            }
          }

          map
        });
      PrecClimber { unops, binops }
    }
}



/// List of operators and precedences, which can perform [precedence climbing][1] on infix
/// expressions contained in a [`Pairs`]. The token pairs contained in the `Pairs` should start
/// with a *primary* pair and then alternate between an *operator* and a *primary*.
///
/// [1]: https://en.wikipedia.org/wiki/Operator-precedence_parser#Precedence_climbing_method
/// [`Pairs`]: ../iterators/struct.Pairs.html
#[derive(Debug)]
pub struct PrecClimber<R: RuleType> {
    binops: HashMap<R, (u32, Assoc)>,
    unops: HashMap<R, Position>
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
    /// #     power
    /// # }
    /// PrecClimber::new(vec![
    ///     Operator::new(Rule::plus, Assoc::Left) | Operator::new(Rule::minus, Assoc::Left),
    ///     Operator::new(Rule::times, Assoc::Left) | Operator::new(Rule::divide, Assoc::Left),
    ///     Operator::new(Rule::power, Assoc::Right)
    /// ]);
    /// ```

    pub fn climb<'i, P, F, G, H, I, T>(
        &self,
        pairs: P,
        primary: F,
        prefix: G,
        suffix: H,
        infix: I
    ) -> T
    where
        P: Iterator<Item = Pair<'i, R>>,
        F: Fn(Pair<'i, R>) -> T,
        G: Fn(Pair<'i, R>, T) -> T,
        H: Fn(T, Pair<'i, R>) -> T,
        I: Fn(T, Pair<'i, R>, T) -> T,
    {
        let peekable = &mut pairs.peekable();
        let lhs = self.climb_unary(peekable, &primary, &prefix, &suffix);
        self.climb_binary(lhs, 0, peekable, &primary, &prefix, &suffix, &infix)
    }


    fn climb_unary<'i, P, F, G, H, T>(&self, pairs: &mut Peekable<P>, primary: &F, prefix: &G, suffix: &H) -> T
    where
        P: Iterator<Item = Pair<'i, R>>,
        F: Fn(Pair<'i, R>) -> T,
        G: Fn(Pair<'i, R>, T) -> T,
        H: Fn(T, Pair<'i, R>) -> T,
    {
        let expr = self.climb_prefix(pairs, primary, prefix);
        let expr = self.climb_suffix(pairs, suffix, expr);
        expr
    }

    // Climb the suffix of a unary expression
    fn climb_suffix<'i, P, F, T>(&self, pairs: &mut Peekable<P>, suffix: &F, mut expr: T) -> T
    where 
        P: Iterator<Item = Pair<'i, R>>,
        F: Fn(T, Pair<'i, R>) -> T,
    {
        while pairs.peek().is_some() {
            let rule = pairs.peek().unwrap().as_rule();
            if let Some(Position::Suffix) = self.unops.get(&rule) {
                expr = suffix(expr, pairs.next().unwrap());
            } else {
                break;
            }
        }
        expr
    }

    // Climb the prefix of a unary expression
    fn climb_prefix<'i, P, F, G, T>(&self, pairs: &mut Peekable<P>, primary: &F, prefix: &G) -> T
    where
        P: Iterator<Item = Pair<'i, R>>,
        F: Fn(Pair<'i, R>) -> T,
        G: Fn(Pair<'i, R>, T) -> T,
    {
        let pair = pairs.next().unwrap();
        match self.unops.get(&pair.as_rule()) {
            Some(Position::Prefix) => {
                let expr = self.climb_prefix(pairs, primary, prefix);
                prefix(pair, expr)
            },
            _ => primary(pair),
        }
    }

    // Climb a binary expression
    fn climb_binary<'i, P, F, G, H, I, T>(
        &self,
        mut lhs: T,
        min_prec: u32,
        pairs: &mut Peekable<P>,
        primary: &F,
        prefix: &G,
        suffix: &H,
        infix: &I
    ) -> T
    where
        P: Iterator<Item = Pair<'i, R>>,
        F: Fn(Pair<'i, R>) -> T,
        G: Fn(Pair<'i, R>, T) -> T,
        H: Fn(T, Pair<'i, R>) -> T,
        I: Fn(T, Pair<'i, R>, T) -> T,
    {
        while pairs.peek().is_some() {
            let rule = pairs.peek().unwrap().as_rule();
            if let Some(&(prec, _)) = self.binops.get(&rule) {
                if prec >= min_prec {
                    let op = pairs.next().unwrap();
                    let mut rhs = self.climb_unary(pairs, primary, prefix, suffix);

                    while pairs.peek().is_some() {
                        let rule = pairs.peek().unwrap().as_rule();
                        if let Some(&(new_prec, assoc)) = self.binops.get(&rule) {
                            if new_prec > prec || assoc == Assoc::Right && new_prec == prec {
                                rhs = self.climb_binary(rhs, new_prec, pairs, primary, prefix, suffix, infix);
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
