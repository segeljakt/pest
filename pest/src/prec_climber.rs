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
use std::marker::PhantomData;

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

  pub fn prefix(rule: R) -> Op<R> {
    Op {
      rule: rule,
      kind: OpKind::Prefix,
      next: None
    }
  }

  pub fn suffix(rule: R) -> Op<R> {
    Op {
      rule: rule,
      kind: OpKind::Suffix,
      next: None
    }
  }

  pub fn infix(rule: R, assoc: Assoc) -> Op<R> {
    Op {
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

pub struct PrecClimberMap<R: 'static, F, G, H, I, T> 
where
    R: RuleType,
    for<'i> F: Fn(Pair<'i, R>) -> T,
    for<'i> G: Fn(Pair<'i, R>, T) -> T,
    for<'i> H: Fn(T, Pair<'i, R>) -> T,
    for<'i> I: Fn(T, Pair<'i, R>, T) -> T
{
  ops: &'static HashMap<R, (OpKind, Prec)>,
  primary: F,
  prefix: Option<G>,
  suffix: Option<H>,
  infix: Option<I>,
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
    /// #     power
    /// # }
    /// PrecClimber::new(vec![
    ///     Operator::new(Rule::plus, Assoc::Left) | Operator::new(Rule::minus, Assoc::Left),
    ///     Operator::new(Rule::times, Assoc::Left) | Operator::new(Rule::divide, Assoc::Left),
    ///     Operator::new(Rule::power, Assoc::Right)
    /// ]);
    /// ```

  pub fn new() -> Self {
    Self {
      prec: 1,
      ops: HashMap::new(),
    }
  }

  pub fn op<T>(mut self, op: Op<R>) -> Self {
    self.prec += 1;
    let mut iter = Some(op);
    while let Some( Op { rule, kind, next } ) = iter.take() {
      self.ops.insert(rule, (kind, self.prec));
      iter = next.map(|op| *op);
    }
    self
  }

  pub fn map_primary<F, G, H, I, T>(&'static self, primary: F)
    -> PrecClimberMap<R, F, G, H, I, T>
  where
    R: RuleType,
    for<'i> F: Fn(Pair<'i, R>) -> T,
    for<'i> G: Fn(Pair<'i, R>, T) -> T,
    for<'i> H: Fn(T, Pair<'i, R>) -> T,
    for<'i> I: Fn(T, Pair<'i, R>, T) -> T,
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

impl<R, F, G, H, I, T> PrecClimberMap<R, F, G, H, I, T> 
where
    R: RuleType,
    for<'i> F: Fn(Pair<'i, R>) -> T,
    for<'i> G: Fn(Pair<'i, R>, T) -> T,
    for<'i> H: Fn(T, Pair<'i, R>) -> T,
    for<'i> I: Fn(T, Pair<'i, R>, T) -> T,
{
  pub fn map_prefix<X>(self, prefix: X)
    -> PrecClimberMap<R, F, X, H, I, T>
  where
    for<'i> X: Fn(Pair<'i, R>, T) -> T,
  {
    PrecClimberMap {
      ops: self.ops,
      primary: self.primary,
      prefix: Some(prefix),
      suffix: self.suffix,
      infix: self.infix,
      phantom: PhantomData
    }
  }

  pub fn map_suffix<X>(self, suffix: X)
    -> PrecClimberMap<R, F, G, X, I, T>
  where
    for<'i> X: Fn(T, Pair<'i, R>) -> T,
  {
    PrecClimberMap {
      ops: self.ops,
      primary: self.primary,
      prefix: self.prefix,
      suffix: Some(suffix),
      infix: self.infix,
      phantom: PhantomData
    }
  }

  pub fn map_infix<X>(self, infix: X)
    -> PrecClimberMap<R, F, G, H, X, T>
  where
    for<'i> X: Fn(T, Pair<'i, R>, T) -> T,
  {
    PrecClimberMap {
      ops: self.ops,
      primary: self.primary,
      prefix: self.prefix,
      suffix: self.suffix,
      infix: Some(infix),
      phantom: PhantomData
    }
  }

  pub fn climb<'i,P>(&self, pairs: P) -> T
  where
      P: Iterator<Item = Pair<'i, R>>,
  {
      let peekable = &mut pairs.peekable();
      let lhs = self.climb_unary(peekable);
      let expr = if let Some(ref infix) = self.infix {
        self.climb_binary(lhs, 0, peekable, infix)
      } else {
        lhs
      };
      expr
  }


  fn climb_unary<'i,P>(&self, pairs: &mut Peekable<P>) -> T
  where
      P: Iterator<Item = Pair<'i, R>>,
  {
    let expr = if let Some(ref prefix) = self.prefix {
      self.climb_prefix(pairs, prefix)
    } else {
      (self.primary)(pairs.next().unwrap())
    };
    let expr = if let Some(ref suffix) = self.suffix {
      self.climb_suffix(pairs, expr, suffix)
    } else {
      expr
    };
    expr
  }

  // Climb the prefix of a unary expression
  fn climb_prefix<'i,P>(&self, pairs: &mut Peekable<P>, prefix: &G) -> T
  where
      P: Iterator<Item = Pair<'i, R>>,
  {
      let pair = pairs.next().unwrap();
      if let Some((OpKind::Prefix, _)) = self.ops.get(&pair.as_rule()) {
        let expr = self.climb_prefix(pairs, prefix);
        prefix(pair, expr)
      } else {
        (self.primary)(pair)
      }
  }

  // Climb the suffix of a unary expression
  fn climb_suffix<'i,P>(&self, pairs: &mut Peekable<P>, mut expr: T, suffix: &H) -> T
  where 
      P: Iterator<Item = Pair<'i, R>>,
  {
      while pairs.peek().is_some() {
          let rule = pairs.peek().unwrap().as_rule();
          if let Some((OpKind::Suffix, _)) = self.ops.get(&rule) {
              expr = suffix(expr, pairs.next().unwrap());
          } else {
              break;
          }
      }
      expr
  }

  // Climb a binary expression
  fn climb_binary<'i,P>(
      &self,
      mut lhs: T,
      min_prec: u32,
      pairs: &mut Peekable<P>,
      infix: &I,
  ) -> T
  where
      P: Iterator<Item = Pair<'i, R>>,
  {
      while pairs.peek().is_some() {
          let rule = pairs.peek().unwrap().as_rule();
          if let Some(&(OpKind::Infix(_), prec)) = self.ops.get(&rule) {
              if prec >= min_prec {
                  let op = pairs.next().unwrap();
                  let mut rhs = self.climb_unary(pairs);

                  while pairs.peek().is_some() {
                      let rule = pairs.peek().unwrap().as_rule();
                      if let Some(&(OpKind::Infix(assoc), new_prec)) = self.ops.get(&rule) {
                          if new_prec > prec || assoc == Assoc::Right && new_prec == prec {
                              rhs = self.climb_binary(rhs, new_prec, pairs, infix);
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
