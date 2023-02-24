/*
 * Copyright (c) 2018, 2020-2022 Frank Fischer <frank-fischer@shadow-soft.de>
 *
 * This program is free software: you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see  <http://www.gnu.org/licenses/>
 */

//! Abstraction of neighboring edges.
//!
//! This module implements the arguably simplest representation of a graph: for
//! each node the list of adjacent edges and nodes. No further information like
//! the number of nodes or edges in a graph is available.
//!
//! The purpose of the trait [`Adjacencies`] is therefore to abstract over the concept
//! of adjacent edges and nodes. Standard examples are "all edges" (in the
//! undirected sense), "incoming edges" and "outgoing edges" represented by the structs
//! [`Neighbors`], [`InEdges`] and [`OutEdges`].
//!
//! Some algorithms (e.g. breadth-first search or depth-first search) can be
//! described in terms of adjacencies only.
//!
//! There are three basic ways to define an adjacency:
//!
//! 1. From an existing graph or digraph using [`Neighbors`], [`OutEdges`] or [`InEdges`],
//! 2. From a function returning an iterator over adjacent edges for a given node, see [`FnAdj`],
//! 3. By implementing the [`Adjacencies`] trait on your own.
//!
//! # Example
//!
//! ```
//! use rs_graph::classes;
//! use rs_graph::Net;
//! use rs_graph::traits::*;
//! use rs_graph::adjacencies::*;
//!
//! let g = classes::peterson::<Net>();
//!
//! let neighs = Neighbors(&g);
//! let neighs = neighs.filter(|&(e, _)| {
//!   let (u,v) = g.enodes(e);
//!   (g.node_id(u) < 5) == (g.node_id(v) < 5)
//! });
//! for u in g.nodes() {
//!     assert_eq!(neighs.neighs(u).count(), 2);
//! }
//! ```

use crate::traits::{Directed, GraphIter, GraphIterator, Undirected};
use std::marker::PhantomData;

//pub type AdjacenciesIter<'a, G> = GraphIter<'a, G, <G as Adjacencies<'a>>::IncidenceIt>;

pub trait Adjacencies<'a> {
    type Node: Copy + Eq + 'a;

    type Edge: Copy + Eq + 'a;

    type IncidenceIt: GraphIterator<Self, Item = (Self::Edge, Self::Node)>;

    fn neigh_iter(&self, u: Self::Node) -> Self::IncidenceIt;

    fn neighs<'b>(&'b self, u: Self::Node) -> GraphIter<'b, Self, Self::IncidenceIt>
    where
        'a: 'b,
        Self: Sized,
    {
        GraphIter(self.neigh_iter(u), self)
    }

    fn filter<P>(self, predicate: P) -> FilterAdjacencies<Self, P>
    where
        Self: Sized,
        P: for<'r> Fn(&'r (Self::Edge, Self::Node)) -> bool,
    {
        FilterAdjacencies(self, predicate)
    }
}

pub struct FilterAdjacencies<A, P>(A, P);

#[derive(Clone)]
pub struct Filtered<I>(I);

impl<A, P, I> GraphIterator<FilterAdjacencies<A, P>> for Filtered<I>
where
    I: GraphIterator<A>,
    P: for<'r> Fn(&'r I::Item) -> bool,
{
    type Item = I::Item;

    fn next(&mut self, adj: &FilterAdjacencies<A, P>) -> Option<Self::Item> {
        while let Some(it) = self.0.next(&adj.0) {
            if (adj.1)(&it) {
                return Some(it);
            }
        }
        None
    }
}

impl<'a, A, P> Adjacencies<'a> for FilterAdjacencies<A, P>
where
    A: Adjacencies<'a>,
    P: 'a + Clone + for<'r> Fn(&'r (A::Edge, A::Node)) -> bool,
{
    type Node = A::Node;
    type Edge = A::Edge;
    type IncidenceIt = Filtered<A::IncidenceIt>;

    fn neigh_iter(&self, u: Self::Node) -> Self::IncidenceIt {
        Filtered(self.0.neigh_iter(u))
    }
}

#[derive(Clone)]
pub struct AdjacenciesWrapIt<I>(I);

impl<I> From<I> for AdjacenciesWrapIt<I> {
    fn from(it: I) -> Self {
        AdjacenciesWrapIt(it)
    }
}

impl<'g, G, I> GraphIterator<Neighbors<'g, G>> for AdjacenciesWrapIt<I>
where
    I: GraphIterator<G>,
{
    type Item = I::Item;

    fn next(&mut self, adj: &Neighbors<'g, G>) -> Option<Self::Item> {
        self.0.next(adj.0)
    }

    fn size_hint(&self, adj: &Neighbors<'g, G>) -> (usize, Option<usize>) {
        self.0.size_hint(adj.0)
    }

    fn count(self, adj: &Neighbors<'g, G>) -> usize {
        self.0.count(adj.0)
    }
}

impl<'g, G, I> GraphIterator<OutEdges<'g, G>> for AdjacenciesWrapIt<I>
where
    I: GraphIterator<G>,
{
    type Item = I::Item;

    fn next(&mut self, adj: &OutEdges<'g, G>) -> Option<Self::Item> {
        self.0.next(adj.0)
    }

    fn size_hint(&self, adj: &OutEdges<'g, G>) -> (usize, Option<usize>) {
        self.0.size_hint(adj.0)
    }

    fn count(self, adj: &OutEdges<'g, G>) -> usize {
        self.0.count(adj.0)
    }
}

impl<'g, G, I> GraphIterator<InEdges<'g, G>> for AdjacenciesWrapIt<I>
where
    I: GraphIterator<G>,
{
    type Item = I::Item;

    fn next(&mut self, adj: &InEdges<'g, G>) -> Option<Self::Item> {
        self.0.next(adj.0)
    }

    fn size_hint(&self, adj: &InEdges<'g, G>) -> (usize, Option<usize>) {
        self.0.size_hint(adj.0)
    }

    fn count(self, adj: &InEdges<'g, G>) -> usize {
        self.0.count(adj.0)
    }
}

/// Neighbor access over all adjacent (undirected) edges.
pub struct Neighbors<'g, G>(pub &'g G);

impl<'a, 'g: 'a, G> Adjacencies<'a> for Neighbors<'g, G>
where
    G: Undirected,
{
    type Node = G::Node<'a>;
    type Edge = G::Edge<'a>;
    type IncidenceIt = AdjacenciesWrapIt<G::NeighIt<'a>>;

    fn neigh_iter(&self, u: Self::Node) -> Self::IncidenceIt {
        self.0.neigh_iter(u).into()
    }
}

/// Neighbor access over all outgoing edges of a `Digraph`.
pub struct OutEdges<'g, G>(pub &'g G);

impl<'a, 'g: 'a, G> Adjacencies<'a> for OutEdges<'g, G>
where
    G: Directed,
{
    type Node = G::Node<'a>;
    type Edge = G::Edge<'a>;
    type IncidenceIt = AdjacenciesWrapIt<G::OutIt<'a>>;

    fn neigh_iter(&self, u: Self::Node) -> Self::IncidenceIt {
        self.0.out_iter(u).into()
    }
}

/// Neighbor access over all incoming edges of a `Digraph`.
pub struct InEdges<'g, G>(pub &'g G);

impl<'a, 'g: 'a, G> Adjacencies<'a> for InEdges<'g, G>
where
    G: Directed,
{
    type Node = G::Node<'a>;
    type Edge = G::Edge<'a>;
    type IncidenceIt = AdjacenciesWrapIt<G::InIt<'a>>;

    fn neigh_iter(&self, u: Self::Node) -> Self::IncidenceIt {
        self.0.in_iter(u).into()
    }
}

impl<'a, A, I> GraphIterator<&'a A> for AdjacenciesWrapIt<I>
where
    I: GraphIterator<A>,
{
    type Item = I::Item;

    fn next(&mut self, adj: &&'a A) -> Option<Self::Item> {
        self.0.next(*adj)
    }

    fn size_hint(&self, adj: &&'a A) -> (usize, Option<usize>) {
        self.0.size_hint(*adj)
    }

    fn count(self, adj: &&'a A) -> usize {
        self.0.count(*adj)
    }
}

/// Implement Adjacencies for references.
impl<'a, A> Adjacencies<'a> for &'a A
where
    A: Adjacencies<'a>,
{
    type Node = A::Node;
    type Edge = A::Edge;
    type IncidenceIt = AdjacenciesWrapIt<A::IncidenceIt>;

    fn neigh_iter(&self, u: Self::Node) -> Self::IncidenceIt {
        (*self).neigh_iter(u).into()
    }
}

/// An adjacency defined by a function returning iterators.
///
/// This struct wraps a `Fn(N) -> I` which provides for each node of
/// type `N` an iterator over the adjacent edges. This allows to create
/// simple graphs on the fly.
///
/// # Example
///
/// The following adjacency describes a simple grid graph.
///
/// ```
/// use rs_graph::adjacencies::*;
///
/// // Create a 5 x 7 grid graph.
/// // The nodes are pairs (i,j) and the edges are pairs of nodes.
/// let n = 5;
/// let m = 7;
/// let g = FnAdj::from(move |u: (isize, isize)| {
///     IntoIterator::into_iter([(-1, 0), (1, 0), (0, -1), (0, 1)])
///         .map(move |d| (u.0 + d.0, u.1 + d.1))
///         .filter(move |v| 0 <= v.0 && v.0 < n && 0 <= v.1 && v.1 < m)
///         .map(move |v| ((u, v), v))
/// });
///
/// // count the number of nodes with degree 2, 3 and 4
/// let mut cnt2 = 0;
/// let mut cnt3 = 0;
/// let mut cnt4 = 0;
/// for i in 0..n {
///     for j in 0..m {
///         match g.neighs((i, j)).count() {
///             2 => cnt2 += 1,
///             3 => cnt3 += 1,
///             4 => cnt4 += 1,
///             _ => unreachable!(),
///         }
///     }
/// }
/// assert_eq!(4, cnt2);
/// assert_eq!(16, cnt3);
/// assert_eq!(15, cnt4);
/// ```
pub struct FnAdj<N, E, Ne, NeIt> {
    neighsfn: Ne,
    phantom: PhantomData<(N, E, NeIt)>,
}

#[derive(Clone)]
pub struct FnNeighIt<NeIt>
where
    NeIt: Clone,
{
    it: NeIt,
}

impl<N, E, Ne, NeIt> GraphIterator<FnAdj<N, E, Ne, NeIt>> for FnNeighIt<NeIt>
where
    NeIt: Iterator<Item = (E, N)> + Clone,
{
    type Item = (E, N);
    fn next(&mut self, _g: &FnAdj<N, E, Ne, NeIt>) -> Option<Self::Item> {
        self.it.next()
    }
}

impl<'a, N, E, Ne, NeIt: Clone> Adjacencies<'a> for FnAdj<N, E, Ne, NeIt>
where
    N: Copy + Eq + 'a,
    E: Copy + Eq + 'a,
    Ne: Fn(N) -> NeIt,
    NeIt: Iterator<Item = (E, N)> + Clone,
{
    type Node = N;
    type Edge = E;
    type IncidenceIt = FnNeighIt<NeIt>;

    fn neigh_iter(&self, u: Self::Node) -> Self::IncidenceIt {
        FnNeighIt { it: (self.neighsfn)(u) }
    }
}

impl<'a, N, E, Ne, NeIt: Clone> From<Ne> for FnAdj<N, E, Ne, NeIt>
where
    N: Copy + Eq + 'a,
    E: Copy + Eq + 'a,
    Ne: Fn(N) -> NeIt,
    NeIt: Iterator<Item = (E, N)> + Clone,
{
    fn from(neighs: Ne) -> Self {
        FnAdj {
            neighsfn: neighs,
            phantom: PhantomData,
        }
    }
}
