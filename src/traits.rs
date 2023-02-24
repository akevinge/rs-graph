/*
 * Copyright (c) 2017-2022 Frank Fischer <frank-fischer@shadow-soft.de>
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

//! Traits for graph data structures.
//!
//! The traits for graph data structures provide an additional level
//! of information about (the edges of) the graph. There are three
//! levels:
//!
//! 1. `Graph`: an undirected graph, edges have no defined source or
//!     sink.
//! 2. `Digraph`: a directed graph, each edge has a designated source
//!     and a designated sink node. Furthermore, there is the concept
//!     of "outgoing" and "incoming" edges. A `Digraph` is also a
//!     `Graph`, which basically means ignoring the direction
//!     information of the edges.

use crate::adjacencies::{InEdges, Neighbors, OutEdges};
use std::rc::Rc;

pub mod refs;

/// A graph iterator.
///
/// This is roughly the same interface as a standard iterator. However,
/// all its method take additionally the graph itself as parameter. This
/// allows the iterator to not contain a reference to internal graph data.
///
/// This might be useful for algorithms that need to store several
/// iterators because they require less memory (they do not need to store
/// a reference to the same graph, each!).
pub trait GraphIterator<G: ?Sized>: Clone {
    type Item;

    fn next(&mut self, g: &G) -> Option<Self::Item>;

    fn size_hint(&self, _g: &G) -> (usize, Option<usize>) {
        (0, None)
    }

    fn count(mut self, g: &G) -> usize {
        let mut c = 0;
        while self.next(g).is_some() {
            c += 1
        }
        c
    }

    fn iter(self, g: &G) -> GraphIter<G, Self>
    where
        G: Sized,
    {
        GraphIter(self, g)
    }
}

/// A graph iterator as a standard iterator.
///
/// This is a pair consisting of a graph iterator and a reference the
/// graph itself. It can be used as a standard iterator.
pub struct GraphIter<'a, G, I>(pub(crate) I, pub(crate) &'a G);

impl<'a, G, I> Clone for GraphIter<'a, G, I>
where
    I: Clone,
{
    fn clone(&self) -> Self {
        GraphIter(self.0.clone(), self.1)
    }
}

impl<'a, G, I> Iterator for GraphIter<'a, G, I>
where
    I: GraphIterator<G>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next(self.1)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint(self.1)
    }

    fn count(self) -> usize {
        self.0.count(self.1)
    }
}

/// Base information of a graph.
pub trait GraphType {
    /// Type of a node.
    type Node<'a>: Copy + Eq;

    /// Type of an edge.
    type Edge<'a>: Copy + Eq;
}

/// Iterator over all nodes of a graph.
pub type NodeIterator<'a, G> = GraphIter<'a, G, <G as FiniteGraph>::NodeIt<'a>>;

/// Iterator over all edges of a graph.
pub type EdgeIterator<'a, G> = GraphIter<'a, G, <G as FiniteGraph>::EdgeIt<'a>>;

/// A (finite) graph with a known number of nodes and edges.
///
/// Finite graphs also provide access to the list of all nodes and edges.
pub trait FiniteGraph: GraphType {
    /// Type of an iterator over all nodes.
    type NodeIt<'a>: GraphIterator<Self, Item = Self::Node<'a>>
    where
        Self: 'a;

    /// Type of an iterator over all edges.
    type EdgeIt<'a>: GraphIterator<Self, Item = Self::Edge<'a>>
    where
        Self: 'a;

    /// Return the number of nodes in the graph.
    fn num_nodes(&self) -> usize;
    /// Return the number of edges in the graph.
    fn num_edges(&self) -> usize;

    /// Return a graph iterator over all nodes.
    fn nodes_iter(&self) -> Self::NodeIt<'_>;

    /// Return an iterator over all nodes.
    fn nodes(&self) -> NodeIterator<'_, Self>
    where
        Self: Sized,
    {
        GraphIter(self.nodes_iter(), self)
    }

    /// Return a graph iterator over all edges.
    ///
    /// This iterator traverses only the forward edges.
    fn edges_iter(&self) -> Self::EdgeIt<'_>;

    /// Return an iterator over all edges.
    ///
    /// This iterator traverses only the forward edges.
    fn edges(&self) -> EdgeIterator<Self>
    where
        Self: Sized,
    {
        GraphIter(self.edges_iter(), self)
    }

    /// Return the nodes connected by an edge.
    ///
    /// The order of the nodes is undefined.
    fn enodes(&self, e: Self::Edge<'_>) -> (Self::Node<'_>, Self::Node<'_>);
}

/// A (finite) directed graph with a known number of nodes and edges.
///
/// For each edge the source and the sink node may be returned.
pub trait FiniteDigraph: FiniteGraph {
    /// Return the source node of an edge.
    fn src(&self, e: Self::Edge<'_>) -> Self::Node<'_>;

    /// Return the sink node of an edge.
    fn snk(&self, e: Self::Edge<'_>) -> Self::Node<'_>;
}

/// Iterator over incident edges and neighbors of some node.
type NeighIterator<'a, G> = GraphIter<'a, G, <G as Undirected>::NeighIt<'a>>;

/// A graph with list access to undirected incident edges.
pub trait Undirected: GraphType {
    /// Type of a graph iterator over all incident edges.
    type NeighIt<'a>: GraphIterator<Self, Item = (Self::Edge<'a>, Self::Node<'a>)>
    where
        Self: 'a;

    /// Return a graph iterator over the edges adjacent to some node.
    fn neigh_iter(&self, u: Self::Node<'_>) -> Self::NeighIt<'_>;

    /// Return an iterator over the edges adjacent to some node.
    fn neighs(&self, u: Self::Node<'_>) -> NeighIterator<Self>
    where
        Self: Sized,
    {
        self.neigh_iter(u).iter(self)
    }

    /// Return access to the neighbors via an `Adjacencies` trait.
    ///
    /// This is the same as calling `Neighbors(&g)` on the graph.
    fn neighbors(&self) -> Neighbors<Self>
    where
        Self: Sized,
    {
        Neighbors(self)
    }
}

/// A directed edge.
///
/// A directed edge is either incoming or outgoing.
pub trait DirectedEdge {
    /// The underlying edge.
    type Edge;

    /// Whether the edge is incoming.
    fn is_incoming(&self) -> bool;

    /// Whether the edge is outgoing.
    fn is_outgoing(&self) -> bool {
        !self.is_incoming()
    }

    /// The underlying edge.
    fn edge(&self) -> Self::Edge;
}

/// Iterator over edges leaving a node.
type OutIterator<'a, G> = GraphIter<'a, G, <G as Directed>::OutIt<'a>>;

/// Iterator over edges entering a node.
type InIterator<'a, G> = GraphIter<'a, G, <G as Directed>::InIt<'a>>;

/// Iterator over directed edges incident with a node.
type IncidentIterator<'a, G> = GraphIter<'a, G, <G as Directed>::IncidentIt<'a>>;

/// A graph with list access to directed incident edges.
///
/// Note that each directed graph is also an undirected graph
/// by simply ignoring the direction of each edge. Hence, each
/// type implementing `Directed` must also implement `Undirected`.
///
/// This trait adds a few additional methods to explicitely access the
/// direction information of an edge. In particular, the direction
/// information can be used in the following ways:
///
///  - The `src` and `snk` methods return the source and sink nodes of
///    an edge.
///  - The iterators `outedges` and `inedges` iterate only over edges
///    leaving or entering a certain node, respectively.
pub trait Directed: Undirected {
    /// Type of a graph iterator over edges leaving a node.
    type OutIt<'a>: GraphIterator<Self, Item = (Self::Edge<'a>, Self::Node<'a>)>
    where
        Self: 'a;

    /// Type of a graph iterator over edges entering a node.
    type InIt<'a>: GraphIterator<Self, Item = (Self::Edge<'a>, Self::Node<'a>)>
    where
        Self: 'a;

    /// Type of an iterator over all incident edges.
    type IncidentIt<'a>: GraphIterator<Self, Item = (Self::DirectedEdge<'a>, Self::Node<'a>)>
    where
        Self: 'a;

    /// Type of a directed edge.
    type DirectedEdge<'a>: DirectedEdge<Edge = Self::Edge<'a>> + Copy + Eq
    where
        Self: 'a;

    /// Return a graph iterator over the edges leaving a node.
    fn out_iter(&self, u: Self::Node<'_>) -> Self::OutIt<'_>;

    /// Return an iterator over the edges leaving a node.
    fn outedges(&self, u: Self::Node<'_>) -> OutIterator<Self>
    where
        Self: Sized,
    {
        GraphIter(self.out_iter(u), self)
    }

    /// Return access to the outgoing arcs via an `Adjacencies` trait.
    ///
    /// This is the same as calling `OutEdges(&g)` on the graph.
    fn outgoing(&self) -> OutEdges<Self>
    where
        Self: Sized,
    {
        OutEdges(self)
    }

    /// Return a graph iterator over the edges leaving a node.
    fn in_iter(&self, u: Self::Node<'_>) -> Self::InIt<'_>;

    /// Return an iterator over the edges leaving a node.
    fn inedges(&self, u: Self::Node<'_>) -> InIterator<Self>
    where
        Self: Sized,
    {
        GraphIter(self.in_iter(u), self)
    }

    /// Return access to the incoming arcs via an `Adjacencies` trait.
    ///
    /// This is the same as calling `InEdges(&g)` on the graph.
    fn incoming(&self) -> InEdges<Self>
    where
        Self: Sized,
    {
        InEdges(self)
    }

    /// Return an iterator over all directed edges incident with a node.
    fn incident_iter(&self, u: Self::Node<'_>) -> Self::IncidentIt<'_>;

    /// Return an iterator over all directed edges incident with a node.
    fn incident_edges(&self, u: Self::Node<'_>) -> IncidentIterator<Self>
    where
        Self: Sized,
    {
        GraphIter(self.incident_iter(u), self)
    }
}

/// A trait for general undirected, finite graphs.
pub trait Graph: FiniteGraph + Undirected {}

impl<G> Graph for G where G: FiniteGraph + Undirected {}

/// A trait for general directed, finite graphs.
pub trait Digraph: Graph + FiniteDigraph + Directed {}

impl<G> Digraph for G where G: FiniteDigraph + Directed {}

/// An item that has an index.
pub trait Indexable {
    fn index(&self) -> usize;
}

/// Associates nodes and edges with unique ids.
pub trait IndexGraph: Graph {
    /// Return a unique id associated with a node.
    fn node_id(&self, u: Self::Node<'_>) -> usize;

    /// Return the node associated with the given id.
    ///
    /// The method panics if the id is invalid.
    fn id2node(&self, id: usize) -> Self::Node<'_>;

    /// Return a unique id associated with an edge.
    ///
    /// The returned id is the same for the edge and its reverse edge.
    fn edge_id(&self, e: Self::Edge<'_>) -> usize;

    /// Return the edge associated with the given id.
    ///
    /// The method returns the forward edge.
    ///
    /// The method panics if the id is invalid.
    fn id2edge(&self, id: usize) -> Self::Edge<'_>;
}

/// A `Digraph` that is also an `IndexGraph`.
pub trait IndexDigraph: IndexGraph + Digraph {}

impl<T> IndexDigraph for T where T: IndexGraph + Digraph {}

/// Marker trait for graphs with directly numbered nodes and edges.
pub trait NumberedGraph: Graph
where
    for<'a> <Self as GraphType>::Node<'a>: Indexable,
    for<'a> <Self as GraphType>::Edge<'a>: Indexable,
{
}

impl<G> NumberedGraph for G
where
    G: Graph,
    for<'a> G::Node<'a>: Indexable,
    for<'a> G::Edge<'a>: Indexable,
{
}

/// Marker trait for digraphs with directly numbered nodes and edges.
pub trait NumberedDigraph: NumberedGraph + Digraph
where
    for<'a> <Self as GraphType>::Node<'a>: Indexable,
    for<'a> <Self as GraphType>::Edge<'a>: Indexable,
{
}

impl<G> NumberedDigraph for G
where
    G: Digraph + NumberedGraph,
    for<'a> G::Node<'a>: Indexable,
    for<'a> G::Edge<'a>: Indexable,
{
}

// Implementation of basis traits for refs
impl<'g, G> GraphType for &'g G
where
    G: GraphType,
{
    type Node<'a> = G::Node<'a>;
    type Edge<'a> = G::Edge<'a>;
}

impl<'g, G> FiniteGraph for &'g G
where
    G: FiniteGraph,
{
    type NodeIt<'a> = refs::WrapIt<G::NodeIt<'a>>
    where
        G: 'a,
        'g: 'a;

    type EdgeIt<'a> = refs::WrapIt<G::EdgeIt<'a>>
    where
        G: 'a,
        'g: 'a;

    fn num_nodes(&self) -> usize {
        (*self).num_nodes()
    }

    fn nodes_iter(&self) -> Self::NodeIt<'_> {
        (*self).nodes_iter().into()
    }

    fn num_edges(&self) -> usize {
        (*self).num_edges()
    }

    fn edges_iter(&self) -> Self::EdgeIt<'_> {
        (*self).edges_iter().into()
    }

    fn enodes(&self, e: Self::Edge<'_>) -> (Self::Node<'_>, Self::Node<'_>) {
        (*self).enodes(e)
    }
}

impl<'g, G> Undirected for &'g G
where
    G: Undirected,
{
    type NeighIt<'a> = refs::WrapIt<G::NeighIt<'a>>
    where
        G: 'a,
        'g: 'a;

    fn neigh_iter(&self, u: Self::Node<'_>) -> Self::NeighIt<'_> {
        (*self).neigh_iter(u).into()
    }
}

impl<'g, G> Directed for &'g G
where
    G: Directed,
{
    type OutIt<'a> = refs::WrapIt<G::OutIt<'a>>
    where
        G: 'a,
        'g: 'a;

    type InIt<'a> = refs::WrapIt<G::InIt<'a>>
    where
        G: 'a,
        'g: 'a;

    type IncidentIt<'a> = refs::WrapIt<G::IncidentIt<'a>>
    where
        G: 'a,
        'g: 'a;

    type DirectedEdge<'a> = G::DirectedEdge<'a>
    where
        Self: 'a;

    fn out_iter(&self, u: Self::Node<'_>) -> Self::OutIt<'_> {
        (*self).out_iter(u).into()
    }

    fn in_iter(&self, u: Self::Node<'_>) -> Self::InIt<'_> {
        (*self).in_iter(u).into()
    }

    fn incident_iter(&self, u: Self::Node<'_>) -> Self::IncidentIt<'_> {
        (*self).incident_iter(u).into()
    }
}

impl<'g, G> FiniteDigraph for &'g G
where
    G: FiniteDigraph,
{
    fn src(&self, e: Self::Edge<'_>) -> Self::Node<'_> {
        (*self).src(e)
    }

    fn snk(&self, e: Self::Edge<'_>) -> Self::Node<'_> {
        (*self).snk(e)
    }
}

impl<'g, G> IndexGraph for &'g G
where
    G: IndexGraph,
{
    fn node_id(&self, u: Self::Node<'_>) -> usize {
        (*self).node_id(u)
    }

    fn edge_id(&self, e: Self::Edge<'_>) -> usize {
        (*self).edge_id(e)
    }

    fn id2node(&self, id: usize) -> Self::Node<'_> {
        (*self).id2node(id)
    }

    fn id2edge(&self, id: usize) -> Self::Edge<'_> {
        (*self).id2edge(id)
    }
}

// Implementation of basis traits for Rc
impl<G, I> GraphIterator<Rc<G>> for refs::WrapIt<I>
where
    I: GraphIterator<G>,
{
    type Item = I::Item;

    fn next(&mut self, g: &Rc<G>) -> Option<Self::Item> {
        self.0.next(g.as_ref())
    }

    fn size_hint(&self, g: &Rc<G>) -> (usize, Option<usize>) {
        self.0.size_hint(g.as_ref())
    }

    fn count(self, g: &Rc<G>) -> usize {
        self.0.count(g.as_ref())
    }
}

impl<G> GraphType for Rc<G>
where
    G: GraphType,
{
    type Node<'a> = G::Node<'a>;
    type Edge<'a> = G::Edge<'a>;
}

impl<G> FiniteGraph for Rc<G>
where
    G: FiniteGraph,
{
    type NodeIt<'a> = refs::WrapIt<G::NodeIt<'a>>
    where
        G: 'a;

    type EdgeIt<'a> = refs::WrapIt<G::EdgeIt<'a>>
    where
        G: 'a;

    fn num_nodes(&self) -> usize {
        self.as_ref().num_nodes()
    }

    fn nodes_iter(&self) -> Self::NodeIt<'_> {
        self.as_ref().nodes_iter().into()
    }

    fn num_edges(&self) -> usize {
        self.as_ref().num_edges()
    }
    fn edges_iter(&self) -> Self::EdgeIt<'_> {
        self.as_ref().edges_iter().into()
    }

    fn enodes(&self, e: Self::Edge<'_>) -> (Self::Node<'_>, Self::Node<'_>) {
        self.as_ref().enodes(e)
    }
}

impl<G> FiniteDigraph for Rc<G>
where
    G: FiniteDigraph,
{
    fn src(&self, e: Self::Edge<'_>) -> Self::Node<'_> {
        self.as_ref().src(e)
    }

    fn snk(&self, e: Self::Edge<'_>) -> Self::Node<'_> {
        self.as_ref().snk(e)
    }
}

impl<G> Undirected for Rc<G>
where
    G: Undirected,
{
    type NeighIt<'a> = refs::WrapIt<G::NeighIt<'a>>
    where
        G: 'a;

    fn neigh_iter(&self, u: Self::Node<'_>) -> Self::NeighIt<'_> {
        self.as_ref().neigh_iter(u).into()
    }
}

impl<G> Directed for Rc<G>
where
    G: Directed,
{
    type OutIt<'a> = refs::WrapIt<G::OutIt<'a>>
    where
        G: 'a;

    type InIt<'a> = refs::WrapIt<G::InIt<'a>>
    where
        G: 'a;

    type IncidentIt<'a> = refs::WrapIt<G::IncidentIt<'a>>
    where
        G: 'a;

    type DirectedEdge<'a> = G::DirectedEdge<'a>
    where
        G: 'a;

    fn out_iter(&self, u: Self::Node<'_>) -> Self::OutIt<'_> {
        self.as_ref().out_iter(u).into()
    }

    fn in_iter(&self, u: Self::Node<'_>) -> Self::InIt<'_> {
        self.as_ref().in_iter(u).into()
    }

    fn incident_iter(&self, u: Self::Node<'_>) -> Self::IncidentIt<'_> {
        self.as_ref().incident_iter(u).into()
    }
}

impl<G> IndexGraph for Rc<G>
where
    G: IndexGraph,
{
    fn node_id(&self, u: Self::Node<'_>) -> usize {
        self.as_ref().node_id(u)
    }

    fn edge_id(&self, e: Self::Edge<'_>) -> usize {
        self.as_ref().edge_id(e)
    }

    fn id2node(&self, id: usize) -> Self::Node<'_> {
        self.as_ref().id2node(id)
    }

    fn id2edge(&self, id: usize) -> Self::Edge<'_> {
        self.as_ref().id2edge(id)
    }
}
