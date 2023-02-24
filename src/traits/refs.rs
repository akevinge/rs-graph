/*
 * Copyright (c) 2020-2022 Frank Fischer <frank-fischer@shadow-soft.de>
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

///! Reference graph traits.
use super::{
    Directed, DirectedEdge, FiniteGraph, GraphIter, GraphIterator, GraphType, IndexDigraph, IndexGraph, Undirected,
};
use std::ptr::NonNull;

/// A reference to a basic graph type.
pub trait GraphTypeRef<'a>: Clone {
    /// Type of a node.
    type Node: Copy + Eq;

    /// Type of an edge.
    type Edge: Copy + Eq;
}

/// A reference to a basic finite graph.
///
/// This trait contains methods with a unrestricted lifetime for `self`.
pub trait FiniteGraphRef<'a>: GraphTypeRef<'a> {
    /// Type of an iterator over all nodes.
    type NodeIt: GraphIterator<Self, Item = Self::Node>;

    /// Type of an iterator over all edges.
    type EdgeIt: GraphIterator<Self, Item = Self::Edge>;

    /// Return the number of nodes in the graph.
    fn num_nodes(&self) -> usize;

    /// Return a graph iterator over all nodes.
    fn nodes_iter(&self) -> Self::NodeIt;

    /// Return an iterator over all nodes.
    fn nodes(&self) -> GraphIter<Self, Self::NodeIt>
    where
        Self: Sized,
    {
        GraphIter(FiniteGraphRef::nodes_iter(self), self)
    }

    /// Return the number of edges in the graph.
    fn num_edges(&self) -> usize;

    /// Return a graph iterator over all edges.
    ///
    /// This iterator traverses only the forward edges.
    fn edges_iter(&self) -> Self::EdgeIt;

    /// Return an iterator over all edges.
    ///
    /// This iterator traverses only the forward edges.
    fn edges(&self) -> GraphIter<Self, Self::EdgeIt>
    where
        Self: Sized,
    {
        GraphIter(FiniteGraphRef::edges_iter(self), self)
    }

    /// Return the nodes connected by an edge.
    ///
    /// The order of the nodes is undefined.
    fn enodes(&self, e: Self::Edge) -> (Self::Node, Self::Node);
}

/// A reference to a basic graph.
///
/// This trait contains methods with a unrestricted lifetime for `self`.
pub trait FiniteDigraphRef<'a>: FiniteGraphRef<'a> {
    fn src(&self, e: Self::Edge) -> Self::Node;
    fn snk(&self, e: Self::Edge) -> Self::Node;
}

/// A reference to an undirected graph.
///
/// This trait contains methods with a unrestricted lifetime for `self`.
pub trait UndirectedRef<'a>: GraphTypeRef<'a> {
    /// Type of a graph iterator over all incident edges.
    type NeighIt: GraphIterator<Self, Item = (Self::Edge, Self::Node)>;

    /// Return a graph iterator over the edges adjacent to some node.
    fn neigh_iter(&self, u: Self::Node) -> Self::NeighIt;

    /// Return an iterator over the edges adjacent to some node.
    fn neighs(&self, u: Self::Node) -> super::GraphIter<Self, Self::NeighIt>
    where
        Self: Sized,
    {
        GraphIter(UndirectedRef::neigh_iter(self, u), self)
    }
}

/// A reference to a digraph.
///
/// This trait contains methods with a unrestricted lifetime for `self`.
pub trait DirectedRef<'a>: UndirectedRef<'a> {
    /// Type of a graph iterator over edges leaving a node.
    type OutIt: GraphIterator<Self, Item = (Self::Edge, Self::Node)>;

    /// Type of a graph iterator over edges entering a node.
    type InIt: GraphIterator<Self, Item = (Self::Edge, Self::Node)>;

    /// Type of an iterator over all incident edges.
    type IncidentIt: GraphIterator<Self, Item = (Self::DirectedEdge, Self::Node)>;

    /// Type of a directed edge.
    type DirectedEdge: DirectedEdge<Edge = Self::Edge> + Copy + Eq;

    /// Return the source node of an edge.

    /// Return the sink node of an edge.
    /// Return a graph iterator over the edges leaving a node.
    fn out_iter(&self, u: Self::Node) -> Self::OutIt;

    /// Return an iterator over the edges leaving a node.
    fn outedges(&self, u: Self::Node) -> super::GraphIter<Self, Self::OutIt>
    where
        Self: Sized,
    {
        GraphIter(DirectedRef::out_iter(self, u), self)
    }

    /// Return a graph iterator over the edges leaving a node.
    fn in_iter(&self, u: Self::Node) -> Self::InIt;

    /// Return an iterator over the edges leaving a node.
    fn inedges(&self, u: Self::Node) -> super::GraphIter<Self, Self::InIt>
    where
        Self: Sized,
    {
        GraphIter(DirectedRef::in_iter(self, u), self)
    }

    /// Return an iterator over all directed edges incident with a node.
    fn incident_iter(&self, u: Self::Node) -> Self::IncidentIt;

    /// Return an iterator over all directed edges incident with a node.
    fn incident_edges(&self, u: Self::Node) -> super::GraphIter<Self, Self::IncidentIt>
    where
        Self: Sized,
    {
        GraphIter(DirectedRef::incident_iter(self, u), self)
    }
}

/// A reference to an indexed graph.
///
/// This trait contains methods with a unrestricted lifetime for `self`.
pub trait IndexGraphRef<'a>: UndirectedRef<'a> {
    /// Return a unique id associated with a node.
    fn node_id(&self, u: Self::Node) -> usize;

    /// Return the node associated with the given id.
    ///
    /// The method panics if the id is invalid.
    fn id2node(&self, id: usize) -> Self::Node;

    /// Return a unique id associated with an edge.
    ///
    /// The returned id is the same for the edge and its reverse edge.
    fn edge_id(&self, e: Self::Edge) -> usize;

    /// Return the edge associated with the given id.
    ///
    /// The method returns the forward edge.
    ///
    /// The method panics if the id is invalid.
    fn id2edge(&self, id: usize) -> Self::Edge;
}

/// A reference to an indexed digraph.
pub trait IndexDigraphRef<'a>: IndexGraphRef<'a> + DirectedRef<'a> {}

#[derive(Clone)]
pub struct WrapIt<I>(pub I);

impl<'a, G, I> GraphIterator<&'a G> for WrapIt<I>
where
    I: GraphIterator<G>,
{
    type Item = I::Item;

    fn next(&mut self, g: &&'a G) -> Option<Self::Item> {
        self.0.next(*g)
    }

    fn size_hint(&self, g: &&'a G) -> (usize, Option<usize>) {
        self.0.size_hint(*g)
    }

    fn count(self, g: &&'a G) -> usize {
        self.0.count(*g)
    }
}

impl<I> From<I> for WrapIt<I> {
    fn from(it: I) -> WrapIt<I> {
        WrapIt(it)
    }
}

// Implementation for &'a G

impl<'a, G> GraphTypeRef<'a> for &'a G
where
    G: GraphType,
{
    type Node = G::Node<'a>;
    type Edge = G::Edge<'a>;
}

impl<'a, G> FiniteGraphRef<'a> for &'a G
where
    G: FiniteGraph,
{
    type NodeIt = WrapIt<G::NodeIt<'a>>;

    type EdgeIt = WrapIt<G::EdgeIt<'a>>;

    fn num_nodes(&self) -> usize {
        (*self).num_nodes()
    }

    fn nodes_iter(&self) -> Self::NodeIt {
        (*self).nodes_iter().into()
    }

    fn num_edges(&self) -> usize {
        (*self).num_edges()
    }

    fn edges_iter(&self) -> Self::EdgeIt {
        (*self).edges_iter().into()
    }

    fn enodes(&self, e: Self::Edge) -> (Self::Node, Self::Node) {
        (*self).enodes(e)
    }
}

impl<'a, G> UndirectedRef<'a> for &'a G
where
    G: Undirected,
{
    type NeighIt = WrapIt<G::NeighIt<'a>>;

    fn neigh_iter(&self, u: Self::Node) -> Self::NeighIt {
        (*self).neigh_iter(u).into()
    }
}

impl<'a, G> DirectedRef<'a> for &'a G
where
    G: Directed,
{
    type OutIt = WrapIt<G::OutIt<'a>>;

    type InIt = WrapIt<G::InIt<'a>>;

    type IncidentIt = WrapIt<G::IncidentIt<'a>>;

    type DirectedEdge = G::DirectedEdge<'a>;

    fn out_iter(&self, u: Self::Node) -> Self::OutIt {
        (*self).out_iter(u).into()
    }

    fn in_iter(&self, u: Self::Node) -> Self::InIt {
        (*self).in_iter(u).into()
    }

    fn incident_iter(&self, u: Self::Node) -> Self::IncidentIt {
        (*self).incident_iter(u).into()
    }
}

impl<'a, G> IndexGraphRef<'a> for &'a G
where
    G: IndexGraph,
{
    fn node_id(&self, u: Self::Node) -> usize {
        (*self).node_id(u)
    }

    fn edge_id(&self, e: Self::Edge) -> usize {
        (*self).edge_id(e)
    }

    fn id2node(&self, id: usize) -> Self::Node {
        (*self).id2node(id)
    }

    fn id2edge(&self, id: usize) -> Self::Edge {
        (*self).id2edge(id)
    }
}

impl<'a, G> IndexDigraphRef<'a> for &'a G where G: IndexDigraph {}

// Implementation for NonNull<G>

impl<G, I> GraphIterator<NonNull<G>> for WrapIt<I>
where
    I: GraphIterator<G>,
{
    type Item = I::Item;

    fn next(&mut self, g: &NonNull<G>) -> Option<Self::Item> {
        unsafe { self.0.next(g.as_ref()) }
    }

    fn size_hint(&self, g: &NonNull<G>) -> (usize, Option<usize>) {
        unsafe { self.0.size_hint(g.as_ref()) }
    }

    fn count(self, g: &NonNull<G>) -> usize {
        unsafe { self.0.count(g.as_ref()) }
    }
}

impl<'a, G> GraphTypeRef<'a> for NonNull<G>
where
    G: GraphType,
{
    type Node = G::Node<'a>;
    type Edge = G::Edge<'a>;
}

impl<'a, G> FiniteGraphRef<'a> for NonNull<G>
where
    G: FiniteGraph + 'a,
{
    type NodeIt = WrapIt<G::NodeIt<'a>>;

    type EdgeIt = WrapIt<G::EdgeIt<'a>>;

    fn num_nodes(&self) -> usize {
        unsafe { self.as_ref().num_nodes() }
    }

    fn nodes_iter(&self) -> Self::NodeIt {
        unsafe { self.as_ref().nodes_iter().into() }
    }

    fn num_edges(&self) -> usize {
        unsafe { self.as_ref().num_edges() }
    }

    fn edges_iter(&self) -> Self::EdgeIt {
        unsafe { self.as_ref().edges_iter().into() }
    }

    fn enodes(&self, e: Self::Edge) -> (Self::Node, Self::Node) {
        unsafe { self.as_ref().enodes(e) }
    }
}

impl<'a, G> UndirectedRef<'a> for NonNull<G>
where
    G: Undirected + 'a,
{
    type NeighIt = WrapIt<G::NeighIt<'a>>;

    fn neigh_iter(&self, u: Self::Node) -> Self::NeighIt {
        unsafe { self.as_ref().neigh_iter(u).into() }
    }
}

impl<'a, G> DirectedRef<'a> for NonNull<G>
where
    G: Directed + 'a,
{
    type OutIt = WrapIt<G::OutIt<'a>>;

    type InIt = WrapIt<G::InIt<'a>>;

    type IncidentIt = WrapIt<G::IncidentIt<'a>>;

    type DirectedEdge = G::DirectedEdge<'a>;

    fn out_iter(&self, u: Self::Node) -> Self::OutIt {
        unsafe { self.as_ref().out_iter(u).into() }
    }

    fn in_iter(&self, u: Self::Node) -> Self::InIt {
        unsafe { self.as_ref().in_iter(u).into() }
    }

    fn incident_iter(&self, u: Self::Node) -> Self::IncidentIt {
        unsafe { self.as_ref().incident_iter(u).into() }
    }
}

impl<'a, G> IndexGraphRef<'a> for NonNull<G>
where
    G: IndexGraph + 'a,
{
    fn node_id(&self, u: Self::Node) -> usize {
        unsafe { self.as_ref().node_id(u) }
    }

    fn edge_id(&self, e: Self::Edge) -> usize {
        unsafe { self.as_ref().edge_id(e) }
    }

    fn id2node(&self, id: usize) -> Self::Node {
        unsafe { self.as_ref().id2node(id) }
    }

    fn id2edge(&self, id: usize) -> Self::Edge {
        unsafe { self.as_ref().id2edge(id) }
    }
}

impl<'a, G> IndexDigraphRef<'a> for NonNull<G> where G: IndexDigraph + 'a {}
