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

#![recursion_limit = "256"]
#![forbid(unsafe_code)]

//! This crate provides automatic graph derivations.
//!
//! In order to automatically implement graph traits for a struct that contains
//! the actual graph data structure in a field, add #[derive(Graph)] to the
//! struct. The field containing the graph must either be named `graph` or be
//! attributed with `#[graph]`. All graph traits (`Graph`, `Digraph`, and
//! `IndexGraph`) that are implemented for the nested graph, are implemented for
//! the annotated struct, too.
//!
//! # Example
//!
//! ```
//! use rs_graph_derive::Graph;
//! use rs_graph::traits::*;
//! use rs_graph::linkedlistgraph::*;
//! use rs_graph::classes;
//!
//! #[derive(Graph)]
//! struct MyGraph {
//!     #[graph] graph: LinkedListGraph, // #[graph] not needed for fields named `graph`.
//!     balances: Vec<f64>,
//!     bounds: Vec<f64>,
//! }
//!
//! impl From<LinkedListGraph> for MyGraph {
//!     fn from(g: LinkedListGraph) -> MyGraph {
//!         let n = g.num_nodes();
//!         let m = g.num_edges();
//!         MyGraph {
//!             graph: g,
//!             balances: vec![0.0; n],
//!             bounds: vec![0.0; m],
//!         }
//!     }
//! }
//!
//! impl MyGraph {
//!     fn balance_mut(&mut self, u: Node) -> &mut f64 {
//!         &mut self.balances[self.graph.node_id(u)]
//!     }
//!
//!     fn bound_mut(&mut self, e: Edge) -> &mut f64 {
//!         &mut self.bounds[self.graph.edge_id(e)]
//!     }
//! }
//!
//! # fn main() {
//! let mut g: MyGraph = classes::path::<LinkedListGraph>(5).into();
//! let (s, t) = (g.id2node(0), g.id2node(4));
//! *g.balance_mut(s) = 1.0;
//! *g.balance_mut(t) = -1.0;
//! for eid in 0..g.num_edges() { *g.bound_mut(g.id2edge(eid)) = eid as f64; }
//! # }
//! ```
//!
//! # Attributed graphs
//!
//! Some algorithms require the presence of specific node or edge attributes.
//! These requirements are represented by `NodeAttributes` and `EdgeAttributes`
//! traits from `rs_graph::attributes`. These traits can also be automatically
//! implemented using `#[derive(Graph)]` given that the wrapped graph is an
//! `IndexGraph`. The node/edge attributes must be collected in indexable arrays
//! (slice, `Vec`, ...) of an appropriate size and be annotated with `nodeattrs`
//! or `edgeattrs` attributes. Note that it is the responsibility of the user to
//! ensure that these vectors have to correct size.
//!
//! # Example
//!
//! ```
//! use rs_graph_derive::Graph;
//! use rs_graph::{traits::*};
//! use rs_graph::linkedlistgraph::*;
//! use rs_graph::classes;
//! use rs_graph::attributes::{NodeAttributes, EdgeAttributes, AttributedGraph};
//!
//! #[derive(Clone, Default)]
//! struct NodeData {
//!     balance: f64,
//! }
//!
//! #[derive(Clone, Default)]
//! struct EdgeData {
//!     bound: f64,
//! }
//!
//! #[derive(Graph)]
//! struct MyGraph {
//!     #[graph] graph: LinkedListGraph,
//!     #[nodeattrs(NodeData)] nodedata: Vec<NodeData>,
//!     #[edgeattrs(EdgeData)] edgedata: Vec<EdgeData>,
//! }
//!
//! #[derive(Graph)]
//! struct MyGraph2 {
//!     #[graph] graph: LinkedListGraph,
//!     #[nodeattrs(NodeData)] nodedata: Vec<NodeData>,
//!     #[edgeattrs(EdgeData)] edgedata: Vec<EdgeData>,
//! }
//!
//! impl From<LinkedListGraph> for MyGraph {
//!     fn from(g: LinkedListGraph) -> MyGraph {
//!         let n = g.num_nodes();
//!         let m = g.num_edges();
//!         MyGraph {
//!             graph: g,
//!             nodedata: vec![Default::default(); n],
//!             edgedata: vec![Default::default(); m],
//!         }
//!     }
//! }
//!
//! # fn main() {
//! let mut g: MyGraph = classes::peterson::<LinkedListGraph>().into();
//! let (s, t) = (g.id2node(0), g.id2node(4));
//! g.node_mut(s).balance = 1.0;
//! g.node_mut(t).balance = -1.0;
//! for eid in 0..g.num_edges() { g.edge_mut(g.id2edge(eid)).bound = eid as f64; }
//!
//! {
//!     let (g, mut attrs) = g.split();
//!     // this would also work: let (g, mut attrs) = attrs.split();
//!     for u in g.nodes() {
//!         for (e, v) in g.outedges(u) {
//!             attrs.node_mut(v).balance = 42.0 + g.node_id(v) as f64;
//!         }
//!     }
//! }
//! for u in g.nodes() {
//!     assert_eq!(g.node(u).balance, 42.0 + g.node_id(u) as f64);
//! }
//! # }
//! ```
//!

use quote::{format_ident, quote};
#[allow(unused_imports)]
use syn::Token; // we use the `Token!` macro
use syn::{self, parse_quote};

use proc_macro::TokenStream;
use proc_macro2::Span;
use proc_macro2::TokenStream as TokenStream2;

#[derive(Debug, PartialEq)]
struct Var {
    name: syn::Ident,
    typ: syn::Type,
}

struct StructInfo {
    name: syn::Ident,
    visibility: syn::Visibility,
    generic_parameters: syn::Generics,

    graph: Var,

    node_attr: Option<Var>,
    edge_attr: Option<Var>,
}

fn parse_graph_structure(input: TokenStream2) -> StructInfo {
    let mut ast: syn::DeriveInput = syn::parse2(input).unwrap();
    let vis = &ast.vis;
    let name = &ast.ident;
    let generics = &mut ast.generics;

    let mut have_graph_attr = false;
    let mut graph = None;

    let mut node_attr = None;
    let mut edge_attr = None;

    // Collect all fields with attribute #[graph] or named `graph`.
    if let syn::Data::Struct(syn::DataStruct { ref fields, .. }) = ast.data {
        for (i, ref field) in fields.iter().enumerate() {
            if let Some(attrvar) = get_attr_var(field, i, "nodeattrs") {
                if node_attr.is_some() {
                    panic!("Only one field can be tagged `nodeattrs`");
                }
                node_attr = Some(attrvar);
            }

            if let Some(attrvar) = get_attr_var(field, i, "edgeattrs") {
                if edge_attr.is_some() {
                    panic!("Only one field can be tagged `edgeattrs`");
                }
                edge_attr = Some(attrvar);
            }

            if field.attrs.iter().any(|attr| attr.path.is_ident("graph")) {
                if have_graph_attr {
                    panic!("Only one field can be tagged `graph`");
                }
                have_graph_attr = true;
            } else if field.ident.as_ref().map(|s| s == "graph").unwrap_or(false) {
                if have_graph_attr {
                    continue;
                }
            } else {
                continue;
            }

            graph = Some(Var {
                name: field.ident.clone().unwrap_or_else(|| format_ident!("{}", i)),
                typ: field.ty.clone(),
            });
        }
    }

    StructInfo {
        name: name.clone(),
        visibility: vis.clone(),
        generic_parameters: generics.clone(),

        graph: graph.expect("No field `graph` or field with attribute #[graph] found"),
        node_attr,
        edge_attr,
    }
}

fn get_attr_var(field: &syn::Field, index: usize, attrname: &str) -> Option<Var> {
    for attr in field.attrs.iter() {
        if attr.path.is_ident(attrname) {
            return Some(Var {
                name: field.ident.clone().unwrap_or_else(|| format_ident!("{}", index)),
                typ: match attr
                    .parse_meta()
                    .unwrap_or_else(|_| panic!("Missing `{}` type", attrname))
                {
                    syn::Meta::List(list) => {
                        assert_eq!(
                            list.nested.len(),
                            1,
                            "expected exactly one type argument for `{}`",
                            attrname
                        );
                        if let Some(syn::NestedMeta::Meta(syn::Meta::Path(id))) = list.nested.iter().next() {
                            // TODO: This is actually not very sophisticated. It only
                            // extracts plain path types without generics (nothing fancy).
                            syn::Type::Path(syn::TypePath {
                                qself: None,
                                path: id.clone(),
                            })
                        } else {
                            panic!("expected exactly one type argument for `{}`", attrname);
                        }
                    }
                    _ => panic!("expected exactly one type argument for `{}`", attrname),
                },
            });
        }
    }

    None
}

fn graph_derive(input: TokenStream2) -> TokenStream2 {
    let graph = parse_graph_structure(input);

    let name = graph.name;
    let generics = graph.generic_parameters;
    let vis = graph.visibility;
    let var = graph.graph.name;
    let typ = graph.graph.typ;
    let nodeattrs = graph.node_attr;
    let edgeattrs = graph.edge_attr;

    // Implement all graph traits the nested graph implements.

    let ident_it = format_ident!("{}", "__rs_graph_I__");
    let ident_lt = syn::Lifetime::new("'__rs_graph_z__", Span::call_site());
    let ty_generics = generics.clone();
    let mut it_generics = generics.clone();
    it_generics
        .params
        .push(syn::GenericParam::Type(ident_it.clone().into()));
    // generics
    //     .params
    //     .push(syn::GenericParam::Lifetime(syn::LifetimeDef::new(ident_lt.clone())));

    let gens = [
        "GraphType",
        "FiniteGraph",
        "FiniteDigraph",
        "Undirected",
        "Directed",
        "IndexGraph",
    ]
    .iter()
    .map(|name| {
        let name = format_ident!("{}", name);
        let mut g = generics.clone();
        g.make_where_clause()
            .predicates
            .push(parse_quote!(#typ: ::rs_graph::traits::#name));
        //.push(parse_quote!(#typ: ::rs_graph::traits::#name<#ident_lt>));
        g
    })
    .collect::<Vec<_>>();

    let (basegraph_impl, _, basegraph_where) = gens[0].split_for_impl();
    let (finitegraph_impl, _, finitegraph_where) = gens[1].split_for_impl();
    let (finitedigraph_impl, _, finitedigraph_where) = gens[2].split_for_impl();
    let (undirected_impl, _, undirected_where) = gens[3].split_for_impl();
    let (directed_impl, _, directed_where) = gens[4].split_for_impl();
    let (indexgraph_impl, _, indexgraph_where) = gens[5].split_for_impl();

    let mut expanded = quote! {
        impl #it_generics ::rs_graph::traits::GraphIterator<#name #ty_generics> for ::rs_graph::traits::refs::WrapIt<#ident_it> where #ident_it: GraphIterator<#typ> {
            type Item = #ident_it :: Item;

            fn next(&mut self, g: &#name #ty_generics) -> Option<Self::Item> {
                self.0.next(&g.#var)
            }
        }

        impl #basegraph_impl ::rs_graph::traits::GraphType for #name #ty_generics #basegraph_where
        {
            type Node<#ident_lt> = <#typ as ::rs_graph::traits::GraphType>::Node<#ident_lt>;

            type Edge<#ident_lt> = <#typ as ::rs_graph::traits::GraphType>::Edge<#ident_lt>;
        }

        impl #finitegraph_impl ::rs_graph::traits::FiniteGraph for #name #ty_generics #finitegraph_where
        {
            type NodeIt<#ident_lt> where Self: #ident_lt = ::rs_graph::traits::refs::WrapIt<<#typ as ::rs_graph::traits::FiniteGraph>::NodeIt<#ident_lt>>;

            type EdgeIt<#ident_lt> where Self: #ident_lt = ::rs_graph::traits::refs::WrapIt<<#typ as ::rs_graph::traits::FiniteGraph>::EdgeIt<#ident_lt>>;

            fn num_nodes(&self) -> usize {
                self.#var.num_nodes()
            }

            fn num_edges(&self) -> usize {
                self.#var.num_edges()
            }

            fn nodes_iter(&self) -> Self::NodeIt<'_> {
                ::rs_graph::traits::refs::WrapIt(self.#var.nodes_iter())
            }

            fn edges_iter(&self) -> Self::EdgeIt<'_> {
                ::rs_graph::traits::refs::WrapIt(self.#var.edges_iter())
            }

            fn enodes(&self, e: Self::Edge<'_>) -> (Self::Node<'_>, Self::Node<'_>) {
                self.#var.enodes(e)
            }
        }

        impl #finitedigraph_impl ::rs_graph::traits::FiniteDigraph for #name #ty_generics #finitedigraph_where
        {
            fn src(&self, e: Self::Edge<'_>) -> Self::Node<'_> {
                self.#var.src(e)
            }

            fn snk(&self, e: Self::Edge<'_>) -> Self::Node<'_> {
                self.#var.snk(e)
            }
        }

        impl #undirected_impl ::rs_graph::traits::Undirected for #name #ty_generics #undirected_where
        {
            type NeighIt<#ident_lt> where Self: #ident_lt = ::rs_graph::traits::refs::WrapIt<<#typ as ::rs_graph::traits::Undirected>::NeighIt<#ident_lt>>;

            fn neigh_iter(&self, u: Self::Node<'_>) -> Self::NeighIt<'_> {
                ::rs_graph::traits::refs::WrapIt(self.#var.neigh_iter(u))
            }
        }

        impl #directed_impl ::rs_graph::traits::Directed for #name #ty_generics #directed_where
        {
            type OutIt<#ident_lt> where Self: #ident_lt = ::rs_graph::traits::refs::WrapIt<<#typ as ::rs_graph::traits::Directed>::OutIt<#ident_lt>>;

            type InIt<#ident_lt> where Self: #ident_lt = ::rs_graph::traits::refs::WrapIt<<#typ as ::rs_graph::traits::Directed>::InIt<#ident_lt>>;

            type IncidentIt<#ident_lt> where Self: #ident_lt = ::rs_graph::traits::refs::WrapIt<<#typ as ::rs_graph::traits::Directed>::IncidentIt<#ident_lt>>;

            type DirectedEdge<#ident_lt> where Self: #ident_lt = <#typ as ::rs_graph::traits::Directed>::DirectedEdge<#ident_lt>;

            fn out_iter(&self, u: Self::Node<'_>) -> Self::OutIt<'_> {
                ::rs_graph::traits::refs::WrapIt(self.#var.out_iter(u))
            }

            fn in_iter(&self, u: Self::Node<'_>) -> Self::InIt<'_> {
                ::rs_graph::traits::refs::WrapIt(self.#var.in_iter(u))
            }

            fn incident_iter(&self, u: Self::Node<'_>) -> Self::IncidentIt<'_> {
                ::rs_graph::traits::refs::WrapIt(self.#var.incident_iter(u))
            }
        }

        impl #indexgraph_impl ::rs_graph::traits::IndexGraph for #name #ty_generics #indexgraph_where
        {
            fn node_id(&self, u: Self::Node<'_>) -> usize {
                self.#var.node_id(u)
            }

            fn id2node(&self, id: usize) -> Self::Node<'_> {
                self.#var.id2node(id)
            }

            fn edge_id(&self, e: Self::Edge<'_>) -> usize {
                self.#var.edge_id(e)
            }

            fn id2edge(&self, id: usize) -> Self::Edge<'_> {
                self.#var.id2edge(id)
            }
        }
    };

    let mut attrdefs = TokenStream2::new();
    let mut attrsets = TokenStream2::new();
    let mut attrsets2 = TokenStream2::new();
    if let Some(Var {
        name: attrvar,
        typ: attrtyp,
    }) = nodeattrs.as_ref()
    {
        expanded.extend(quote! {
            impl #indexgraph_impl ::rs_graph::attributes::NodeAttributes<#typ, #attrtyp> for #name #ty_generics #indexgraph_where
            {
                fn node(&self, u: <#typ as ::rs_graph::traits::GraphType>::Node<'_>) -> &#attrtyp {
                    &self.#attrvar[self.#var.node_id(u)]
                }

                fn node_mut(&mut self, u: <#typ as ::rs_graph::traits::GraphType>::Node<'_>) -> &mut #attrtyp {
                    &mut self.#attrvar[self.#var.node_id(u)]
                }
            }
        });
        attrdefs.extend(quote!(nodeattrs: &#ident_lt mut [#attrtyp],));
        attrsets.extend(quote!(nodeattrs: &mut self.#attrvar,));
        attrsets2.extend(quote!(nodeattrs: self.nodeattrs,));
    }

    if let Some(Var {
        name: attrvar,
        typ: attrtyp,
    }) = edgeattrs.as_ref()
    {
        expanded.extend(quote! {
            impl #indexgraph_impl ::rs_graph::attributes::EdgeAttributes<#typ, #attrtyp> for #name #ty_generics #indexgraph_where
            {
                fn edge(&self, u: <#typ as ::rs_graph::traits::GraphType>::Edge<'_>) -> &#attrtyp {
                    &self.#attrvar[self.#var.edge_id(u)]
                }

                fn edge_mut(&mut self, u: <#typ as ::rs_graph::traits::GraphType>::Edge<'_>) -> &mut #attrtyp {
                    &mut self.#attrvar[self.#var.edge_id(u)]
                }
            }
        });
        attrdefs.extend(quote!(edgeattrs: &#ident_lt mut [#attrtyp],));
        attrsets.extend(quote!(edgeattrs: &mut self.#attrvar,));
        attrsets2.extend(quote!(edgeattrs: self.edgeattrs,));
    }

    if !attrdefs.is_empty() {
        let (_, orig_ty_generics, orig_where) = ty_generics.split_for_impl();
        let attrstruct = format_ident!("{}_Attributes", name);
        expanded.extend(quote! {
            #vis struct #attrstruct<#ident_lt> {
                graph: &#ident_lt #typ,
                #attrdefs
            }

            impl #basegraph_impl ::rs_graph::attributes::AttributedGraph for #name #orig_ty_generics #orig_where {
                type Graph = #typ;
                type Attributes<#ident_lt> = #attrstruct<#ident_lt>;
                fn split(&mut self) -> (&#typ, #attrstruct<'_>) {
                        (
                            &self.#var,
                            #attrstruct {
                                graph: &self.#var,
                                #attrsets
                            },
                        )
                }
            }

            // impl ::rs_graph::attributes::AttributedGraph for #attrstruct {
            //     type Graph = #typ;
            //     type Attributes<#ident_lt> = #attrstruct<#ident_lt>;
            //     fn split(&mut self) -> (&#typ, #attrstruct<'_>) {
            //         (self.graph, #attrstruct {
            //             graph: self.graph,
            //             #attrsets2
            //         })
            //     }
            // }
        });

        if let Some(Var { typ: attrtyp, .. }) = nodeattrs.as_ref() {
            expanded.extend(quote! {
                impl<#ident_lt> #indexgraph_impl ::rs_graph::attributes::NodeAttributes<#typ, #attrtyp> for #attrstruct <#ident_lt> #indexgraph_where
                {
                    fn node(&self, u: <#typ as ::rs_graph::traits::GraphType>::Node<'_>) -> &#attrtyp {
                        &self.nodeattrs[self.#var.node_id(u)]
                    }

                    fn node_mut(&mut self, u: <#typ as ::rs_graph::traits::GraphType>::Node<'_>) -> &mut #attrtyp {
                        &mut self.nodeattrs[self.#var.node_id(u)]
                    }
                }
            });
        }

        if let Some(Var { typ: attrtyp, .. }) = edgeattrs.as_ref() {
            expanded.extend(quote! {
                impl<#ident_lt> #indexgraph_impl ::rs_graph::attributes::EdgeAttributes<#typ, #attrtyp> for #attrstruct <#ident_lt> #indexgraph_where
                {
                    fn edge(&self, u: <#typ as ::rs_graph::traits::GraphType>::Edge<'_>) -> &#attrtyp {
                        &self.edgeattrs[self.#var.edge_id(u)]
                    }

                    fn edge_mut(&mut self, u: <#typ as ::rs_graph::traits::GraphType>::Edge<'_>) -> &mut #attrtyp {
                        &mut self.edgeattrs[self.#var.edge_id(u)]
                    }
                }
            });
        }
    }

    expanded
}

#[proc_macro_derive(Graph, attributes(graph, nodeattrs, edgeattrs))]
pub fn graph(input: TokenStream) -> TokenStream {
    graph_derive(TokenStream2::from(input)).into()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(name: &str, vartyp: &str) -> Var {
        Var {
            name: format_ident!("{}", name),
            typ: typ(vartyp),
        }
    }

    fn typ(t: &str) -> syn::Type {
        syn::TypePath {
            qself: None,
            path: format_ident!("{}", t).into(),
        }
        .into()
    }

    #[test]
    fn test_parse_simple_graph() {
        let g = parse_graph_structure(quote!(
            struct MyGraph {
                graph: Graph,
                other: usize,
            }
        ));
        assert_eq!(g.name, "MyGraph");
        assert_eq!(g.visibility, syn::Visibility::Inherited);
        assert!(g.generic_parameters.params.is_empty());
        assert!(g.generic_parameters.where_clause.is_none());
        assert_eq!(g.graph, var("graph", "Graph"));
        assert!(g.node_attr.is_none());
        assert!(g.edge_attr.is_none());
    }

    #[test]
    fn test_parse_simple_graph_with_graph_tag() {
        let g = parse_graph_structure(quote!(
            struct MyGraph {
                graph: usize,
                #[graph]
                other: Graph,
            }
        ));
        assert_eq!(g.name, "MyGraph");
        assert_eq!(g.visibility, syn::Visibility::Inherited);
        assert!(g.generic_parameters.params.is_empty());
        assert!(g.generic_parameters.where_clause.is_none());
        assert_eq!(g.graph, var("other", "Graph"));
        assert!(g.node_attr.is_none());
        assert!(g.edge_attr.is_none());
    }

    #[test]
    #[should_panic]
    fn test_parse_simple_graph_without_graph_tag() {
        parse_graph_structure(quote!(
            struct MyGraph {
                something: usize,
                other: Graph,
            }
        ));
    }

    #[test]
    #[should_panic]
    fn test_parse_simple_graph_with_multiple_graph_tags() {
        parse_graph_structure(quote!(
            struct MyGraph {
                #[graph]
                something: Graph,
                #[graph]
                other: Graph,
            }
        ));
    }

    #[test]
    fn test_parse_graph_with_node_attr() {
        let g = parse_graph_structure(quote!(
            struct MyGraph {
                graph: Graph,
                #[nodeattrs(NodeData)]
                nodes: Vec<NodeData>,
            }
        ));
        assert_eq!(g.name, "MyGraph");
        assert_eq!(g.visibility, syn::Visibility::Inherited);
        assert!(g.generic_parameters.params.is_empty());
        assert!(g.generic_parameters.where_clause.is_none());
        assert_eq!(g.graph, var("graph", "Graph"));
        assert_eq!(g.node_attr, Some(var("nodes", "NodeData")));
        assert!(g.edge_attr.is_none());
    }

    #[test]
    #[should_panic]
    fn test_parse_graph_with_multiple_node_attr() {
        parse_graph_structure(quote!(
            struct MyGraph {
                graph: Graph,
                #[nodeattrs(NodeData)]
                nodes: Vec<NodeData>,
                #[nodeattrs(NodeData)]
                nodes2: Vec<NodeData>,
            }
        ));
    }

    #[test]
    fn test_parse_graph_with_edge_attr() {
        let g = parse_graph_structure(quote!(
            struct MyGraph {
                graph: Graph,
                #[edgeattrs(EdgeData)]
                edges: Vec<EdgeData>,
            }
        ));
        assert_eq!(g.name, "MyGraph");
        assert_eq!(g.visibility, syn::Visibility::Inherited);
        assert!(g.generic_parameters.params.is_empty());
        assert!(g.generic_parameters.where_clause.is_none());
        assert_eq!(g.graph, var("graph", "Graph"));
        assert!(g.node_attr.is_none());
        assert_eq!(g.edge_attr, Some(var("edges", "EdgeData")));
    }

    #[test]
    #[should_panic]
    fn test_parse_graph_with_multiple_edge_attr() {
        parse_graph_structure(quote!(
            struct MyGraph {
                graph: Graph,
                #[edgeattrs(EdgeData)]
                edges: Vec<EdgeData>,
                #[edgeattrs(EdgeData)]
                edges2: Vec<EdgeData>,
            }
        ));
    }

    #[test]
    fn test_parse_graph_with_visiblity() {
        let g = parse_graph_structure(quote!(
            pub struct MyGraph {
                graph: Graph,
                other: usize,
            }
        ));
        assert_eq!(g.name, "MyGraph");
        assert_eq!(
            g.visibility,
            syn::VisPublic {
                pub_token: <Token![pub]>::default().into()
            }
            .into()
        );
        assert!(g.generic_parameters.params.is_empty());
        assert!(g.generic_parameters.where_clause.is_none());
        assert_eq!(g.graph, var("graph", "Graph"));
        assert!(g.node_attr.is_none());
        assert!(g.edge_attr.is_none());
    }

    #[test]
    fn test_graph_traits() {
        let generated = graph_derive(quote!(
            struct MyGraph {
                graph: Graph,
            }
        ));

        let expected = quote! {
            impl<__rs_graph_I__>::rs_graph::traits::GraphIterator<MyGraph>
                for ::rs_graph::traits::refs::WrapIt<__rs_graph_I__>
            where
                __rs_graph_I__: GraphIterator<Graph>
            {
                type Item = __rs_graph_I__::Item;
                fn next(&mut self, g: &MyGraph) -> Option<Self::Item> {
                    self.0.next(&g.graph)
                }
            }
        };

        assert!(generated.to_string().starts_with(&expected.to_string()));
    }
}
